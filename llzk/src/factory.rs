use std::{
    collections::HashMap,
    hash::{DefaultHasher, Hash, Hasher},
};

use haloumi_synthesis::io::{AdviceIO, InstanceIO};
use llzk::{
    attributes::NamedAttribute,
    builder::OpBuilder,
    prelude::{
        dialect::r#struct::{self, helpers},
        *,
    },
};

use melior::{
    Context,
    ir::{Identifier, Location, Type},
};

use crate::{
    error::Error,
    members::{MemberKind, Members},
    state::LlzkCodegenState,
};

/// Generates a pseudo-filename for use in location metadata in the generated IR.
pub fn filename(name: &str, section: Option<&str>) -> String {
    use std::fmt::Write;
    const STRUCT: &str = "struct ";
    const SEP: &str = " | ";
    let mut s = String::with_capacity(
        STRUCT.len() + name.len() + section.map(|s| s.len() + SEP.len()).unwrap_or_default(),
    );
    write!(s, "{STRUCT}{name}").expect("write to string");
    if let Some(section) = section {
        write!(s, "{SEP}{section}").expect("write to string");
    }
    s
}

fn struct_def_op_location<'c>(context: &'c Context, name: &str, index: usize) -> Location<'c> {
    Location::new(context, filename(name, None).as_str(), index, 0)
}

#[derive(Debug)]
pub struct StructIO {
    name: String,
    private_inputs: usize,
    public_inputs: usize,
    private_outputs: usize,
    public_outputs: usize,
    callees: Vec<String>,
}

impl StructIO {
    fn fields(&self) -> impl Iterator<Item = MemberKind<'_>> {
        let public_outputs = MemberKind::outputs(0..self.public_outputs, true);
        let private_outputs = MemberKind::outputs(
            self.public_outputs..(self.public_outputs + self.private_outputs),
            false,
        );
        let callees = MemberKind::callees(&self.callees);

        public_outputs.chain(private_outputs).chain(callees)
    }

    pub fn callees_mapping(&self) -> HashMap<usize, String> {
        self.callees.iter().cloned().enumerate().collect()
    }

    fn inputs(&self) -> usize {
        self.public_inputs + self.private_inputs
    }

    pub fn args<'c>(
        &self,
        state: &LlzkCodegenState<'c>,
        struct_name: &str,
    ) -> Vec<(Type<'c>, Location<'c>)> {
        let public_filename = filename(struct_name, Some("public inputs"));
        let private_filename = filename(struct_name, Some("private inputs"));
        let public_locs = std::iter::repeat_n(&public_filename, self.public_inputs).enumerate();
        let private_locs = std::iter::repeat_n(&private_filename, self.private_inputs).enumerate();
        let locs = public_locs
            .chain(private_locs)
            .map(|(n, filename)| Location::new(state.context(), filename, n, 0));

        let types = std::iter::repeat_n(Type::from(state.felt_type()), self.inputs());

        std::iter::zip(types, locs).collect()
    }

    /// Returns the list of argument attributes for the struct's functions.
    pub fn arg_attrs<'c>(&self, ctx: &'c Context) -> Vec<Vec<NamedAttribute<'c>>> {
        let pub_attr = (
            Identifier::new(ctx, "llzk.pub"),
            PublicAttribute::new(ctx).into(),
        );
        std::iter::repeat_n(vec![pub_attr], self.public_inputs)
            .chain(std::iter::repeat_n(vec![], self.private_inputs))
            .collect()
    }

    pub fn from_io(
        name: String,
        advice: &AdviceIO,
        instance: &InstanceIO,
        callees: impl IntoIterator<Item = String>,
    ) -> Self {
        Self {
            name,
            private_inputs: advice.inputs().len(),
            public_inputs: instance.inputs().len(),
            private_outputs: advice.outputs().len(),
            public_outputs: instance.outputs().len(),
            callees: Vec::from_iter(callees),
        }
    }

    pub fn from_io_count(
        name: String,
        inputs: usize,
        outputs: usize,
        callees: impl IntoIterator<Item = String>,
    ) -> Self {
        Self {
            name,
            private_inputs: inputs,
            public_inputs: 0,
            private_outputs: 0,
            public_outputs: outputs,
            callees: Vec::from_iter(callees),
        }
    }

    pub fn callees_count(&self) -> usize {
        self.callees.len()
    }

    pub fn callee(&self, id: usize) -> Result<MemberKind<'_>, Error> {
        log::debug!("Requesting callee {id} (callees: {:?})", self.callees);
        self.callees
            .get(id)
            .map(|name| MemberKind::Callee { id, name })
            .ok_or_else(|| Error::MissingCalleeMember(self.name.clone(), id))
    }
}

pub fn create_struct<'c: 'v, 'v, 's: 'v>(
    builder: &OpBuilder<'c, '_>,
    state: &'s LlzkCodegenState<'c>,
    struct_name: &str,
    idx: usize,
    io: &StructIO,
    members: &Members<'c, 'v>,
) -> Result<StructDefOpRef<'c, 'v>, LlzkError> {
    log::debug!("context = {:?}", state.context());
    let loc = struct_def_op_location(state.context(), struct_name, idx);
    log::debug!("Struct location: {loc:?}");

    let func_args = io.args(state, struct_name);
    let arg_attrs = io.arg_attrs(state.context());

    log::debug!("Creating function with arguments: {func_args:?}");

    r#struct::def(builder, loc, struct_name, |builder| {
        for field in io.fields() {
            members.get(state, struct_name, builder, field)?;
        }

        let ty = StructType::from_str(state.context(), struct_name);
        helpers::compute_fn(builder, loc, ty, &func_args, Some(&arg_attrs))?;
        let func_op = helpers::constrain_fn(builder, loc, ty, &func_args, Some(&arg_attrs))?;
        let func_op = unsafe { FuncDefOpRefMut::from_raw(func_op.to_raw()) };
        func_op.set_allow_verif_ops_attr(true);

        Ok(())
    })
}
