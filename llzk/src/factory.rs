use std::collections::HashMap;

use haloumi_synthesis::io::{AdviceIO, InstanceIO};
use llzk::{attributes::NamedAttribute, prelude::*};

use melior::{
    Context,
    ir::{Identifier, Location, Operation, Type},
};

use crate::{error::Error, state::LlzkCodegenState};

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

/// Types of members the circuit could have.
#[derive(Debug)]
pub enum MemberKind<'s> {
    /// Advice cells.
    Advice { col: usize, row: usize },
    /// Fixed cells.
    Fixed { col: usize, row: usize },
    /// Subcomponents called by the circuit.
    Callee { name: &'s str, id: usize },
    /// Output of the circuit
    Output { id: usize, public: bool },
    /// A temporary
    Temp { id: usize },
}

impl MemberKind<'_> {
    /// String representation of the member's name.
    pub fn member_name(&self) -> String {
        match self {
            MemberKind::Advice { col, row } => format!("adv_{col}_{row}"),
            MemberKind::Fixed { col, row } => format!("fix_{col}_{row}"),
            MemberKind::Callee { name, id } => format!("subgrp_{name}_{id}"),
            MemberKind::Output { id, .. } => format!("out_{id}"),
            MemberKind::Temp { id } => format!("temp_{id}"),
        }
    }

    pub fn location<'c>(&self, context: &'c Context, struct_name: &str) -> Location<'c> {
        match self {
            MemberKind::Advice { col, row } => {
                let filename = filename(struct_name, Some("advice cell"));
                Location::new(context, &filename, *col, *row)
            }
            MemberKind::Fixed { col, row } => {
                let filename = filename(struct_name, Some("fixed cell"));
                Location::new(context, &filename, *col, *row)
            }
            MemberKind::Callee { name, id } => {
                let filename = filename(struct_name, Some(&format!("subgroup '{name}'")));
                Location::new(context, &filename, *id, 0)
            }
            MemberKind::Output { id, public } => {
                let section = if *public {
                    "public outputs"
                } else {
                    "private outputs"
                };
                let filename = filename(struct_name, Some(section));
                Location::new(context, &filename, *id, 0)
            }
            MemberKind::Temp { id } => {
                let filename = filename(struct_name, Some("Temporaries"));
                Location::new(context, &filename, *id, 0)
            }
        }
    }

    pub fn member_type<'c>(&self, state: &LlzkCodegenState<'c>) -> Type<'c> {
        match self {
            MemberKind::Advice { .. }
            | MemberKind::Fixed { .. }
            | MemberKind::Output { .. }
            | MemberKind::Temp { .. } => state.felt_type().into(),
            MemberKind::Callee { name, .. } => StructType::from_str(state.context(), name).into(),
        }
    }

    pub fn is_public(&self) -> bool {
        match self {
            MemberKind::Advice { .. }
            | MemberKind::Fixed { .. }
            | MemberKind::Callee { .. }
            | MemberKind::Temp { .. } => false,
            MemberKind::Output { public, .. } => *public,
        }
    }

    pub fn create_member_op<'c>(
        &self,
        state: &LlzkCodegenState<'c>,
        struct_name: &str,
    ) -> Result<MemberDefOp<'c>, LlzkError> {
        dialect::r#struct::member(
            self.location(state.context(), struct_name),
            &self.member_name(),
            self.member_type(state),
            false,
            self.is_public(),
        )
    }

    /// Returns an iterator of outputs set to either public or private with ids in the given range.
    fn outputs(range: impl IntoIterator<Item = usize>, public: bool) -> impl Iterator<Item = Self> {
        range
            .into_iter()
            .map(move |id| MemberKind::Output { id, public })
    }
}

impl<'m> MemberKind<'m> {
    /// Returns an iterator of callees taken from the names list.
    fn callees<S: AsRef<str> + 'm>(
        callees: impl IntoIterator<Item = &'m S>,
    ) -> impl Iterator<Item = Self> {
        callees
            .into_iter()
            .map(AsRef::as_ref)
            .enumerate()
            .map(|(id, name)| MemberKind::Callee { name, id })
    }
}

#[derive(Debug)]
pub struct StructIO {
    private_inputs: usize,
    public_inputs: usize,
    private_outputs: usize,
    public_outputs: usize,
    callees: Vec<String>,
}

impl StructIO {
    fn fields<'c>(
        &self,
        state: &LlzkCodegenState<'c>,
        struct_name: &str,
    ) -> impl Iterator<Item = Result<MemberDefOp<'c>, LlzkError>> {
        let public_outputs = MemberKind::outputs(0..self.public_outputs, true);
        let private_outputs = MemberKind::outputs(
            self.public_outputs..(self.public_outputs + self.private_outputs),
            false,
        );
        let callees = MemberKind::callees(&self.callees);

        public_outputs
            .chain(private_outputs)
            .chain(callees)
            .map(|m| m.create_member_op(state, struct_name))
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
        advice: &AdviceIO,
        instance: &InstanceIO,
        callees: impl IntoIterator<Item = String>,
    ) -> Self {
        Self {
            private_inputs: advice.inputs().len(),
            public_inputs: instance.inputs().len(),
            private_outputs: advice.outputs().len(),
            public_outputs: instance.outputs().len(),
            callees: Vec::from_iter(callees),
        }
    }

    pub fn from_io_count(
        inputs: usize,
        outputs: usize,
        callees: impl IntoIterator<Item = String>,
    ) -> Self {
        Self {
            private_inputs: inputs,
            public_inputs: 0,
            private_outputs: 0,
            public_outputs: outputs,
            callees: Vec::from_iter(callees),
        }
    }

    pub fn callee(&self, id: usize) -> Result<MemberKind<'_>, Error> {
        log::debug!("Requesting callee {id} (callees: {:?})", self.callees);
        self.callees
            .get(id)
            .map(|name| MemberKind::Callee { id, name })
            .ok_or(Error::MissingCalleeMember(id))
    }
}

pub fn create_struct<'c>(
    state: &LlzkCodegenState<'c>,
    struct_name: &str,
    idx: usize,
    io: &StructIO,
) -> Result<StructDefOp<'c>, LlzkError> {
    log::debug!("context = {:?}", state.context());
    let loc = struct_def_op_location(state.context(), struct_name, idx);
    log::debug!("Struct location: {loc:?}");
    let fields = io
        .fields(state, struct_name)
        .map(|r| r.map(Operation::from));

    let func_args = io.args(state, struct_name);
    let arg_attrs = io.arg_attrs(state.context());

    log::debug!("Creating function with arguments: {func_args:?}");

    let funcs = [
        dialect::r#struct::helpers::compute_fn(
            loc,
            StructType::from_str(state.context(), struct_name),
            &func_args,
            Some(&arg_attrs),
        )
        .map(Operation::from),
        dialect::r#struct::helpers::constrain_fn(
            loc,
            StructType::from_str(state.context(), struct_name),
            &func_args,
            Some(&arg_attrs),
        )
        .map(Operation::from),
    ];

    dialect::r#struct::def(loc, struct_name, fields.chain(funcs))
}
