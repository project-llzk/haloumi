//! Structs for handling calls between groups.

use eqv::{EqvRelation, equiv};
use haloumi_core::{eqv::SymbolicEqv, slot::Slot};
use haloumi_lowering::{
    Lowering,
    lowerable::{LowerableExpr, LowerableStmt},
};

use crate::{
    stmt::IRStmt,
    traits::{Canonicalize, ConstantFolding},
};

use super::GroupKey;

/// Data related to a single callsite
#[derive(Debug, Clone)]
pub struct CallSite<E> {
    name: String,
    callee: GroupKey,
    /// The index in the original groups array to the called group.
    callee_id: usize,
    inputs: Vec<E>,
    output_vars: Vec<Slot>,
    outputs: Vec<E>,
}

impl<E> CallSite<E> {
    /// Creates a new callsite.
    pub fn new(
        name: String,
        callee: GroupKey,
        callee_id: usize,
        inputs: Vec<E>,
        output_vars: Vec<Slot>,
        outputs: Vec<E>,
    ) -> Self {
        Self {
            name,
            callee,
            callee_id,
            inputs,
            output_vars,
            outputs,
        }
    }

    /// Returns the name of the callee.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Sets the name of the called group.
    pub fn set_name(&mut self, name: String) {
        self.name = name;
    }

    /// Returns the id of the callee.
    pub fn callee_id(&self) -> usize {
        self.callee_id
    }

    /// Sets the callee id.
    pub fn set_callee_id(&mut self, callee_id: usize) {
        self.callee_id = callee_id;
    }

    /// Returns the input arguments.
    pub fn inputs(&self) -> &[E] {
        &self.inputs
    }

    /// Returns the bindings to the call outputs.
    pub fn output_vars(&self) -> &[Slot] {
        &self.output_vars
    }

    /// Returns the outputs of the call.
    pub fn outputs(&self) -> &[E] {
        &self.outputs
    }

    /// Tries to transform the inner expression type into another.
    pub fn try_map<O, Err>(
        self,
        f: &mut impl FnMut(E) -> Result<O, Err>,
    ) -> Result<CallSite<O>, Err> {
        Ok(CallSite {
            name: self.name,
            callee: self.callee,
            callee_id: self.callee_id,
            inputs: self
                .inputs
                .into_iter()
                .map(&mut *f)
                .collect::<Result<Vec<_>, _>>()?,
            output_vars: self.output_vars,
            outputs: self
                .outputs
                .into_iter()
                .map(f)
                .collect::<Result<Vec<_>, _>>()?,
        })
    }
}

impl<E> ConstantFolding for CallSite<E>
where
    E: ConstantFolding,
{
    type Error = E::Error;

    type T = Vec<E::T>;

    fn constant_fold(&mut self) -> Result<(), Self::Error> {
        self.inputs.constant_fold()
    }

    fn const_value(&self) -> Option<Self::T> {
        self.inputs.const_value()
    }
}

impl<E> Canonicalize for CallSite<E>
where
    E: Canonicalize,
{
    fn canonicalize(&mut self) {
        self.inputs.canonicalize();
    }
}

impl<E> EqvRelation<CallSite<E>> for SymbolicEqv
where
    SymbolicEqv: EqvRelation<E>,
{
    /// Two callsites are equivalent if the call statement they represent is equivalent.
    fn equivalent(lhs: &CallSite<E>, rhs: &CallSite<E>) -> bool {
        lhs.callee == rhs.callee
            && equiv! { Self | &lhs.inputs, &rhs.inputs }
            && equiv! { Self | &lhs.outputs, &rhs.outputs }
    }
}

impl<E> LowerableStmt for CallSite<E>
where
    E: LowerableExpr + From<Slot>,
{
    fn lower<L>(self, l: &L) -> haloumi_lowering::Result<()>
    where
        L: Lowering + ?Sized,
    {
        let inputs: Vec<_> = self
            .inputs
            .into_iter()
            .map(|e| e.lower(l))
            .collect::<Result<_, _>>()?;
        l.generate_call(self.name.as_str(), &inputs, &self.output_vars)?;
        // The call statement creates variables that we need to constraint against the actual
        // outputs.
        for (lhs, rhs) in std::iter::zip(self.outputs, self.output_vars.into_iter().map(Into::into))
        {
            IRStmt::eq(lhs, rhs).lower(l)?
        }
        Ok(())
    }
}
