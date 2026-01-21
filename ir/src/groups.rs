//! IR for representing groups.

use crate::{
    groups::callsite::CallSite,
    printer::IRPrintable,
    stmt::IRStmt,
    traits::{Canonicalize, ConstantFolding},
};
use eqv::{EqvRelation, equiv};
use haloumi_core::eqv::SymbolicEqv;
use haloumi_lowering::{
    Lowering,
    lowerable::{LowerableExpr, LowerableStmt},
};
use std::fmt::Write;
use thiserror::Error;

/// Uniquely identifies groups that represent the same semantics.
pub type GroupKey = u64;

pub mod callsite;

/// Body of a group.
#[derive(Debug, Clone)]
pub struct IRGroup<E> {
    name: String,
    /// Index in the original groups array.
    id: usize,
    input_count: usize,
    output_count: usize,
    key: Option<GroupKey>,
    gates: IRStmt<E>,
    eq_constraints: IRStmt<E>,
    callsites: Vec<CallSite<E>>,
    lookups: IRStmt<E>,
    injected: Vec<IRStmt<E>>,
    generate_debug_comments: bool,
}

impl<E> IRGroup<E> {
    /// Creates a new empty group.
    pub fn new(name: String, id: usize) -> Self {
        Self {
            name,
            id,
            input_count: Default::default(),
            output_count: Default::default(),
            key: Default::default(),
            gates: Default::default(),
            eq_constraints: Default::default(),
            callsites: Default::default(),
            lookups: Default::default(),
            injected: Default::default(),
            generate_debug_comments: Default::default(),
        }
    }

    /// Updates the input count of the group.
    pub fn with_input_count(mut self, input_count: usize) -> Self {
        self.input_count = input_count;
        self
    }

    /// Updates the output count of the group.
    pub fn with_output_count(mut self, output_count: usize) -> Self {
        self.output_count = output_count;
        self
    }

    /// Updates the group key.
    pub fn with_key(mut self, key: Option<GroupKey>) -> Self {
        self.key = key;
        self
    }

    /// Removes the group key.
    pub fn no_key(mut self) -> Self {
        self.key = None;
        self
    }

    /// Updates the IR of the PLONK gates.
    pub fn with_gates(mut self, gates: impl IntoIterator<Item = IRStmt<E>>) -> Self {
        self.gates = IRStmt::from_iter(gates);
        self
    }

    /// Updates the IR of the copy constraints.
    pub fn with_copy_constraints(
        mut self,
        constraints: impl IntoIterator<Item = IRStmt<E>>,
    ) -> Self {
        self.eq_constraints = IRStmt::from_iter(constraints);
        self
    }

    /// Adds a callsite to the group.
    pub fn with_callsites(mut self, callsites: impl IntoIterator<Item = CallSite<E>>) -> Self {
        self.callsites = Vec::from_iter(callsites);
        self
    }

    /// Updates the IR of the lookups.
    pub fn with_lookups(mut self, lookups: impl IntoIterator<Item = IRStmt<E>>) -> Self {
        self.lookups = IRStmt::from_iter(lookups);
        self
    }

    /// Injects IR into the body of the group.
    pub fn inject(&mut self, ir: IRStmt<E>) {
        self.injected.push(ir);
    }

    /// Sets the flag that control the generation of debug comments.
    pub fn do_debug_comments(mut self, do_it: bool) -> Self {
        self.generate_debug_comments = do_it;
        self
    }

    /// Returns true if the group is the top-level.
    pub fn is_main(&self) -> bool {
        self.key.is_none()
    }

    /// Returns the name of the group.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns a mutable reference to the group's name.
    pub fn name_mut(&mut self) -> &mut String {
        &mut self.name
    }

    /// Returns the id of the group.
    pub fn id(&self) -> usize {
        self.id
    }

    /// Sets the id of the group.
    pub fn set_id(&mut self, id: usize) {
        self.id = id;
    }

    /// Returns the number of inputs.
    pub fn input_count(&self) -> usize {
        self.input_count
    }

    /// Returns the number of outputs.
    pub fn output_count(&self) -> usize {
        self.output_count
    }

    /// Returns the key of the group.
    pub fn key(&self) -> Option<GroupKey> {
        self.key
    }

    /// Returns a referece to the callsites.
    pub fn callsites(&self) -> &[CallSite<E>] {
        &self.callsites
    }

    /// Returns a mutable referece to the callsites.
    pub fn callsites_mut(&mut self) -> &mut Vec<CallSite<E>> {
        &mut self.callsites
    }

    /// Returns an iterator with all the [`IRStmt`] in the group.
    pub fn statements(&self) -> impl Iterator<Item = &IRStmt<E>> {
        self.gates
            .iter()
            .chain(self.eq_constraints.iter())
            .chain(self.lookups.iter())
            .chain(self.injected.iter().flatten())
    }

    /// Tries to convert the inner expression type to another.
    pub fn try_map<O, Err>(
        self,
        f: &mut impl FnMut(E) -> Result<O, Err>,
    ) -> Result<IRGroup<O>, Err> {
        Ok(IRGroup {
            name: self.name,
            id: self.id,
            input_count: self.input_count,
            output_count: self.output_count,
            key: self.key,
            gates: self.gates.try_map(f)?,
            eq_constraints: self.eq_constraints.try_map(f)?,
            callsites: self
                .callsites
                .into_iter()
                .map(|cs| cs.try_map(f))
                .collect::<Result<Vec<_>, _>>()?,
            lookups: self.lookups.try_map(f)?,
            injected: self
                .injected
                .into_iter()
                .map(|i| i.try_map(f))
                .collect::<Result<Vec<_>, _>>()?,
            generate_debug_comments: self.generate_debug_comments,
        })
    }

    fn validate_callsite(
        &self,
        callsite: &CallSite<E>,
        groups: &[Self],
    ) -> Result<(), ValidationErrors> {
        let callee_id = callsite.callee_id();
        let callee = groups
            .get(callee_id)
            .ok_or(ValidationErrors::CalleeNotFound { callee_id })?;
        if callee.id() != callsite.callee_id() {
            return Err(ValidationErrors::WrongCallee {
                callsite_name: callsite.name().to_string(),
                callsite_id: callee_id,
                callee_name: callee.name().to_string(),
                callee_id: callee.id(),
            });
        }
        if callee.input_count != callsite.inputs().len() {
            return Err(ValidationErrors::UnexpectedInputs {
                callee_name: callee.name().to_string(),
                callee_id: callee.id(),
                callee_count: callee.input_count,
                callsite_count: callsite.inputs().len(),
            });
        }
        if callee.output_count != callsite.outputs().len() {
            return Err(ValidationErrors::UnexpectedOutputs {
                callee_name: callee.name().to_string(),
                callee_id: callee.id(),
                callee_count: callee.output_count,
                callsite_count: callsite.outputs().len(),
            });
        }
        if callsite.outputs().len() != callsite.output_vars().len() {
            return Err(ValidationErrors::UnexpectedOutputsVars {
                callsite_name: callsite.name().to_string(),
                callsite_id: callee_id,
                callsite_count: callsite.outputs().len(),
                callsite_vars_count: callsite.output_vars().len(),
            });
        }

        Ok(())
    }

    /// Validates the IR in the group.
    pub fn validate(&self, groups: &[Self]) -> (Result<(), ValidationFailed>, Vec<String>) {
        let mut errors = vec![];

        // Check 1. Consistency of callsites arity.
        for (call_no, callsite) in self.callsites().iter().enumerate() {
            if let Err(err) = self.validate_callsite(callsite, groups) {
                errors.push(format!("On callsite {call_no}: {err}"));
            }
        }

        // Return errors if any.
        (
            if errors.is_empty() {
                Ok(())
            } else {
                Err(ValidationFailed {
                    name: self.name.clone(),
                    error_count: errors.len(),
                })
            },
            errors,
        )
    }

    /// Returns a mutable reference to the copy constraints.
    pub fn eq_constraints_mut(&mut self) -> &mut IRStmt<E> {
        &mut self.eq_constraints
    }
}

/// Error type for when validation fails.
#[derive(Error, Debug)]
#[error("Validation of group {name} failed with {error_count} errors")]
pub struct ValidationFailed {
    pub(crate) name: String,
    pub(crate) error_count: usize,
}

impl ValidationFailed {
    /// Returns the number of errors
    pub fn error_count(&self) -> usize {
        self.error_count
    }
}

#[derive(Error, Debug)]
enum ValidationErrors {
    #[error("Callee with id {callee_id} was not found")]
    CalleeNotFound { callee_id: usize },
    #[error(
        "Callsite points to \"{callsite_name}\" ({callsite_id}) but callee was \"{callee_name}\" ({callee_id})"
    )]
    WrongCallee {
        callsite_name: String,
        callsite_id: usize,
        callee_name: String,
        callee_id: usize,
    },
    #[error(
        "Callee \"{callee_name}\" ({callee_id}) was expecting {callee_count} inputs but callsite has {callsite_count}"
    )]
    UnexpectedInputs {
        callee_name: String,
        callee_id: usize,
        callee_count: usize,
        callsite_count: usize,
    },
    #[error(
        "Callee \"{callee_name}\" ({callee_id}) was expecting {callee_count} outputs but callsite has {callsite_count}"
    )]
    UnexpectedOutputs {
        callee_name: String,
        callee_id: usize,
        callee_count: usize,
        callsite_count: usize,
    },
    #[error(
        "Call to \"{callsite_name}\" ({callsite_id}) has {callsite_count} outputs but declared {callsite_vars_count} output variables"
    )]
    UnexpectedOutputsVars {
        callsite_name: String,
        callsite_id: usize,
        callsite_count: usize,
        callsite_vars_count: usize,
    },
}

impl<E: ConstantFolding> ConstantFolding for IRGroup<E>
where
    IRStmt<E>: ConstantFolding,
{
    type Error = ConstantFoldingError<E>;

    type T = ();

    fn constant_fold(&mut self) -> Result<(), Self::Error> {
        self.gates
            .constant_fold()
            .map_err(ConstantFoldingError::Stmt)?;
        self.eq_constraints
            .constant_fold()
            .map_err(ConstantFoldingError::Stmt)?;
        self.lookups
            .constant_fold()
            .map_err(ConstantFoldingError::Stmt)?;
        self.callsites
            .constant_fold()
            .map_err(ConstantFoldingError::CallsiteArg)?;
        self.injected
            .constant_fold()
            .map_err(ConstantFoldingError::Stmt)
    }
}

/// Error type for constant folding of [`IRGroup`].
#[derive(Error)]
pub enum ConstantFoldingError<E>
where
    IRStmt<E>: ConstantFolding,
    E: ConstantFolding,
{
    /// Case where the error happened while folding a statement.
    #[error(transparent)]
    Stmt(<IRStmt<E> as ConstantFolding>::Error),
    /// Case where the error happened while folding a callsite argument.
    #[error(transparent)]
    CallsiteArg(<E as ConstantFolding>::Error),
}

impl<E, Err1, Err2> std::fmt::Debug for ConstantFoldingError<E>
where
    IRStmt<E>: ConstantFolding<Error = Err1>,
    E: ConstantFolding<Error = Err2>,
    Err1: std::fmt::Debug,
    Err2: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Stmt(e) => std::fmt::Debug::fmt(e, f),
            Self::CallsiteArg(e) => std::fmt::Debug::fmt(e, f),
        }
    }
}

impl<E> Canonicalize for IRGroup<E>
where
    IRStmt<E>: Canonicalize,
    CallSite<E>: Canonicalize,
{
    fn canonicalize(&mut self) {
        self.gates.canonicalize();
        self.eq_constraints.canonicalize();
        self.lookups.canonicalize();
        self.callsites.canonicalize();
        self.injected.canonicalize();
    }
}

impl<E> EqvRelation<IRGroup<E>> for SymbolicEqv
where
    SymbolicEqv: EqvRelation<E>,
{
    /// Two groups are equivalent if the code they represent is equivalent and have the same key.
    ///
    /// Special case is main which is never equivalent to anything.
    fn equivalent(lhs: &IRGroup<E>, rhs: &IRGroup<E>) -> bool {
        // Main is never equivalent to others
        if lhs.is_main() || rhs.is_main() {
            return false;
        }

        let lhs_key = lhs.key.unwrap();
        let rhs_key = rhs.key.unwrap();

        let k = lhs_key == rhs_key;
        log::debug!("[equivalent({} ~ {})] key: {k}", lhs.id(), rhs.id());
        let io = lhs.input_count == rhs.input_count && lhs.output_count == rhs.output_count;
        log::debug!("[equivalent({} ~ {})] io: {io}", lhs.id(), rhs.id());
        let gates = equiv! { Self | &lhs.gates, &rhs.gates };
        log::debug!("[equivalent({} ~ {})] gates: {gates}", lhs.id(), rhs.id());
        let eqc = equiv! { Self | &lhs.eq_constraints, &rhs.eq_constraints };
        log::debug!("[equivalent({} ~ {})] eqc: {eqc}", lhs.id(), rhs.id());
        let lookups = equiv! { Self | &lhs.lookups, &rhs.lookups };
        log::debug!(
            "[equivalent({} ~ {})] lookups: {lookups}",
            lhs.id(),
            rhs.id()
        );
        let callsites = equiv! { Self | &lhs.callsites, &rhs.callsites };
        log::debug!(
            "[equivalent({} ~ {})] callsites: {callsites}",
            lhs.id(),
            rhs.id()
        );

        k && io && gates && eqc && lookups && callsites
    }
}

impl<E> LowerableStmt for IRGroup<E>
where
    E: LowerableExpr + std::fmt::Debug,
    CallSite<E>: LowerableStmt,
{
    fn lower<L>(self, l: &L) -> haloumi_lowering::Result<()>
    where
        L: Lowering + ?Sized,
    {
        log::debug!("Lowering {self:?}");
        if self.generate_debug_comments {
            l.generate_comment("Calls to subgroups".to_owned())?;
        }
        log::debug!("  Lowering callsites");
        for callsite in self.callsites {
            callsite.lower(l)?;
        }
        if self.generate_debug_comments {
            l.generate_comment("Gate constraints".to_owned())?;
        }
        log::debug!("  Lowering gates");
        self.gates.lower(l)?;
        if self.generate_debug_comments {
            l.generate_comment("Equality constraints".to_owned())?;
        }
        log::debug!("  Lowering equality constraints");
        self.eq_constraints.lower(l)?;
        if self.generate_debug_comments {
            l.generate_comment("Lookups".to_owned())?;
        }
        log::debug!("  Lowering lookups");
        self.lookups.lower(l)?;
        if self.generate_debug_comments {
            l.generate_comment("Injected".to_owned())?;
        }
        log::debug!("  Lowering injected IR");
        for stmt in self.injected {
            stmt.lower(l)?;
        }

        Ok(())
    }
}

impl<E: IRPrintable> IRPrintable for IRGroup<E> {
    fn fmt(&self, ctx: &mut crate::printer::IRPrinterCtx<'_, '_>) -> crate::printer::Result {
        ctx.block("group", |ctx| {
            writeln!(
                ctx,
                "{} \"{}\" (inputs {}) (outputs {})",
                self.id(),
                self.name(),
                self.input_count(),
                self.output_count()
            )?;

            for callsite in self.callsites() {
                ctx.fmt_call(
                    callsite.name(),
                    callsite.inputs(),
                    callsite.output_vars(),
                    Some(callsite.callee_id()),
                )?;
                ctx.nl()?;
            }

            for stmt in self.statements() {
                stmt.fmt(ctx)?;
                ctx.nl()?;
            }

            Ok(())
        })
    }
}
