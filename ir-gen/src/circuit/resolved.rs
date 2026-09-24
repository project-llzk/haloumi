//! Types for working with circuits that are in the _resolved_ stage.

use haloumi_ir::{
    IRCircuit, Prime,
    diagnostics::DiagnosticsError,
    expr::IRAexpr,
    groups::{ConstantFoldingError, IRGroup},
    printer::{self, IRPrintable, IRPrinter, IRPrinterCtx},
    traits::{Canonicalize as _, ConstantFolding, Validatable as _},
};
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use crate::{ctx::IRCtx, error::Error};

type Circuit = IRCircuit<IRAexpr, ResolvedCtx>;

#[derive(Debug)]
pub(super) struct ResolvedCtx(pub IRCtx, pub Prime);

/// Circuit that has resolved its expressions and is no longer tied to the lifetime of the
/// synthesis and is not parametrized on a prime field.
#[derive(Debug)]
pub struct ResolvedIRCircuit(pub(super) Circuit, Vec<IRGroup<IRAexpr>>);

const PRELUDE_GROUP_ID_MASK: usize = 1usize << (usize::BITS - 1);

impl ResolvedIRCircuit {
    pub(super) fn new(circuit: Circuit) -> Self {
        Self(circuit, Vec::new())
    }

    /// Returns a list of the groups inside the circuit.
    pub fn groups(&self) -> &[IRGroup<IRAexpr>] {
        self.0.body()
    }

    /// Returns the semantic prelude groups attached to this circuit.
    pub fn prelude_groups(&self) -> &[IRGroup<IRAexpr>] {
        &self.1
    }

    /// Adds semantic prelude groups to this circuit.
    ///
    /// Prelude groups are assigned IDs in a separate, high-bit-masked range. Call sites inside
    /// the supplied groups are rebased to those IDs and may only target a group supplied in the
    /// same call.
    pub fn add_prelude_groups(&mut self, mut groups: Vec<IRGroup<IRAexpr>>) -> Result<(), Error> {
        let mut names = self
            .0
            .body()
            .iter()
            .chain(self.1.iter())
            .map(|group| group.name().to_owned())
            .collect::<HashSet<_>>();
        let start = self.1.len();
        let mut ids = HashMap::new();

        for (offset, group) in groups.iter().enumerate() {
            if group.is_main() {
                return Err(Error::new(PreludeError::MainGroup(group.name().to_owned())));
            }
            if !names.insert(group.name().to_owned()) {
                return Err(Error::new(PreludeError::DuplicateName(
                    group.name().to_owned(),
                )));
            }
            let old_id = group.id();
            let new_id = PRELUDE_GROUP_ID_MASK | (start + offset);
            if ids.insert(old_id, new_id).is_some() {
                return Err(Error::new(PreludeError::DuplicateId(old_id)));
            }
        }

        for group in &mut groups {
            for callsite in group.callsites_mut() {
                let old_id = callsite.callee_id();
                let new_id = ids
                    .get(&old_id)
                    .copied()
                    .ok_or_else(|| Error::new(PreludeError::UnknownCallsiteTarget(old_id)))?;
                callsite.set_callee_id(new_id);
            }
            group.set_id(ids[&group.id()]);
        }
        self.1.extend(groups);
        Ok(())
    }

    /// Returns the context associated with this circuit.
    pub fn ctx(&self) -> &IRCtx {
        &self.0.context().0
    }

    /// Returns a printer of the circuit.
    pub fn display(&self) -> IRPrinter<'_> {
        IRPrinter::from(self)
    }

    /// Returns the main group.
    ///
    /// Panics if there isn't a main group.
    pub fn main(&self) -> &IRGroup<IRAexpr> {
        self.0.main()
    }

    /// Returns the prime that defines the finite field the circuit uses.
    pub fn prime(&self) -> Prime {
        self.0.context().1
    }

    /// Folds the statements if the expressions are constant.
    ///
    /// If any of the statements fails to fold returns an error.
    pub fn constant_fold(&mut self) -> Result<(), Error> {
        self.0
            .body_mut()
            .constant_fold()
            .map_err(ResolvedIRError::ConstantFold)?;
        self.1
            .constant_fold()
            .map_err(ResolvedIRError::ConstantFold)?;
        Ok(())
    }

    /// Matches the statements against a series of known patterns and applies rewrites if able to.
    pub fn canonicalize(&mut self) {
        self.0.body_mut().canonicalize();
        self.1.canonicalize();
    }

    /// Validates the IR, returning errors if it failed.
    pub fn validate(&self) -> Result<(), Error> {
        let groups = self
            .0
            .body()
            .iter()
            .chain(self.1.iter())
            .cloned()
            .collect::<Vec<_>>();
        let mut errors = Vec::new();
        for group in &groups {
            if let Err(group_errors) = group.validate_with_context(&groups) {
                errors.extend(group_errors);
            }
        }
        if !errors.is_empty() {
            return Err(ResolvedIRError::Validation {
                count: errors.len(),
                errors: DiagnosticsError::from_iter(errors),
            }
            .into());
        }
        Ok(())
    }
}

impl IRPrintable for ResolvedIRCircuit {
    fn fmt(&self, ctx: &mut IRPrinterCtx<'_, '_>) -> printer::Result {
        self.0.context().fmt(ctx)?;
        for group in self.0.body().iter().chain(self.1.iter()) {
            ctx.nl()?;
            group.fmt(ctx)?;
        }
        Ok(())
    }
}

/// Errors raised while attaching semantic prelude groups.
#[derive(Debug, thiserror::Error)]
pub enum PreludeError {
    /// A prelude group was declared as a main group.
    #[error("prelude group {0:?} must not be a main group")]
    MainGroup(String),
    /// More than one group uses the same backend module name.
    #[error("duplicate group name {0:?}")]
    DuplicateName(String),
    /// More than one prelude group uses the same local ID.
    #[error("duplicate prelude group ID {0}")]
    DuplicateId(usize),
    /// A prelude call site targets a group outside the appended prelude.
    #[error("prelude call site targets unknown local group ID {0}")]
    UnknownCallsiteTarget(usize),
}

impl IRPrintable for ResolvedCtx {
    fn fmt(&self, ctx: &mut IRPrinterCtx<'_, '_>) -> printer::Result {
        ctx.list_nl("prime-number", |ctx| write!(ctx, "{}", self.1))
    }
}

/// Unresolved IR error
#[derive(Debug, thiserror::Error)]
pub(crate) enum ResolvedIRError {
    /// Error raised by [`ResolvedIRCircuit::constant_fold`].
    #[error(transparent)]
    ConstantFold(#[from] ConstantFoldingError<IRAexpr>),
    /// Error raised by [`ResolvedIRCircuit::validate`].
    #[error("validation of unresolved IR failed with {count} errors: \n{errors}")]
    Validation {
        /// Number of errors.
        count: usize,
        /// List of errors.
        errors: DiagnosticsError,
    },
}

impl From<ResolvedIRError> for Error {
    fn from(value: ResolvedIRError) -> Self {
        Error::new(value)
    }
}
