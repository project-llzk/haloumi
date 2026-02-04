//! Types for working with circuits that are in the _resolved_ stage.

use haloumi_ir::{
    IRCircuit, Prime,
    diagnostics::DiagnosticsError,
    expr::IRAexpr,
    groups::{ConstantFoldingError, IRGroup},
    printer::{self, IRPrintable, IRPrinter, IRPrinterCtx},
    traits::{Canonicalize as _, ConstantFolding, Validatable as _},
};
use std::fmt::Write as _;

use crate::{ctx::IRCtx, error::Error};

type Circuit = IRCircuit<IRAexpr, ResolvedCtx>;

#[derive(Debug)]
pub(super) struct ResolvedCtx(pub IRCtx, pub Prime);

/// Circuit that has resolved its expressions and is no longer tied to the lifetime of the
/// synthesis and is not parametrized on a prime field.
#[derive(Debug)]
pub struct ResolvedIRCircuit(pub(super) Circuit);

impl ResolvedIRCircuit {
    /// Returns a list of the groups inside the circuit.
    pub fn groups(&self) -> &[IRGroup<IRAexpr>] {
        self.0.body()
    }

    /// Returns the context associated with this circuit.
    pub fn ctx(&self) -> &IRCtx {
        &self.0.context().0
    }

    /// Returns a printer of the circuit.
    pub fn display(&self) -> IRPrinter<'_> {
        self.0.display()
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
        Ok(())
    }

    /// Matches the statements against a series of known patterns and applies rewrites if able to.
    pub fn canonicalize(&mut self) {
        self.0.body_mut().canonicalize();
    }

    /// Validates the IR, returning errors if it failed.
    pub fn validate(&self) -> Result<(), Error> {
        self.0
            .validate()
            .map(|_| {})
            .map_err(move |errors| ResolvedIRError::Validation {
                count: errors.len(),
                errors: DiagnosticsError::from_iter(errors),
            })?;
        Ok(())
    }
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
