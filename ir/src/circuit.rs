//! Types for representing a complete circuit.

use crate::{
    groups::{IRGroup, ValidationFailed},
    printer::{IRPrintable, IRPrinter},
    traits::{Canonicalize, ConstantFolding},
};

/// Generic type representing a circuit.
///
/// Is parametrized on the expression type and the type used to represent the external context
/// relative to the circuit.
#[derive(Debug)]
pub struct IRCircuit<E, C> {
    body: Vec<IRGroup<E>>,
    context: C,
}

impl<E, C> IRCircuit<E, C> {
    /// Creates a new circuit.
    pub fn new(body: Vec<IRGroup<E>>, context: C) -> Self {
        Self { body, context }
    }

    /// Returns a reference to the context.
    pub fn context(&self) -> &C {
        &self.context
    }

    /// Returns a list of the groups inside the circuit.
    pub fn body(&self) -> &[IRGroup<E>] {
        &self.body
    }

    /// Returns a list of mutable references to the groups inside the circuit.
    pub fn body_mut(&mut self) -> &mut [IRGroup<E>] {
        &mut self.body
    }

    /// Returns the body of the circuit, consuming it.
    pub fn take_body(self) -> Vec<IRGroup<E>> {
        self.body
    }

    /// Returns a printer of the circuit.
    pub fn display(&self) -> IRPrinter<'_>
    where
        Self: IRPrintable,
    {
        IRPrinter::from(self)
    }

    /// Returns the main group.
    ///
    /// Panics if there isn't a main group.
    pub fn main(&self) -> &IRGroup<E> {
        // Reverse the iterator because the main group is likely to be the last one.
        self.body
            .iter()
            .rev()
            .find(|g| g.is_main())
            .expect("A main group is required")
    }

    /// Validates the IR, returning errors if it failed.
    pub fn validate(&self) -> (Result<(), ValidationFailed>, Vec<String>) {
        let mut errors = vec![];

        for group in &self.body {
            let (status, group_errors) = group.validate(&self.body);
            if status.is_err() {
                for err in group_errors {
                    errors.push(format!("Error in group \"{}\": {err}", group.name()));
                }
            }
        }

        (
            if errors.is_empty() {
                Ok(())
            } else {
                Err(ValidationFailed {
                    name: self
                        .body
                        .iter()
                        .find_map(|g| g.is_main().then_some(g.name()))
                        .unwrap_or("circuit")
                        .to_string(),
                    error_count: errors.len(),
                })
            },
            errors,
        )
    }
}

impl<E, C, Err> ConstantFolding for IRCircuit<E, C>
where
    IRGroup<E>: ConstantFolding<Error = Err>,
{
    type Error = Err;

    type T = ();

    fn constant_fold(&mut self) -> Result<(), Self::Error> {
        self.body.constant_fold()
    }
}

impl<E, C> Canonicalize for IRCircuit<E, C>
where
    IRGroup<E>: Canonicalize,
{
    fn canonicalize(&mut self) {
        self.body.canonicalize()
    }
}

impl<E: IRPrintable, C: IRPrintable> IRPrintable for IRCircuit<E, C> {
    fn fmt(&self, ctx: &mut crate::printer::IRPrinterCtx<'_, '_>) -> crate::printer::Result {
        self.context().fmt(ctx)?;
        for group in self.body() {
            ctx.nl()?;
            group.fmt(ctx)?;
        }
        Ok(())
    }
}
