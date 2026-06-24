//! Traits for passing custom behaviors for IR generation of PLONK gates.

use ff::Field;

use crate::gates::rewrite::GateRewritePattern;

/// User configuration for the lowering process of gates.
pub trait GateCallbacks<F, E> {
    /// Asks wether a gate's polynomial whose selectors are all disabled for a given region should be emitted or
    /// not. Defaults to true.
    fn ignore_disabled_gates(&self) -> bool {
        true
    }

    /// Asks for a list of patterns that are checked before the default ones.
    fn patterns(&self) -> Vec<Box<dyn GateRewritePattern<F, E>>>
    where
        F: Field;
}

/// Default gate callbacks.
pub(crate) struct DefaultGateCallbacks;

impl<F, E> GateCallbacks<F, E> for DefaultGateCallbacks {
    fn patterns(&self) -> Vec<Box<dyn GateRewritePattern<F, E>>>
    where
        F: Field,
    {
        vec![]
    }
}
