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
    fn patterns(&self) -> Vec<&dyn GateRewritePattern<F, E>>
    where
        F: Field;
}

/// Default gate callbacks.
pub(crate) struct DefaultGateCallbacks;

impl<F, E> GateCallbacks<F, E> for DefaultGateCallbacks {
    fn patterns(&self) -> Vec<&dyn GateRewritePattern<F, E>>
    where
        F: Field,
    {
        vec![]
    }
}

/// Basic gate callbacks container that stores a list of callbacks
/// on the heap.
pub struct SimpleGateCallbacks<F, E> {
    callbacks: Vec<Box<dyn GateRewritePattern<F, E>>>,
    ignore_disabled_gates: bool,
}

impl<F, E> SimpleGateCallbacks<F, E> {
    /// Creates a new instance.
    pub fn new() -> Self {
        Self {
            callbacks: Default::default(),
            ignore_disabled_gates: true,
        }
    }

    /// Make haloumi ignore disabled gates
    pub fn ignore_disabled_gates(&mut self) {
        self.ignore_disabled_gates = true
    }

    /// Make haloumi not ignore disabled gates
    pub fn no_ignore_disabled_gates(&mut self) {
        self.ignore_disabled_gates = false
    }

    /// Adds a new pattern to the list.
    pub fn add(&mut self, pattern: impl GateRewritePattern<F, E> + 'static) {
        self.callbacks.push(Box::new(pattern))
    }
}

impl<F, E> Default for SimpleGateCallbacks<F, E> {
    fn default() -> Self {
        Self::new()
    }
}

impl<F, E> GateCallbacks<F, E> for SimpleGateCallbacks<F, E> {
    fn patterns(&self) -> Vec<&dyn GateRewritePattern<F, E>>
    where
        F: Field,
    {
        self.callbacks.iter().map(|p| p.as_ref()).collect()
    }

    fn ignore_disabled_gates(&self) -> bool {
        self.ignore_disabled_gates
    }
}

impl<F, E> std::fmt::Debug for SimpleGateCallbacks<F, E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SimpleGateCallbacks")
            .field("callbacks", &self.callbacks.len())
            .field("ignore_disabled_gates", &self.ignore_disabled_gates)
            .finish()
    }
}
