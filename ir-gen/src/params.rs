use ff::Field;

use crate::{gates::callbacks::GateCallbacks, lookups::callbacks::LookupCallbacks};

/// Configuration parameters for IR generation.
pub struct IRGenParams<'lc, 'gc, F: Field, E> {
    pub(crate) debug_comments: bool,
    pub(crate) lookup_cb: Option<&'lc dyn LookupCallbacks<F, E>>,
    pub(crate) gate_cb: Option<&'gc dyn GateCallbacks<F, E>>,
}

impl<'lc, 'gc, F: Field, E> IRGenParams<'lc, 'gc, F, E> {
    fn new() -> Self {
        Self {
            debug_comments: false,
            lookup_cb: None,
            gate_cb: None,
        }
    }

    /// Returns wether debug comments are enabled or not.
    pub fn debug_comments(&self) -> bool {
        self.debug_comments
    }

    //=====-----------------------------------------------------------------------=====//
    // Builder methods
    //=====-----------------------------------------------------------------------=====//

    /// Enables debug comments.
    pub fn with_debug_comments(&mut self) -> &mut Self {
        self.debug_comments = true;
        self
    }

    /// Disables debug comments.
    pub fn without_debug_comments(&mut self) -> &mut Self {
        self.debug_comments = false;
        self
    }

    /// Sets the lookup callbacks.
    pub fn lookup_callbacks(&mut self, lc: &'lc dyn LookupCallbacks<F, E>) -> &mut Self {
        self.lookup_cb = Some(lc);
        self
    }

    /// Unsets the lookup callbacks.
    pub fn no_lookup_callbacks(&mut self) -> &mut Self {
        self.lookup_cb = None;
        self
    }

    /// Sets the gate callbacks.
    pub fn gate_callbacks(&mut self, gc: &'gc dyn GateCallbacks<F, E>) -> &mut Self {
        self.gate_cb = Some(gc);
        self
    }

    /// Unsets the gate callbacks.
    pub fn no_gate_callbacks(&mut self) -> &mut Self {
        self.gate_cb = None;
        self
    }
}

impl<F: Field, E> Default for IRGenParams<'_, '_, F, E> {
    fn default() -> Self {
        Self::new()
    }
}

impl<F: Field, E> std::fmt::Debug for IRGenParams<'_, '_, F, E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("IRGenParams")
            .field("debug_comments", &self.debug_comments)
            .field(
                "lookup_cb",
                if self.lookup_cb.is_some() {
                    &"set"
                } else {
                    &"default"
                },
            )
            .field(
                "gate_cb",
                if self.gate_cb.is_some() {
                    &"set"
                } else {
                    &"default"
                },
            )
            .finish()
    }
}
