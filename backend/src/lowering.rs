//! Helpers for lowering IR.

use std::{cell::RefCell, rc::Rc};

/// Tracks the number of calls lowered in the current scope.
#[derive(Debug, Clone)]
pub struct CallTracker {
    count: Rc<RefCell<usize>>,
}

impl CallTracker {
    /// Creates a new tracker.
    pub fn new() -> Self {
        Self {
            count: Rc::new(Default::default()),
        }
    }

    /// Returns the current call number and advances the counter.
    pub fn next(&self) -> usize {
        let c = *self.count.borrow();
        *self.count.borrow_mut() = c + 1;
        c
    }

    /// Returns the current call number.
    pub fn peek(&self) -> usize {
        *self.count.borrow()
    }
}

impl Default for CallTracker {
    fn default() -> Self {
        Self::new()
    }
}
