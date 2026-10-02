//! Helper for building preludes.

use haloumi_core::groups::{GroupKey, GroupKeyInstance};
use haloumi_ir::{Slot, expr::IRAexpr, groups::IRGroup, stmt::IRStmt};

/// Builder for defining prelude groups.
#[derive(Debug)]
pub struct Prelude {
    ir: Vec<IRGroup<IRAexpr>>,
}

impl Prelude {
    /// Creates a new instance.
    pub fn new() -> Self {
        Self {
            ir: Default::default(),
        }
    }

    /// Adds a new prelude to the list.
    pub fn add<F>(mut self, name: String, n_inputs: usize, n_outputs: usize, body: F) -> Self
    where
        F: Fn(&[Slot], &[Slot]) -> IRStmt<IRAexpr>,
    {
        let id = self.ir.len();
        let mut group = IRGroup::new(name, id)
            .with_key(Some(GroupKeyInstance::from(PreludeKey(id)).into()))
            .with_input_count(n_inputs)
            .with_output_count(n_outputs);
        group.inject(body(&Slot::args(n_inputs), &Slot::outputs(n_outputs)));
        self.ir.push(group);
        self
    }
}

impl Default for Prelude {
    fn default() -> Self {
        Self::new()
    }
}

impl From<Prelude> for Vec<IRGroup<IRAexpr>> {
    fn from(value: Prelude) -> Self {
        value.ir
    }
}

#[derive(Debug, Copy, Clone, Hash)]
struct PreludeKey(usize);

impl GroupKey for PreludeKey {}
