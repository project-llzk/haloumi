use cargo_toml::Dependency;

use crate::{actions::InjectAction, crate_info::CrateMut, error::Error};

/// Adds a dependency to the manifest.
pub struct AddDepAction<'a> {
    name: &'a str,
    dep: &'a Dependency,
}

impl<'a> AddDepAction<'a> {
    /// Creates a new action.
    pub fn new(name: &'a str, dep: &'a Dependency) -> Self {
        Self { name, dep }
    }

    /// Creates a new action.
    pub fn boxed(name: &'a str, dep: &'a Dependency) -> Box<dyn InjectAction + 'a> {
        Box::new(Self::new(name, dep))
    }
}

impl InjectAction for AddDepAction<'_> {
    fn apply(&self, dest_crate: &mut CrateMut) -> Result<(), Error> {
        dest_crate.add_dependency(self.name.to_owned(), self.dep.clone())
    }
}
