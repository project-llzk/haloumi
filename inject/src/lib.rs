#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

use crate::{
    crate_info::{Crate, CrateMut},
    error::Error,
    spec::{Spec, SpecRegistry},
};
use std::path::Path;

mod actions;
pub mod crate_info;
pub mod error;
pub mod spec;

/// The injector coordinates the modification of a crate following a spec.
#[derive(Debug)]
pub struct Injector<'s, 'c> {
    source: &'c Crate,
    spec: &'s Spec,
}

impl<'s, 'c> Injector<'s, 'c> {
    /// Creates a new injector.
    ///
    /// Fails if the name or the version of the source crate could not be obtained,
    /// or if couldn't pick a spec from the registry.
    pub fn new(source: &'c Crate, registry: &'s SpecRegistry) -> Result<Self, Error> {
        let source_name = source.name()?;
        let source_version = source.version()?;
        let usable_specs = registry
            .specs()
            .iter()
            .filter(|spec| spec.valid_target(source_name, source_version))
            .collect::<Vec<_>>();
        match usable_specs.as_slice() {
            [] => Err(Error::NoValidSpec(
                source_name.to_owned(),
                source_version.clone(),
            )),
            [spec] => Ok(Self {
                source,
                spec: *spec,
            }),
            other => Err(Error::TooManyValidSpec(
                source_name.to_owned(),
                source_version.clone(),
                other.len(),
            )),
        }
    }

    /// Applies the spec to the source crate in a copy located in the given path.
    pub fn apply(&self, dest: impl AsRef<Path>) -> Result<CrateMut, Error> {
        log::debug!("Cloning source into destination...");
        let mut dest_crate = self.source.clone_in_path(dest)?;

        self.spec
            .actions()
            .try_for_each(|action| action.apply(&mut dest_crate))?;

        // Commit changes to disk
        log::debug!("Commiting patches to disk...");
        dest_crate.commit()?;

        log::debug!("Done");
        Ok(dest_crate)
    }
}
