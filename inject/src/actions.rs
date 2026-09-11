//! Inject actions.

use crate::{crate_info::CrateMut, error::Error};

pub mod add_dep;
pub mod append;
pub mod derive;

/// An inject action performed by the injector.
pub trait InjectAction {
    fn apply(&self, dest_crate: &mut CrateMut) -> Result<(), Error>;
}
