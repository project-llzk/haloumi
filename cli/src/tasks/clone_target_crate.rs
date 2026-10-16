use haloumi_inject::crate_info::{Crate, CrateLike, CrateMut};

use crate::{Error, app::AppState};

pub(crate) fn clone_target_crate(state: &AppState) -> Result<CrateMut, Error> {
    let source = Crate::open(state.target.manifest_directory()?)?;
    Ok(source.clone_in_path(state.paths.root_copy(&state.target.package))?)
}
