use haloumi_inject::crate_info::CrateMut;

use crate::{Error, app::AppState};

pub(crate) fn commit_root_crate(_state: &AppState, root: &CrateMut) -> Result<(), Error> {
    root.commit()?;
    Ok(())
}
