use crate::{Error, app::AppState};

pub(crate) fn prepare_workspace(state: &AppState) -> Result<(), Error> {
    state.paths.reset_output()
}
