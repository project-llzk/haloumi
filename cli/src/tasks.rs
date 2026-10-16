//! Concrete steps in the Haloumi extraction workflow.

mod add_extractor_binary;
mod clone_target_crate;
mod commit_root_crate;
mod patch_direct_dependencies;
mod prepare_workspace;
mod run_extractor;

pub(crate) use add_extractor_binary::add_extractor_binary;
pub(crate) use clone_target_crate::clone_target_crate;
pub(crate) use commit_root_crate::commit_root_crate;
pub(crate) use patch_direct_dependencies::patch_direct_dependencies;
pub(crate) use prepare_workspace::prepare_workspace;
pub(crate) use run_extractor::run_extractor;
