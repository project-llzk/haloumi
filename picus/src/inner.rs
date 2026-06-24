use crate::{PicusCodegenError, PicusModule, Pipeline, PipelineBuilder, params::PicusParams};

use haloumi_backend::codegen::CodegenParams;
use haloumi_ir::Prime;

pub use super::lowering::PicusModuleLowering;
use super::{
    lowering::PicusModuleRef,
    vars::{NamingConvention, VarKey},
};
use crate::pcl::{
    opt::passes::{ConsolidateVarNamesPass, FoldExprsPass, ReplaceKnownConstsPass},
    vars::VarStr,
};

#[derive(Debug)]
pub struct PicusCodegenInner {
    params: PicusParams,
    prime: Option<Prime>,
    modules: Vec<PicusModuleRef>,
    current_scope: Option<PicusModuleLowering>,
}

impl PicusCodegenInner {
    pub fn new(params: PicusParams) -> Self {
        Self {
            prime: None,
            params,
            modules: Default::default(),
            current_scope: Default::default(),
        }
    }

    pub fn naming_convention(&self) -> NamingConvention {
        self.params.naming_convention()
    }

    pub fn modules(&self) -> &[PicusModuleRef] {
        &self.modules
    }

    pub fn prime(&self) -> Result<Prime, PicusCodegenError> {
        self.prime.ok_or_else(|| PicusCodegenError::PrimeNotSet)
    }

    pub fn optimization_pipeline(&self) -> Option<Pipeline> {
        if !self.params.optimize() {
            return None;
        }
        let pipeline = PipelineBuilder::new()
            .add_pass::<FoldExprsPass>()
            .add_pass::<ConsolidateVarNamesPass>()
            .add_pass::<ReplaceKnownConstsPass>()
            .add_pass::<FoldExprsPass>();
        Some(pipeline.into())
    }

    pub fn set_prime(&mut self, prime: Prime) {
        self.prime = Some(prime);
    }

    pub fn add_module<O>(
        &mut self,
        name: String,
        inputs: impl Iterator<Item = O>,
        outputs: impl Iterator<Item = O>,
    ) -> Result<PicusModuleLowering, PicusCodegenError>
    where
        O: Into<VarKey> + Into<VarStr> + Clone,
    {
        let module = PicusModule::shared(name.clone(), inputs, outputs);

        self.modules.push(module.clone());
        let scope =
            PicusModuleLowering::new(module, self.params.naming_convention(), self.prime()?);
        log::debug!("Setting the scope to {name}");
        self.current_scope = Some(scope.clone());
        Ok(scope)
    }

    pub fn entrypoint(&self) -> String {
        self.params.entrypoint().to_owned()
    }
}

impl CodegenParams for PicusCodegenInner {
    fn inlining_enabled(&self) -> bool {
        self.params.inline()
    }
}
