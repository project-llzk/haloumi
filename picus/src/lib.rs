#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

use haloumi_backend::{Backend, codegen::Codegen};
use haloumi_core::{felt::Prime, slot::Slot as FuncIO};
use haloumi_synthesis::io::{AdviceIO, InstanceIO};

use inner::PicusCodegenInner;
use lowering::PicusModuleLowering;
pub use params::{PicusParams, PicusParamsBuilder};
use pcl::{opt::MutOptimizer as _, vars::VarStr};
use utils::mk_io;
use vars::{NamingConvention, VarKey, VarKeySeed};

mod inner;
mod lowering;
mod params;
mod pcl;
mod utils;
mod vars;

/// Instance of a [`Backend`] prepared for lowering to PCL.
pub type PicusBackend = Backend<PicusCodegen, InnerState>;
type InnerState = Rc<RefCell<PicusCodegenInner>>;
type PicusModule = pcl::Module<VarKey>;
/// Output produced by the picus backend.
pub type PicusOutput = pcl::Program<VarKey>;
type PipelineBuilder = pcl::opt::OptimizerPipelineBuilder<VarKey>;
type Pipeline = pcl::opt::OptimizerPipeline<VarKey>;

impl From<PicusParams> for InnerState {
    fn from(value: PicusParams) -> Self {
        Rc::new(RefCell::new(PicusCodegenInner::new(value)))
    }
}

/// Code generator for PCL.
#[derive(Debug, Clone)]
pub struct PicusCodegen {
    inner: InnerState,
}

impl PicusCodegen {
    fn naming_convention(&self) -> NamingConvention {
        self.inner.borrow().naming_convention()
    }

    fn var_consistency_check(&self, output: &PicusOutput) -> Result<(), PicusCodegenError> {
        // Var consistency check
        for module in output.modules() {
            let vars = module.vars();
            // Get the set of io variables, without the fqn.
            // This set will have all the circuit cells that have been queried and resolved
            // during lowering.
            let io_vars = vars
                .keys()
                .filter_map(|k| match k {
                    VarKey::Slot(slot) => Some(*slot),
                    _ => None,
                })
                .collect::<HashSet<_>>();

            // The set of io variables, with names, should be the same length.
            let io_var_count = vars
                .iter()
                .filter_map(|(k, v)| match k {
                    VarKey::Slot(_) => Some(v),
                    _ => None,
                })
                .count();
            if io_vars.len() != io_var_count {
                // Inconsistency. Let's see which ones.
                let mut dups = HashMap::<FuncIO, Vec<&VarStr>>::new();
                for (k, v) in vars {
                    if let VarKey::Slot(slot) = k {
                        dups.entry(*slot).or_default().push(v);
                    }
                }

                let dups = dups;
                for (k, names) in dups {
                    if names.len() == 1 {
                        continue;
                    }
                    log::error!("Mismatched variable! (key = {k:?}) (names = {names:?})");
                }
                return Err(PicusCodegenError::ConsistencyCheckFailed {
                    expected: io_vars.len(),
                    actual: io_var_count,
                });
            }
        }
        Ok(())
    }

    fn optimization_pipeline(&self) -> Option<Pipeline> {
        self.inner.borrow().optimization_pipeline()
    }
}

impl<'c: 's, 's> Codegen<'c, 's> for PicusCodegen {
    type FuncOutput = PicusModuleLowering;
    type Output = PicusOutput;
    type State = InnerState;
    type Error = PicusCodegenError;

    fn initialize(state: &'s Self::State) -> Self {
        Self {
            inner: state.clone(),
        }
    }

    fn set_prime_field(&self, prime: Prime) -> Result<(), PicusCodegenError> {
        self.inner.borrow_mut().set_prime(prime);
        Ok(())
    }

    fn define_main_function(
        &self,
        advice_io: &AdviceIO,
        instance_io: &InstanceIO,
        _: impl IntoIterator<Item = String>,
    ) -> Result<Self::FuncOutput, PicusCodegenError> {
        let ep = self.inner.borrow().entrypoint();
        let nc = self.naming_convention();
        self.inner.borrow_mut().add_module(
            ep,
            mk_io(
                instance_io.inputs().len() + advice_io.inputs().len(),
                VarKeySeed::arg,
                nc,
            ),
            mk_io(
                instance_io.outputs().len() + advice_io.outputs().len(),
                VarKeySeed::field,
                nc,
            ),
        )
    }

    fn on_scope_end(&self, _scope: Self::FuncOutput) -> Result<(), PicusCodegenError> {
        log::debug!("Closing scope");
        Ok(())
    }

    fn generate_output(self) -> Result<Self::Output, PicusCodegenError> {
        let mut output = PicusOutput::new(
            self.inner.borrow().prime()?,
            self.inner.borrow().modules().to_vec(),
        );
        self.var_consistency_check(&output)?;
        if let Some(mut opt) = self.optimization_pipeline() {
            opt.optimize(&mut output)?;
        }
        Ok(output)
    }

    fn define_function(
        &self,
        name: &str,
        inputs: usize,
        outputs: usize,
        _: impl IntoIterator<Item = String>,
    ) -> Result<Self::FuncOutput, PicusCodegenError> {
        let nc = self.naming_convention();
        self.inner.borrow_mut().add_module(
            name.to_owned(),
            mk_io(inputs, VarKeySeed::arg, nc),
            mk_io(outputs, VarKeySeed::field, nc),
        )
    }
}

/// Error type used by [`PicusCodegen`].
#[derive(Debug, thiserror::Error)]
pub enum PicusCodegenError {
    /// Wraps a lowering error.
    #[error(transparent)]
    Lowering(#[from] haloumi_lowering::error::Error),
    /// Wraps an IR related error.
    #[error(transparent)]
    IR(#[from] haloumi_ir_gen::error::Error),
    /// Wraps a optimization pass error.
    #[error("optimization pass error: {0}")]
    Pass(crate::pcl::opt::PassError),
    /// Consistency check.
    #[error(
        "Inconsistency detected in circuit variables. Was expecting {expected} IO variables by {actual} were generated"
    )]
    ConsistencyCheckFailed {
        /// Expected number of variables.
        expected: usize,
        /// Actual number of variables.
        actual: usize,
    },
    /// Prime not set for program.
    #[error("Prime was not set!")]
    PrimeNotSet,
}

impl From<crate::pcl::opt::PassError> for PicusCodegenError {
    fn from(value: crate::pcl::opt::PassError) -> Self {
        Self::Pass(value)
    }
}
