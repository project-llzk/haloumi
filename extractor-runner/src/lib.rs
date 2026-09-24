#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

use std::{borrow::Cow, path::Path, process::exit};

use clap::Parser;
use haloumi_driver::backends::llzk::{LlzkParams, llzk::prelude::LlzkContext};
use haloumi_driver::backends::picus::PicusParamsBuilder;
use haloumi_extractor::extractor::{Comments, Extractor, ExtractorCfg, InjectedIRPolicy};
use haloumi_extractor::{Harness, PreludeEntry};
use haloumi_ir_gen::circuit::resolved::ResolvedIRCircuit;

use crate::logging::setup_logging;
use crate::{
    app_error::AppError,
    cli::Cli,
    ir::write_ir_output,
    llzk::{LlzkConfig, write_llzk_output},
    picus::{PicusConfig, write_picus_output},
};

pub mod app_error;
mod cli;
mod constants;
mod ir;
mod llzk;
mod logging;
mod picus;

enum Action {
    List,
    Extract,
}

enum FailMode {
    Fast,
    Continue,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, clap::ValueEnum)]
enum OutputFormat {
    Ir,
    Picus,
    Llzk,
}

enum OptStep {
    ConstantFold,
    Canonicalization,
}

/// Entry-point for the extractor tool.
#[derive(Debug)]
pub struct ExtractorMain {
    extractor_cfg: ExtractorCfg,
    cli: Cli,
}

impl ExtractorMain {
    /// Runs the extraction logic.
    pub fn run(harnesses: impl Iterator<Item = &'static Harness>) {
        let main = match ExtractorMain::new() {
            Ok(main) => main,
            Err(err) => {
                eprintln!("Initialization failed: {err}");
                exit(1)
            }
        };

        let preludes = haloumi_extractor::inventory::iter::<PreludeEntry>().collect::<Vec<_>>();
        let Err(err) = main.run_impl(harnesses, preludes) else {
            return;
        };
        eprintln!("Extraction failed: {err}");
    }

    fn new() -> Result<Self, Error> {
        let mut cli = Cli::parse();
        cli.setup()?;
        setup_logging(cli.logging())?;

        let mut extractor_cfg = ExtractorCfg::new();
        extractor_cfg.set_constants(cli.constants().to_vec());
        extractor_cfg.set_debug_comments(
            cli.debug_comments
                .then_some(Comments::Debug)
                .unwrap_or_default(),
        );
        extractor_cfg.set_injected_ir(
            cli.allow_injected_ir_for_outputs
                .then_some(InjectedIRPolicy::AllowAll)
                .unwrap_or_default(),
        );
        Ok(Self { cli, extractor_cfg })
    }

    fn run_impl(
        &self,
        harnesses: impl Iterator<Item = &'static Harness>,
        preludes: Vec<&'static PreludeEntry>,
    ) -> Result<(), Error> {
        match self.cli.action() {
            Action::List => {
                if self.cli.list {
                    self.print_harness_list(harnesses);
                }
                if self.cli.list_preludes {
                    self.print_prelude_list(&preludes);
                }
                Ok(())
            }
            Action::Extract => {
                let preludes = self.select_preludes(preludes)?;
                self.extract(harnesses, &preludes)
            }
        }
    }

    fn print_harness_list(&self, harnesses: impl Iterator<Item = &'static Harness>) {
        println!("Harnesses:");
        for h in harnesses {
            println!("{}", h.name());
        }
    }

    fn print_prelude_list(&self, preludes: &[&'static PreludeEntry]) {
        println!("Preludes:");
        for prelude in preludes {
            println!("{}", prelude.name());
        }
    }

    fn select_preludes(
        &self,
        preludes: Vec<&'static PreludeEntry>,
    ) -> Result<Vec<&'static PreludeEntry>, Error> {
        let mut available = std::collections::HashMap::new();
        for prelude in preludes {
            if available.insert(prelude.name(), prelude).is_some() {
                return Err(Error::DuplicateRegisteredPrelude(prelude.name().to_owned()));
            }
        }
        let mut selected = Vec::with_capacity(self.cli.preludes().len());
        let mut requested = std::collections::HashSet::new();
        for name in self.cli.preludes() {
            if !requested.insert(name) {
                return Err(Error::DuplicateRequestedPrelude(name.clone()));
            }
            let prelude = available
                .get(name.as_str())
                .copied()
                .ok_or_else(|| Error::UnknownPrelude(name.clone()))?;
            selected.push(prelude);
        }
        Ok(selected)
    }

    fn extract(
        &self,
        harnesses: impl Iterator<Item = &'static Harness>,
        preludes: &[&'static PreludeEntry],
    ) -> Result<(), Error> {
        let extractor = Extractor::new(&self.extractor_cfg);
        let picus_config = self.cli.picus_config();
        let llzk_config = self.cli.llzk_config();
        let output_base = self.output_base()?;
        let mut summary = Summary::default();
        for h in harnesses {
            self.handle_extract_result(
                || {
                    self.extract_one(
                        h,
                        preludes,
                        &extractor,
                        &output_base,
                        &picus_config,
                        &llzk_config,
                    )
                },
                &mut summary,
            )?;
        }
        if summary.errors > 0 {
            return Err(Error::FailedExtraction(summary.errors));
        }
        if summary.generated == 0 {
            return Err(Error::EmptyExtraction);
        }
        Ok(())
    }

    fn extract_one(
        &self,
        harness: &'static Harness,
        preludes: &[&'static PreludeEntry],
        extractor: &Extractor,
        output_base: &Path,
        picus_config: &PicusConfig,
        llzk_config: &LlzkConfig,
    ) -> Result<(), Error> {
        let name = harness.name();
        log::info!("Extracting harness {name}");

        let mut ir = harness.run(extractor).map_err(AppError::harness(name))?;
        for prelude in preludes {
            ir.add_prelude_groups(prelude.groups().into())?;
        }
        if self.cli.optimize_ir() {
            self.optimize_ir(&mut ir).map_err(AppError::opt(name))?;
        }
        for format in self.cli.formats() {
            match format {
                OutputFormat::Ir => write_ir_output(name, output_base.join("ir"), &ir)
                    .map_err(AppError::ir(name))?,
                OutputFormat::Picus => write_picus_output(
                    picus_config,
                    name,
                    output_base.join("picus"),
                    &ir,
                    PicusParamsBuilder::new(),
                )
                .map_err(AppError::picus(name))?,
                OutputFormat::Llzk => {
                    let field_name = self
                        .cli
                        .llzk_field_name
                        .as_deref()
                        .ok_or(Error::RequiredLlzkFieldName)?;
                    let context = LlzkContext::new();
                    let mut params = LlzkParams::new(&context);
                    params.with_builtin_field(field_name);
                    write_llzk_output(llzk_config, name, output_base.join("llzk"), &ir, params)
                        .map_err(AppError::llzk(name))?;
                }
            }
        }

        Ok(())
    }

    fn check_validation(&self, status: Result<(), Error>, step: OptStep) -> Result<(), Error> {
        if let Err(err) = status {
            log::error!(
                "Validation error after {}: {err}",
                match step {
                    OptStep::ConstantFold => "constant folding",
                    OptStep::Canonicalization => "canonicalization",
                }
            );
            return Err(Error::Opt(match step {
                OptStep::ConstantFold => "Constant fold",
                OptStep::Canonicalization => "Canonicalization",
            }));
        }

        Ok(())
    }

    fn optimize_ir(&self, ir: &mut ResolvedIRCircuit) -> Result<(), Error> {
        ir.constant_fold()?;
        self.check_validation(Ok(ir.validate()?), OptStep::ConstantFold)?;
        ir.canonicalize();
        self.check_validation(Ok(ir.validate()?), OptStep::Canonicalization)
    }

    fn handle_extract_result(
        &self,
        extract: impl FnOnce() -> Result<(), Error>,
        summary: &mut Summary,
    ) -> Result<(), Error> {
        summary.generated += 1;
        match extract() {
            Err(err) => match self.cli.fail_mode() {
                FailMode::Fast => Err(err.into()),
                FailMode::Continue => {
                    log::error!("{err}");
                    summary.errors += 1;
                    Ok(())
                }
            },
            _ => Ok(()),
        }
    }

    fn output_base(&self) -> Result<Cow<'_, Path>, Error> {
        let path = if let Some(path) = self.cli.output() {
            Cow::Borrowed(path)
        } else {
            // Default is $PWD/picus_files
            std::env::current_dir().map(|dir| Cow::Owned(dir.join("picus_files")))?
        };

        // Create if it doesn't exist.
        if !path.exists() {
            std::fs::create_dir_all(&path)?;
        }

        if !path.is_dir() {
            return Err(Error::OutputNotDir(format!("{}", path.display())));
        }

        Ok(path)
    }
}

#[derive(Default)]
struct Summary {
    errors: usize,
    generated: usize,
}

/// Error type.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Forwarded integration error.
    #[error(transparent)]
    Integration(#[from] haloumi_core::error::Error),
    /// IR generation error.
    #[error(transparent)]
    IrGen(#[from] haloumi_ir_gen::error::Error),
    /// Driver error.
    #[error(transparent)]
    Driver(#[from] haloumi_driver::error::Error),
    /// Logging configuration error.
    #[error(transparent)]
    Logging(#[from] log::SetLoggerError),
    /// IO error.
    #[error(transparent)]
    Io(#[from] std::io::Error),
    /// Raised when both parameters are passed at the same time.
    #[error("Cannot set --constants and --constants-file at the same time")]
    ConstantsConfigErr,
    /// Extraction failed with some errors.
    #[error("Extraction failed with {0} errors")]
    FailedExtraction(usize),
    /// Raised when the tool didn't extract any circuits.
    #[error("No circuits were generated!")]
    EmptyExtraction,
    /// Raised when the configured output path is not a directory.
    #[error("Output path {0} must be a directory")]
    OutputNotDir(String),
    /// Main entrypoint error.
    #[error(transparent)]
    App(#[from] AppError),
    /// Raised when an optimization pass fails.
    #[error("{0} pass failed")]
    Opt(&'static str),
    /// Raised when LLZK output is emitted but the field name was not passed.
    #[error("Pass the --llzk-field-name=<name> parameter when emitting LLZK IR")]
    RequiredLlzkFieldName,
    /// Raised when a requested prelude does not exist in the registry.
    #[error("Unknown prelude {0:?}")]
    UnknownPrelude(String),
    /// Raised when a prelude name is passed more than once.
    #[error("Prelude {0:?} was requested more than once")]
    DuplicateRequestedPrelude(String),
    /// Raised when multiple linked crates register the same prelude name.
    #[error("Prelude {0:?} is registered more than once")]
    DuplicateRegisteredPrelude(String),
}
