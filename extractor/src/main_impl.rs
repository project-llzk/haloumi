//! Main entrypoint of the extractor tool.

use std::{borrow::Cow, fs::File, io::Write as _, path::Path, process::exit};

use clap::Parser;
use haloumi_driver::backends::llzk::{LlzkParams, llzk::prelude::LlzkContext};
use haloumi_driver::backends::picus::PicusParamsBuilder;
use haloumi_ir_gen::circuit::resolved::ResolvedIRCircuit;

use crate::main_impl::logging::setup_logging;
use crate::{
    Harness,
    error::Error,
    extractor::{Comments, Extractor, ExtractorCfg, InjectedIRPolicy},
    main_impl::{
        app_error::AppError,
        cli::Cli,
        llzk::{LlzkConfig, write_llzk_output},
        picus::{PicusConfig, write_picus_output},
    },
};

pub mod app_error;
mod cli;
mod constants;
mod llzk;
mod logging;
mod picus;
mod prelude;

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

        let Err(err) = main.run_impl(harnesses) else {
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

    fn run_impl(&self, harnesses: impl Iterator<Item = &'static Harness>) -> Result<(), Error> {
        match self.cli.action() {
            Action::List => {
                self.print_harness_list(harnesses);
                Ok(())
            }
            Action::Extract => self.extract(harnesses),
        }
    }

    fn print_harness_list(&self, harnesses: impl Iterator<Item = &'static Harness>) {
        for h in harnesses {
            println!("{}", h.name());
        }
    }

    fn extract(&self, harnesses: impl Iterator<Item = &'static Harness>) -> Result<(), Error> {
        let extractor = Extractor::new(&self.extractor_cfg);
        let picus_config = self.cli.picus_config();
        let llzk_config = self.cli.llzk_config();
        let output_base = self.output_base()?;
        let mut summary = Summary::default();
        for h in harnesses {
            self.handle_extract_result(
                || self.extract_one(h, &extractor, &output_base, &picus_config, &llzk_config),
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
        extractor: &Extractor,
        output_base: &Path,
        picus_config: &PicusConfig,
        llzk_config: &LlzkConfig,
    ) -> Result<(), Error> {
        let name = harness.name();
        log::info!("Extracting harness {name}");

        let mut ir = harness.run(extractor).map_err(AppError::harness(name))?;
        if self.cli.optimize_ir() {
            self.optimize_ir(&mut ir).map_err(AppError::opt(name))?;
        }
        if self.cli.dump_ir() {
            self.dump_ir(name, output_base, &ir)
                .map_err(AppError::ir_dump(name))?;
        }
        for format in self.cli.formats() {
            match format {
                OutputFormat::Picus => write_picus_output(
                    picus_config,
                    name,
                    output_base,
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
                    write_llzk_output(llzk_config, name, output_base, &ir, params)
                        .map_err(AppError::llzk(name))?;
                }
            }
        }

        Ok(())
    }

    fn dump_ir(
        &self,
        name: &'static str,
        output_base: impl AsRef<Path>,
        ir: &ResolvedIRCircuit,
    ) -> Result<(), Error> {
        let output_dir = output_base.as_ref().join(name);
        std::fs::create_dir_all(&output_dir)?;

        let output_path = output_dir.join("dump.ir");
        let mut output_file = File::create(&output_path)?;
        writeln!(output_file, "{}", ir.display())?;
        log::info!("Saved IR dump output in {}", output_path.display());
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
