use log::Level;
use std::{
    fs::File,
    io::BufReader,
    path::{Path, PathBuf},
};

use crate::{
    Action, Error, FailMode, OutputFormat, constants::parse_constants_file, llzk::LlzkConfig,
    logging::LoggingConfig, picus::PicusConfig,
};
use clap::Parser;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
pub struct Cli {
    //#[arg(value_enum)]
    //instructions: Vec<Instructions>,
    //#[arg(long, value_enum)]
    //chip: Option<Chip>,
    //#[arg(long, value_delimiter = ',')]
    //ignore_chips: Vec<Chip>,
    #[arg(long, value_delimiter = ',')]
    format: Vec<OutputFormat>,
    //#[arg(long, value_enum)]
    //r#type: Option<Type>,
    #[arg(short, long)]
    output: Option<PathBuf>,
    #[arg(long, value_delimiter = ',')]
    constants: Vec<String>,
    #[arg(long)]
    constants_file: Option<PathBuf>,
    //#[arg(long, value_delimiter = ',')]
    //method_whitelist: Vec<String>,
    //#[arg(long, value_delimiter = ',')]
    //method_blacklist: Vec<String>,
    #[arg(long)]
    pub log: Option<PathBuf>,
    #[arg(long, default_value_t = Level::Info)]
    pub log_level: Level,
    //#[arg(long)]
    //pub disable_decomposition_rewrite: bool,
    #[arg(long)]
    pub debug_comments: bool,
    #[arg(long)]
    pub picus_no_opt: bool,
    #[arg(long)]
    pub llzk_no_opt: bool,
    #[arg(long)]
    pub no_opt: bool,
    #[arg(long)]
    pub fail_fast: bool,
    #[arg(long)]
    #[arg(long, value_delimiter = ',')]
    pub preludes: Vec<String>,
    #[arg(long)]
    pub list: bool,
    #[arg(long)]
    pub list_preludes: bool,
    #[arg(long)]
    pub allow_injected_ir_for_outputs: bool,
    #[arg(long)]
    pub llzk_field_name: Option<String>,
}

impl Cli {
    pub fn logging(&self) -> Option<LoggingConfig> {
        self.log
            .as_deref()
            .map(|path| LoggingConfig::new(path, self.log_level))
    }

    pub fn fail_mode(&self) -> FailMode {
        if self.fail_fast {
            FailMode::Fast
        } else {
            FailMode::Continue
        }
    }

    pub fn setup(&mut self) -> std::result::Result<(), Error> {
        match (self.constants.is_empty(), self.constants_file.as_ref()) {
            (false, Some(_)) => return Err(Error::ConstantsConfigErr),
            (true, Some(path)) => {
                let f = File::open(path)?;
                let reader = BufReader::new(f);
                self.constants = parse_constants_file(reader)?
            }
            (true, None) => {
                log::warn!("No constants provided! Some circuits may fail to extract due to this.");
            }
            (false, None) => {} // Don't do anything
        }
        Ok(())
    }

    //fn instructions(&self) -> &[Instructions] {
    //    &self.instructions
    //}

    //fn chip(&self) -> Option<Chip> {
    //    self.chip
    //}

    //fn ignore_chips(&self) -> &[Chip] {
    //    &self.ignore_chips
    //}

    //fn r#type(&self) -> Option<Type> {
    //    self.r#type
    //}

    //fn method_whitelist(&self) -> &[String] {
    //    &self.method_whitelist
    //}

    //fn method_blacklist(&self) -> &[String] {
    //    &self.method_blacklist
    //}

    pub fn constants(&self) -> &[String] {
        &self.constants
    }

    pub fn output(&self) -> Option<&Path> {
        self.output.as_deref()
    }

    pub fn picus_config(&self) -> PicusConfig {
        PicusConfig::new(!(self.picus_no_opt || self.no_opt))
    }

    pub fn llzk_config(&self) -> LlzkConfig {
        LlzkConfig::new(!(self.llzk_no_opt || self.no_opt))
    }

    pub fn action(&self) -> Action {
        if self.list || self.list_preludes {
            Action::List
        } else {
            Action::Extract
        }
    }

    pub fn formats(&self) -> &[OutputFormat] {
        &self.format
    }

    pub fn preludes(&self) -> &[String] {
        &self.preludes
    }

    //fn harness_config(&self) -> HarnessConfig {
    //    HarnessConfig::new(
    //        &self.constants,
    //        self.debug_comments,
    //        !self.disable_decomposition_rewrite,
    //        self.allow_injected_ir_for_outputs,
    //    )
    //}

    pub fn optimize_ir(&self) -> bool {
        !self.no_opt
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accepts_ir_as_an_output_format() {
        let cli = Cli::try_parse_from(["extractor", "--format", "ir"]).unwrap();
        assert_eq!(cli.formats(), &[OutputFormat::Ir]);
    }

    #[test]
    fn defaults_to_no_output_formats() {
        let cli = Cli::try_parse_from(["extractor"]).unwrap();
        assert!(cli.formats().is_empty());
    }

    #[test]
    fn accepts_comma_delimited_preludes() {
        let cli = Cli::try_parse_from(["extractor", "--preludes", "alpha,beta"]).unwrap();
        assert_eq!(cli.preludes(), ["alpha", "beta"]);
    }

    #[test]
    fn list_preludes_is_a_listing_action() {
        let cli = Cli::try_parse_from(["extractor", "--list-preludes"]).unwrap();
        assert!(matches!(cli.action(), Action::List));
    }
}
