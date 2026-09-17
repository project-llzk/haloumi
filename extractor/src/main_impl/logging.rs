//! Logging management.

use std::{
    fs::File,
    path::{Path, PathBuf},
};

use log::{Level, Log};

use crate::error::Error;

pub struct LoggingConfig {
    path: PathBuf,
    level: Level,
}

impl LoggingConfig {
    pub fn new(path: impl AsRef<Path>, level: Level) -> Self {
        LoggingConfig {
            path: PathBuf::from(path.as_ref()),
            level,
        }
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn level(&self) -> Level {
        self.level
    }
}

pub fn setup_logging(config: Option<LoggingConfig>) -> Result<(), Error> {
    let env_logger = Box::new(env_logger::Builder::from_default_env().build());
    let mut loggers: Vec<Box<dyn Log>> = vec![env_logger];
    if let Some(config) = config {
        loggers.push(simplelog::WriteLogger::new(
            config.level().to_level_filter(),
            Default::default(),
            File::create(config.path())?,
        ));
    }

    multi_log::MultiLogger::init(loggers, log::Level::Trace)?;
    Ok(())
}
