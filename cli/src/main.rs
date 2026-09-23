#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

use std::{
    ffi::{OsStr, OsString},
    path::PathBuf,
};

use clap::Parser;

mod app;
mod config;

use app::App;

#[derive(Debug, Parser)]
#[command(name = "cargo-haloumi", bin_name = "cargo-haloumi")]
struct Args {
    /// Root directory of the Cargo project to extract.
    #[arg(long)]
    root: Option<PathBuf>,
    /// Workspace package to extract.
    #[arg(short = 'p', long)]
    package: Option<String>,
}

#[derive(Debug, thiserror::Error)]
enum Error {
    #[error("{0}")]
    Message(String),
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    Metadata(#[from] cargo_metadata::Error),
    #[error(transparent)]
    Inject(#[from] haloumi_inject::error::Error),
    #[error(transparent)]
    CargoToml(#[from] cargo_toml::Error),
    #[error(transparent)]
    Toml(#[from] toml::de::Error),
}

fn main() {
    env_logger::init();
    let args = parse_args(std::env::args_os());
    if let Err(error) = resolve_root(&args)
        .and_then(|root| App::new(root, args))
        .and_then(App::run)
    {
        eprintln!("cargo-haloumi: {error}");
        std::process::exit(1);
    }
}

fn resolve_root(args: &Args) -> Result<PathBuf, Error> {
    let current = std::env::current_dir()?;
    Ok(match &args.root {
        Some(root) if root.is_absolute() => root.clone(),
        Some(root) => current.join(root),
        None => current,
    })
}

fn parse_args(args: impl IntoIterator<Item = OsString>) -> Args {
    let mut args = args.into_iter();
    let program = args.next().expect("program name must be available");
    let first = args.next();
    let args: Vec<OsString> = if first.as_deref() == Some(OsStr::new("haloumi")) {
        std::iter::once(program).chain(args).collect()
    } else {
        std::iter::once(program).chain(first).chain(args).collect()
    };
    Args::parse_from(args)
}
