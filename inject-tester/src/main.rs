use std::{ffi::OsString, path::PathBuf, process::Command};

use anyhow::ensure;
use clap::Parser;
use haloumi_inject::{Injector, crate_info::Crate, spec::SpecRegistry};

#[derive(Debug, Parser)]
struct Args {
    #[arg(long)]
    spec: PathBuf,
    #[arg(long)]
    build: bool,
    source: PathBuf,
    destination: Option<PathBuf>,
    #[arg(last = true)]
    cargo_args: Vec<OsString>,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let registry = SpecRegistry::load(&args.spec)?;
    let source = Crate::open(&args.source)?;
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let run_cargo = |path: &std::path::Path| -> anyhow::Result<()> {
        let status = Command::new(&cargo)
            .current_dir(path)
            .arg(if args.build { "build" } else { "check" })
            .args(&args.cargo_args)
            .status()?;
        ensure!(
            status.success(),
            "cargo validation failed in {}",
            path.display()
        );
        Ok(())
    };
    run_cargo(source.base_path())?;
    let destination = args
        .destination
        .unwrap_or_else(|| args.source.join("target/haloumi/.inject-test"));
    let patched = Injector::new(&source, &registry)?.apply(destination)?;
    run_cargo(patched.base_path())
}
