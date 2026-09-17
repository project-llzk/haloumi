use std::{
    fs::{self, File},
    io::Write as _,
    path::Path,
};

use haloumi_driver::backends::llzk::LlzkParams;
use haloumi_driver::{driver::Driver, ir::r#gen::circuit::resolved::ResolvedIRCircuit};

pub struct LlzkConfig {
    opt: bool,
}

impl LlzkConfig {
    pub fn new(opt: bool) -> Self {
        Self { opt }
    }
}

pub fn write_llzk_output(
    config: &LlzkConfig,
    name: &'static str,
    output_base: impl AsRef<Path>,
    ir: &ResolvedIRCircuit,
    mut params: LlzkParams,
) -> anyhow::Result<()> {
    let output_dir = output_base.as_ref().join(name);
    fs::create_dir_all(&output_dir)?;
    params.with_top_level(name);
    if !config.opt {
        params.no_optimize();
    }
    let output = Driver::default().llzk(ir, params)?;

    let output_path = output_dir.join("output.llzk");
    let mut output_file = File::create(&output_path)?;

    writeln!(output_file, "{}", output)?;
    log::info!("Saved LLZK output in {}", output_path.display());
    Ok(())
}
