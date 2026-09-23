//! Textual IR output backend.

use std::{
    fs::{self, File},
    io::Write as _,
    path::Path,
};

use haloumi_ir_gen::circuit::resolved::ResolvedIRCircuit;

/// Writes resolved Haloumi IR for one harness.
pub fn write_ir_output(
    name: &'static str,
    output_base: impl AsRef<Path>,
    ir: &ResolvedIRCircuit,
) -> anyhow::Result<()> {
    let output_dir = output_base.as_ref().join(name);
    fs::create_dir_all(&output_dir)?;
    let output_path = output_dir.join("output.ir");
    let mut output_file = File::create(&output_path)?;
    writeln!(output_file, "{}", ir.display())?;
    log::info!("Saved IR output in {}", output_path.display());
    Ok(())
}
