use std::{
    fs::{self, File},
    io::Write as _,
    path::Path,
};

use haloumi_core::felt::Prime;
use haloumi_core::llzk::LlzkOutputFormat;
use haloumi_driver::backends::llzk::LlzkParams;
use haloumi_driver::{driver::Driver, ir::r#gen::circuit::resolved::ResolvedIRCircuit};

/// LLZK's builtin fields and their primes, as registered by `Field::initKnownFields` in LLZK.
const BUILTIN_FIELDS: [(&str, &str); 7] = [
    (
        "bn128",
        "21888242871839275222246405745257275088548364400416034343698204186575808495617",
    ),
    (
        "bn254",
        "21888242871839275222246405745257275088548364400416034343698204186575808495617",
    ),
    (
        "grumpkin",
        "21888242871839275222246405745257275088696311157297823662689037894645226208583",
    ),
    ("babybear", "2013265921"),
    ("goldilocks", "18446744069414584321"),
    ("mersenne31", "2147483647"),
    ("koalabear", "2130706433"),
];

/// Errors raised while configuring the field of the LLZK output.
#[derive(Debug, thiserror::Error)]
pub enum FieldError {
    /// Raised when a builtin field is requested for a circuit over a different prime.
    #[error("LLZK field '{name}' has prime {builtin}, but the circuit is defined over {circuit}")]
    PrimeMismatch {
        name: String,
        builtin: &'static str,
        circuit: Prime,
    },
}

/// How the field of the LLZK output is defined.
#[derive(Debug, PartialEq, Eq)]
enum FieldSpec {
    /// One of LLZK's builtin fields.
    Builtin,
    /// A new field with the circuit's prime.
    Custom,
}

/// Decides how to define the field named `name` for a circuit over `prime`.
fn field_spec(name: &str, prime: Prime) -> Result<FieldSpec, FieldError> {
    match BUILTIN_FIELDS.iter().find(|(builtin, _)| *builtin == name) {
        None => Ok(FieldSpec::Custom),
        Some((_, builtin)) if *builtin == prime.to_string() => Ok(FieldSpec::Builtin),
        Some((_, builtin)) => Err(FieldError::PrimeMismatch {
            name: name.to_owned(),
            builtin,
            circuit: prime,
        }),
    }
}

/// Sets the field of the LLZK output.
///
/// A builtin field name must match the circuit's prime. Any other name defines a new field with
/// the circuit's prime, e.g. for BLS12-381's scalar field.
pub fn set_field(params: &mut LlzkParams, name: &str, prime: Prime) -> Result<(), FieldError> {
    match field_spec(name, prime)? {
        FieldSpec::Builtin => params.with_builtin_field(name),
        FieldSpec::Custom => params.with_prime_field(name, prime),
    };
    Ok(())
}

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
    format: LlzkOutputFormat,
    mut params: LlzkParams,
) -> anyhow::Result<()> {
    let output_dir = output_base.as_ref().join(name);
    fs::create_dir_all(&output_dir)?;
    params.with_top_level(name);
    if !config.opt {
        params.no_optimize();
    }
    let output = Driver::default().llzk(ir, params)?;

    log::info!("Writing LLZK output as {format}...");
    let output_path = output_dir.join("output.llzk");
    let mut output_file = File::create(&output_path)?;

    match format {
        LlzkOutputFormat::Assembly => writeln!(output_file, "{}", output)?,
        LlzkOutputFormat::Bytecode => output.dump(&mut output_file)?,
    }
    log::info!("Saved LLZK output in {}", output_path.display());
    Ok(())
}

#[cfg(test)]
mod tests {
    use halo2curves::bn256::{Fq, Fr};

    use super::*;

    #[test]
    fn builtin_with_matching_prime() {
        assert_eq!(
            field_spec("bn254", Prime::new::<Fr>()).unwrap(),
            FieldSpec::Builtin
        );
        assert_eq!(
            field_spec("bn128", Prime::new::<Fr>()).unwrap(),
            FieldSpec::Builtin
        );
        // Grumpkin's scalar field is BN254's base field.
        assert_eq!(
            field_spec("grumpkin", Prime::new::<Fq>()).unwrap(),
            FieldSpec::Builtin
        );
    }

    #[test]
    fn builtin_with_other_prime_is_rejected() {
        let err = field_spec("bn254", Prime::new::<Fq>()).unwrap_err();
        assert!(matches!(err, FieldError::PrimeMismatch { name, .. } if name == "bn254"));
    }

    #[test]
    fn unknown_name_defines_a_field() {
        assert_eq!(
            field_spec("bls12-381", Prime::new::<Fq>()).unwrap(),
            FieldSpec::Custom
        );
    }
}
