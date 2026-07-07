use ff::{Field, PrimeField};
use haloumi::{
    driver::Driver,
    ir::r#gen::gates::{GateScope, callbacks::GateCallbacks, rewrite::GateRewritePattern},
    ir::r#gen::{IRGenParams, circuit::resolved::ResolvedIRCircuit},
    synthesis::CircuitSynthesis,
};
use haloumi_ir_gen::gates::rewrite::{Match, MatchResult};
use haloumi_midnight_integration::plonk::{_Expression, ConstraintSystem};

pub mod llzk;
pub mod picus;

pub fn setup() {
    let _ = simplelog::TestLogger::init(log::LevelFilter::Debug, simplelog::Config::default());
}

#[macro_export]
macro_rules! ensure_validation {
    ($x:expr) => {{
        $x.validate().expect("Test failed due to validation errors");
    }};
}

/// We run the synthesis separately to test that the lifetimes of the values
/// can be untied to the CircuitSynthesis struct. But also if we want to add LLZK tests
/// this makes sure to test the retargeability of the driver.
pub fn synthesize_and_generate_ir<F, C>(
    driver: &mut Driver,
    circuit: C,
    params: IRGenParams<F, _Expression<F>>,
) -> ResolvedIRCircuit
where
    F: PrimeField + std::cmp::Ord,
    C: CircuitSynthesis<F>,
    C: CircuitSynthesis<F, CS = ConstraintSystem<F>>,
{
    let syn = driver.synthesize(&circuit).unwrap();
    let unresolved = driver.generate_ir(&syn, params).unwrap();
    ensure_validation!(unresolved);
    let resolved = unresolved.resolve().unwrap();
    ensure_validation!(resolved);
    resolved
}

fn common_lowering<F, C>(
    circuit: C,
    driver: &mut Driver,
    ir_params: IRGenParams<F, _Expression<F>>,
    canonicalize: bool,
) -> ResolvedIRCircuit
where
    F: PrimeField + std::cmp::Ord,
    C: CircuitSynthesis<F, CS = ConstraintSystem<F>>,
{
    let mut resolved = synthesize_and_generate_ir(driver, circuit, ir_params);
    if canonicalize {
        resolved.constant_fold().unwrap();
        ensure_validation!(resolved);
        resolved.canonicalize();
        ensure_validation!(resolved);
    }
    resolved
}

fn clean_string(s: &str) -> String {
    let mut r = String::with_capacity(s.len());
    for line in s.lines() {
        let line = line.trim();
        if line.starts_with(";") || line.is_empty() {
            continue;
        }
        let line = match line.find(';') {
            Some(idx) => &line[..idx],
            None => line,
        }
        .trim();

        r.push_str(line);
        r.push('\n');
    }
    r
}

#[allow(dead_code)]
struct DummyPattern;

impl<F: Field> GateRewritePattern<F, _Expression<F>> for DummyPattern {
    fn match_gate<'a>(&self, _gate: GateScope<'a, '_, F, _Expression<F>>) -> MatchResult
    where
        F: Field,
    {
        Ok(Match::NoMatch)
    }
}

#[allow(dead_code)]
pub struct GC;

impl<F: Field> GateCallbacks<F, _Expression<F>> for GC {
    fn patterns(&self) -> Vec<Box<dyn GateRewritePattern<F, _Expression<F>>>>
    where
        F: Field,
    {
        vec![Box::new(DummyPattern)]
    }
}

macro_rules! synthesis_impl {
    ($name:ident, $circuit:ty, $inputs:expr, $outputs:expr) => {
        #[derive(Default)]
        struct $name($circuit);

        impl haloumi::synthesis::CircuitSynthesis<halo2curves::bn256::Fr> for $name {
            type Circuit = $circuit;
            type Config =
                <$circuit as haloumi_midnight_integration::halo2_proofs::plonk::Circuit<
                    halo2curves::bn256::Fr,
                >>::Config;

            type CS = haloumi_midnight_integration::plonk::ConstraintSystem<halo2curves::bn256::Fr>;

            type Error = haloumi_midnight_integration::halo2_proofs::plonk::Error;

            fn circuit(&self) -> &Self::Circuit {
                &self.0
            }
            fn configure(cs: &mut Self::CS) -> Self::Config {
                <$circuit as haloumi_midnight_integration::halo2_proofs::plonk::Circuit<
                    halo2curves::bn256::Fr,
                >>::configure(cs.inner_mut())
            }

            fn advice_io(
                _: &Self::Config,
            ) -> anyhow::Result<haloumi::synthesis::io::AdviceIO, haloumi::synthesis::error::Error>
            {
                Ok(haloumi::synthesis::io::CircuitIO::empty())
            }
            fn instance_io(
                config: &Self::Config,
            ) -> Result<haloumi::synthesis::io::InstanceIO, haloumi::synthesis::error::Error> {
                haloumi::synthesis::io::CircuitIO::new::<
                    haloumi_midnight_integration::plonk::_Column<
                        haloumi_midnight_integration::plonk::_Instance,
                    >,
                >(
                    &[(config.instance.into(), &$inputs)],
                    &[(config.instance.into(), &$outputs)],
                )
            }
            fn synthesize(
                circuit: &Self::Circuit,
                config: Self::Config,
                synthesizer: &mut haloumi::synthesis::synthesizer::Synthesizer<
                    halo2curves::bn256::Fr,
                >,
                cs: &Self::CS,
            ) -> Result<(), Self::Error> {
                haloumi_midnight_integration::synthesizer::SynthesizerAssignment::synthesize(
                    circuit,
                    config,
                    synthesizer,
                    cs,
                )
            }
        }
    };
}

pub(crate) use synthesis_impl;

macro_rules! basic_test {
    ($name:ident, $circuit:expr, $expected:expr, $expected_opt:expr, $ir_params:expr $(,)?) => {
        $crate::mdnt_common::picus::basic_picus_test! {
            $name,
            $circuit,
            include_str!(concat!("expected/picus/", $expected, ".picus")),
            include_str!(concat!("expected/picus/", $expected_opt, ".picus")),
            $ir_params
        }
        $crate::mdnt_common::llzk::basic_llzk_test! {
            $name,
            $circuit,
            include_str!(concat!("expected/llzk/", $expected, ".mlir")),
            include_str!(concat!("expected/llzk/", $expected_opt, ".mlir")),
            $ir_params
        }
    };
    ($name:ident, $circuit:expr, $expected:expr, $expected_opt:expr $(,)?) => {
        $crate::mdnt_common::basic_test! {
            $name,
            $circuit,
            $expected,
            $expected_opt,
            haloumi::ir::r#gen::IRGenParams::new()
        }
    };
}

pub(crate) use basic_test;
