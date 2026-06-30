use ff::{Field, PrimeField};
use haloumi::{
    ir::r#gen::gates::{GateScope, callbacks::GateCallbacks, rewrite::GateRewritePattern},
    ir::r#gen::{IRGenParams, circuit::resolved::ResolvedIRCircuit},
};
use haloumi_ir_gen::gates::rewrite::{Match, MatchResult};
use zcash_halo2_proofs::{
    dev::haloumi::{Haloumi, SynthesizableCircuit},
    plonk::Expression,
};

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
    driver: &mut Haloumi,
    circuit: C,
    params: IRGenParams<F, Expression<F>>,
) -> ResolvedIRCircuit
where
    F: PrimeField + std::cmp::Ord,
    C: SynthesizableCircuit<F>,
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
    driver: &mut Haloumi,
    ir_params: IRGenParams<F, Expression<F>>,
    canonicalize: bool,
) -> ResolvedIRCircuit
where
    F: PrimeField + std::cmp::Ord,
    C: SynthesizableCircuit<F>,
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

impl<F: Field> GateRewritePattern<F, Expression<F>> for DummyPattern {
    fn match_gate<'a>(&self, _gate: GateScope<'a, '_, F, Expression<F>>) -> MatchResult
    where
        F: Field,
    {
        Ok(Match::NoMatch)
    }
}

#[allow(dead_code)]
pub struct GC;

impl<F: Field> GateCallbacks<F, Expression<F>> for GC {
    fn patterns(&self) -> Vec<Box<dyn GateRewritePattern<F, Expression<F>>>>
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

        impl zcash_halo2_proofs::dev::haloumi::SynthesizableCircuit<halo2curves::bn256::Fr>
            for $name
        {
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
                    zcash_halo2_proofs::plonk::Column<zcash_halo2_proofs::plonk::Instance>,
                >(
                    &[(config.instance.into(), &$inputs)],
                    &[(config.instance.into(), &$outputs)],
                )
            }
        }

        impl zcash_halo2_proofs::plonk::Circuit<halo2curves::bn256::Fr> for $name {
            type Config =
                <$circuit as zcash_halo2_proofs::plonk::Circuit<halo2curves::bn256::Fr>>::Config;
            type FloorPlanner = <$circuit as zcash_halo2_proofs::plonk::Circuit<
                halo2curves::bn256::Fr,
            >>::FloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(
                meta: &mut zcash_halo2_proofs::plonk::ConstraintSystem<halo2curves::bn256::Fr>,
            ) -> Self::Config {
                <$circuit as zcash_halo2_proofs::plonk::Circuit<halo2curves::bn256::Fr>>::configure(
                    meta,
                )
            }

            fn synthesize(
                &self,
                config: Self::Config,
                layouter: impl zcash_halo2_proofs::circuit::Layouter<halo2curves::bn256::Fr>,
            ) -> Result<(), zcash_halo2_proofs::plonk::Error> {
                self.0.synthesize(config, layouter)
            }
        }
    };
}

pub(crate) use synthesis_impl;
