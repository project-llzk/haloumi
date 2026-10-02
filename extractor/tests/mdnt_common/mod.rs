pub mod llzk;
pub mod picus;

pub fn setup() {
    let _ = simplelog::TestLogger::init(log::LevelFilter::Debug, simplelog::Config::default());
}

pub fn clean_string(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    for line in s.lines() {
        let line = line.trim();
        if line.starts_with(';') || line.is_empty() {
            continue;
        }
        result.push_str(line.split_once(';').map_or(line, |(code, _)| code).trim());
        result.push('\n');
    }
    result
}

macro_rules! extract {
    ($circuit:expr, $lookups:expr, $canonicalize:expr) => {{
        let cfg = haloumi_extractor::extractor::ExtractorCfg::default();
        let extractor = haloumi_extractor::extractor::Extractor::new(&cfg).with_sort_injected_ir();
        let circuit = extractor.make_circuit($circuit);
        //let circuit = haloumi_extractor::circuit::CircuitImpl::<
        //    halo2curves::bn256::Fr,
        //    _,
        //    midnight_proofs::plonk::ConstraintSystem<halo2curves::bn256::Fr>,
        //    midnight_proofs::ExtractionSupport,
        //    haloumi_extractor::circuit::Function,
        //>::new(
        //    $circuit,
        //    extractor.constants(),
        //    extractor.allow_injected_ir_for_outputs(),
        //);
        let mut resolved = extractor.extract_circuit(circuit, $lookups).unwrap();
        if $canonicalize {
            resolved.constant_fold().unwrap();
            resolved
                .validate()
                .expect("optimized IR must validate after folding");
            resolved.canonicalize();
            resolved
                .validate()
                .expect("optimized IR must validate after canonicalization");
        }
        resolved
    }};
}
pub(crate) use extract;

macro_rules! basic_test {
    ($name:ident, $circuit:expr, $expected:expr, $expected_opt:expr, $lookups:expr $(,)?) => {
        $crate::mdnt_common::picus::basic_picus_test!(
            $name,
            $circuit,
            include_str!(concat!("expected/picus/", $expected, ".picus")),
            include_str!(concat!("expected/picus/", $expected_opt, ".picus")),
            $lookups,
        );
        $crate::mdnt_common::llzk::basic_llzk_test!(
            $name,
            $circuit,
            include_str!(concat!("expected/llzk/", $expected, ".mlir")),
            include_str!(concat!("expected/llzk/", $expected_opt, ".mlir")),
            $lookups,
        );
    };
    ($name:ident, $circuit:expr, $expected:expr, $expected_opt:expr $(,)?) => {
        $crate::mdnt_common::basic_test!($name, $circuit, $expected, $expected_opt, None);
    };
}
pub(crate) use basic_test;
