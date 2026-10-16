pub struct Harness;

pub use main_impl::ExtractorMain;

pub mod main_impl {
    pub struct ExtractorMain;

    impl ExtractorMain {
        pub fn run(_: impl Iterator<Item = &'static crate::Harness>) {
            let output = std::env::var("HALOUMI_TEST_ARGS_OUTPUT").unwrap();
            std::fs::write(output, std::env::args().collect::<Vec<_>>().join("\n")).unwrap();
        }
    }
}
