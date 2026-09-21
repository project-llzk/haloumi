pub struct Harness;

pub mod main_impl {
    pub struct ExtractorMain;

    impl ExtractorMain {
        pub fn run(_: impl Iterator<Item = &'static crate::Harness>) {}
    }
}
