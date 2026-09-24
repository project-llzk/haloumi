pub struct Harness;

pub use main_impl::ExtractorMain;

pub mod main_impl {
    pub struct ExtractorMain;

    impl ExtractorMain {
        pub fn run(_: impl Iterator<Item = &'static crate::Harness>) {}
    }
}
