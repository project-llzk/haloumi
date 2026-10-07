#[cfg(any(
    all(feature = "configured-feature", not(feature = "default-feature")),
    feature = "all-feature"
))]
pub fn harnesses() -> impl Iterator<Item = &'static custom_extractor::Harness> {
    std::iter::empty()
}
