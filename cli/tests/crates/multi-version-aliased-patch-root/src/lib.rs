pub fn harnesses() -> impl Iterator<Item = &'static haloumi_extractor_runner::Harness> {
    let _ = (foo_10::VERSION, foo_11::VERSION, foo_20::VERSION);
    std::iter::empty()
}
