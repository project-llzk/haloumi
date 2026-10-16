pub struct Harness;

pub struct ExtractorMain;

impl ExtractorMain {
    pub fn run(_: impl Iterator<Item = &'static Harness>) {}
}
