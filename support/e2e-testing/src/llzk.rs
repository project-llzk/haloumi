use std::path::{Path, PathBuf};

use llzk::prelude::{LlzkContext, Module};

/// LLZK artifact result.
#[derive(Debug)]
pub struct LlzkArtifact<'p> {
    pub(crate) requested: PathBuf,
    pub(crate) path: Option<&'p Path>,
}

impl LlzkArtifact<'_> {
    /// Checks if the contents of the artifact match the expected value.
    pub fn matches(&self, expected: &str) {
        let Some(path) = self.path else {
            panic!(
                "Expected PCL artifact {} not found",
                self.requested.display()
            );
        };
        let context = LlzkContext::new();
        let Some(output) = (match std::fs::read_to_string(path) {
            Ok(output) => Module::parse(&context, &output),
            Err(err) => panic!("Failed to read artifact {}: {err}", path.display()),
        }) else {
            panic!("Failed to parse LLZK artifact: {}", path.display());
        };

        mlir_testutils::assert_module_eq(&output, expected);
    }
}
