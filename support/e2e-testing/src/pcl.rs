use std::path::{Path, PathBuf};

/// PCL artifact result.
#[derive(Debug)]
pub struct PclArtifact<'p> {
    pub(crate) requested: PathBuf,
    pub(crate) path: Option<&'p Path>,
}

impl PclArtifact<'_> {
    /// Checks if the contents of the artifact match the expected value.
    pub fn matches(&self, expected: &str) {
        let Some(path) = self.path else {
            panic!(
                "Expected PCL artifact {} not found",
                self.requested.display()
            );
        };
        let output = match std::fs::read_to_string(path) {
            Ok(output) => clean_string(&output),
            Err(err) => panic!("Failed to read artifact {}: {err}", path.display()),
        };
        similar_asserts::assert_eq!(clean_string(expected), output);
    }
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
