//! Error type.

use semver::Version;

/// Error type.
#[derive(thiserror::Error, Debug)]
pub enum Error {
    /// Raised when the injector couldn't find a valid specification to apply.
    #[error("Could not find a valid spec for source crate {0} version {1}")]
    NoValidSpec(String, Version),
    /// Raised when there is more than one specification that can be applied.
    #[error("Too many valid specs for source crate {0} version {1}. Found {2} but expected 1")]
    TooManyValidSpec(String, Version, usize),
    /// Raised when the injector fails to find the target of a `[[patch.derive]]` entry.
    #[error("Derive target '{0}' not found")]
    DeriveTargetNotFound(String),
    /// Forwards an error related to `cargo_toml`.
    #[error(transparent)]
    Cargo(#[from] cargo_toml::Error),
    /// Forwards an error related to TOML serialization.
    #[error(transparent)]
    TomlSer(#[from] toml::ser::Error),
    /// Forwards an error related to TOML deserialization.
    #[error(transparent)]
    TomlDe(#[from] toml::de::Error),
    /// Forwards an IO related error.
    #[error(transparent)]
    Io(#[from] std::io::Error),
    /// Forwards an error while parsing Rust entities.
    #[error(transparent)]
    Parsing(#[from] syn::Error),
    /// Forwards an error related to path prefix stripping.
    #[error(transparent)]
    StripPrefix(#[from] std::path::StripPrefixError),
    /// Raised when a crate's manifest does not contain a package definition.
    #[error("Package not found")]
    PackageNotFound,
    /// Raised if an injected dependency is already in a crate's manifest.
    #[error("Dependency '{0}' is already in the manifest")]
    DuplicateDep(String),
    /// Raised if encountered an unsupported file type during IO operations.
    #[error("Unsupported file type")]
    UnsupportedFileType,
}
