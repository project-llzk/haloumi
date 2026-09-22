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
    /// Raised when an attribute target is not present on the derived item.
    #[error("Attribute target '{0}' not found on derive target '{1}'")]
    AttributeTargetNotFound(String, String),
    /// Raised when an attribute target cannot exist on the derived item kind.
    #[error("Attribute target '{0}' is not valid for derive target '{1}'")]
    InvalidAttributeTarget(String, String),
    /// Raised when an attribute patch target is not a supported Rust-style path.
    #[error("Invalid attribute path '{0}'")]
    InvalidAttributePath(String),
    /// Raised when an attribute patch target does not match a node.
    #[error("Attribute path target '{0}' not found")]
    AttributePathTargetNotFound(String),
    /// Raised when an attribute patch target matches more than one node.
    #[error("Attribute path target '{0}' is ambiguous; found {1} matches")]
    AmbiguousAttributePathTarget(String, usize),
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
    /// Raised if encountered an unsupported filesystem object during copying.
    #[error("Unsupported filesystem object at '{0}'")]
    UnsupportedFileType(std::path::PathBuf),
    /// Raised when a requested manifest dependency does not exist.
    #[error("Dependency '{0}' was not found in the manifest")]
    DependencyNotFound(String),
    /// Raised when a generated source file would overwrite an existing file.
    #[error("Refusing to overwrite existing generated file '{0}'")]
    GeneratedFileExists(std::path::PathBuf),
    /// Raised when a generated source file path is not contained in the crate.
    #[error("Generated file path '{0}' must be relative to the crate and may not contain '..'")]
    InvalidCrateRelativePath(std::path::PathBuf),
    /// Raised when the `content` attribute of an append patch contains anything other than
    /// a list `syn::Item`
    #[error("Unexpected elements in 'content' key: {0}")]
    ForeignElementInContent(String),
}
