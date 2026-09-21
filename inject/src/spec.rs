//! Types for working with specifications.

use std::{
    borrow::Cow,
    collections::BTreeMap,
    path::{Path, PathBuf},
};

use cargo_toml::{Dependency, DepsSet, SemVer, VersionReq};
use serde::Deserialize;
use syn::parse::Parser;

use crate::{
    actions::{InjectAction, add_dep::AddDepAction, append::AppendAction, derive::DeriveAction},
    error::Error,
};

/// Registry of specifications
#[derive(Debug)]
pub struct SpecRegistry {
    specs: Vec<Spec>,
}

/// The result of looking up specifications for one resolved Cargo package.
#[derive(Debug)]
pub enum SpecMatch<'a> {
    /// No registered specification targets the package.
    None,
    /// Exactly one specification targets the package.
    One(&'a Spec),
    /// More than one specification targets the package.
    Ambiguous(Vec<&'a Spec>),
}

impl SpecRegistry {
    /// Creates a registry with no specifications.
    pub fn empty() -> Self {
        Self { specs: Vec::new() }
    }

    /// Loads all the specifications found in the given path.
    ///
    /// If the path is a file, loads a single specification.
    /// If the path is a directory, loads all the files in that directory.
    /// It does not recurse into subdirectories.
    pub fn load(path: impl AsRef<Path>) -> Result<Self, Error> {
        let mut specs = Vec::new();
        if path.as_ref().is_file() {
            specs.push(Spec::from_path(path.as_ref())?);
        } else if path.as_ref().is_dir() {
            for entry in std::fs::read_dir(path)? {
                let entry = entry?;
                if entry.file_type()?.is_file()
                    && entry.path().extension().is_some_and(|extension| extension == "toml")
                {
                    specs.push(Spec::from_path(entry.path())?);
                }
            }
        } else {
            return Err(Error::UnsupportedFileType(path.as_ref().to_path_buf()));
        }

        Ok(Self { specs })
    }

    /// Returns the registered specifications.
    pub fn specs(&self) -> &[Spec] {
        &self.specs
    }

    /// Finds specifications targeting the supplied resolved package name and version.
    pub fn find_matching(&self, name: &str, version: &SemVer) -> SpecMatch<'_> {
        let matches = self
            .specs
            .iter()
            .filter(|spec| spec.valid_target(name, version))
            .collect::<Vec<_>>();
        match matches.as_slice() {
            [] => SpecMatch::None,
            [spec] => SpecMatch::One(spec),
            _ => SpecMatch::Ambiguous(matches),
        }
    }
}

/// Top-level type representing a specification file for the injector.
#[derive(Debug, Deserialize, PartialEq)]
pub struct Spec {
    /// List of crates the specification targets, represented as a list of dependencies.
    ///
    /// The crate where the injector applies the modifications must satisfy one of these
    /// "dependencies".
    targets: Option<BTreeMap<String, VersionReq>>,
    /// Additional dependencies required by the specification.
    dependencies: Option<DepsSet>,
    patch: Option<Patches>,
}

impl Spec {
    /// Loads a specification from a path.
    pub fn from_path(path: impl AsRef<Path>) -> Result<Self, Error> {
        Ok(toml::from_str(&std::fs::read_to_string(path)?)?)
    }

    /// Returns the dependencies that need to be injected.
    pub fn dependencies(&self) -> impl Iterator<Item = (&str, &Dependency)> {
        self.dependencies
            .iter()
            .flatten()
            .map(|(name, dep)| (name.as_str(), dep))
    }

    /// Returns whether the provided name and version is a valid target for this specification.
    pub fn valid_target(&self, name: &str, version: &SemVer) -> bool {
        self.targets().any(|(target_name, target_version)| {
            name == target_name && target_version.matches(version)
        })
    }

    /// Returns an iterator with the targets of the specification.
    pub fn targets(&self) -> impl Iterator<Item = (&str, &VersionReq)> {
        self.targets
            .iter()
            .flatten()
            .map(|(name, dep)| (name.as_str(), dep))
    }

    /// Returns an iterator of append type patches.
    pub fn appends(&self) -> impl Iterator<Item = &Append> {
        self.patch.iter().flat_map(|p| p.append.as_ref()).flatten()
    }

    /// Returns an iterator of derive type patches.
    pub fn derives(&self) -> impl Iterator<Item = &Derive> {
        self.patch.iter().flat_map(|p| p.derive.as_ref()).flatten()
    }

    /// Returns an iterator of inject actions.
    pub fn actions(&self) -> impl Iterator<Item = Box<dyn InjectAction + '_>> {
        self.dependencies()
            .map(|(name, dep)| AddDepAction::boxed(name, dep))
            .chain(self.derives().map(DeriveAction::boxed))
            .chain(self.appends().map(AppendAction::boxed))
    }
}

/// List of patches that need to be applied.
#[derive(Debug, Deserialize, PartialEq)]
pub struct Patches {
    /// List of append actions.
    append: Option<Vec<Append>>,
    /// List of derive actions.
    derive: Option<Vec<Derive>>,
}

/// Append action
#[derive(Debug, Deserialize, PartialEq)]
pub struct Append {
    /// Path to the file.
    path: PathBuf,
    /// Contents to append at the end of the file.
    content: String,
}

impl Append {
    /// Returns a reference to the target path.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Returns the contents that need to be appened to the file.
    ///
    /// Each piece of content must be a valid top level item in a Rust file.
    pub fn content(&self) -> Result<syn::Item, Error> {
        let content = if self.content.ends_with(";") {
            Cow::Borrowed(&self.content)
        } else {
            Cow::Owned(format!("{};", self.content))
        };
        Ok(syn::parse_str(&content)?)
    }
}

/// Derive action
#[derive(Debug, Deserialize, PartialEq)]
pub struct Derive {
    /// Path to the file where the type is located.
    path: PathBuf,
    /// Name of the type that will derive the trait.
    #[serde(rename = "type")]
    type_name: String,
    /// Name of the trait (the derive macro) that will be derived.
    #[serde(rename = "trait")]
    trait_name: String,
    /// Additional attributes that are appended to the `#[derive(...)]` macro.
    attributes: Option<Vec<String>>,
}

impl Derive {
    /// Returns a reference to the target path.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Returns the target type.
    ///
    /// Must be a valid Rust path relative to the module represented by the file.
    /// If the target type is located inside a non-file module then the path must indicate it.
    pub fn target_type(&self) -> Result<syn::Path, Error> {
        Ok(syn::parse_str(&self.type_name)?)
    }

    /// Returns the target type as a string.
    pub fn target_type_as_str(&self) -> &str {
        &self.type_name
    }

    /// Returns the target trait.
    ///
    /// Must be a valid Rust path.
    pub fn target_trait(&self) -> Result<syn::Path, Error> {
        Ok(syn::parse_str(&self.trait_name)?)
    }

    /// Returns the additional attributes, if any.
    ///
    /// Each must be a valid Rust attribute.
    pub fn attributes(&self) -> Result<Vec<syn::Attribute>, Error> {
        Ok(self
            .attributes
            .iter()
            .flatten()
            .map(|attr| {
                if attr.starts_with("#[") && attr.ends_with("]") {
                    Cow::Borrowed(attr)
                } else {
                    Cow::Owned(format!("#[{attr}]"))
                }
            })
            .map(|s| Ok(syn::Attribute::parse_outer.parse_str(&s)?))
            .collect::<Result<Vec<Vec<_>>, Error>>()?
            .into_iter()
            .flatten()
            .collect())
    }
}

#[cfg(test)]
mod tests {

    use cargo_toml::VersionReq;

    use super::*;

    #[test]
    fn test_parsing_empty_spec() {
        let spec: Spec = toml::from_str("").unwrap();

        let expected = Spec {
            dependencies: None,
            targets: None,
            patch: None,
        };

        assert_eq!(spec, expected);
    }

    #[test]
    fn test_parsing_no_patches_spec() {
        let spec: Spec = toml::from_str(
            r#"
[targets]
midnight-proofs = "0.8"
"#,
        )
        .unwrap();

        let expected = Spec {
            dependencies: None,
            targets: Some(BTreeMap::from_iter([(
                "midnight-proofs".to_owned(),
                VersionReq::parse("0.8").unwrap(),
            )])),
            patch: None,
        };

        assert_eq!(spec, expected);
    }

    #[test]
    fn test_parsing_append_patch_spec() {
        let spec: Spec = toml::from_str(
            r#"
[[patch.append]]
path = "foo.rs"
content = "__impl1!();"
"#,
        )
        .unwrap();

        let expected = Spec {
            dependencies: None,
            targets: None,
            patch: Some(Patches {
                append: Some(vec![Append {
                    path: PathBuf::from("foo.rs"),
                    content: String::from("__impl1!();"),
                }]),
                derive: None,
            }),
        };

        assert_eq!(spec, expected);
    }

    #[test]
    fn test_parsing_append_patches_spec() {
        let spec: Spec = toml::from_str(
            r#"
[[patch.append]]
path = "foo.rs"
content = "__impl1!();"

[[patch.append]]
path = "bar.rs"
content = "__impl2!();"
"#,
        )
        .unwrap();

        let expected = Spec {
            dependencies: None,
            targets: None,
            patch: Some(Patches {
                append: Some(vec![
                    Append {
                        path: PathBuf::from("foo.rs"),
                        content: String::from("__impl1!();"),
                    },
                    Append {
                        path: PathBuf::from("bar.rs"),
                        content: String::from("__impl2!();"),
                    },
                ]),
                derive: None,
            }),
        };

        assert_eq!(spec, expected);
    }

    #[test]
    fn test_parsing_append_derive_spec() {
        let spec: Spec = toml::from_str(
            r#"
[[patch.derive]]
path = "foo.rs"
type = "Foo"
trait = "Bar"
"#,
        )
        .unwrap();

        let expected = Spec {
            dependencies: None,
            targets: None,
            patch: Some(Patches {
                derive: Some(vec![Derive {
                    path: PathBuf::from("foo.rs"),
                    type_name: String::from("Foo"),
                    trait_name: String::from("Bar"),
                    attributes: None,
                }]),
                append: None,
            }),
        };

        assert_eq!(spec, expected);
    }

    #[test]
    fn test_parsing_append_derive_with_attrs_spec() {
        let spec: Spec = toml::from_str(
            r#"
[[patch.derive]]
path = "foo.rs"
type = "Foo"
trait = "Bar"
attributes = ["baz()"]
"#,
        )
        .unwrap();

        let expected = Spec {
            dependencies: None,
            targets: None,
            patch: Some(Patches {
                derive: Some(vec![Derive {
                    path: PathBuf::from("foo.rs"),
                    type_name: String::from("Foo"),
                    trait_name: String::from("Bar"),
                    attributes: Some(vec![String::from("baz()")]),
                }]),
                append: None,
            }),
        };

        assert_eq!(spec, expected);
    }
}
