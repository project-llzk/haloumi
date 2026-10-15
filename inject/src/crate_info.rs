//! Types for working with Rust crates in the filesystem.

use crate::{
    crate_info::fs::{IgnoredFiles, copy_files_rec, resolve_path},
    error::Error,
};
use cargo_toml::{Dependency, DepsSet, Manifest, Package, Product, SemVer, Workspace};
use std::{
    collections::{HashMap, btree_map, hash_map::Entry},
    path::{Component, Path, PathBuf},
};

mod fs;

mod sealed {
    pub trait Sealed {}
}

/// Shared read-only operations for crate representations managed by this crate.
///
/// This trait is sealed and cannot be implemented outside of `haloumi-inject`.
pub trait CrateLike: sealed::Sealed {
    /// Returns the canonical base path of the crate.
    fn base_path(&self) -> &Path;

    /// Returns the path of the manifest.
    fn manifest_path(&self) -> PathBuf {
        self.base_path().join("Cargo.toml")
    }

    /// Returns the version of the package.
    fn version(&self) -> Result<&SemVer, Error>;

    /// Returns the name of the package.
    fn name(&self) -> Result<&str, Error>;

    /// Creates a copy of the crate in the provided, nonexistent path.
    ///
    /// The destination cannot already exist.
    /// [`CrateMut`] clones only the committed filesystem state, excluding uncommitted edits.
    fn clone_in_path(&self, dest: impl AsRef<Path>) -> Result<CrateMut, Error>;
}

/// Represents a Rust crate located in a directory.
#[derive(Debug)]
pub struct Crate {
    base_path: PathBuf,
    manifest: Manifest,
}

impl Crate {
    /// Opens a crate at the given location in read-only mode.
    ///
    /// Canonicalizes the base path, then parses its `Cargo.toml`. Fails if the directory or
    /// manifest could not be found, or if the manifest is malformed.
    pub fn open(base_path: impl AsRef<Path>) -> Result<Self, Error> {
        let base_path = base_path.as_ref().canonicalize()?;
        let manifest = Manifest::from_path(base_path.join("Cargo.toml"))?;
        Ok(Self {
            base_path,
            manifest,
        })
    }
}

impl sealed::Sealed for Crate {}

impl CrateLike for Crate {
    fn base_path(&self) -> &Path {
        &self.base_path
    }

    fn version(&self) -> Result<&SemVer, Error> {
        Ok(package(&self.manifest)?.version())
    }

    fn name(&self) -> Result<&str, Error> {
        Ok(package(&self.manifest)?.name())
    }

    fn clone_in_path(&self, dest: impl AsRef<Path>) -> Result<CrateMut, Error> {
        clone_crate_in_path(&self.base_path, &self.manifest, dest)
    }
}

fn package(manifest: &Manifest) -> Result<&Package, Error> {
    manifest.package.as_ref().ok_or(Error::PackageNotFound)
}

fn clone_crate_in_path(
    base_path: &Path,
    manifest: &Manifest,
    dest: impl AsRef<Path>,
) -> Result<CrateMut, Error> {
    log::debug!(
        "Cloning crate in '{}' into '{}'",
        base_path.display(),
        dest.as_ref().display()
    );
    let dest = dest.as_ref();

    warn_manifest_overrides(base_path, manifest);

    match std::fs::symlink_metadata(dest) {
        Ok(_) => return Err(Error::CloneDestinationExists(dest.to_path_buf())),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(error.into()),
    }
    log::debug!("Creating dest directory...");
    std::fs::create_dir_all(dest)?;

    let mut ignore = IgnoredFiles::new();
    ignore.add(Path::new("target"));
    let resolved_destination = resolve_path(dest)?;
    if resolved_destination.starts_with(base_path) {
        let relative_destination = resolved_destination.strip_prefix(base_path)?;
        ignore.add(relative_destination);
    }
    copy_files_rec(base_path, dest, base_path, &ignore)?;
    std::fs::write(
        dest.join("Cargo.toml"),
        toml::to_string_pretty(&standalone_manifest(manifest, base_path))?,
    )?;

    CrateMut::open(dest)
}

fn standalone_manifest(manifest: &Manifest, base_path: &Path) -> Manifest {
    let mut manifest = manifest.clone();
    rebase_relative_path_dependencies(&mut manifest, base_path);
    detach_from_workspace(&mut manifest);
    manifest
}

fn rebase_relative_path_dependencies(manifest: &mut Manifest, base_path: &Path) {
    rebase_dependencies(&mut manifest.dependencies, base_path);
    rebase_dependencies(&mut manifest.build_dependencies, base_path);
    rebase_dependencies(&mut manifest.dev_dependencies, base_path);
    for target in manifest.target.values_mut() {
        rebase_dependencies(&mut target.dependencies, base_path);
        rebase_dependencies(&mut target.build_dependencies, base_path);
        rebase_dependencies(&mut target.dev_dependencies, base_path);
    }
}

fn rebase_dependencies(dependencies: &mut DepsSet, base_path: &Path) {
    for dependency in dependencies.values_mut() {
        let Dependency::Detailed(detail) = dependency else {
            continue;
        };
        let Some(path) = detail.path.as_mut() else {
            continue;
        };
        if Path::new(path).is_relative() {
            *path = base_path.join(&path).display().to_string();
        }
    }
}

fn detach_from_workspace(manifest: &mut Manifest) {
    if let Some(package) = &mut manifest.package {
        package.workspace = None;
    }
    // An empty workspace prevents Cargo from associating a copy nested beneath
    // the source workspace's target directory with that ancestor workspace.
    manifest.workspace = Some(Workspace {
        members: Vec::new(),
        default_members: Vec::new(),
        package: None,
        exclude: Vec::new(),
        metadata: None,
        resolver: None,
        dependencies: DepsSet::default(),
        lints: Default::default(),
    });
}

#[expect(
    deprecated,
    reason = "[replace] manifests remain supported for copied crates"
)]
fn warn_manifest_overrides(base_path: &Path, manifest: &Manifest) {
    if !manifest.patch.is_empty() {
        log::warn!(
            "Copied crate '{}' contains [patch] overrides; they are preserved and may affect dependency resolution",
            base_path.display()
        );
    }
    if !manifest.replace.is_empty() {
        log::warn!(
            "Copied crate '{}' contains deprecated [replace] overrides; they are preserved and may affect dependency resolution",
            base_path.display()
        );
    }
}

/// A crate whose contents can be modified.
///
/// Modifications are done in-memory and are not actually applied to the corresponding
/// files in the filesystem until commited.
#[derive(Debug)]
pub struct CrateMut {
    manifest: Manifest,
    rust_files_cache: RustFilesCache,
}

/// In-memory Rust source files staged for a crate.
#[derive(Debug)]
struct RustFilesCache {
    base_path: PathBuf,
    files: HashMap<PathBuf, syn::File>,
}

impl RustFilesCache {
    fn new(base_path: PathBuf) -> Self {
        Self {
            base_path,
            files: HashMap::new(),
        }
    }

    fn base_path(&self) -> &Path {
        &self.base_path
    }

    fn open(&mut self, path: &Path) -> Result<&mut syn::File, Error> {
        let full_path = self.resolve_path(path)?;
        match self.files.entry(full_path) {
            Entry::Occupied(entry) => Ok(entry.into_mut()),
            Entry::Vacant(entry) => {
                let file = syn::parse_file(&std::fs::read_to_string(entry.key())?)?;
                Ok(entry.insert(file))
            }
        }
    }

    fn create(&mut self, path: &Path, file: RustFile) -> Result<(), Error> {
        let full_path = self.resolve_path(path)?;
        if full_path.exists() || self.files.contains_key(&full_path) {
            return Err(Error::GeneratedFileExists(path.to_path_buf()));
        }
        self.files.insert(full_path, file.into_inner());
        Ok(())
    }

    fn commit(&self) -> Result<(), Error> {
        self.files.iter().try_for_each(|(path, contents)| {
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent)?;
            }
            std::fs::write(path, prettyplease::unparse(contents))
        })?;
        Ok(())
    }

    fn resolve_path(&self, path: &Path) -> Result<PathBuf, Error> {
        validate_crate_relative_path(path)?;
        resolve_path(&self.base_path.join(path))
    }
}

fn validate_crate_relative_path(path: &Path) -> Result<(), Error> {
    if path.is_absolute()
        || path
            .components()
            .any(|component| matches!(component, Component::ParentDir))
    {
        return Err(Error::InvalidCrateRelativePath(path.to_path_buf()));
    }
    Ok(())
}

/// A Rust source file that has been parsed successfully.
#[derive(Debug)]
pub struct RustFile {
    file: syn::File,
}

impl RustFile {
    /// Creates an empty Rust source file.
    pub fn new() -> Self {
        Self {
            file: syn::parse_file("").expect("an empty Rust source file is valid"),
        }
    }

    /// Parses Rust source into a source file.
    pub fn parse_str(contents: &str) -> Result<Self, Error> {
        Ok(Self {
            file: syn::parse_file(contents)?,
        })
    }

    fn into_inner(self) -> syn::File {
        self.file
    }
}

impl Default for RustFile {
    fn default() -> Self {
        Self::new()
    }
}

impl CrateMut {
    /// Opens a crate at the given location.
    ///
    /// Will try to parse `Cargo.toml` relative to that path. Fails if the file could not be found
    /// or if it is malformed.
    fn open(base_path: impl AsRef<Path>) -> Result<Self, Error> {
        let crate_info = Crate::open(base_path)?;
        Ok(Self {
            rust_files_cache: RustFilesCache::new(crate_info.base_path),
            manifest: crate_info.manifest,
        })
    }

    /// Opens a Rust file for editing. The path must be relative to the crate and cannot contain
    /// `..`.
    ///
    /// Returns the parsed AST. That means that this method will fail
    /// if the file is not found or if the file couldn't be parsed.
    pub fn open_rust_file(&mut self, path: impl AsRef<Path>) -> Result<&mut syn::File, Error> {
        self.rust_files_cache.open(path.as_ref())
    }

    /// Adds a dependency to the crate.
    pub fn add_dependency(&mut self, name: String, dep: Dependency) -> Result<(), Error> {
        match self.manifest.dependencies.entry(name) {
            btree_map::Entry::Vacant(entry) => {
                entry.insert(dep);
                Ok(())
            }
            btree_map::Entry::Occupied(entry) => Err(Error::DuplicateDep(entry.key().clone())),
        }
    }

    /// Adds an explicitly declared binary target to the crate.
    ///
    /// The source path must be relative to the crate and cannot contain `..`. The target name
    /// must not already be declared by another `[[bin]]` entry.
    pub fn add_binary_target(
        &mut self,
        name: impl Into<String>,
        path: impl AsRef<Path>,
    ) -> Result<(), Error> {
        let name = name.into();
        let path = path.as_ref();
        validate_crate_relative_path(path)?;
        if self
            .manifest
            .bin
            .iter()
            .any(|target| target.name.as_deref() == Some(&name))
        {
            return Err(Error::DuplicateBin(name));
        }
        self.manifest.bin.push(Product {
            name: Some(name),
            path: Some(path.display().to_string()),
            ..Product::default()
        });
        Ok(())
    }

    /// Replaces a named normal dependency with a local path dependency.
    ///
    /// Existing dependency options such as package rename, version requirement, features,
    /// optionality, and default-feature selection are retained where Cargo permits them.
    pub fn replace_dependency_with_path(
        &mut self,
        name: &str,
        path: impl AsRef<Path>,
    ) -> Result<(), Error> {
        let dependency = self
            .manifest
            .dependencies
            .get_mut(name)
            .ok_or_else(|| Error::DependencyNotFound(name.to_owned()))?;
        let detail = dependency.try_detail_mut()?;
        detail.path = Some(path.as_ref().display().to_string());
        detail.registry = None;
        detail.registry_index = None;
        detail.git = None;
        detail.branch = None;
        detail.tag = None;
        detail.rev = None;
        Ok(())
    }

    /// Creates a new Rust source file relative to the copied crate.
    ///
    /// The source is parsed before staging and cannot overwrite either an existing file or a
    /// previously staged file.
    pub fn create_rust_file(
        &mut self,
        path: impl AsRef<Path>,
        file: RustFile,
    ) -> Result<(), Error> {
        self.rust_files_cache.create(path.as_ref(), file)
    }

    /// Commits the local edits to disk.
    ///
    /// Possible modifications are:
    ///  - Modifications to the in-memory manifest.
    ///  - Modifications to opened rust files.
    pub fn commit(&self) -> Result<(), Error> {
        self.commit_manifest()?;
        self.commit_rust_files()?;

        Ok(())
    }

    fn commit_manifest(&self) -> Result<(), Error> {
        let contents = toml::to_string_pretty(&self.manifest)?;
        std::fs::write(self.manifest_path(), contents)?;
        Ok(())
    }

    fn commit_rust_files(&self) -> Result<(), Error> {
        self.rust_files_cache.commit()
    }
}

impl sealed::Sealed for CrateMut {}

impl CrateLike for CrateMut {
    fn base_path(&self) -> &Path {
        self.rust_files_cache.base_path()
    }

    fn version(&self) -> Result<&SemVer, Error> {
        Ok(package(&self.manifest)?.version())
    }

    fn name(&self) -> Result<&str, Error> {
        Ok(package(&self.manifest)?.name())
    }

    fn clone_in_path(&self, dest: impl AsRef<Path>) -> Result<CrateMut, Error> {
        let manifest = Manifest::from_path(self.manifest_path())?;
        clone_crate_in_path(self.base_path(), &manifest, dest)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_creates_an_empty_file() {
        let file = RustFile::new();
        assert!(file.file.attrs.is_empty());
        assert!(file.file.items.is_empty());
    }

    #[test]
    fn default_creates_an_empty_file() {
        let file = RustFile::default();
        assert!(file.file.attrs.is_empty());
        assert!(file.file.items.is_empty());
    }

    #[test]
    fn parse_str_accepts_valid_rust() {
        let file = RustFile::parse_str("pub fn fixture() {}\n").unwrap();
        assert_eq!(file.file.items.len(), 1);
    }

    #[test]
    fn parse_str_rejects_invalid_rust() {
        assert!(matches!(
            RustFile::parse_str("fn {"),
            Err(Error::Parsing(_))
        ));
    }
}
