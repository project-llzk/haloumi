//! Types for working with Rust crates in the filesystem.

use crate::error::Error;
use cargo_toml::{Dependency, Manifest, Package, SemVer};
use std::{
    collections::{HashMap, btree_map, hash_map::Entry},
    fs::ReadDir,
    ops::Deref,
    path::{Path, PathBuf},
};

/// Represents a Rust crate located in a directory.
#[derive(Debug)]
pub struct Crate {
    base_path: PathBuf,
    manifest: Manifest,
}

impl Crate {
    /// Opens a crate at the given location in read-only mode.
    ///
    /// Will try to parse `Cargo.toml` relative to that path. Fails if the file could not be found
    /// or if it is malformed.
    pub fn open(base_path: impl AsRef<Path>) -> Result<Self, Error> {
        let manifest = Manifest::from_path(base_path.as_ref().join("Cargo.toml"))?;
        Ok(Self {
            base_path: base_path.as_ref().to_path_buf(),
            manifest,
        })
    }

    /// Returns the base path of the crate.
    pub fn base_path(&self) -> &Path {
        &self.base_path
    }

    /// Returns the path of the manifest.
    pub fn manifest_path(&self) -> PathBuf {
        self.base_path.join("Cargo.toml")
    }

    /// Returns the version of the package.
    pub fn version(&self) -> Result<&SemVer, Error> {
        Ok(self.package()?.version())
    }

    /// Returns the name of the package.
    pub fn name(&self) -> Result<&str, Error> {
        Ok(self.package()?.name())
    }

    /// Returns a reference to the package entry.
    fn package(&self) -> Result<&Package, Error> {
        self.manifest.package.as_ref().ok_or(Error::PackageNotFound)
    }

    /// Creates a copy of the crate in the provided path.
    ///
    /// Creates the directory if it doesn't exists.
    ///
    /// This is the only way to create a [`CrateMut`] from the public API.
    pub fn clone_in_path(&self, dest: impl AsRef<Path>) -> Result<CrateMut, Error> {
        log::debug!(
            "Cloning crate in '{}' into '{}'",
            self.base_path().display(),
            dest.as_ref().display()
        );
        let dest = dest.as_ref();

        if !dest.is_dir() {
            log::debug!("Creating dest directory...");
            std::fs::create_dir_all(dest)?;
        }

        let dir = std::fs::read_dir(self.base_path())?;
        copy_files_rec(self.base_path(), dest, dir)?;

        CrateMut::open(dest)
    }
}

fn copy_files_rec(base: &Path, dest: &Path, current: ReadDir) -> Result<(), Error> {
    for entry in current {
        let entry = entry?;

        let full_path = entry.path();
        let rel_path = full_path.strip_prefix(&base)?;
        let dest_path = dest.join(rel_path);
        log::debug!("{} -> {}", full_path.display(), dest_path.display());
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            std::fs::create_dir_all(dest_path)?;
            let dir = std::fs::read_dir(full_path)?;
            copy_files_rec(&base, &dest, dir)?;
        } else if file_type.is_file() {
            std::fs::copy(full_path, dest_path)?;
        } else {
            return Err(Error::UnsupportedFileType);
        }
    }
    Ok(())
}

/// A crate whose contents can be modified.
///
/// Modifications are done in-memory and are not actually applied to the corresponding
/// files in the filesystem until commited.
#[derive(Debug)]
pub struct CrateMut {
    crt: Crate,
    rust_files_cache: HashMap<PathBuf, syn::File>,
}

impl CrateMut {
    /// Opens a crate at the given location.
    ///
    /// Will try to parse `Cargo.toml` relative to that path. Fails if the file could not be found
    /// or if it is malformed.
    fn open(base_path: impl AsRef<Path>) -> Result<Self, Error> {
        Ok(Self {
            crt: Crate::open(base_path)?,
            rust_files_cache: Default::default(),
        })
    }

    /// Opens a Rust file for editing. The path of the Rust file must be relative to the crate.
    ///
    /// Returns the parsed AST. That means that this method will fail
    /// if the file is not found or if the file couldn't be parsed.
    pub fn open_rust_file(&mut self, path: impl AsRef<Path>) -> Result<&mut syn::File, Error> {
        let full_path = self.base_path().join(&path);
        let path = path.as_ref().to_path_buf();
        let entry = self.rust_files_cache.entry(path);
        match entry {
            Entry::Occupied(entry) => Ok(entry.into_mut()),
            Entry::Vacant(entry) => {
                let file = syn::parse_file(&std::fs::read_to_string(full_path)?)?;
                Ok(entry.insert(file))
            }
        }
    }

    /// Adds a dependency to the crate.
    pub fn add_dependency(&mut self, name: String, dep: Dependency) -> Result<(), Error> {
        match self.crt.manifest.dependencies.entry(name) {
            btree_map::Entry::Vacant(entry) => {
                entry.insert(dep);
                Ok(())
            }
            btree_map::Entry::Occupied(entry) => Err(Error::DuplicateDep(entry.key().clone())),
        }
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
        let base_path = self.base_path();
        self.rust_files_cache
            .iter()
            .try_for_each(|(path, contents)| {
                let full_path = base_path.join(path);
                std::fs::write(full_path, prettyplease::unparse(&contents))
            })?;
        Ok(())
    }
}

impl Deref for CrateMut {
    type Target = Crate;

    fn deref(&self) -> &Self::Target {
        &self.crt
    }
}
