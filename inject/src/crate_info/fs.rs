//! Utilities for interacting with the file system.

use std::{
    collections::HashSet,
    path::{Path, PathBuf},
};

use crate::error::Error;

pub fn resolve_path(path: &Path) -> Result<PathBuf, Error> {
    let path = std::path::absolute(path)?;
    let mut existing_ancestor = path.as_path();
    while !existing_ancestor.exists() {
        existing_ancestor = existing_ancestor
            .parent()
            .expect("an absolute path has an existing ancestor");
    }

    let suffix = path
        .strip_prefix(existing_ancestor)
        .expect("an ancestor is a path prefix");
    Ok(existing_ancestor.canonicalize()?.join(suffix))
}

pub struct IgnoredFiles<'p> {
    files: HashSet<&'p Path>,
}

impl<'p> IgnoredFiles<'p> {
    pub fn new() -> Self {
        Self {
            files: Default::default(),
        }
    }

    pub fn add(&mut self, path: &'p Path) -> &mut Self {
        self.files.insert(path);
        self
    }

    pub fn ignored(&self, path: &Path) -> bool {
        self.files.contains(path)
    }
}

/// Abstraction over the file system.
///
/// For production use, [`copy_files_rec`] uses an implementation that
/// wraps over [`std::fs`].
///
/// For unit testing, we use a mock implementation that does not touch the file system.
trait FileSystem {
    type DirEntry;
    type Error: Into<Error>;
    type ReadDir: Iterator<Item = Result<Self::DirEntry, Self::Error>>;
    type FileType;

    fn read_dir(&self, path: impl AsRef<Path>) -> Result<Self::ReadDir, Error>;

    fn create_dir_all(&mut self, path: impl AsRef<Path>) -> Result<(), Error>;

    fn copy(&mut self, from: impl AsRef<Path>, to: impl AsRef<Path>) -> Result<(), Error>;

    fn copy_symlink(&mut self, from: impl AsRef<Path>, to: impl AsRef<Path>) -> Result<(), Error>;

    fn entry_path(&self, entry: &Self::DirEntry) -> PathBuf;

    fn entry_file_type(&self, entry: &Self::DirEntry) -> Result<Self::FileType, Error>;

    fn is_dir(&self, file_type: &Self::FileType) -> bool;

    fn is_file(&self, file_type: &Self::FileType) -> bool;

    fn is_symlink(&self, file_type: &Self::FileType) -> bool;
}

struct DefaultFileSystem;

impl FileSystem for DefaultFileSystem {
    type DirEntry = std::fs::DirEntry;
    type Error = std::io::Error;
    type ReadDir = std::fs::ReadDir;
    type FileType = std::fs::FileType;

    fn read_dir(&self, path: impl AsRef<Path>) -> Result<Self::ReadDir, Error> {
        Ok(std::fs::read_dir(path)?)
    }

    fn create_dir_all(&mut self, path: impl AsRef<Path>) -> Result<(), Error> {
        Ok(std::fs::create_dir_all(path)?)
    }

    fn copy(&mut self, from: impl AsRef<Path>, to: impl AsRef<Path>) -> Result<(), Error> {
        std::fs::copy(from, to)?;
        Ok(())
    }

    #[cfg(unix)]
    fn copy_symlink(&mut self, from: impl AsRef<Path>, to: impl AsRef<Path>) -> Result<(), Error> {
        std::os::unix::fs::symlink(std::fs::read_link(from)?, to)?;
        Ok(())
    }

    #[cfg(windows)]
    fn copy_symlink(&mut self, from: impl AsRef<Path>, to: impl AsRef<Path>) -> Result<(), Error> {
        let target = std::fs::read_link(from)?;
        if source.metadata()?.is_dir() {
            std::os::windows::fs::symlink_dir(target, to)?;
        } else {
            std::os::windows::fs::symlink_file(target, to)?;
        }
        Ok(())
    }

    fn entry_path(&self, entry: &Self::DirEntry) -> PathBuf {
        entry.path()
    }

    fn entry_file_type(&self, entry: &Self::DirEntry) -> Result<Self::FileType, Error> {
        Ok(entry.file_type()?)
    }

    fn is_dir(&self, file_type: &Self::FileType) -> bool {
        file_type.is_dir()
    }

    fn is_file(&self, file_type: &Self::FileType) -> bool {
        file_type.is_file()
    }

    fn is_symlink(&self, file_type: &Self::FileType) -> bool {
        file_type.is_symlink()
    }
}

fn copy_files_rec_impl<FS: FileSystem>(
    fs: &mut FS,
    base: &Path,
    dest: &Path,
    current: &Path,
    ignore: &IgnoredFiles<'_>,
) -> Result<(), Error>
where
    Error: From<<FS as FileSystem>::Error>,
{
    for entry in fs.read_dir(current)? {
        let entry = entry?;

        let full_path = fs.entry_path(&entry);
        let rel_path = full_path.strip_prefix(base)?;
        let dest_path = dest.join(rel_path);
        if ignore.ignored(rel_path) {
            continue;
        }

        log::debug!("{} -> {}", full_path.display(), dest_path.display());
        let file_type = fs.entry_file_type(&entry)?;
        if fs.is_dir(&file_type) {
            fs.create_dir_all(dest_path)?;
            copy_files_rec_impl(fs, base, dest, &full_path, ignore)?;
        } else if fs.is_file(&file_type) {
            fs.copy(full_path, dest_path)?;
        } else if fs.is_symlink(&file_type) {
            fs.copy_symlink(&full_path, &dest_path)?;
        } else {
            return Err(Error::UnsupportedFileType(full_path));
        }
    }
    Ok(())
}

pub fn copy_files_rec(
    base: &Path,
    dest: &Path,
    current: &Path,
    ignore: &IgnoredFiles<'_>,
) -> Result<(), Error> {
    copy_files_rec_impl(&mut DefaultFileSystem, base, dest, current, ignore)
}
