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

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        cell::RefCell,
        collections::{HashMap, HashSet},
        io,
    };

    const BASE: &str = "/source";
    const DEST: &str = "/destination";

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum MockFileType {
        Dir,
        File,
        Symlink,
        Other,
    }

    #[derive(Clone, Debug)]
    struct MockDirEntry {
        path: PathBuf,
        file_type: MockFileType,
        fails_to_read: bool,
        fails_file_type: bool,
    }

    impl MockDirEntry {
        fn new(path: impl Into<PathBuf>, file_type: MockFileType) -> Self {
            Self {
                path: path.into(),
                file_type,
                fails_to_read: false,
                fails_file_type: false,
            }
        }

        fn unreadable(mut self) -> Self {
            self.fails_to_read = true;
            self
        }

        fn without_file_type(mut self) -> Self {
            self.fails_file_type = true;
            self
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    enum OperationKind {
        ReadDir,
        CreateDir,
        Copy,
        CopySymlink,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Operation {
        CreateDir(PathBuf),
        Copy { from: PathBuf, to: PathBuf },
        CopySymlink { from: PathBuf, to: PathBuf },
    }

    impl Operation {
        fn kind(&self) -> OperationKind {
            match self {
                Self::CreateDir(_) => OperationKind::CreateDir,
                Self::Copy { .. } => OperationKind::Copy,
                Self::CopySymlink { .. } => OperationKind::CopySymlink,
            }
        }

        fn path(&self) -> &Path {
            match self {
                Self::CreateDir(path) => path,
                Self::Copy { from, .. } | Self::CopySymlink { from, .. } => from,
            }
        }
    }

    struct MockFileSystem {
        entries: HashMap<PathBuf, Vec<MockDirEntry>>,
        failing_operations: HashSet<(OperationKind, PathBuf)>,
        read_dirs: RefCell<Vec<PathBuf>>,
        operations: Vec<Operation>,
    }

    impl MockFileSystem {
        fn with_entries(entries: impl IntoIterator<Item = (PathBuf, Vec<MockDirEntry>)>) -> Self {
            Self {
                entries: entries.into_iter().collect(),
                failing_operations: HashSet::new(),
                read_dirs: RefCell::new(Vec::new()),
                operations: Vec::new(),
            }
        }

        fn fail(&mut self, operation: OperationKind, path: impl Into<PathBuf>) {
            self.failing_operations.insert((operation, path.into()));
        }

        fn record(&mut self, operation: Operation) -> Result<(), Error> {
            let fails = self
                .failing_operations
                .contains(&(operation.kind(), operation.path().to_path_buf()));
            self.operations.push(operation.clone());
            if fails {
                return Err(io::Error::other(format!("mock failure: {operation:?}")).into());
            }
            Ok(())
        }
    }

    impl FileSystem for MockFileSystem {
        type DirEntry = MockDirEntry;
        type Error = io::Error;
        type ReadDir = std::vec::IntoIter<Result<Self::DirEntry, Self::Error>>;
        type FileType = MockFileType;

        fn read_dir(&self, path: impl AsRef<Path>) -> Result<Self::ReadDir, Error> {
            let path = path.as_ref().to_path_buf();
            self.read_dirs.borrow_mut().push(path.clone());
            if self
                .failing_operations
                .contains(&(OperationKind::ReadDir, path.clone()))
            {
                return Err(
                    io::Error::other(format!("mock failure: read_dir {}", path.display())).into(),
                );
            }
            Ok(self
                .entries
                .get(&path)
                .cloned()
                .unwrap_or_default()
                .into_iter()
                .map(|entry| {
                    if entry.fails_to_read {
                        Err(io::Error::other("mock failure: directory entry"))
                    } else {
                        Ok(entry)
                    }
                })
                .collect::<Vec<_>>()
                .into_iter())
        }

        fn create_dir_all(&mut self, path: impl AsRef<Path>) -> Result<(), Error> {
            self.record(Operation::CreateDir(path.as_ref().to_path_buf()))
        }

        fn copy(&mut self, from: impl AsRef<Path>, to: impl AsRef<Path>) -> Result<(), Error> {
            self.record(Operation::Copy {
                from: from.as_ref().to_path_buf(),
                to: to.as_ref().to_path_buf(),
            })
        }

        fn copy_symlink(
            &mut self,
            from: impl AsRef<Path>,
            to: impl AsRef<Path>,
        ) -> Result<(), Error> {
            self.record(Operation::CopySymlink {
                from: from.as_ref().to_path_buf(),
                to: to.as_ref().to_path_buf(),
            })
        }

        fn entry_path(&self, entry: &Self::DirEntry) -> PathBuf {
            entry.path.clone()
        }

        fn entry_file_type(&self, entry: &Self::DirEntry) -> Result<Self::FileType, Error> {
            if entry.fails_file_type {
                return Err(io::Error::other("mock failure: file type").into());
            }
            Ok(entry.file_type)
        }

        fn is_dir(&self, file_type: &Self::FileType) -> bool {
            *file_type == MockFileType::Dir
        }

        fn is_file(&self, file_type: &Self::FileType) -> bool {
            *file_type == MockFileType::File
        }

        fn is_symlink(&self, file_type: &Self::FileType) -> bool {
            *file_type == MockFileType::Symlink
        }
    }

    fn path(path: &str) -> PathBuf {
        PathBuf::from(path)
    }

    fn copy_with(fs: &mut MockFileSystem, ignore: &IgnoredFiles<'_>) -> Result<(), Error> {
        copy_files_rec_impl(
            fs,
            Path::new(BASE),
            Path::new(DEST),
            Path::new(BASE),
            ignore,
        )
    }

    #[test]
    fn copies_nested_files_symlinks_and_empty_directories() {
        let mut fs = MockFileSystem::with_entries([
            (
                path(BASE),
                vec![
                    MockDirEntry::new("/source/src", MockFileType::Dir),
                    MockDirEntry::new("/source/linked.rs", MockFileType::Symlink),
                    MockDirEntry::new("/source/empty", MockFileType::Dir),
                ],
            ),
            (
                path("/source/src"),
                vec![MockDirEntry::new("/source/src/lib.rs", MockFileType::File)],
            ),
            (path("/source/empty"), vec![]),
        ]);

        copy_with(&mut fs, &IgnoredFiles::new()).unwrap();

        assert!(
            fs.operations
                .contains(&Operation::CreateDir(path("/destination/src")))
        );
        assert!(
            fs.operations
                .contains(&Operation::CreateDir(path("/destination/empty")))
        );
        assert!(fs.operations.contains(&Operation::Copy {
            from: path("/source/src/lib.rs"),
            to: path("/destination/src/lib.rs"),
        }));
        assert!(fs.operations.contains(&Operation::CopySymlink {
            from: path("/source/linked.rs"),
            to: path("/destination/linked.rs"),
        }));
    }

    #[test]
    fn ignored_entries_are_not_copied_or_traversed() {
        let ignored_dir = Path::new("ignored");
        let ignored_file = Path::new("kept/ignored.rs");
        let mut ignore = IgnoredFiles::new();
        ignore.add(ignored_dir).add(ignored_file);
        let mut fs = MockFileSystem::with_entries([
            (
                path(BASE),
                vec![
                    MockDirEntry::new("/source/ignored", MockFileType::Dir),
                    MockDirEntry::new("/source/kept", MockFileType::Dir),
                ],
            ),
            (
                path("/source/kept"),
                vec![
                    MockDirEntry::new("/source/kept/ignored.rs", MockFileType::File),
                    MockDirEntry::new("/source/kept/copied.rs", MockFileType::File),
                ],
            ),
            (
                path("/source/ignored"),
                vec![MockDirEntry::new(
                    "/source/ignored/child.rs",
                    MockFileType::File,
                )],
            ),
        ]);

        copy_with(&mut fs, &ignore).unwrap();

        assert!(
            !fs.operations
                .contains(&Operation::CreateDir(path("/destination/ignored")))
        );
        assert!(!fs.read_dirs.borrow().contains(&path("/source/ignored")));
        assert!(!fs.operations.contains(&Operation::Copy {
            from: path("/source/kept/ignored.rs"),
            to: path("/destination/kept/ignored.rs"),
        }));
        assert!(fs.operations.contains(&Operation::Copy {
            from: path("/source/kept/copied.rs"),
            to: path("/destination/kept/copied.rs"),
        }));
    }

    #[test]
    fn rejects_unsupported_file_types() {
        let mut fs = MockFileSystem::with_entries([(
            path(BASE),
            vec![MockDirEntry::new("/source/socket", MockFileType::Other)],
        )]);

        let result = copy_with(&mut fs, &IgnoredFiles::new());

        assert!(matches!(
            result,
            Err(Error::UnsupportedFileType(path)) if path == Path::new("/source/socket")
        ));
        assert!(fs.operations.is_empty());
    }

    #[test]
    fn propagates_filesystem_failures() {
        let cases = [
            (
                "reading a directory",
                MockFileSystem::with_entries([(path(BASE), vec![])]),
                Some((OperationKind::ReadDir, path(BASE))),
            ),
            (
                "reading a directory entry",
                MockFileSystem::with_entries([(
                    path(BASE),
                    vec![MockDirEntry::new("/source/file", MockFileType::File).unreadable()],
                )]),
                None,
            ),
            (
                "reading a file type",
                MockFileSystem::with_entries([(
                    path(BASE),
                    vec![MockDirEntry::new("/source/file", MockFileType::File).without_file_type()],
                )]),
                None,
            ),
            (
                "creating a directory",
                MockFileSystem::with_entries([(
                    path(BASE),
                    vec![MockDirEntry::new("/source/dir", MockFileType::Dir)],
                )]),
                Some((OperationKind::CreateDir, path("/destination/dir"))),
            ),
            (
                "copying a file",
                MockFileSystem::with_entries([(
                    path(BASE),
                    vec![MockDirEntry::new("/source/file", MockFileType::File)],
                )]),
                Some((OperationKind::Copy, path("/source/file"))),
            ),
            (
                "copying a symlink",
                MockFileSystem::with_entries([(
                    path(BASE),
                    vec![MockDirEntry::new("/source/link", MockFileType::Symlink)],
                )]),
                Some((OperationKind::CopySymlink, path("/source/link"))),
            ),
        ];

        for (description, mut fs, failure) in cases {
            if let Some((operation, path)) = failure {
                fs.fail(operation, path);
            }
            assert!(
                copy_with(&mut fs, &IgnoredFiles::new()).is_err(),
                "{description}"
            );
        }
    }
}
