//! Application orchestration for the `cargo haloumi` command.

use std::{
    fs,
    path::{Path, PathBuf},
};

use cargo_metadata::{CargoOpt, DependencyKind, Metadata, MetadataCommand, Package, PackageId};
use haloumi_inject::spec::SpecRegistry;

use crate::{
    Args, Error,
    config::{Config, TargetConfig},
    tasks,
};

/// The initialized `cargo haloumi` application.
#[derive(Debug)]
pub(crate) struct App {
    state: AppState,
}

/// Shared state for the extraction workflow tasks.
#[derive(Debug)]
pub(crate) struct AppState {
    pub(crate) project: CargoProject,
    pub(crate) target: SelectedPackage,
    pub(crate) config: Config,
    pub(crate) paths: ManagedPaths,
    pub(crate) specs: SpecRegistry,
    pub(crate) dry_run: bool,
}

#[derive(Debug)]
pub(crate) struct CargoProject {
    root: PathBuf,
    metadata: Metadata,
}

#[derive(Debug)]
pub(crate) struct SelectedPackage {
    pub(crate) package: Package,
    pub(crate) library_target_name: String,
}

#[derive(Debug)]
pub(crate) struct DirectDependency {
    pub(crate) name: String,
    pub(crate) package: Package,
}

#[derive(Debug)]
pub(crate) struct ManagedPaths {
    root: PathBuf,
    pub(crate) output: PathBuf,
    crates: PathBuf,
    pub(crate) cargo_target: PathBuf,
}

impl App {
    /// Creates an application after performing all read-only discovery and validation.
    pub(crate) fn new(root: PathBuf, args: Args) -> Result<Self, Error> {
        let config = Config::load(&root)?;
        let project = CargoProject::load(root, &config.target())?;
        let target = project.select_package(&args)?;
        config.validate()?;
        let paths = ManagedPaths::new(project.root());
        let specs_path = config.specs_path();
        let specs = if specs_path.is_file() || specs_path.is_dir() {
            SpecRegistry::load(&specs_path)?
        } else {
            SpecRegistry::empty()
        };
        Ok(Self {
            state: AppState {
                project,
                target,
                config,
                paths,
                specs,
                dry_run: args.dry_run,
            },
        })
    }

    /// Performs the isolated extraction workflow.
    pub(crate) fn run(self) -> Result<(), Error> {
        log::info!("Preparing workspace.");
        tasks::prepare_workspace(&self.state)?;
        log::info!("Cloning target into work directory.");
        let mut root = tasks::clone_target_crate(&self.state)?;
        log::info!("Applying specs to dependencies.");
        tasks::patch_direct_dependencies(&self.state, &mut root)?;
        log::info!("Adding runner binary.");
        tasks::add_extractor_binary(&self.state, &mut root)?;
        log::info!("Commiting all changes to target crate.");
        tasks::commit_root_crate(&self.state, &root)?;
        log::info!("Running extraction");
        tasks::run_extractor(&self.state, &root)
    }
}

impl CargoProject {
    fn load(root: PathBuf, target: &TargetConfig) -> Result<Self, Error> {
        let mut command = MetadataCommand::new();
        command.current_dir(&root);
        if target.all_features() {
            command.features(CargoOpt::AllFeatures);
        }
        if target.no_default_features() {
            command.features(CargoOpt::NoDefaultFeatures);
        }
        if !target.features().is_empty() {
            command.features(CargoOpt::SomeFeatures(target.features().to_vec()));
        }
        Ok(Self {
            root,
            metadata: command.exec()?,
        })
    }

    fn root(&self) -> &Path {
        &self.root
    }

    fn select_package(&self, args: &Args) -> Result<SelectedPackage, Error> {
        let manifest = self.metadata.workspace_root.join("Cargo.toml");
        let is_workspace = toml::from_str::<toml::Value>(&fs::read_to_string(manifest)?)?
            .get("workspace")
            .is_some();
        if is_workspace && args.package.is_none() {
            let names = self
                .workspace_packages()
                .map(|package| package.name.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            return Err(Error::Message(format!(
                "workspace package must be selected with -p; available packages: {names}"
            )));
        }
        let name = args
            .package
            .as_deref()
            .map(str::to_owned)
            .or_else(|| {
                self.metadata
                    .root_package()
                    .map(|package| package.name.clone())
            })
            .ok_or_else(|| Error::Message("could not determine root package".into()))?;
        let package = self
            .workspace_packages()
            .find(|package| package.name == name)
            .cloned()
            .ok_or_else(|| Error::Message(format!("'{name}' is not a workspace member")))?;
        let library_target_name = package
            .targets
            .iter()
            .find(|target| target.is_lib())
            .map(|target| target.name.clone())
            .ok_or_else(|| {
                Error::Message(format!("package '{name}' does not define a library target"))
            })?;
        Ok(SelectedPackage {
            package,
            library_target_name,
        })
    }

    pub(crate) fn normal_direct_dependencies(
        &self,
        target: &SelectedPackage,
    ) -> Result<Vec<DirectDependency>, Error> {
        let resolve = self.metadata.resolve.as_ref().ok_or_else(|| {
            Error::Message("Cargo metadata did not include a dependency resolution".into())
        })?;
        let node = resolve
            .nodes
            .iter()
            .find(|node| node.id == target.package.id)
            .ok_or_else(|| {
                Error::Message("selected package is absent from Cargo resolution".into())
            })?;
        node.deps
            .iter()
            .filter(|dependency| {
                dependency
                    .dep_kinds
                    .iter()
                    .any(|kind| kind.kind == DependencyKind::Normal)
            })
            .map(|dependency| {
                let name = self.dependency_name(target, &dependency.name)?;
                let package = self.package(&dependency.pkg).cloned().ok_or_else(|| {
                    Error::Message("resolved dependency metadata is missing".into())
                })?;
                Ok(DirectDependency { name, package })
            })
            .collect()
    }

    fn dependency_name(
        &self,
        target: &SelectedPackage,
        resolved_name: &str,
    ) -> Result<String, Error> {
        target
            .package
            .dependencies
            .iter()
            .find(|dependency| {
                dependency.kind == DependencyKind::Normal
                    && dependency
                        .rename
                        .as_deref()
                        .unwrap_or(&dependency.name)
                        .replace('-', "_")
                        == resolved_name
            })
            .map(|dependency| {
                dependency
                    .rename
                    .clone()
                    .unwrap_or_else(|| dependency.name.clone())
            })
            .ok_or_else(|| Error::Message("resolved dependency is missing from manifest".into()))
    }

    fn workspace_packages(&self) -> impl Iterator<Item = &Package> {
        self.metadata
            .workspace_members
            .iter()
            .filter_map(|id| self.package(id))
    }
    fn package(&self, id: &PackageId) -> Option<&Package> {
        self.metadata
            .packages
            .iter()
            .find(|package| package.id == *id)
    }
}

impl SelectedPackage {
    pub(crate) fn manifest_directory(&self) -> Result<&Path, Error> {
        Path::new(self.package.manifest_path.as_str())
            .parent()
            .ok_or_else(|| Error::Message("package manifest has no parent".into()))
    }
}

impl ManagedPaths {
    fn new(root: &Path) -> Self {
        let output = root.join("target/haloumi");
        Self {
            root: root.to_path_buf(),
            crates: output.join(".crates"),
            cargo_target: output.join(".cargo"),
            output,
        }
    }

    pub(crate) fn reset_output(&self) -> Result<(), Error> {
        if !self.output.starts_with(&self.root) || self.output == self.root {
            return Err(Error::Message(
                "Haloumi output directory is outside the project root".into(),
            ));
        }
        // TODO: Replace this conservative reset with selective artifact management (#34).
        if self.output.exists() {
            fs::remove_dir_all(&self.output)?;
        }
        fs::create_dir_all(&self.output)?;
        Ok(())
    }

    pub(crate) fn root_copy(&self, package: &Package) -> PathBuf {
        self.crates
            .join(format!("{}-{}", package.name, package.version))
    }
    pub(crate) fn dependency_copy(&self, package: &Package) -> PathBuf {
        self.root_copy(package)
    }
}
