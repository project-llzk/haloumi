//! Application orchestration for the `cargo haloumi` command.

use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use cargo_metadata::{CargoOpt, DependencyKind, Metadata, MetadataCommand, Package, PackageId};
use haloumi_inject::{
    Injector,
    crate_info::{Crate, CrateMut, RustFile},
    error::Error as InjectError,
    spec::{SpecMatch, SpecRegistry},
};

use crate::{
    Args, Error,
    config::{Config, TargetConfig},
};

/// The initialized `cargo haloumi` application.
#[derive(Debug)]
pub(crate) struct App {
    project: CargoProject,
    target: SelectedPackage,
    config: Config,
    paths: ManagedPaths,
    specs: SpecRegistry,
    dry_run: bool,
}

#[derive(Debug)]
struct CargoProject {
    root: PathBuf,
    metadata: Metadata,
}

#[derive(Debug)]
struct SelectedPackage {
    package: Package,
}

#[derive(Debug)]
struct ManagedPaths {
    output: PathBuf,
    crates: PathBuf,
    cargo_target: PathBuf,
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
        let specs = if specs_path.is_dir() {
            SpecRegistry::load(&specs_path)?
        } else {
            SpecRegistry::empty()
        };

        Ok(Self {
            project,
            target,
            config,
            paths,
            specs,
            dry_run: args.dry_run,
        })
    }

    /// Performs the isolated extraction workflow.
    pub(crate) fn run(self) -> Result<(), Error> {
        log::info!("Preparing workspace.");
        self.prepare_workspace()?;
        log::info!("Cloning target into work directory.");
        let mut root = self.clone_target_crate()?;
        log::info!("Applying specs to dependencies.");
        self.patch_direct_dependencies(&mut root)?;
        log::info!("Adding runner binary.");
        self.add_extractor_binary(&mut root)?;
        log::info!("Commiting all changes to target crate.");
        self.commit_root_crate(&root)?;
        log::info!("Running extraction");
        self.run_extractor(&root)
    }

    fn prepare_workspace(&self) -> Result<(), Error> {
        self.paths.reset_crates()
    }

    fn clone_target_crate(&self) -> Result<CrateMut, Error> {
        let source = Crate::open(self.target.manifest_directory()?)?;
        Ok(source.clone_in_path(self.paths.root_copy(&self.target.package))?)
    }

    fn patch_direct_dependencies(&self, root: &mut CrateMut) -> Result<(), Error> {
        for dependency in self.project.normal_direct_dependencies(&self.target)? {
            match self
                .specs
                .find_matching(&dependency.name, &dependency.version)
            {
                SpecMatch::None => {
                    log::debug!("No spec matches {} {}", dependency.name, dependency.version);
                }
                SpecMatch::Ambiguous(specs) => {
                    return Err(Error::Message(format!(
                        "{} specs match {} {}",
                        specs.len(),
                        dependency.name,
                        dependency.version
                    )));
                }
                SpecMatch::One(_) => {
                    let destination = self.paths.dependency_copy(&dependency);
                    let source =
                        Crate::open(dependency.manifest_path.parent().ok_or_else(|| {
                            Error::Message("dependency manifest has no parent".into())
                        })?)?;
                    Injector::new(&source, &self.specs)?.apply(&destination)?;
                    root.replace_dependency_with_path(
                        self.project.dependency_name(&self.target, &dependency)?,
                        destination,
                    )?;
                }
            }
        }
        Ok(())
    }

    fn add_extractor_binary(&self, root: &mut CrateMut) -> Result<(), Error> {
        let extractor = self.config.extractor()?;
        self.add_dependency(
            root,
            extractor.name().to_owned(),
            extractor.dependency().clone(),
        )?;
        for (name, dependency) in extractor.dependencies() {
            self.add_dependency(root, name.clone(), dependency.clone())?;
        }
        let crate_ident = self.target.package.name.replace('-', "_");
        let extractor_ident = extractor.name().replace('-', "_");
        let source = format!(
            "fn main() {{ {extractor_ident}::ExtractorMain::run({crate_ident}::harnesses()); }}"
        );
        root.create_rust_file(
            "src/bin/haloumi-extractor.rs",
            RustFile::parse_str(&source)?,
        )?;
        Ok(())
    }

    fn add_dependency(
        &self,
        root: &mut CrateMut,
        name: String,
        dependency: cargo_toml::Dependency,
    ) -> Result<(), Error> {
        match root.add_dependency(name, dependency) {
            Ok(()) | Err(InjectError::DuplicateDep(_)) => Ok(()),
            Err(error) => Err(error.into()),
        }
    }

    fn commit_root_crate(&self, root: &CrateMut) -> Result<(), Error> {
        root.commit()?;
        Ok(())
    }

    fn run_extractor(&self, root: &CrateMut) -> Result<(), Error> {
        let mut command = Command::new("cargo");
        command
            .current_dir(root.base_path())
            .arg(if self.dry_run { "build" } else { "run" })
            .arg("--bin")
            .arg("haloumi-extractor")
            .arg("--target-dir")
            .arg(&self.paths.cargo_target);
        add_target_feature_args(&mut command, &self.config.target());
        let extractor = self.config.extractor()?;
        if extractor.groups_enabled() {
            command.env("HALOUMI_ENABLE_GROUPS", "1");
        }
        if !self.dry_run {
            command.arg("--").arg("--output").arg(&self.paths.output);
            if !extractor.optimize() {
                command.arg("--no-opt");
            }
            if !self.config.picus_optimize() {
                command.arg("--picus-no-opt");
            }
            if !self.config.llzk_optimize() {
                command.arg("--llzk-no-opt");
            }
            let formats = self.config.formats();
            if !formats.is_empty() {
                command.arg("--format").arg(formats.join(","));
            }
            if let Some(field) = self.config.llzk_field() {
                command.arg("--llzk-field-name").arg(field);
            }
            if let Some(preludes) = extractor.preludes().filter(|preludes| !preludes.is_empty()) {
                command.arg("--preludes").arg(preludes.join(","));
            }
        }
        log::debug!("Running {:?}", command);
        if !command.status()?.success() {
            return Err(Error::Message("generated extractor command failed".into()));
        }
        Ok(())
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
        let metadata = command.exec()?;
        Ok(Self { root, metadata })
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
        Ok(SelectedPackage { package })
    }

    fn normal_direct_dependencies(&self, target: &SelectedPackage) -> Result<Vec<Package>, Error> {
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
                self.package(&dependency.pkg)
                    .cloned()
                    .ok_or_else(|| Error::Message("resolved dependency metadata is missing".into()))
            })
            .collect()
    }

    fn dependency_name<'a>(
        &'a self,
        target: &'a SelectedPackage,
        package: &Package,
    ) -> Result<&'a str, Error> {
        target
            .package
            .dependencies
            .iter()
            .find(|dependency| {
                dependency.kind == DependencyKind::Normal && dependency.name == package.name
            })
            .map(|dependency| dependency.rename.as_deref().unwrap_or(&dependency.name))
            .ok_or_else(|| Error::Message("resolved dependency metadata is missing".into()))
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

fn add_target_feature_args(command: &mut Command, target: &TargetConfig) {
    if target.all_features() {
        command.arg("--all-features");
    }
    if target.no_default_features() {
        command.arg("--no-default-features");
    }
    if !target.features().is_empty() {
        command.arg("--features").arg(target.features().join(","));
    }
}

impl SelectedPackage {
    fn manifest_directory(&self) -> Result<&Path, Error> {
        Path::new(self.package.manifest_path.as_str())
            .parent()
            .ok_or_else(|| Error::Message("package manifest has no parent".into()))
    }
}

impl ManagedPaths {
    fn new(root: &Path) -> Self {
        let output = root.join("target/haloumi");
        Self {
            crates: output.join(".crates"),
            cargo_target: output.join(".cargo"),
            output,
        }
    }

    fn reset_crates(&self) -> Result<(), Error> {
        if !self.crates.starts_with(&self.output) {
            return Err(Error::Message(
                "managed crate directory is outside the Haloumi output directory".into(),
            ));
        }
        if self.crates.exists() {
            fs::remove_dir_all(&self.crates)?;
        }
        fs::create_dir_all(&self.crates)?;
        Ok(())
    }

    fn root_copy(&self, package: &Package) -> PathBuf {
        self.crates
            .join(format!("{}-{}", package.name, package.version))
    }

    fn dependency_copy(&self, package: &Package) -> PathBuf {
        self.root_copy(package)
    }
}
