//! Application orchestration for the `cargo haloumi` command.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use cargo_metadata::{CargoOpt, DependencyKind, Metadata, MetadataCommand, Package, PackageId};
use cargo_toml::{Dependency, DependencyDetail, VersionReq};
use haloumi_inject::{
    Injector,
    crate_info::{Crate, CrateLike, CrateMut, RustFile},
    error::Error as InjectError,
    spec::{SpecMatch, SpecRegistry},
};
use serde::Serialize;

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
    library_target_name: String,
}

#[derive(Debug)]
struct DirectDependency {
    name: String,
    package: Package,
}

#[derive(Debug)]
struct ManagedPaths {
    root: PathBuf,
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
        let specs = if specs_path.is_file() || specs_path.is_dir() {
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
        self.paths.reset_output()
    }

    fn clone_target_crate(&self) -> Result<CrateMut, Error> {
        let source = Crate::open(self.target.manifest_directory()?)?;
        Ok(source.clone_in_path(self.paths.root_copy(&self.target.package))?)
    }

    fn patch_direct_dependencies(&self, root: &mut CrateMut) -> Result<(), Error> {
        let dependencies = self.project.normal_direct_dependencies(&self.target)?;
        let mut package_ids = BTreeMap::new();
        for dependency in &dependencies {
            match self
                .specs
                .find_matching(&dependency.package.name, &dependency.package.version)
            {
                SpecMatch::None => {}
                SpecMatch::Ambiguous(specs) => {
                    return Err(Error::Message(format!(
                        "{} specs match {} {}",
                        specs.len(),
                        dependency.package.name,
                        dependency.package.version
                    )));
                }
                SpecMatch::One(_) => {
                    let key = (
                        dependency.package.name.clone(),
                        dependency.package.version.to_string(),
                    );
                    if let Some(existing_id) =
                        package_ids.insert(key, dependency.package.id.clone())
                        && existing_id != dependency.package.id
                    {
                        return Err(Error::Message(format!(
                            "multiple direct dependencies named {} {} resolve to different package IDs; patching them is unsupported",
                            dependency.package.name, dependency.package.version
                        )));
                    }
                }
            }
        }

        for dependency in dependencies {
            match self
                .specs
                .find_matching(&dependency.package.name, &dependency.package.version)
            {
                SpecMatch::None => {
                    log::debug!(
                        "No spec matches {} {}",
                        dependency.package.name,
                        dependency.package.version
                    );
                }
                SpecMatch::Ambiguous(specs) => {
                    return Err(Error::Message(format!(
                        "{} specs match {} {}",
                        specs.len(),
                        dependency.package.name,
                        dependency.package.version
                    )));
                }
                SpecMatch::One(_) => {
                    let destination = self.paths.dependency_copy(&dependency.package);
                    let source =
                        Crate::open(dependency.package.manifest_path.parent().ok_or_else(
                            || Error::Message("dependency manifest has no parent".into()),
                        )?)?;
                    Injector::new(&source, &self.specs)?.apply(&destination)?;
                    root.replace_dependency_with_path(&dependency.name, destination)?;
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
            !extractor.dependency_explicit(),
        )?;
        for (name, dependency) in extractor.dependencies() {
            self.add_dependency(root, name.clone(), dependency.clone(), false)?;
        }
        let crate_ident = self.target.library_target_name.replace('-', "_");
        let extractor_ident = extractor.name().replace('-', "_");
        let source = format!(
            "fn main() {{ {extractor_ident}::ExtractorMain::run({crate_ident}::harnesses()); }}"
        );
        root.add_binary_target("haloumi-extractor", "src/bin/haloumi-extractor.rs")?;
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
        allow_existing_source: bool,
    ) -> Result<(), Error> {
        match root.add_dependency(name.clone(), dependency.clone()) {
            Ok(()) => Ok(()),
            Err(InjectError::DuplicateDep(_)) => {
                let existing = root
                    .dependency(&name)
                    .expect("duplicate dependency must be present");
                let merged = merge_dependencies(&name, existing, &dependency, allow_existing_source).ok_or_else(|| {
                    Error::Message(format!(
                        "dependency '{name}' conflicts with extractor configuration; align its package, source, version, and features"
                    ))
                })?;
                if !cargo_can_resolve_dependency(&name, &merged)? {
                    return Err(Error::Message(format!(
                        "dependency '{name}' conflicts with extractor configuration; Cargo cannot resolve a version satisfying both declarations"
                    )));
                }
                root.replace_dependency(&name, merged)?;
                Ok(())
            }
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
            .arg("--release")
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

fn merge_dependencies(
    name: &str,
    existing: &Dependency,
    requested: &Dependency,
    allow_existing_source: bool,
) -> Option<Dependency> {
    let existing = dependency_detail(existing.clone()).ok()?;
    let requested = dependency_detail(requested.clone()).ok()?;

    if effective_package(name, &existing) != effective_package(name, &requested)
        || (!allow_existing_source && !same_source(&existing, &requested))
        || (!allow_existing_source && existing.unstable != requested.unstable)
    {
        return None;
    }

    let version = match (&existing.version, &requested.version) {
        (Some(existing), Some(requested)) => {
            VersionReq::parse(&format!("{existing}, {requested}")).ok()?
        }
        (Some(version), None) | (None, Some(version)) => version.clone(),
        (None, None) => VersionReq::STAR,
    };
    let features = existing
        .features
        .iter()
        .chain(&requested.features)
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let default_features = existing.default_features || requested.default_features;

    let source = if allow_existing_source {
        existing
    } else {
        requested
    };
    Some(Dependency::Detailed(Box::new(DependencyDetail {
        version: Some(version),
        package: source.package,
        registry: source.registry,
        registry_index: source.registry_index,
        path: source.path,
        inherited: false,
        git: source.git,
        branch: source.branch,
        tag: source.tag,
        rev: source.rev,
        features,
        // The generated extractor imports every dependency it injects.
        optional: false,
        default_features,
        unstable: source.unstable,
    })))
}

fn dependency_detail(dependency: Dependency) -> Result<DependencyDetail, cargo_toml::Error> {
    match dependency {
        Dependency::Detailed(detail) => Ok(*detail),
        Dependency::Simple(version) => Ok(DependencyDetail {
            version: Some(version),
            ..DependencyDetail::default()
        }),
        Dependency::Inherited(_) => Err(cargo_toml::Error::InheritedUnknownValue),
    }
}

fn effective_package<'a>(name: &'a str, dependency: &'a DependencyDetail) -> &'a str {
    dependency.package.as_deref().unwrap_or(name)
}

fn same_source(left: &DependencyDetail, right: &DependencyDetail) -> bool {
    left.registry == right.registry
        && left.registry_index == right.registry_index
        && left.path == right.path
        && left.git == right.git
        && left.branch == right.branch
        && left.tag == right.tag
        && left.rev == right.rev
}

#[derive(Serialize)]
struct ResolutionManifest {
    package: BTreeMap<&'static str, &'static str>,
    dependencies: BTreeMap<String, Dependency>,
}

fn cargo_can_resolve_dependency(name: &str, dependency: &Dependency) -> Result<bool, Error> {
    let directory = tempfile::tempdir()?;
    let manifest = ResolutionManifest {
        package: BTreeMap::from([
            ("name", "haloumi-dependency-resolution-check"),
            ("version", "0.0.0"),
            ("edition", "2024"),
        ]),
        dependencies: BTreeMap::from([(name.to_owned(), dependency.clone())]),
    };
    let contents = toml::to_string(&manifest).map_err(|error| Error::Message(error.to_string()))?;
    fs::write(directory.path().join("Cargo.toml"), &contents)?;
    fs::create_dir(directory.path().join("src"))?;
    fs::write(directory.path().join("src/lib.rs"), "")?;
    Ok(MetadataCommand::new()
        .manifest_path(directory.path().join("Cargo.toml"))
        .exec()
        .is_ok())
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

    fn normal_direct_dependencies(
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
            root: root.to_path_buf(),
            crates: output.join(".crates"),
            cargo_target: output.join(".cargo"),
            output,
        }
    }

    fn reset_output(&self) -> Result<(), Error> {
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

    fn root_copy(&self, package: &Package) -> PathBuf {
        self.crates
            .join(format!("{}-{}", package.name, package.version))
    }

    fn dependency_copy(&self, package: &Package) -> PathBuf {
        self.root_copy(package)
    }
}
