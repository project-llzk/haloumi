use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
};

use cargo_metadata::MetadataCommand;
use cargo_toml::{Dependency, DependencyDetail, VersionReq};
use haloumi_inject::{
    crate_info::{CrateLike, CrateMut, RustFile},
    error::Error as InjectError,
};
use serde::Serialize;

use crate::{Error, app::AppState};

pub(crate) fn add_extractor_binary(state: &AppState, root: &mut CrateMut) -> Result<(), Error> {
    let extractor = state.config.extractor();
    let dependency = extractor.dependency();
    add_dependency(
        root,
        extractor.name().to_owned(),
        dependency.dependency().clone(),
        !dependency.explicit(),
    )?;
    for (name, dependency) in extractor.dependencies() {
        add_dependency(root, name.clone(), dependency.clone(), false)?;
    }
    let crate_ident = state.target.library_target_ident();
    let extractor_ident = extractor.ident();
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
    root: &mut CrateMut,
    name: String,
    dependency: Dependency,
    allow_existing_source: bool,
) -> Result<(), Error> {
    match root.add_dependency(name.clone(), dependency.clone()) {
        Ok(()) => Ok(()),
        Err(InjectError::DuplicateDep(_)) => {
            let existing = root
                .dependency(&name)
                .expect("duplicate dependency must be present");
            let merged = merge_dependencies(&name, existing, &dependency, allow_existing_source).ok_or_else(|| Error::Message(format!("dependency '{name}' conflicts with extractor configuration; align its package, source, version, and features")))?;
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
