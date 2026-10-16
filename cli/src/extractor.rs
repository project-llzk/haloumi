use std::{borrow::Cow, path::Path};

use cargo_toml::{Dependency, DepsSet, VersionReq};

use crate::Error;

#[derive(Debug, Clone)]
pub struct ExtractorDependency {
    explicit: bool,
    dependency: Dependency,
}

impl ExtractorDependency {
    pub fn new(dep: &Dependency) -> Self {
        Self {
            explicit: true,
            dependency: dep.clone(),
        }
    }

    pub fn explicit(&self) -> bool {
        self.explicit
    }

    pub fn dependency(&self) -> &Dependency {
        &self.dependency
    }
}

impl Default for ExtractorDependency {
    fn default() -> Self {
        Self {
            explicit: false,
            dependency: Dependency::Simple(
                VersionReq::parse(&format!("<= {}", env!("CARGO_PKG_VERSION")))
                    .expect("package version is valid"),
            ),
        }
    }
}

impl From<ExtractorDependency> for Dependency {
    fn from(value: ExtractorDependency) -> Self {
        value.dependency
    }
}

const DEFAULT_EXTRACTOR_NAME: &str = "haloumi-extractor-runner";

/// The resolved dependencies required by the generated extractor binary.
#[derive(Debug)]
pub(crate) struct ExtractorConfig {
    name: Cow<'static, str>,
    dependency: ExtractorDependency,
    dependencies: DepsSet,
    /// Configures whether groups are enabled or not during extraction.
    ///
    /// On by default.
    groups_enabled: bool,
    /// Named semantic preludes forwarded to the extractor runner.
    preludes: Option<Vec<String>>,
    /// Configures whether the runner optimizes resolved IR.
    optimize: bool,
}

impl ExtractorConfig {
    pub fn new() -> Self {
        Self {
            name: Cow::Borrowed(DEFAULT_EXTRACTOR_NAME),
            dependency: Default::default(),
            dependencies: Default::default(),
            groups_enabled: true,
            preludes: Default::default(),
            optimize: true,
        }
    }

    pub(crate) fn name(&self) -> &str {
        &self.name
    }

    pub(crate) fn ident(&self) -> String {
        self.name.replace("-", "_")
    }

    pub(crate) fn dependency(&self) -> &ExtractorDependency {
        &self.dependency
    }

    pub(crate) fn dependencies(&self) -> &DepsSet {
        &self.dependencies
    }

    pub(crate) fn groups_enabled(&self) -> bool {
        self.groups_enabled
    }

    pub(crate) fn preludes(&self) -> Option<&[String]> {
        self.preludes.as_deref()
    }

    pub(crate) fn optimize(&self) -> bool {
        self.optimize
    }

    pub(crate) fn set_dependency(
        &mut self,
        dependency: &Dependency,
        base: impl AsRef<Path>,
    ) -> Result<(), Error> {
        let mut dependency = ExtractorDependency::new(dependency);
        rebase_dependency(&mut dependency.dependency, base)?;
        self.dependency = dependency;
        Ok(())
    }

    pub(crate) fn set_dependencies<'d>(
        &mut self,
        dependencies: impl IntoIterator<Item = (&'d String, &'d Dependency)>,
        base: impl AsRef<Path>,
    ) -> Result<(), Error> {
        let mut dependencies = DepsSet::from_iter(
            dependencies
                .into_iter()
                .map(|(s, d)| (s.to_owned(), d.clone())),
        );
        for dep in dependencies.values_mut() {
            rebase_dependency(dep, &base)?;
        }
        self.dependencies = dependencies;
        Ok(())
    }

    pub(crate) fn set_groups_enabled(&mut self, groups_enabled: bool) {
        self.groups_enabled = groups_enabled;
    }

    pub(crate) fn set_preludes(&mut self, preludes: Vec<String>) {
        self.preludes = Some(preludes);
    }

    pub(crate) fn set_optimize(&mut self, optimize: bool) {
        self.optimize = optimize;
    }

    pub(crate) fn set_name(&mut self, name: &str) {
        self.name = Cow::Owned(name.to_owned());
    }
}

impl Default for ExtractorConfig {
    fn default() -> Self {
        Self::new()
    }
}

fn rebase_dependency(dependency: &mut Dependency, base: impl AsRef<Path>) -> Result<(), Error> {
    if dependency.detail().is_none() {
        return Ok(());
    }
    let detail = dependency.try_detail_mut()?;
    if let Some(path) = detail.path.as_ref()
        && Path::new(path).is_relative()
    {
        detail.path = Some(base.as_ref().join(path).display().to_string());
    }
    Ok(())
}
