//! Build script for Haloumi's main integration point.
//!
//! The script is configured with environment variables and Cargo features that
//! enable or disable parts of Haloumi.

/// List of cfgs used in Haloumi for controling compilation.
const CFGS: [Configuration; 1] = [
    // `HALOUMI_ENABLE_GROUPS` is the production extraction switch. The
    // feature mirrors it so the integration-macros test dependency can use
    // the production macro implementations in an ordinary Cargo test build.
    Configuration::new(
        "groups",
        "HALOUMI_ENABLE_GROUPS",
        Some("CARGO_FEATURE_CFG_GROUPS"),
        None,
    ),
];

fn main() -> anyhow::Result<()> {
    let mut out = std::io::stdout();
    for cfg in CFGS {
        cfg.declare(&mut out)?;
        cfg.enable(&mut out)?;
    }
    Ok(())
}

struct Configuration {
    name: &'static str,
    var: &'static str,
    feature_var: Option<&'static str>,
    values: Option<&'static [&'static str]>,
}

impl Configuration {
    const fn new(
        name: &'static str,
        var: &'static str,
        feature_var: Option<&'static str>,
        values: Option<&'static [&'static str]>,
    ) -> Self {
        Self {
            name,
            var,
            feature_var,
            values,
        }
    }

    /// Declares the configuration s.t. the compiler recognizes it inside Haloumi's code.
    fn declare(&self, mut out: impl std::io::Write) -> anyhow::Result<()> {
        writeln!(out, "cargo::rerun-if-env-changed={}", self.var)?;
        if let Some(feature_var) = self.feature_var {
            writeln!(out, "cargo::rerun-if-env-changed={feature_var}")?;
        }
        write!(out, "cargo::rustc-check-cfg=cfg({}", self.name)?;
        if let Some(values) = self.values {
            assert!(!values.is_empty());
            write!(out, ", values(\"{}\")", values.join("\", \""))?;
        }
        writeln!(out, ")")?;
        Ok(())
    }

    /// Enables the configuration if its environment variable or feature is set.
    fn enable(&self, mut out: impl std::io::Write) -> anyhow::Result<()> {
        let var = std::env::var_os(self.var);
        let feature_enabled = self
            .feature_var
            .is_some_and(|feature_var| std::env::var_os(feature_var).is_some());
        if var.is_none() && !feature_enabled {
            return Ok(());
        }
        write!(out, "cargo::rustc-cfg={}", self.name)?;
        if let Some(values) = self.values {
            let var = var
                .expect("a valued configuration must be enabled by its environment variable")
                .into_string()
                .map_err(|s| anyhow::anyhow!("String {s:?} is not a valid UTF8 string"))?;
            if !values.contains(&var.as_str()) {
                anyhow::bail!(
                    "{var} is not a valid value for {}. Valid values: {values:?}",
                    self.name
                );
            }
            write!(out, "={var}")?;
        }
        writeln!(out)?;
        Ok(())
    }
}
