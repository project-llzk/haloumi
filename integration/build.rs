//! Build script for Haloumi's main integration point.
//!
//! The script is configured with environment variables that
//! enable or disable parts of Haloumi.

/// List of cfgs used in Haloumi for controling compilation.
const CFGS: [Configuration; 1] = [
    // Enables group extraction.
    Configuration::new("groups", "HALOUMI_ENABLE_GROUPS", None),
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
    values: Option<&'static [&'static str]>,
}

impl Configuration {
    const fn new(
        name: &'static str,
        var: &'static str,
        values: Option<&'static [&'static str]>,
    ) -> Self {
        Self { name, var, values }
    }

    /// Declares the configuration s.t. the compiler recognizes it inside Haloumi's code.
    fn declare(&self, mut out: impl std::io::Write) -> anyhow::Result<()> {
        writeln!(out, "cargo::rerun-if-env-changed={}", self.var)?;
        write!(out, "cargo::rustc-check-cfg=cfg({}", self.name)?;
        if let Some(values) = self.values {
            assert!(!values.is_empty());
            write!(out, ", values(\"{}\")", values.join("\", \""))?;
        }
        writeln!(out, ")")?;
        Ok(())
    }

    /// Enables the configuration if the appropriate environment variable is set.
    fn enable(&self, mut out: impl std::io::Write) -> anyhow::Result<()> {
        let Some(var) = std::env::var_os(self.var) else {
            return Ok(());
        };
        let var = var
            .into_string()
            .map_err(|s| anyhow::anyhow!("String {s:?} is not a valid UTF8 string"))?;
        write!(out, "cargo::rustc-cfg={}", self.name)?;
        if let Some(values) = self.values {
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
