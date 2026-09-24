# cargo-haloumi

Run `cargo haloumi [--root path] [-p package]` from a Cargo repository to create an isolated
extraction copy under `target/haloumi`. `--root` selects the Cargo project
directory and defaults to the current directory. Configuration is read from
`.haloumi.toml`, then `.haloumi/cfg.toml`; fields in the former take priority.

The command is also available directly as `cargo-haloumi`.

## Target features

Configure features for the extraction target in the main configuration file:

```toml
[target]
features = ["feature-a", "feature-b"]
no-default-features = true
all-features = false
```

These settings are forwarded to Cargo when resolving dependencies and when building or running
the generated extractor.
