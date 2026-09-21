# cargo-haloumi

Run `cargo haloumi [-p package]` from a Cargo repository to create an isolated
extraction copy under `target/haloumi`. Configuration is read from
`.haloumi.toml`, then `.haloumi/cfg.toml`; fields in the former take priority.

The command is also available directly as `cargo-haloumi`.
