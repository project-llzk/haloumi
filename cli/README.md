# cargo-haloumi

Run `cargo haloumi [--root path] [-p package]` from a Cargo repository to create an isolated
extraction copy under `target/haloumi`. `--root` selects the Cargo project
directory and defaults to the current directory. Configuration is read from
`.haloumi.toml`, then `.haloumi/cfg.toml`; fields in the former take priority.

The command is also available directly as `cargo-haloumi`.
