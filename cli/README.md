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

## Backends

Backends can be explicitly enabled or disabled with `enabled`. Without an explicit value, a
backend is enabled only when its mandatory parameter blocks are configured. IR and Picus have no
mandatory parameters today, while LLZK is implicitly enabled by a `field` block:

```toml
[backends.ir]
enabled = true

[backends.picus]
enabled = true

[backends.llzk.field]
builtin = "bn256"
```

Set `enabled = false` to disable a backend even when its parameters are configured. Explicitly
enabled LLZK still requires a valid field configuration.

Set `optimize = false` to forward a backend-specific optimization flag to the extractor runner:

```toml
[backends.picus]
optimize = false # --picus-no-opt

[backends.llzk]
optimize = false # --llzk-no-opt
```

Both settings default to `true`.

## Extractor preludes

Configure semantic preludes for the generated extractor with an optional list of registered
prelude names:

```toml
[extractor]
preludes = ["example-prelude", "another-prelude"]
```

When the list is nonempty, `cargo-haloumi` forwards it to the runner as
`--preludes example-prelude,another-prelude`. Omit the setting or use an empty list to avoid
passing the argument.

Set `optimize = false` in `[extractor]` to disable resolved-IR optimization by forwarding
`--no-opt`; it defaults to `true`.
