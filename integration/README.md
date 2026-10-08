# haloumi-integration

`HALOUMI_ENABLE_GROUPS` enables the group-extraction integration used by
Haloumi's production extraction flow. Without it, the hidden group macros
transparently forward a layouter and ignore annotations so downstream circuits
can build normally.

The non-default `cfg-groups` Cargo feature selects the same implementation for
the `haloumi-integration-macros` test harness. It is test-only and must not be
enabled by downstream circuit consumers.
