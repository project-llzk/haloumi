#!/bin/sh 

cargo publish -p haloumi-core && \
cargo publish -p haloumi-lowering && \
cargo publish -p haloumi-ir && \
cargo publish -p haloumi-synthesis && \
cargo publish -p haloumi-ir-gen && \
cargo publish -p haloumi-backend && \
cargo publish -p haloumi-picus && \
cargo publish -p haloumi-llzk && \
cargo publish -p haloumi 
