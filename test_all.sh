#!/bin/bash
set -e

cargo +nightly fmt --all -- --check
cargo clippy --workspace --all-features --all-targets -- -D clippy::all
cargo doc --no-deps

cargo test --workspace --all-targets
# NOTE: --all-targets option doesn't invoke doctest, see https://github.com/rust-lang/cargo/issues/6669
cargo test --workspace --all-features --doc
cargo run -p sonatina-filecheck
