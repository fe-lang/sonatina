#!/bin/bash
set -e

cargo +nightly fmt --all -- --check
cargo clippy --workspace --all-features --all-targets -- -D clippy::all
cargo doc --no-deps

cargo test --workspace --all-targets
cargo run -p sonatina-filecheck
