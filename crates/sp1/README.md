# SP1 RV64IM objects and executables

Enable `sonatina-codegen/sp1` and use the exact target
`riscv64im-succinct-zkvm-elf` (`TargetTriple::SP1`) to emit an ELF object with
`Compile` and `CraneliftObjectBackend`. Object emission needs neither the
Succinct toolchain nor an executor/prover SDK. The JIT remains host-native;
RV32, other RISC-V targets, wasm, and EVM runtime emulation are unsupported.

`sonatina-sp1` is a separate, optional consumer dependency for static linking.
It uses a locked upstream `sp1-zkvm` 6.8.0 runtime and the
[`succinct-1.96.0-64bit-v2` toolchain](https://github.com/succinctlabs/rust/releases/tag/succinct-1.96.0-64bit-v2).
It has no Cranelift, executor, or prover dependency. Ordinary compiler builds
do not compile or install the guest runtime.

## Install and link

Install into a new directory on Linux or macOS:

```sh
export SONATINA_SP1_TOOLCHAIN="$PWD/target/sp1-toolchain"
bash crates/sp1/install-toolchain.sh "$SONATINA_SP1_TOOLCHAIN"
```

The installer verifies the published SHA-256 archive digest, refuses to
overwrite an installation, and does not change rustup aliases. The library
only locates/checks the installation; it never downloads a toolchain.
Runtime compilation requires Cargo and may fetch the locked guest dependencies.

```rust,no_run
use sonatina_sp1::{Sp1Runtime, Sp1Toolchain};

fn link(object: &[u8]) -> Result<Vec<u8>, sonatina_sp1::Sp1Error> {
    let runtime = Sp1Runtime::build(Sp1Toolchain::from_env()?)?;
    runtime.link_objects(&[object])
}
```

Build one `Sp1Runtime` and reuse it to link multiple programs. Temporary
runtime build files are owned by that value. Each program must export exactly
one `main() -> i32`. The upstream runtime supplies `_start`, initialization,
public-value digest finalization, and halt. A zero return denotes success.

## Guest ABI and input format

Memory is little-endian with 64-bit pointers; i128/i256 have 16-byte alignment.
The existing [native value/reference ABI](https://github.com/fe-lang/sonatina/blob/main/crates/codegen/docs/native.md) applies
to internal Sonatina calls. External C interop is limited to fixed, non-variadic
u32/i32, u64/i64 and pointer arguments, with no result or one scalar/pointer
result. RV64 sign-extends 32-bit arguments and results, including u32 values.
Do not assume C compatibility for aggregate, narrow-integer, or i128 signatures.

The runtime exports only these guest I/O adapters:

| Symbol | Signature | Encoding |
| --- | --- | --- |
| `sys_sp1_read_u32` | `() -> i32` | One hint containing exactly 4 little-endian bytes |
| `sys_sp1_read_u64` | `() -> i64` | One hint containing exactly 8 little-endian bytes |
| `sys_sp1_commit_u32` | `(i32)` | Append 4 little-endian public bytes |
| `sys_sp1_commit_u64` | `(i64)` | Append 8 little-endian public bytes |

Host SDK callers use `SP1Stdin::write_slice(&value.to_le_bytes())` for each
read, in order. Public output is concatenated raw bytes, not a serialized
container. Missing or incorrectly sized input fails the guest. SP1 6.8.0
execution may return `Ok` with a nonzero `ExecutionReport.exit_code`; inspect
that field, and verify proofs against success status. Taken compiler traps
fail execution; portable SP1 currently reports EBREAK through a worker panic.

## Code and link constraints

SP1 uses explicit RV64IM/LP64 settings, four-byte EBREAK traps, and instruction
sequences for integer constants. All code/data symbols, including imported
globals and generated libcalls, use PC-relative references. Objects are
statically linked at `0x78000000`; unresolved symbols and relocation overflow
are linker errors. No far-address literal fallback is supported. The linker
rejects non-RV64 soft-float ELF inputs and absolute address literals in text;
it does not establish arbitrary input objects' instruction-set or ABI safety.

This slice uses a pinned temporary fe-lang Cranelift fork based on upstream
0.135.2 for LP64, EBREAK, checked arithmetic, and integer constant support.
Native and SP1 share that dependency graph; enabling only `cranelift` does not
select a separate upstream source. The optional features keep codegen/JIT out
of default builds, not Git dependencies out of Cargo's resolution process.

## Dedicated integration suite

The excluded `tests/sp1` workspace pins SDK 6.8.0 separately from the compiler:

```sh
cargo test --locked --release --manifest-path tests/sp1/Cargo.toml
cargo test --locked --release --manifest-path tests/sp1/Cargo.toml --test execute -- --ignored
```

Missing prerequisites fail these tests; there are no silent skips. The second
command runs the CPU core-proof check. Recursive proofs, precompile APIs,
unconstrained execution, and performance tuning are outside this slice.
