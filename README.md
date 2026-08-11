# Sonatina

Sonatina is a compiler backend for the EVM.
It is not yet ready for production use.

It's currently used by [Fe](http://github.com/argotorg/fe/),
and as an optional backend for [Plank](https://github.com/plankevm/plank-monorepo).

## IR

Sonatina uses a fairly typical SSA/CFG representation.
Here's an example of the textual form:

```
target = "evm-ethereum-osaka"

type @Pair = { i256, i256 };

func public %init() {
    block0:
        v0.i256 = sym_addr &runtime;
        v1.i256 = sym_size &runtime;
        evm_code_copy 0.i256 v0 v1;
        evm_return 0.i256 v1;
}

func private %make_pair(v0.i256, v1.i256) -> objref<@Pair> {
    block0:
        v2.objref<@Pair> = obj.alloc @Pair;
        v3.objref<i256> = obj.proj v2 0.i8;
        obj.store v3 v0;
        v4.objref<i256> = obj.proj v2 1.i8;
        obj.store v4 v1;
        return v2;
}

func public %runtime() {
    block0:
        v0.objref<@Pair> = call %make_pair 7.i256 35.i256;
        v1.objref<i256> = obj.proj v0 0.i8;
        v2.objref<i256> = obj.proj v0 1.i8;
        v3.i256 = obj.load v1;
        v4.i256 = obj.load v2;
        v5.i256 = add v3 v4;
        mstore 0.i256 v5 i256;
        evm_return 0.i256 32.i256;
}

object @Contract {
    section init {
        entry %init;
        embed .runtime as &runtime;
    }

    section runtime {
        entry %runtime;
    }
}
```

Sonatina provides an easy IR Builder API, including automatic SSA construction via `.declare_var`/`.def_var`/`.use_var` methods.

## Optimization Pipeline

Sonatina currently performs the following optimizations:

- Inlining, dead argument elimination, and dead function elimination.
- CFG cleanup, branch canonicalization, SCCP, ADCE, GVN, LICM, and loop strength reduction.
- Scalar canonicalization, known-bits simplification, checked-arithmetic elimination.
- Aggregate combine/scalarization plus object-aware load/store forwarding and dead-store elimination.

## EVM Backend

- Stack layout is determined via symbolic execution. Unreachable values are spilled to memory as needed.
- Memory planner and memory reuse optimization: shared ephemeral memory region for short-lived values, stable regions with static offsets for non-recursive code, dynamic call frames for recursive code.

## CLI

```sh
// Check if IR is valid
cargo run -p sonatina-cli -- verify input.sntn
// Apply optimization passes and write out optimized sonatina IR
cargo run -p sonatina-cli -- optimize -p input.sntn
// Build EVM bytecode
cargo run -p sonatina-cli -- build -O s -p input.sntn
```

## Tests

```sh
./test_all.sh
```

## Trace and Debug Substrate

The frontend-neutral trace/debug/content-addressing scope is documented in
[docs/trace-debug-content-addressing.md](docs/trace-debug-content-addressing.md).
