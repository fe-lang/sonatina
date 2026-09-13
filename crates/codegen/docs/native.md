# Host-native Cranelift backend

The optional `sonatina-codegen/cranelift` feature emits native object files
through released upstream Cranelift 0.135 (Rust 1.95 or newer). The separate
`cranelift-jit` feature enables in-process execution and includes `cranelift`.
Neither feature is enabled by default; EVM users do not need the Cranelift
code generator or JIT dependencies.

## Targets and artifacts

Only `x86_64-unknown-native` and `aarch64-unknown-native` are accepted, and the
architecture must match the compiler's host. The host determines the real
operating system, object format and calling convention. CPU features are
inferred from the local CPU: these are host-tuned artifacts, not portable
baseline binaries or cross-compilation targets.

| Host | Runtime coverage / object format |
| --- | --- |
| x86_64 Linux | JIT and linked executables / ELF |
| AArch64 macOS | JIT and linked executables / Mach-O |
| Windows | Compilation-only CI; runtime support is not promised |

Other OS/architecture combinations have no runtime guarantee in this slice.
SP1, RISC-V, wasm and EVM instruction emulation are outside its scope.

Use `Compile` with `CraneliftObjectBackend` for object bytes. Linking them,
providing imports and selecting an executable entry point are the caller's
responsibility. The Sonatina CLI's `build` command remains EVM-specific.

```no_run
use sonatina_codegen::{Compile, compile::OptLevel, isa::cranelift::CraneliftObjectBackend};
use sonatina_ir::Module;

fn compile_object(module: Module) -> Vec<u8> {
    Compile::new(module, CraneliftObjectBackend::new())
        .with_opt_level(OptLevel::O2)
        .compile()
        .expect("native compilation failed")
        .into_bytes()
}
```

One optimization level configures both the shared Sonatina pipeline and
Cranelift: O0 uses `none`, O1/O2 use `speed`, and Os uses `speed_and_size`.
Backend legalization runs on a private module clone at every level; it does
not rely on inlining to make return storage safe.

## Native layout and function ABI

Native memory is little-endian with 64-bit pointers. Integer types are
signless; individual instructions select signed or unsigned semantics.

| Sonatina type | Memory size / alignment (bytes) | Argument / single return |
| --- | --- | --- |
| `i1` | 1 / 1; low bit, canonical 0 or 1 | Cranelift `I8` scalar |
| `i8`, `i16`, `i32`, `i64` | 1/1, 2/2, 4/4, 8/8 | Corresponding scalar |
| `i128` | 16 / 16 | Cranelift `I128` scalar |
| `*T` | 8 / 8 | Native pointer |
| `i256` | 32 / 16 | Pointer to value / hidden return buffer |
| Arrays and unpacked structs | Native element/field layout | Pointer to value / hidden return buffer |
| `objref<T>` (private only) | 8 / 8 | Reference pointer, subject to lifetime legalization |
| `constref<T>` (private only) | 8 / 8 | Reference pointer / hidden buffer containing a copy of `T` |

Arrays use the element size as their stride and inherit its alignment.
Struct fields are individually aligned; total size includes trailing padding
to the maximum field alignment. Empty arrays/structs can have size zero but
retain their layout alignment. Packed structs are unsupported. Enums are
legalized to product layouts before native translation; do not assume a C
enum or union layout. Use the legalized module's type layout for storage.

Scalars use the host platform calling convention. LLVM ABI extensions are
enabled so x86_64 can pass and return `i128`, including register/stack
placement. No signed/unsigned extension attributes are attached to narrow
integer parameters or results. Only the declared width is meaningful;
upper register bits are not a sign-extension contract. `i1` inputs, loads
and results are normalized to their low bit.

Indirect value arguments point to caller-owned readable storage for the
whole value. Passing that pointer does not turn the value into a mutable
reference or transfer ownership. Keep its contents stable for the call.
Value-producing loads and updates create independent snapshots; private
object references instead preserve mutation aliases.

A single indirect return uses a caller-allocated, writable, suitably aligned
buffer large enough for the complete native value, including padding. Its
pointer is the first CLIF parameter with the `StructReturn` purpose, not
necessarily an ordinary first machine argument: AArch64 uses `x8`, for
example. Keep it distinct from live argument storage. The callee copies the
value into this buffer, so no result depends on a dead callee stack frame.
Even zero-sized indirect values retain the pointer parameter; provide a
valid aligned address, although no bytes are copied.

Multiple direct scalar returns follow Cranelift's platform convention, not
a C struct convention. Multi-return signatures containing indirect returns
are rejected. A function with no result has no return values; explicit
`unit` arguments or results are unsupported.

### Private references

Public and external signatures must not expose `objref` or `constref`,
including references nested inside other types. Private object returns may
borrow caller arguments or their projections. Proven fresh whole-object
return roots are rewritten into hidden caller-owned stack storage while
retaining the actual reference result. Thus a function can return a fresh
object on one path and a borrowed alias on another without copying the
borrowed object or losing its mutation semantics.

The stack-only proof is conservative. Unproven fresh projections, captured
local references, reference-bearing aggregate returns, recursive fresh
escapes and loop-carried fresh objects are rejected. There is no heap/arena
fallback. This private ABI may change during legalization; do not call
private reference-bearing functions directly from foreign code.

## Calling from C or a JIT host

The supported C interop subset is fixed, non-variadic signatures using
`i32`/`i64`, native pointers and either no result or one scalar/pointer
result. Use matching fixed-width C integer types. Raw pointers carry no
bounds or ownership checks: the caller must provide valid storage for all
accesses and keep it alive for the call.

Do not infer general C compatibility from the platform calling convention.
In particular, C aggregate-by-value signatures, `_Bool`, narrow signed
parameters/results, variadic calls and arbitrary multiple returns do not
have a documented mapping here. Use explicit scalar/pointer wrappers,
extending or truncating narrow values inside Sonatina. `i128` is supported
in the native ABI, but is not part of this portable C subset. Likewise an
`i256` result is not interchangeable with a C struct result.

With `CraneliftJitBackend`, `artifact.function_address(name)` returns a raw
code pointer for a defined function, or `None` for an unknown/import-only
name. Calling it is unsafe: use the exact ABI described here and keep the
artifact alive throughout every call. Prefer public scalar/pointer wrappers
when converting an address to an `extern "C"` function pointer. Generated
code is not sandboxed and must not unwind through foreign frames.

## Globals, imports and unsupported operations

Each defined global has one shared native data definition. Public globals
are exported, private globals are local, and external globals are imports.
Constants use read-only storage; mutable globals use writable storage.
Initializers use native little-endian field offsets with zero-filled
padding. Definitions without an initializer are zero-filled. Ordinary
global addresses and `const.ref` refer to the same definition; writing a
constant through a raw pointer is not supported.

Object imports are resolved by the system linker. JIT imports use
Cranelift's default process-symbol resolver, including its default libcall
names. A function or global present in an executable is not necessarily
visible to that resolver: it must be exported for dynamic lookup. There is
no user-supplied JIT symbol map in this API. Unresolved JIT symbols can panic
during finalization in upstream Cranelift; do not treat this as a recoverable
symbol-registration interface. Native memory helpers may require platform
libc symbols such as `memset`.

Representable `undef` values surviving to native translation are materialized
as zero, null or zero-filled aggregate storage. This is a backend choice,
not a guarantee that earlier IR optimization preserves a particular undef
value. Unresolved SSA values are compilation errors, not implicit undef.

The native instruction set includes integer arithmetic, comparisons, casts,
control flow, direct calls, memory and aggregate/object operations. Enum
operations must disappear during legalization. `get_function_ptr`,
`sym_addr` and `sym_size` are unsupported; dynamic allocation and object
materialization instructions must be lowered before native translation.
There are no first-class function values, indirect calls, varargs, floating
point operations or EVM-specific runtime services in this slice. Division
by zero is undefined at the IR level; callers must not rely on an EVM-style
zero result or a uniform trap policy across widths.
