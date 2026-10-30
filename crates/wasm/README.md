# WebAssembly backend

The `sonatina-wasm` crate emits a WebAssembly module from a module for the
`wasm32-unknown-native` target. It is a separate crate, as the Cranelift backend
is, so EVM and native users do not build it. Translation uses the
[WAFFLE](https://crates.io/crates/waffle) crate, which recovers structured
control flow and encodes the module.

The backend translates integer programs, structs and arrays held in linear
memory, global data, dynamic allocation and 256-bit integers. Floating point,
indirect calls and function pointers are not translated; see
[Unsupported input](#unsupported-input).

```no_run
use sonatina_codegen::{Compile, compile::OptLevel};
use sonatina_ir::Module;
use sonatina_wasm::WasmBackend;

fn compile_wasm(module: Module) -> Vec<u8> {
    Compile::new(module, WasmBackend::new())
        .with_opt_level(OptLevel::O2)
        .compile()
        .expect("wasm compilation failed")
        .into_bytes()
}
```

Compiling the same module twice produces identical bytes.

The module uses the multi-value, sign-extension and bulk-memory
(`memory.copy`, `memory.fill`) extensions of WebAssembly, which every current
engine enables.

## Target and layout

The `wasm32` ISA shares the instruction set and little-endian layout of the
native ISA, with 4-byte pointers represented as `i32`. There is one address
space, the module's linear memory. Sizes and alignments are those of the native
layout with 4-byte pointers: scalars are aligned to their size, a struct to
its widest field, an array to its element, and `i256` takes 32 bytes aligned to
16. An enum has its tag at offset zero and the fields of every variant from one
payload offset, aligned for the widest field of any variant, so the payloads of
different variants share bytes.

| Sonatina type | WebAssembly value |
| --- | --- |
| `i1`, `i8`, `i16`, `i32` | `i32` |
| `i64` | `i64` |
| `*T`, `objref<T>`, `constref<T>` | `i32`, an offset into linear memory |
| struct, array, enum | `i32`, the address of the value in memory |
| `i256` | four `i64` values, least significant limb first |

`i128`, `unit` and function types cannot be parameters, results, phi values or
operands. A module that uses one is rejected with an error naming the type.
Enum tags become their integer types before translation, as on the native
target.

A narrow integer is held zero-extended in its `i32`. Signed operations
sign-extend their operands and re-canonicalize results. Parameters of
exported functions and results of imports are canonicalized on entry, so a
host may pass or return any bits above the width. Results of exported functions
are canonical: an `i8` holding -1 is returned as 255.

## Module structure

- One linear memory is always emitted and exported as `memory`, with no
  maximum. A module that needs no frame, global data or arena has one page and
  the backend places nothing in it: addresses used by `mload` and `mstore` are
  chosen by the program or the host. Any other module has the layout below.
- A function with `public` linkage is exported under its symbol. `private`
  functions are only callable from the module. Export names must be unique. The
  parameters and results of an exported function are integers of at most 64 bits
  and pointers (as `i32`); a struct, array, `i256` or reference in the signature
  of a public function is an error.
- A function with `external` linkage and no body is imported as a function
  whose field name is its symbol. The module name is `env` unless
  `WasmBackend::with_import_module` selects another. Imports take the same
  kinds of parameters as exports.
- Functions may return several values (WebAssembly multi-value).

## Linear memory

A module that uses `alloca`, `obj.alloc`, struct or array values, constants,
global variables or `mem.alloc_dynamic` has this layout, from the lowest
address:

1. A reserved block of 16 bytes, so that address 0 is never an object.
2. The global variables, each at its alignment, in declaration order. Their
   initial contents are data segments of the module (all-zero data is not
   emitted). `const.ref` and the address of a global variable are these
   addresses. Only `private` global variables are supported.
3. The stack, `WasmBackend::with_stack_size` bytes (1 MiB by default) rounded
   up so that it ends on a page boundary. It holds the frames of calls.
4. The arena, from the end of the stack to the end of the memory. The initial
   memory has one page of it. It grows by `memory.grow`.

The host must not write to regions 3 and 4 while the module is running, and
should treat regions 1 and 2 as owned by the module.

### Frames

Every function of such a module takes the address of the first free byte of the
stack as a hidden first parameter. It places its frame there: one slot, with
the alignment of its type, for each `alloca`, each `obj.alloc` (an object lives until
its function returns, as the front end promises), each struct or array that an instruction builds (results of
`insert_value`, `obj.load`, `mload` of an aggregate, a call that returns an
aggregate, an aggregate `undef`), and each aggregate phi. It passes the end of
its frame to the functions it calls. Frames are 16-byte aligned. A call whose
frame does not fit below the end of the stack traps. Slots are static: an
instruction in a loop uses the same slot on each iteration, as `alloca` does on
the native target. Slot contents are not initialized.

There is no mutable stack pointer, so a trap leaves nothing to repair. An
exported function is a wrapper that starts the stack at the `stack_top` global of
the module (initially the start of region 3) and calls the function with it.
A call to an import first stores the end of its caller's frame in that global, so
that an export that the host calls back runs above the caller's frames, and puts
the global back when the import returns. The wrapper of an export also restores
it when the export returns. A trap in the module therefore leaves the global as
it was, except a trap during the call to an import: when the host throws an
error or a callback traps, the module does not run again before the host call
ends, and the frame of the caller stays reserved. Each such error costs the
frame of one function.

### The arena

`mem.alloc_dynamic` allocates from the arena. No object does: every `obj.alloc` is a slot of
the frame. An allocation takes the size rounded up to 16 bytes (a size of
zero takes 16 bytes, so that it has an address of its own), returns the old
arena top and moves it. Blocks are never freed and never overlap, and the memory
of a block is zero when it is returned, because the arena only moves up.

- If the new top is above the end of the memory, the memory grows by the missing
  pages. The module declares no maximum, so the arena can use as much memory as
  the host allows, up to the 4 GiB of a 32-bit address space.
- The allocation traps, and leaves the arena as it was, if the new top does not
  fit in 32 bits or if the engine refuses to grow the memory. A size operand
  wider than 32 bits traps if its value does not fit.
- Nothing is freed. A trap leaves the blocks that were allocated before it
  allocated and unchanged, and the instance can be called again.

### The host allocator

`WasmBackend::with_host_allocator` lets the host place data in the arena before
it calls an export, for example the bytes of a text argument. The module then
has a stack and an arena even if its code uses neither, and exports three
functions, whose names no function of the module may use (the module is
rejected with an error that names the function):

| Export | Meaning |
| --- | --- |
| `alloc(size: i32) -> i32` | The arena allocator described above. The block is 16-byte aligned, zeroed and at least 16 bytes. The call traps, and changes nothing, when the memory cannot grow. |
| `arena_mark() -> i32` | The arena top: the address the next block gets. |
| `arena_release(mark: i32)` | Frees every block allocated after `mark` was read: clears the bytes from `mark` to the arena top, so that new blocks read zero as before, and moves the top back to `mark`. Traps, and changes nothing, unless `mark` is a multiple of 16, not below the start of the arena and not above the top. |

The protocol for one call is `mark = arena_mark()`, one `alloc` per argument,
the call, reading whatever the call returned by address, and
`arena_release(mark)`. Blocks that the call allocated itself are freed by the
release as well, so an export must not keep arena data for a later call. The
memory that the arena grew stays; a release does not shrink it. Releasing to a
mark that an earlier release has already passed traps, which catches a host
that releases twice.

## Aggregates, objects and constants

The semantics follow the host-native backend, whose legalization of enum tags,
aggregate combination and object returns the backend runs first.

- A struct, array or enum value is the address of an immutable snapshot.
  `insert_value`, `enum.make` and `obj.load` make a new snapshot;
  `extract_value` and `enum.extract` of an aggregate and `const.load` view the
  source in place.
- A function receives aggregates by address and returns a single aggregate through
  a buffer in the caller's frame, which is a hidden parameter after the stack
  top. A `constref` result is the address of the constant. A function cannot
  return an aggregate together with other values.
- `obj.alloc`, `obj.proj`, `obj.index`, `obj.load`, `obj.store`,
  `obj.from_ptr`, `const.ref`, `const.proj`, `const.index` and `const.load` are
  address arithmetic and loads and stores. `obj.from_ptr`
  is the pointer itself: an object reference is the address of its storage.
- The enum instructions read and write the tag and the variant fields at their
  offsets. `enum.make` writes a new snapshot in the frame; `enum.write_variant`
  and `enum.set_tag` write through an object reference; `enum.proj` and
  `enum.assert_variant_ref` are addresses; `enum.assert_variant` emits nothing.
  Writing a variant leaves the bytes of the other variants' payloads as they
  were.
- `gep` adds the scaled index at each array or pointer step and the field offset
  at each struct step. Indices are signed and sign-extended (`true` of type `i1`
  is -1); an index of 64 or 256 bits that does not fit in 32 bits traps. The
  address arithmetic wraps modulo 2^32, and an access outside the memory traps.
  `obj.index` and `const.index` do not check the index against the length; a
  program that needs the check compares first, as Fe does.
- `memzero` is `memory.fill`. A call to an external `memmove` or `memcpy` that
  takes two pointers and a 32- or 64-bit length and returns a pointer is
  `memory.copy` (the ranges may overlap, the call returns its destination) and
  is not an import. A length that does not fit in 32 bits traps, and so does
  an address beyond the memory, even for a length of zero.
- Fe holds raw pointers in 256-bit integers, so `mload`, `mstore`, `memzero`
  and `gep` also take an `i256` address, which traps if it does not fit in 32
  bits.
- Aggregate `undef` is zero-filled storage.

## 256-bit integers

A front end whose `usize` has 256 bits makes every array index and loop counter an `i256`.
The backend supports `add`, `sub`, `mul`, `neg`, `udiv`, `sdiv`, `umod`, `smod`,
`shl`, `shr`, `sar`, `and`, `or`, `xor`, `not`, all comparisons, `is_zero`,
`zext`, `sext` and `trunc` between `i256` and the narrower types, the checked
forms `uaddo`, `usubo`, `umulo`, `saddo`, `ssubo`, `smulo` and `snego`, loads and
stores of `i256`, `bswap`, `ptr_to_int` to `i256` and `int_to_ptr` from `i256`. Not
translated: the saturating forms. `int_to_ptr` traps if the value
does not fit in 32 bits.

Multiplication, division and variable shifts are functions of the module,
emitted only when used. Division traps on a zero divisor. It is one 64-bit
division when both operands fit in 64 bits, and otherwise one step per bit of the
dividend.

## Instruction semantics

Integer arithmetic follows the IR semantics used by the interpreter and the
native backend:

- `add`, `sub`, `mul`, `neg` and shifts wrap to the width of the type.
- A shift by at least the bit width gives zero (`shl`, `shr`) or the sign fill
  (`sar`); WebAssembly itself would mask the count.
- `uaddo`, `usubo`, `umulo`, `saddo`, `ssubo`, `smulo` and `snego` return the
  wrapped result and an `i1` overflow flag. The saturating forms
  (`uaddsat`, `saddsat`, ...) clamp to the bound in the direction of overflow.
- `sdiv` of the minimum value by -1 wraps to the minimum value. Division or
  remainder by zero is undefined in the IR and traps in WebAssembly.
- `mload` and `mstore` access `i1`, `i8`, `i16`, `i32`, `i64`, `i256`, pointers
  and aggregates. An access outside the memory traps. Natural alignment is only
  a hint, so unaligned addresses are valid. An `i1` load keeps the low bit of the
  byte.
- `br_table` compares the scrutinee with each case in order and traps if no
  case matches and there is no default.
- `unreachable` traps.
- An `undef` operand is materialized as zero.

## Order of effects

Reads, writes and calls happen in program order. A test generates straight-line
programs that mix them and compares the results and the final memory with a
model at every optimization level.

## Unsupported input

Every instruction of the native instruction set is either translated or
rejected with an error that names it. These are rejected: `get_function_ptr`,
`sym_addr`, `sym_size`, and any instruction whose type is `i128` or a function
type. Public and external global variables are rejected as a
module-level error. Errors are returned from `compile_module`; the backend does
not panic on unsupported input.
