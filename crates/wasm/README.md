# WebAssembly backend

The `sonatina-wasm` crate emits a WebAssembly module from a module for the
`wasm32-unknown-native` target. It is a separate crate, as the Cranelift backend
is, so EVM and native users do not build it. Translation uses the
[WAFFLE](https://crates.io/crates/waffle) crate, which recovers structured
control flow and encodes the module.

The backend translates integer programs, structs and arrays held in linear
memory, global data, dynamic allocation and 128- and 256-bit integers. Floating point,
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
(`memory.copy`, `memory.fill`) extensions of WebAssembly and, when a recursive
cycle makes a call in tail position, the tail-call extension. Every current
engine enables them.

## Target and layout

The `wasm32` ISA shares the instruction set and little-endian layout of the
native ISA, with 4-byte pointers represented as `i32`. There is one address
space, the module's linear memory. Sizes and alignments are those of the native
layout with 4-byte pointers: scalars are aligned to their size, a struct to
its widest field, an array to its element, `i128` takes 16 bytes aligned to 16
and `i256` 32 bytes aligned to 16. An enum has its tag at offset zero and the fields of every variant from one
payload offset, aligned for the widest field of any variant, so the payloads of
different variants share bytes.

| Sonatina type | WebAssembly value |
| --- | --- |
| `i1`, `i8`, `i16`, `i32` | `i32` |
| `i64` | `i64` |
| `*T`, `objref<T>`, `constref<T>` | `i32`, an offset into linear memory |
| struct, array, enum | `i32`, the address of the value in memory |
| `i128` | two `i64` values, least significant limb first |
| `i256` | four `i64` values, least significant limb first |

`unit` and function types cannot be parameters, results, phi values or
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
  maximum. A module that needs no frame, global data or heap has one page and
  the backend places nothing in it: addresses used by `mload` and `mstore` are
  chosen by the program or the host. Any other module has the layout below.
- A function with `public` linkage is exported under its symbol. `private`
  functions are only callable from the module. Export names must be unique. The
  parameters and results of an exported function are integers of at most 64 bits
  and pointers (as `i32`); a struct, array, `i128`, `i256` or reference in the signature
  of a public function is an error.
- A function with `external` linkage and no body is imported as a function
  whose field name is its symbol. The module name is `env` unless
  `WasmBackend::with_import_module` selects another. Imports take the same
  kinds of parameters as exports.
- Functions may return several values (WebAssembly multi-value).
- The module has a name section with the names of its functions, so an engine
  names them in the stack of a trap. The function behind an export `f` of a
  module with frames is `f$body`.

## Linear memory

A module that uses `alloca`, `obj.alloc`, struct or array values, constants,
global variables, `mem.alloc_dynamic` or the external `malloc` or `free` has this
layout, from the lowest address:

1. A reserved block of 16 bytes, so that address 0 is never an object.
2. The global variables, each at its alignment, in declaration order. Their
   initial contents are data segments of the module (all-zero data is not
   emitted). `const.ref` and the address of a global variable are these
   addresses. Only `private` global variables are supported.
3. When the module has a heap: the table of the heads of the free lists, 128
   bytes, one word for each size class.
4. The stack, `WasmBackend::with_stack_size` bytes (1 MiB by default) rounded
   up so that it ends on a page boundary. It holds the frames of calls.
5. The heap, from the end of the stack to the end of the memory. The initial
   memory has one page of it. It grows by `memory.grow`.

The host must not write to regions 3, 4 and 5 while the module is running, and
should treat regions 1 and 2 as owned by the module.

### Frames

Every function of such a module takes the address of the first free byte of the
stack as a hidden first parameter. It places its frame there: one slot, with
the alignment of its type, for each `alloca`, each `obj.alloc` (an object lives until
its function returns, as the front end promises), each struct, array or enum
that an instruction builds (results of `insert_value`, `enum.make`, `obj.load`,
`mload` of an aggregate, a call that returns an aggregate, an aggregate `undef`),
and each aggregate phi. It passes the end of
its frame to the functions it calls. Frames are 16-byte aligned. A call whose
frame does not fit below the end of the stack traps. Slots are static: an
instruction in a loop uses the same slot on each iteration, as `alloca` does on
the native target. Slot contents are not initialized.

There is no mutable stack pointer, so a trap leaves nothing to repair. An
exported function is a wrapper that starts the stack at the `stack_top` global of
the module (initially the start of region 4) and calls the function with it.
A call to an import first stores the end of its caller's frame in that global, so
that an export that the host calls back runs above the caller's frames, and puts
the global back when the import returns. The wrapper of an export also restores
it when the export returns. A trap in the module therefore leaves the global as
it was, except during the call to an import: when the host throws an error or a
callback traps, the module does not run again before the host call ends, and
the global stays at the end of the caller's frame. Every frame that was active
then stays reserved for later calls.

The host repairs this. A module with frames and at least one import exports the
global as `stack_top` (a mutable `i32`; no function of the module may have the
name). A host reads it before it calls an export and, if the call ends with an
error, writes that value back. Calls that the host makes from inside an import do
the same, so nested calls restore in order. A module with no imports does not
export the global and needs no repair.

### Tail calls

A private function in a recursive cycle makes tail calls, as on the native
target: a call whose results the function returns at once is a `return_call`,
so a deep tail recursion runs in constant stack. The callee starts its frame
where the caller's started. That needs the caller's frame to be dead: no
`alloca`, no reference to an `obj.alloc` that outlives a call, every struct,
array or enum argument one that the caller itself received, and no aggregate
result. A call in tail position that passes an aggregate built in the caller's
frame is still a `return_call`, with a frame above the caller's, so only the
stack of the module grows.

WAFFLE 0.3.3 has no `return_call`. The backend emits the call followed by a
return of its results and rewrites that sequence in the encoded module.

### The heap

`mem.alloc_dynamic` and the external C routines `malloc` and `free` use the
heap. No object does: every `obj.alloc` is a slot of the frame. The heap is an
allocator with size classes and free lists.

- Every block starts with a 16-byte header, so that payloads are 16-byte
  aligned. The class is at offset 0, the state at offset 4 (1 when the block is
  in use, 2 when it is free), and at offset 8 the address of the block cut before
  it (0 for the first block). A block of class `k` has a payload of `2**k`
  bytes, for `k` from 4 to 31. A request takes the smallest class that holds it,
  at least 16 bytes, so a block takes `2**k + 16` bytes: up to twice the request
  plus the header. A request of zero bytes gets a block of its own.
- A freed block goes on the list of its class. The first word of its payload is
  the link to the next free block, and the table in region 3 holds the first
  block of each class. An allocation takes the first block of its class's list
  when there is one, so the block freed last is the first reused. Otherwise a
  block is cut from the top of the heap, and the memory grows by the missing
  pages when it must. Blocks are never split or merged.
- The largest request is `2**31` bytes.
- `malloc(size: i32) -> pointer` returns 0 if the request is larger than that,
  if the end of the new block would not fit in 32 bits, or if the engine refuses
  to grow the memory; nothing has changed then. `mem.alloc_dynamic` traps in
  those cases, also changing nothing, so the instance can be called again.
- `free(pointer)` does nothing for 0. Any other address must be the payload of a
  block in use: aligned, inside the heap, with the state "in use", a class from 4
  to 31, and a block that ends at or below the top. Otherwise the call traps and
  changes nothing, which catches a double free and a free of an address that is
  not a block.
- Contents. A block cut from the top is zero, because memory above the top is
  always zero. A block taken from a list holds what its last user left, except
  its first word, which held the link.
- `WasmBackend::with_heap_poison` fills the payload of every block that `free`
  releases, except its first word, with the byte `0xA5`. A program that reads a
  block after freeing it then sees that pattern, so a comparison with a build for
  another target turns the use after free into a wrong answer. It costs one
  `memory.fill` for each `free` and is meant for tests.
- An external function named `malloc` or `free` is the allocator of the module
  and not an import. `malloc` must take one `i32` and return a pointer, and
  `free` must take a pointer and return nothing; a declaration with another
  signature is an error that says so. A call to `memmove` or `memcpy` is
  `memory.copy`, as described under aggregates.

### The host allocator

`WasmBackend::with_host_allocator` lets the host place data in the heap before
it calls an export, for example the bytes of a text argument. The module then
has a stack and a heap even if its code uses neither, and exports three
functions, whose names no function of the module may use (the module is
rejected with an error that names the function):

| Export | Meaning |
| --- | --- |
| `alloc(size: i32) -> i32` | Cuts a block from the top of the heap. The block is zero, and its payload is 16-byte aligned and 16 bytes after its header. It never takes a block from a free list. The call traps, and changes nothing, if the request cannot be met. |
| `arena_mark() -> i32` | The top of the heap. The next block cut from the top has its header at this address and its payload 16 bytes later. It has no side effect. |
| `arena_release(mark: i32)` | Frees every block at or above `mark`: the free blocks that end above the mark are unlinked from their lists, the bytes from `mark` to the top are cleared, and the top moves back to `mark`. Traps, and changes nothing, unless `mark` is a multiple of 16, not below the start of the heap, not above the top, and a block boundary. |

The protocol for one call is `mark = arena_mark()`, one `alloc` per argument,
the call, reading whatever the call returned by address, and
`arena_release(mark)`. The release also forgets the blocks that the call cut
from the top of the heap, so an export must not keep heap data for a later call.
A block that the call took from a free list, and did not free, stays allocated,
as it would on a native target. The memory that the heap grew stays; a release
does not shrink it.

A release first follows the back links from the top down to the mark, which
visits only the blocks it forgets, and checks each one (aligned, inside the heap,
a valid class, ending where the walk expects). It traps, changing nothing, if
the walk steps past the mark: the mark is inside a block. It then walks every free
list and checks each block it visits (aligned, inside the heap, in the state
"free"), and it traps, changing nothing, if a list is damaged, for example by a
write to a freed block. Only a second walk unlinks.

A call that frees what it allocates, outside any mark, does not make the heap
grow: freed blocks are reused. A call with a text argument is bounded between
calls by the release.

Marks may be nested, if the releases are made innermost first: an import that
calls back into an export that takes text takes its own mark above the outer one.
A mark is only an address, so a release cannot tell a stale mark from a valid one
at the same address. A mark that an earlier release passed traps while it is above
the top or inside a block. Once blocks are cut over it and it lands on a boundary,
it is accepted and frees what lies above it, including blocks in use. Releasing
the same mark twice in a row does nothing the second time.

## Aggregates, objects and constants

The semantics follow the host-native backend, whose legalization of enum tags,
aggregate combination and object returns the backend runs first.

- A struct, array or enum value is the address of an immutable snapshot.
  `insert_value`, `enum.make` and `obj.load` make a new snapshot;
  `extract_value` and `enum.extract` of an aggregate and `const.load` view the
  source in place.
- `insert_value` makes its snapshot in place when it is the only user of an
  insert in the same block. An `undef` aggregate is zero, so the snapshot of an
  insert into `undef` is filled with zero first, and that of another insert is
  a copy of its source, unless the inserts that continue in its storage write
  every byte.
- An aggregate of at most 64 bytes is copied with loads and stores, and a
  larger one with `memory.copy`. At `Os` every copy is a `memory.copy`, which
  is smaller than even one load and store.
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
- `mload`, `mstore`, `memzero`, `memcopy`, `gep` and `int_to_ptr` take an
  integer address of any width as well as a pointer (Fe holds raw pointers in
  256-bit integers). An address that does not fit in 32 bits traps.
- A `gep` index behaves the same whether it is a constant or computed at run
  time: one that does not fit in 32 bits traps when it is executed.
- Aggregate `undef` is zero-filled storage.

## 128- and 256-bit integers

A front end whose `usize` has 256 bits makes every array index and loop counter an `i256`.
The backend supports, for `i128` and `i256`, `add`, `sub`, `mul`, `neg`, `udiv`,
`sdiv`, `umod`, `smod`, `shl`, `shr`, `sar`, `and`, `or`, `xor`, `not`, `select`, all
comparisons, `is_zero`, `zext`, `sext` and `trunc` between them and to and from
the narrower types, the checked forms `uaddo`, `usubo`, `umulo`, `saddo`,
`ssubo`, `smulo` and `snego`, the saturating forms `uaddsat`, `usubsat`,
`umulsat`, `saddsat`, `ssubsat` and `smulsat`, loads and stores, `bswap`,
`clz`, `ctz`, `ptr_to_int`, `int_to_ptr` and `br_table`. `int_to_ptr` traps if
the value does not fit in 32 bits.

An `i128` is computed with the 256-bit code: its operands are extended to 256
bits, with the sign for a signed operation, and the result is the low 128 bits.
Calls, returns, phis and memory carry only its two limbs.

`evm_add_mod` and `evm_mul_mod` compute at 256 bits for every width: narrower
operands are zero-extended, as on the native target, so the sum or product
does not wrap.

Multiplication, division and shifts by a count that is not a constant are
functions of the module, emitted only when used. A shift by a constant, `sar`
included, is built in place, and so is a product with at most three limb products that are not
zero: any 128-bit product, and a 256-bit product of values extended from 64
bits. Limbs that are constants, such as the zero high limbs of a value
extended from 64 or 128 bits, are folded out of additions, subtractions,
comparisons and bitwise operations. A limb that no use reads is not computed:
before encoding, the backend removes every operator without effects whose
value nothing uses, as WAFFLE's encoder writes each value to a local whether
or not it is read.

Division traps on a zero divisor. It is one 64-bit division when both operands
fit in 64 bits, and no step when the dividend is below the divisor. Otherwise
it is long division on 64-bit digits: one step per limb of the dividend for a
divisor of one limb, and at most three steps for a longer divisor. A step
multiplies by the reciprocal of the divisor's top limb, which takes two 64-bit
divisions to compute. `evm_mul_mod` divides the 512-bit product the same way.

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
- `mload` and `mstore` access `i1`, `i8`, `i16`, `i32`, `i64`, `i128`, `i256`, pointers
  and aggregates. An access outside the memory traps. Natural alignment is only
  a hint, so unaligned addresses are valid. An `i1` load keeps the low bit of the
  byte.
- `br_table` takes the first case equal to the scrutinee and traps if no case
  matches and there is no default. Constant cases of at most 64 bits that lie
  close together index a WebAssembly `br_table`; other cases are compared in
  order.
- `unreachable` traps.
- An `undef` operand is materialized as zero.

## Order of effects

Reads, writes and calls happen in program order. A test generates straight-line
programs that mix them and compares the results and the final memory with a
model at every optimization level.

## Unsupported input

Every instruction of the native instruction set is either translated or
rejected with an error that names it. These are rejected: `get_function_ptr`,
`sym_addr`, `sym_size`, and any instruction whose type is a function
type. Public and external global variables are rejected as a
module-level error. Errors are returned from `compile_module`; the backend does
not panic on unsupported input.
