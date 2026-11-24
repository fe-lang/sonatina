# Sonatina IR Value, Memory, and Undefined-Behavior Contract

This document defines the semantics of SSA values, object memory, raw memory,
the EVM address space, and undefined behavior across Sonatina's IR dialects.
It replaces the earlier `docs/undef.md` contract.

## Values

- **V1 (Concrete values only).** Every SSA value holds a concrete value of its
  type. There is no `undef` and no `freeze`. Constants are immediates
  (including `Immediate::zero` for all integral and enum-tag types), globals,
  and `zero.T` (for unit and compound types: zero-filled aggregates, null
  pointers and object references, and the unit value).
- **V2 (Bit-width semantics).** A value of `iN` is an `N`-bit integer. Holding
  narrow integers in zero-extended (unsigned-normalized) 256-bit words on EVM
  is a backend representation invariant, not part of the IR's value domain.
- **V3 (Aggregates and enums).** A struct or array value contains all of its
  fields. An enum value consists of its variant tag together with that active
  variant's fields only; inactive variants have no representation in the IR
  value.
- **V4 (Inhabited types only).** No SSA value, function parameter, or function
  return may have an uninhabited type (0-variant enums, enums whose variants
  are all uninhabited, or structs and non-empty arrays containing an
  uninhabited type). Functions that never return use unit return signatures and
  callers follow them with `unreachable`. The verifier enforces V4.

## Memory, at Two Levels

### Objects (`obj.alloc`, `obj.*`, `enum.*`)

Prior to `ObjectLowerToMemory`:

- **O1.** An object is a tree of typed cells. Each cell is either unwritten or
  holds a concrete value of its type. A fresh `obj.alloc` starts unwritten.
- **O2.** Reading an object is defined if and only if every cell demanded by
  the read has been written (for a whole enum read: its tag and the active
  variant's fields only). Reading an unwritten cell is undefined behavior (U2).

Sonatina's `enum_proofs` verifier checks local intraprocedural enum payload
readability (`docs/enum-object-verification.md`); full O2 initialization is a
frontend contract.

### Raw Memory (`alloca`, `evm_malloc`, `mload`/`mstore`, and lowered objects)

- **R1.** Raw memory consists of byte allocations plus, on EVM, the declared
  fixed scratch region (below). Every byte in an allocation always holds a
  concrete byte value; there is no "unwritten" byte state.
- **R2.** A fresh raw allocation (`alloca`, `evm_malloc`) holds arbitrary bytes
  chosen nondeterministically at allocation time and stable until overwritten.
  Every pass refines an unread allocation locally at the allocation site (for
  example, raw storage promotion in `scalarize.rs` seeds unread paths with
  zero constants, refining the allocation having chosen zero bytes).
- **R3.** Every in-bounds read of raw memory is defined and returns the bytes
  stored there. A typed load decodes those bytes. A typed load of a narrow type
  is undefined behavior (U2) if the bytes do not form a valid representation of
  that type: on EVM, a 32-byte word whose upper `256 - N` bits are non-zero; on
  native/Wasm targets, an `i1` byte outside `{0, 1}`.
- **R4.** A load names the exact byte range it needs and accesses no bytes
  outside it. For sub-word reads out of packed byte buffers on EVM,
  `evm_mload_bytes addr len` reads `len` bytes (`0 <= len <= 32`) starting at
  `addr` and returns them big-endian, zero-extended in a 256-bit word (`len ==
  0` returns `0` without reading memory; `len > 32` is U5). `evm_mload_bytes`
  lowers to `evm_mload` plus shift/mask at machine lowering, where flat EVM
  memory is defined past the allocation.

## The EVM Address Space

- **E1.** An access through a pointer with an allocation origin must stay
  within that allocation. Pointer arithmetic (`gep`, `add`/`sub`, pointer/int
  casts) preserves allocation origin and must stay within the allocation
  (`ptr_provenance.rs`).
- **E2.** An access through an address with no allocation origin must lie
  inside the module's declared fixed scratch region (for Fe, `[0x00, 0x40)`).
  Backend-owned slots (`FREE_PTR_SLOT = 0x40..0x60`, `DYN_SP_SLOT = 0x80..0xa0`)
  are outside the fixed region; when `VerifierConfig::evm_fixed_memory_limit`
  is configured, the verifier rejects constant EVM memory accesses that overlap
  backend-owned slots or exceed the declared limit.
- **E3.** A pointer written to linear memory and read back preserves its
  allocation origin. A pointer written to storage, transient storage, logs, or
  returndata and read back loses its allocation origin and falls under E2.
- **E4.** `evm_msize` observes backend memory placement and spills and is
  outside the certified IR subset.
- **E5.** `evm_return_code off len` is a memory-free terminal instruction whose
  higher-IR semantics returns `code[off..off+len]` directly without touching IR
  memory. It lowers to `CODECOPY 0 off len; RETURN 0 len` at machine lowering,
  preserving E2 for contract init sections with zero immutable slots.

## Undefined Behavior (Complete List)

- **U1.** A memory access disallowed by E1 or E2, including any dereference of
  a null pointer or null object reference (`zero.*T`, `zero.objref<T>`).
- **U2.** An object read disallowed by O2; a narrow typed load of an invalid
  representation (R3); or an unchecked narrowing (`trunc_nuw`) whose discarded
  upper bits are non-zero.
- **U3.** Use of an `obj.alloc` (or any reference or materialized stack pointer
  derived from it) after its enclosing frame returns, or after its `obj.alloc`
  executes again in a loop (`docs/object-aliasing.md`).
- **U4.** Violation of an explicit IR annotation or assumption:
  - `noalias`, `readonly`, `nocapture` — including entry-initialization of
    `noalias readonly` `objref<T>` arguments (the caller guarantees `T`'s cells
    are initialized at call entry);
  - `obj.index` or `const.index` out of bounds;
  - `enum.assert_variant`, `enum.assert_variant_ref`, or `enum.extract` on an
    inactive variant.
- **U5.** An operand outside an instruction's domain:
  - `evm_mload_bytes` with `len > 32` (the verifier rejects a constant one;
    EVM machine lowering yields `0` for a dynamic one);
  - `udiv`, `sdiv`, `umod`, or `smod` with a zero divisor. Targets differ: EVM
    lowers them to its total division and yields `0`, WebAssembly traps,
    Cranelift traps up to 128 bits and at 256 bits yields an all-ones quotient
    and the dividend as remainder, and the interpreter yields no value.

## Defined Operations

- **`unreachable`** traps (EVM emits `INVALID` `0xfe`; Cranelift and Wasm
  trap). No pass propagates branch facts backward from `unreachable`.
- **Default-less `br_table`** is valid if and only if the scrutinee has type
  `enumtag(@E)` and the table contains an arm for every declared variant of
  `@E`. Any other `br_table` requires an explicit default block (enforced by
  the verifier). When `EnumTag` lowers to an integer, exhaustive default-less
  tables promote their last arm to the default target.
- **EVM division and remainder** (`evm_udiv`, `evm_sdiv`, `evm_umod`,
  `evm_smod` and their overflow-reporting variants) are total: dividing or taking
  remainder by zero yields `0`, and signed `INT_MIN / -1` / `INT_MIN % -1`
  follow EVM semantics.
- **Signed division overflow:** `sdiv` of the signed minimum by `-1` wraps to
  the signed minimum, and `smod` of it by `-1` is `0`, at every width, on every
  target and in the interpreter.
- **Enum lowering:** `obj.store p (enum.make V ...)` folds to
  `enum.write_variant p V ...` before `ObjectLowerToMemory` at every
  optimization level. Lowered enum payload words are widened to `i256` (or
  pointers) on EVM, unset payload words are initialized with zero constants,
  and narrow payload extraction uses `trunc_nuw` (discharged by U4's active
  variant contract and lowered without masking on EVM).

## Rules for Passes

Because every SSA value is concrete (V1), value equivalence is exact equality
(or equality on demanded bits) rather than `undef` refinement:

- `fold_fresh_aggregates` folds residual fresh `insert_value` chains into
  `agg.make` after the last IR pass of every backend, and
  `check_fresh_aggregates_folded` verifies none reach the backends.
- Operations with UB preconditions (`trunc_nuw`, `enum.extract`,
  `enum.assert_variant*`, memory accesses) must not be speculated above guards
  that establish their preconditions (`DataFlowGraph::can_speculate`).
- Demanded-bits simplification must treat `trunc_nuw` as demanding all input
  bits so masks clearing discarded high bits are never dropped before it.
