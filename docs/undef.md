# Unspecified values (`undef`)

`undef.T` is the unspecified value of type `T`. In the semantics it is a single
value, not a choice made at each use: `eq x x` with `x` unspecified is the
unspecified value, not true at one use and false at another. Any value of `T`
refines it, and each refinement is separate, so a transform may replace it, or
a result that is unspecified, by any value of the type. A compiled program may
therefore show different bits where the source has the unspecified value, even
at two uses of one source value; only `freeze` gives all its uses one concrete
value.

## Propagation

- An arithmetic, bitwise, comparison or cast instruction with an unspecified
  operand gives the unspecified value, whatever its other operands are:
  `and 0 x`, `mul 0 x` and `or -1 x` are unspecified when `x` is.
- A phi gives the input of the edge taken. `select c a b` gives the arm `c`
  chooses, and the unspecified value when `c` is unspecified.
- Aggregates and enums are field-wise: every part of an unspecified aggregate
  is unspecified, `agg.make` gives each field its operand, `insert_value`
  leaves the other fields as they were, and `extract_value` of an unspecified
  field is unspecified.
- Call arguments, call results, returned values and the value operand of a
  store carry it unchanged.
- `freeze x` is `x` when `x` is specified, and otherwise some concrete value,
  the same for every use of its result.
- A query of chain or account state (`evm_balance`, `evm_ext_code_size`,
  `evm_ext_code_hash`, `evm_block_hash`, `evm_blob_hash`) with an unspecified
  operand gives the unspecified value; only its gas may differ.

## Undefined behavior

Using the unspecified value is undefined behavior only:

- as the condition of a `br` or the scrutinee of a `br_table`;
- as the address or object operand of a load, a store or any other access
  through a pointer or object reference, or as the key of `evm_sload`,
  `evm_sstore`, `evm_tload` or `evm_tstore`;
- as an index that selects a member or computes an address: `gep`,
  `obj.index`, `const.index`, `insert_value`, `extract_value`, the field of
  `enum.extract` or `enum.proj`;
- in a trusted variant assumption: `enum.assert_variant`, `enum.extract`.

Avoiding these is the frontend's obligation. An unspecified word that reaches
observable output (return data, a log, `sstore`, the data of an external call)
is emitted as some bits; there is no obligation there.

An operand that sets what an effect does rather than being data is taken as
some value of its type when it is unspecified, as if frozen: a length or size,
the gas, value or target of a call, the salt of `evm_create2`, an offset into
calldata, code or return data, the size of an allocation. An unspecified `i8`
length is a length from 0 to 255; an unspecified `i256` length is any word.

Division or remainder by zero, or by an unspecified divisor, is a separate
question that this page does not settle.

## Memory

Every scalar a typed store writes occupies a slot; on EVM each scalar, narrow
ones included, takes one 32-byte word, and a typed store writes all of it. A
typed load of a slot gives what the last typed store of the same type to it
wrote; a store of another type writes the slot another way. A slot that nothing
wrote, or that was last written another way, holds the unspecified value; a
typed load does not make it a value of its type.

A copy of whole slots, by `memcopy`, `evm_mcopy`, or a load and store of the
same type, gives each destination slot the value its source slot held,
specified or not. A slot a copy covers only in part is written another way. A
copy from code of a constant's encoding (`evm_code_copy` from a constant
global) gives each slot the value the constant has there.

A raw read of a slot that holds the unspecified value (`evm_mload`,
`evm_keccak256`, the source of `evm_mcopy`) sees some bytes: `evm_mload` of
them is the unspecified value, and so is a hash of them, and as output they
are emitted as some bits.

The contents of raw EVM memory that no typed store wrote (fresh `evm_malloc`
memory, the bytes past a buffer, bytes written by `evm_mstore8`, a word that
overlaps several slots) are not defined here otherwise. The EVM reads zero
there; the byte-level memory model is an open question.

## Lowering

On EVM a narrow value's word is normalized, or the value is unspecified and the
word may be any word; `freeze` and effect operands are where such a value is
made a value of its type, by masking the word.

## The final IR

`zero.T` is the value of `T` whose bits are all zero: zero, the null pointer
or object reference, the tag of variant 0, an aggregate whose fields are each
zero, the unit value. It is an ordinary constant, not a second kind of
unspecified value; an access through a null pointer or object reference is
undefined behavior, as it names no location. EVM pointer provenance follows
this: a null pointer or object reference reaches no memory, as `undef` does,
and an integer or tag `zero`, alone or as a field of a zero aggregate, is a
raw word, as the immediate 0 is.

The last IR phase on every backend, `concretize`, makes every value concrete:
it replaces each literal `undef.T` with `zero.T`, lowers `freeze undef` to
zero (a frozen pointer to `int_to_ptr 0`, a defined pointer, not the null
`zero`), and replaces each other `freeze x` with `x`. On EVM a narrow `freeze`
is by then a mask of a word-typed `freeze`; the mask stays, and is folded where
the word it masks became a constant. Backends compile the final IR, which has no `undef`
and no `freeze`, and check so on entry (`check_concrete`). Until `concretize`,
the rules above hold, and passes may refine an unspecified value to anything.

In the final IR, memory is concrete: every byte holds a definite value at
every point. A slot nothing has written since its allocation holds whatever
the memory held there, which the IR does not determine. On EVM, where memory
legalization stores nothing for an unspecified field, the slot keeps the word
it had.

## Rules for passes

A rewrite is correct when each value of the target refines the source's on the
same path: it is equal, or the source's is unspecified. Folding a result that
may be unspecified is therefore always allowed: `sub x x` to 0 and `eq x x` to
1 hold whether or not `x` is specified. Two things are not:

- adding a branch, address or variant-assumption use of a value that may be
  unspecified on a path where the source made none;
- making a result depend on an operand it did not depend on, on that path.
  `select c a b` must not become arithmetic on both arms, and `select c 1 x`
  must not become `or c x`: where `c` is 1 and `x` unspecified, the source
  gives 1 and the target the unspecified value.

A pass that needs such a form first freezes the operand.

A fact an analysis derives about a value, such as its known bits or its range,
describes the word the compiled code computes, also where the value is
unspecified; `freeze x` has `x`'s facts only because `freeze` is the identity on
that word. A pass that refines an unspecified value to a particular value must
pick one every such fact allows. Refining a literal `undef` to zero is always
allowed, since analyses take nothing from it.
