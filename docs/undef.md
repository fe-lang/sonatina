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
  is unspecified, `insert_value` leaves the other fields as they were, and
  `extract_value` of an unspecified field is unspecified.
- Call arguments, call results, returned values and the value operand of a
  store carry it unchanged.
- `freeze x` is `x` when `x` is specified, and otherwise some concrete value,
  the same for every use of its result.

## Undefined behavior

Using the unspecified value is undefined behavior only:

- as the condition of a `br` or the scrutinee of a `br_table`;
- as the address or object operand of a load, a store or any other access
  through a pointer or object reference;
- in a trusted variant assumption: `enum.assert_variant`, `enum.extract`.

Avoiding these is the frontend's obligation. An unspecified word that reaches
observable output (return data, a log, `sstore`, the data of an external call)
is emitted as some bits; there is no obligation there.

Division or remainder by zero, or by an unspecified divisor, is a separate
question that this page does not settle.

## Memory

Every scalar a typed store writes occupies a slot; on EVM each scalar, narrow
ones included, takes one 32-byte word, and a typed store writes all of it. A
slot of an `alloca` or object that no store has written holds the unspecified
value, and a typed load of a slot gives what the last store to it wrote.

The contents of raw EVM memory that no typed store wrote (fresh `evm_malloc`
memory, the bytes past a buffer, bytes written by `evm_mstore8`, a word that
overlaps several slots) are not defined here. The EVM reads zero there; the
byte-level memory model is an open question.

## Lowering

Every backend materializes a literal `undef` as zero. Any other unspecified
value has whatever bits the compiled code computes or the memory holds: a slot
no store wrote reads its old contents.

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
