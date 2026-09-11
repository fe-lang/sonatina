# Enum object verification

This is the contract and implementation specification for the replacement enum
analysis. It describes local verification at Standard and Full. The current
instruction-pattern checker does not yet implement this contract: in particular,
transporting a projected reference can bypass its read check. The replacement
must enter production in one cutover, without consulting the old checker.

## Contract

An enum payload reference is a **view**: a typed location together with the
ancestor variants that must be active when its contents are read. `enum.proj`
adds an ancestor guard. `obj.proj` and `obj.index` preserve existing guards.
Address formation is permitted before initialization, so constructing an enum
with `enum.set_tag`, projections and field stores remains legal.

At each covered read, all applicable guards must hold and the demanded subtree
must be initialized. A scalar read does not demand initialized sibling fields.
A whole product read demands all its children. A whole enum read demands its
tag and the fields of its active variant, including nested enums. Every local
reference carrier preserves this obligation, including phis, SSA aggregates,
enum payloads and memory-held references.

Initialization means enum payload readability. This is not a general check of
scalar definedness, poison, `undef`, lifetime, bounds or borrowing. In particular,
ordinary whole object loads outside guarded views retain their existing local
verification contract, but transport the source's known initialization state;
copying an uninitialized object cannot manufacture initialized payload facts.
The concrete tests use defined scalar inputs for claims about executed reads.

`enum.set_tag` selects a variant without initializing its fields. Setting the
same tag preserves established selected-payload facts. Selecting a payloadless
variant creates a complete enum value. A different payload-bearing tag does not
acquire initialized fields merely because the old variant was complete.
`Some -> None -> Some` resurrection is outside the required acceptance envelope.
Today's separate physical payload slots do not establish such an IR guarantee.

`enum.write_variant` writes the selected fields and tag. `obj.store` and
`obj.init.const` write the destination subtree. Their initialization effects
come from the written value's shape. Their reference-containment effects follow
the actual overwrite footprint: a tag write does not erase inactive reference
bytes. Loss of logical readability alone cannot remove a may-containment edge.

### Trust and interface boundaries

`enum.assert_variant_ref` is a trusted assumption at its program point, including
readability of the selected payload. It does not initialize storage or check a
runtime tag; lowering erases it. Its result aliases its operand. Later uses do
not reassert the assumption, and an assertion on a nested enum does not assert
the variants of its ancestors.

`enum.assert_variant` refines an immutable SSA enum value. A copied value remains
a snapshot when its source object changes; references within the snapshot still
refer to mutable objects and retain their own guards.

An incoming `objref<T>` has no encoded parent-enum obligation. It predates fresh
allocations in this invocation. Incoming references may alias each other; a
reference recovered later from a holder or opaque call may alias a fresh local
allocation. These are different origins. An unresolved local origin is never
silently reclassified as an imported reference without an obligation.

Calls may publish their reference-bearing arguments and invalidate mutable
guarantees. Retain possible aliases through returned values. Hidden dereferences
inside opaque callees and the truth of imported assumptions are outside this
local proof. Passing a not-yet-initialized field to an initializing helper is
permitted; ordinary signatures do not express the stronger contract needed to
check such a call interprocedurally.

Materialization exposes the entire allocation, including siblings. Raw accesses
remain subject to the existing raw-memory contract. A checked bounded write
directly into an independent raw allocation is disjoint. Derived pointers and
unknown or oversized ranges do not obtain this exception without a proof.

## Instruction and carrier inventory

The semantic dispatcher must explicitly classify every instruction with a
reference-bearing operand/result, an enum read, or a possibly interfering effect.
An unsupported producer yields unknown local provenance, not an empty view.

| Family | Required behavior |
| --- | --- |
| Function arguments | Import typed boundary values; distinguish preexisting roots from recovered aliases. |
| `obj.alloc` | Allocate a fresh, uninitialized instance. |
| `enum.proj`, `obj.proj`, `obj.index` | Derive a typed view, preserving and extending guards. |
| `enum.assert_variant_ref` | Refine current object state; preserve identity and existing ancestor guards. |
| `obj.load` | Query the cell read; copy value state and stored reference views. |
| `enum.get_tag` | Query ancestor guards and tag readability; create a saved tag observation. It does not demand the enum's payload. |
| `obj.store`, `obj.init.const` | Transfer value state into the written subtree; update reference cells. |
| `enum.set_tag`, `enum.write_variant` | Apply tag and selected-payload effects with distinct write footprints. |
| `insert_value`, `extract_value` | Transport the selected immutable child, including guarded references. |
| `enum.make`, `enum.extract` | Construct/query immutable enum state; transport references within selected payloads. |
| `enum.tag`, `enum.is_variant`, `enum.assert_variant` | Observe/refine immutable value state. |
| `phi` | Substitute every incoming value on its predecessor edge before merging. |
| `const.ref`, `const.proj`, `const.index`, `const.load` | Transport typed constant shapes; do not fabricate mutable local aliases. |
| `obj.materialize.stack`, `obj.materialize.heap` | Seed exposure, followed by containment closure. |
| `call`, `return` | Publish reachable reference-bearing values at the interface boundary; calls invalidate mutable guarantees. |
| Raw loads, casts and other opaque producers | Retain possible local aliases/guards in reference-bearing results. |
| Raw stores/copies and other memory writes | Publish reference-bearing stored values and invalidate potentially affected facts. |
| Other instructions | Require explicit proof of irrelevance to enum state/reference transport, or apply the conservative opaque rule. |

## Finite abstract domain

The production solver is a forward analysis over a finite sparse product, not a
set of complete execution paths. Keep `NoFlow` separate from reachable unknown
state. Define `a <= b` to mean that `b` represents at least all states represented
by `a`; a join must overapproximate both operands.

The finite vocabulary is derived from the validated function and its types:

- Allocation identities are `Single(site)` for nonrepeating sites, or
  `Recent(site)` and `Summary(site)` for sites on cycles. Incoming roots and
  opaque/imported alternatives have distinct identities. There are at most two
  identities per local allocation site, regardless of iteration count.
- A location is an identity and a type-correct path within its allocation.
  Paths contain product fields, enum payload fields, and array indices. By-value
  recursive types are already invalid IR. Reference dereference selects another
  allocation; it does not extend the first allocation's structural path.
- Array indices use constants occurring in accesses, symbolic SSA indices, or
  an unknown-index summary. Equal numeric constants normalize across widths.
  Never enumerate an array merely because its declared length is large.
- Materialize only paths demanded by instructions, their ancestors, and paths
  introduced by substitutions through those same finite typed access templates.
  If a substitution cannot retain a finite exact path, use an overlapping
  summary. Summary operations may lose guarantees; they cannot erase obligations.
- A guarded alternative pairs a possible location with a set of
  `(ancestor location, variant)` guards. Deduplicate repeated guards. Unknown
  targets and unknown local guard provenance are explicit alternatives.
- Symbolic views are keyed by SSA value and structural child path. They carry
  guarantees about the location denoted by that value on the current path, in
  addition to conservative facts about its candidate allocations. Reference
  cells carry view identities/alternatives, not frozen mutable object facts.

| Component | Join on reachable predecessor states |
| --- | --- |
| Possible targets and guarded alternatives | Union, retaining unknown contributors. |
| Exact-view equalities | Intersection after predecessor substitution. |
| Tags and initialization | Union possible tags; intersect guarantees separately under each possible tag. |
| Reference-cell contents | Union possible guarded views. |
| Exposed allocations | Union, then transitive closure through containment. |
| Saved tag/object relations | Intersection after substitution of both endpoints. |

Type-shaped initialization uses whole-subtree certificates plus sparse child
overrides. A certificate establishes readability, not a particular nested tag.
Partial writes invalidate/refine affected ancestors and rederive completeness.
At a join of `Some(initialized)` with `None`, both alternatives remain readable;
the Some payload guarantee is conditional on Some, not discarded because None
has no corresponding field. For any variant possible on both sides, retain only
its common guarantees. A possible unknown tag must not disappear at a join.

### Identity, updates and correlation

An exact update requires one concrete location on each represented execution,
with an exact structural path and no summarized allocation multiplicity. A
singleton allocation-site set alone is insufficient. Ambiguous or summary writes
use weak updates for candidate locations and invalidate overlapping must facts.

A store through a multi-target symbolic view can establish a guarantee for that
same view, while only weakly updating its candidate roots. Each predecessor must
first transfer its incoming reference's guarantees to the phi result; intersect
those guarantees afterwards. Otherwise two initialized branch-local allocations
incorrectly lose readability when their references join.

Every possibly aliasing mutation updates/invalidates affected symbolic-view
guarantees as well as allocation facts. Copying a reference into a value or cell
preserves the relevant equality; copying its pointee creates an immutable value
snapshot. Rebinding a phi or allocation result on a loop iteration must not make
an older captured reference equal to the newly bound reference.

Before a repeated allocation, simultaneously rename its previous `Recent` into
`Summary` everywhere: object facts, view alternatives, cell contents, equalities,
exposure and observations. Merge it with existing summary facts conservatively,
then create the new private recent instance. Older objects remain potentially
exposed; no allocation event resets their exposure or proves them initialized.

Containment is a may graph over current physical reference cells. Exact private
overwrites may remove the overwritten edge. Ambiguous writes retain previous
possibilities. Exposure is sticky for an instance and closes transitively over
this graph, handling both store-before-expose and expose-before-store. Raw/opaque
interference can add unknown contents; losing content knowledge cannot prove
the absence of an alias.

Saved tags are immutable values with a separate relation to the current object's
tag. A possible tag write invalidates that relation; a disjoint payload write
does not. Branch refinement requires the relation to survive. Include every
matching explicit case and the default complement when destinations repeat.
Instruction IDs are not dynamic mutation epochs.

## Solver and query boundary

Validate structure, references, arity, local types and required SSA/CFG properties
before semantic dataflow, including at Standard. Do not assume that computing
dominators validates operand availability. Malformed IR must receive diagnostics
before any semantic transfer uses unchecked type/operand information.

Retain the shared CFG policy: real entry plus virtual entries into every block
of a disconnected source SCC; dead-to-live edges do not affect live analysis.
Each entry receives its boundary state. Other blocks start at `NoFlow`. Join
actual edge states and iterate monotone transfers. Assertions restrict admissible
states; they are not memory writes. Emit read diagnostics only after convergence.

Every covered use receives one of:

```text
NoLocalEnumObligation
Proven
Unproved { missing_guard | uninitialized_subtree | unknown_local_provenance }
```

A missing map entry is an implementation error, never an acceptance result.
`NoLocalEnumObligation` requires affirmative classification under the interface
contract. Unknown local provenance yields `Unproved`. Any precision bound must
lose facts conservatively and terminate deterministically.

## Validation and cutover gates

The independent concrete model uses fresh dynamic object identities, nested
storage, guarded references, immutable copies and explicit execution paths.
Assertions filter its executions without initializing memory. Bounded exploration
reports exhaustion separately; an unexplored path is not evidence of safety.

Maintain separate checks for:

1. Rejection of invalid covered reads in every modeled execution.
2. Acceptance of the documented supported forms and transformations.
3. Model self-tests, join laws, transfer monotonicity and worklist-order invariance.

The matrix includes unwritten/inactive payloads through each carrier, incoming
versus recovered roots, private/transitive/exposed holders and overwrite order,
nested same/different tags, partial and whole writes, conditional joins, snapshots,
saved observations, repeated allocations with retained older references, raw
write bounds, calls, disconnected CFGs and malformed input. Mutating the analysis
to drop a guard, invalidation, join contributor or older exposure must fail a
distinguishing test. Passing a bounded model is not a completeness theorem.

Stages are contract/model, validated views, object state/interference, one
production cutover, then integration/review. Retain all existing regressions.
Before committing production changes run nightly formatting, strict workspace
Clippy, all workspace/all-feature tests and doctests, and
`cargo run -p sonatina-filecheck`. Before publication run the Fe regressions and
release nextest suite against the replacement, plus verifier scaling with
independently varied objects, loads, aliases, nesting and CFG size. Downstream
restacking follows validation of the replacement.
