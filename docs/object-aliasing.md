# Object alias and promotion contracts

Exact provenance gives coordinates, not separation. Two incoming object
references may name the same allocation or overlapping subobjects, even when
pointee types and relative leaf numbers differ. `local_only` describes escape
behavior; it grants neither no-alias nor unchanged-memory semantics.

## Shared queries

`object_alias.rs` classifies direct origins independently of optimization
eligibility. Distinct fresh allocations and incoming-versus-new allocations are
separate. Different incoming roots may overlap. A missing origin or unknown
provenance contributor cannot prove separation. Same-base intervals retain their
ordinary field precision. Repeating allocation sites do not identify one dynamic
instance and cannot establish definite overwrite.

`object_access.rs::ObjectAccessFacts` combines those origins with complete/may
provenance and reachability. Its access universe includes operands whose roots
are excluded, inactive, or blocked in a particular optimization. Accesses are
exact projections, whole roots, external memory, or unknown memory. Publication
and materialization close transitively over stored references and expose the
whole allocation. External effects spare unrelated unpublished allocations;
unresolved local origins use the stronger unknown domain.

Instruction effects distinguish may-read, may-write, definite physical overwrite,
initialization sources, capture, logical unreadability, and variant assumptions.
Calls instantiate argument-relative and ambient effects through current actuals.
Unsupported extents widen; they do not clip away possible writes. May-write
summaries never supply definite overwrite or initialization. Only direct typed
writes can construct `DefiniteObjectWrite`, and consumers still require exact
same-instance coverage. Definedness additionally depends on the stored source.

Capture updates use strong replacement only for exact covering writes to one
instance. Aliased, ambiguous, and conditional/call writes preserve old possible
referents and add new or unknown alternatives. Inactive enum reference storage
remains possible containment even after a tag changes logical readability.

## Consumers and coordinate-query audit

| Consumer / remaining coordinate check | Required interpretation |
| --- | --- |
| ObjectLoadStore availability lookup and `same_base_slice_covers(container, contained)` | Extract a value already recorded for the same coordinates. All interfering writes first invalidate through shared semantic overlap. The name makes coverage direction explicit. |
| ObjectLoadStore backward liveness | May-reads make every overlapping store observable. Only `write_covers` kills liveness. Ancestor tag observations protect guarded reads. |
| ObjectMemory relevant-slice/state keys | Identify a tracked observation, never bound the effect universe. Every shared write is checked against every relevant slice before destination eligibility matters. |
| ObjectMemory exact initialization/same-tag selection | Update known coordinates after semantic invalidation; never update another may-alias root with the stored value. |
| AggregateCombine enum identities | Identify the enum whose current fact is cached. Shared may-effects invalidate state, pending stores, and saved tag observations across aliases. |
| AggregateCombine backward DSE | Reuses shared liveness transfer; exact definite coverage is required to remove a write. |
| Capture `slices_overlap_relative` | Translate a captured subrange inside an already selected common return object. It is not an overlap test between unrelated roots. |
| Capture strong kills | `ObjectAliasFacts::exact_write_covers` requires same root, interval coverage, and a single instance. |
| ABI root-return/use-chain checks | Establish a candidate's exact identity and closed uses; do not decide participant separation. |
| ABI participant conflicts and move liveness | Use shared may-overlap for reads, writes, exposure, and ancestor guards. |
| Scalarization exact projections/use chains | Establish rewrite coordinates and explicit mutation restrictions; incoming plans separately require semantic entry-content and placement proofs. |

Backward liveness uses canonical sorted, disjoint half-open leaf intervals per
root. Whole-root demand occupies one interval; insertion and predecessor union
coalesce touching intervals, while exact writes subtract only their covered
range. Capture demand is checked before subtraction. Both ObjectLoadStore and
AggregateCombine use this shared transfer. Range endpoints come from IR accesses
and root extents, so storage grows with access boundaries rather than array leaf
count. No widening threshold sacrifices sibling precision. Canonical ordering
also makes fixed-point equality independent of predecessor/insertion order.

GVN consumes ObjectMemory read keys after alias invalidation. LICM additionally
requires initialized contents and ancestor guards at loop entry. A saved SSA
snapshot retains its own definedness; later writes cannot make its undefined
fields defined. Sparse initialization tracks typed subtrees and selected variants
without expanding large arrays.

ABI sharing requires both a current snapshot and safe participants. Move also
requires ownership and no later observation; a synthetic output is observed at
return even after its last reference use. ForwardDest requires the destination
to behave like a private result throughout the call, including guard stability.
The pass first completes all signatures/calls with copies, then elides in
callee-first SCC and within-function reverse-postorder order using current facts.

## Incoming plans and caller proofs

Before rewriting, `IncomingPromotionPlan` records every original read, its exact
slice, and demanded leaves. Each replaced read must retain exact entry lineage
on all reaching paths, including loop backedges, or have a current caller-derived
unchanged-slice certificate. A write after the last read need not defeat the
local proof. A later store of an old SSA value does not recreate entry lineage.

Placement is independent. Every demanded leaf needs an unconditional original
entry-prefix read before ordering/validity barriers, or separate caller evidence
that its actual region is allocated, initialized, and unguarded at every call.
Unchanged contents alone do not permit speculation. Unused leaves add no reads;
whole-object loads demand every leaf. Mutated ordinary inputs and unsupported
shapes remain excluded. Private roots retain allocation-site undef reseeding.

Caller inference uses baseline effects only. Eligible functions are private,
nonrecursive, have at least one direct caller, and have no non-call symbol use
or object entry/include use. Every actual must map completely to a single-instance
region of validated type/extent. Instantiated writes, including captures,
recovered aliases, ambient writes, and logical unreadability, must not overlap
the demanded slice. One interfering or unsupported caller rejects the generic
certificate. Read-only actuals may alias. There is no cloning, runtime check,
recursive inference, public attribute, or pairwise no-alias interpretation.

## Analysis lifetime

`ModuleObjectFacts` owns a coherent effects/locality pair. Module rounds compute
outside function mutation locks, discard the whole snapshot after invalidating
passes, and drop it at round exit. Overrides can select functions only.

Caller certificates are inferred before and owned by one scalarization batch.
That batch preserves calls, signatures, escaping identities, and borrowed-input
writes. Certificates are checked against function, argument binding/type, and
slice; they cannot be supplied as overrides or retained in the round cache.

Synthetic output guarantees bind identity, ownership, type, initialization, and
return observation. Binding checks alone cannot validate arbitrary edits.
`ObjectAggregateAbi::lower_to_memory` owns the producer-to-consumer interval,
allowing only the known-preserving ObjectLoadStore cleanup between ABI rewriting
and memory lowering. It refreshes inferred facts after cleanup and consumes
contracts before type/signature cutover. Separate invocations receive no old
contracts. Native translation is read-only after inference; native return
legalization and ABI elision rebuild facts after complete rewrites.

## Conservative limits

Incoming candidates remain non-enum reifiable scalar/product roots of at most
four leaves. Caller proofs reject ambiguous projections, repeating allocation
sites, guarded actual views, open entry uses, and recursive SCCs. Their entry
validity route requires a direct allocation and known initialization. Baseline
local entry proofs remain available when caller inference is unavailable.

Effect sets above the exact-leaf budget widen to whole-root may-effects. Unknown
reference producers remain unknown, and source-definedness traversal has a
bounded conservative fallback. Capture/exposure closure is a whole-function
may analysis; it can inhibit optimization before a later publication. No
must-write or must-initialize call summaries are inferred. Native retains its
separate stack-lifetime contract: a reference captured by a helper is not
automatically accepted merely because its caller supplies a local holder. The
acceptance suite checks that native rejection and executes the case on EVM.
