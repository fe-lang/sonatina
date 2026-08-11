# Trace, Debug, and Content Addressing Scope

This branch establishes a frontend-neutral substrate for trace/debug metadata and
content-addressed Sonatina IR views. It deliberately targets Sonatina main and
does not depend on Cranelift, Wasmtime forks, SP1 work, Fe internals, or any
target-specific projection.

## Goals

- Preserve opaque frontend origins through Sonatina IR using local handles.
- Expose deterministic function, block, instruction, and CFG trace views.
- Attach debug locations and debug tags to instructions without making those
  handles global source identity.
- Propagate debug handles conservatively through simple one-to-one transforms
  and cloning/inlining-style flows.
- Provide dimensioned Sonatina shape hashes for regression diffs, fuzzing,
  trace comparison, and future cache consumers.

## Non-Goals

- Sonatina does not interpret Fe `OriginExportKey` values or any other
  frontend-specific identity.
- Sonatina does not own EVM gas, bytecode PC attribution, DWARF, ethdebug,
  Datalog, LSP, or browser-view semantics.
- This branch does not introduce a cache-first compilation API. Content
  addressing is a derived view first; caches can consume it later.
- This branch does not claim full optimizer provenance. Missing or synthetic
  debug state remains explicit.

## Layering Contract

Sonatina owns Sonatina IR identity, CFG/SSA structure, debug handle storage,
conservative propagation rules, and content-addressed Sonatina shape views.

Frontend adapters own the meaning and validation of their origin keys. They may
store those keys in opaque Sonatina frontend-origin records, but Sonatina treats
the stored strings as uninterpreted payloads.

Target adapters own final artifact facts such as EVM bytecode PCs, gas, byte
size, stack or memory locations, and native/CLIF projections.

Downstream trace/query/report tools consume these emitted facts. They do not
create compiler identity.

## Planned Commit Shape

1. Scope rewrite: this document and reviewer-facing constraints.
2. Debug handles: `FrontendOriginId`, `DebugLocId`, `DebugTagId`, metadata
   tables, and instruction attachments.
3. Trace views: deterministic functions, blocks, instructions, CFG edges,
   instruction kinds, and debug handles.
4. Propagation: conservative copy/clone helpers for locations and tags.
5. Content addressing: dimensioned Sonatina IR hashes with deterministic graph
   aggregation.

Fe integration happens after the Sonatina substrate exists. Fe should encode
its canonical origin export keys as opaque frontend records, consume the
Sonatina trace views, and emit Fe trace facts from that adapter layer.
