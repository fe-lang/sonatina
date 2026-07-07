//! The block-entry state machine.
//!
//! Every block obtains its entry stack `StackIn(B) = P(B) ++ T(B)` from exactly one of a few
//! sources. This module reifies that decision as a per-block [`EntryKind`] (a static
//! classification) plus an [`EntryState`] lifecycle (`Pending -> Frozen`), replacing the parallel
//! side tables (`terminal_chain_blocks`, `inherited_stack`, `pending_edges`, `templates`) and the
//! `planned_blocks` set that the driver used to consult.
//!
//! Two operations drive the lifecycle:
//! - [`EntryTable::record_edge`] is called at every terminator for every successor edge and decides
//!   whether the edge is recorded for later (opaque no-op, single-pred inherit, deferred merge) or
//!   must be fixed up now against an already-frozen template (backedge / planned-early block).
//! - [`EntryTable::freeze_entry`] is called once when a block is planned: it consumes the pending
//!   state, selects the transfer region (the single place `choose_transfer` / `project_transfer` /
//!   `canonical_transfer_order` are consulted), freezes the template, and hands the driver the
//!   payload it needs to finish (deferred-edge fixups, the inherited prologue, the initial stack).
//!
//! Freezing is single-assignment by construction: the only `Pending -> Frozen` transition is in
//! `freeze_entry`, so the old `freeze_transfer` "second freeze is silently ignored" convention is
//! gone and a double freeze is unreachable rather than tolerated.

use cranelift_entity::SecondaryMap;
use smallvec::SmallVec;
use sonatina_ir::{BlockId, InstId, ValueId};

use crate::bitset::BitSet;

use super::{
    builder::StackifyContext,
    slots::FreeSlotPools,
    sym_stack::SymStack,
    templates::{
        BlockInterfaces, BlockTemplate, TransferOrder, canonical_transfer_order, choose_transfer,
        project_transfer,
    },
    trace::StackifyObserver,
};

/// Static per-block classification, derived once per fixed-point iteration from the CFG plus the
/// terminal-chain analysis. Determines *which* rule supplies the block's entry stack.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub(super) enum EntryKind {
    /// Function entry: the entry stack is the ABI stack (args ++ optional `FuncRetAddr`).
    FunctionEntry,
    /// Terminal chain: entered with an opaque stack; no normalization anywhere.
    Opaque,
    /// Exactly one predecessor: the entry stack is whatever that predecessor leaves.
    #[default]
    Inherited,
    /// Two or more predecessors (jump-only, by the split-edge precondition): the entry stack is the
    /// frozen template; each incoming jump normalizes to it.
    Merge,
}

/// A merge-block incoming jump whose exit-normalization fixup is deferred until the merge block is
/// planned (its template is frozen from the arrived predecessor stacks). Mirrors what the old
/// `PendingEdge` carried.
#[derive(Clone)]
pub(super) struct DeferredEdge {
    pub(super) pred: BlockId,
    pub(super) inst: InstId,
    pub(super) stack: SymStack,
    pub(super) free_slots: FreeSlotPools,
    pub(super) action_start: usize,
    /// Index of this edge's `DeferredExit` event in the observer's trace (0 for `NullObserver`),
    /// used to backfill the exit fixup actions once the merge template is resolved.
    pub(super) trace_token: usize,
}

/// Dynamic entry-state lifecycle for one block within one fixed-point iteration.
#[derive(Clone)]
pub(super) enum EntryState {
    /// Not planned yet; collects whatever has arrived. `inherited` is used by `FunctionEntry`
    /// (seeded) and `Inherited` kinds; `deferred` by `Merge`. `params` is the stack-resident
    /// parameter prefix, moved into the frozen template.
    Pending {
        params: SmallVec<[ValueId; 4]>,
        inherited: Option<(BlockId, SymStack)>,
        deferred: Vec<DeferredEdge>,
    },
    /// Block planned; template frozen. Later (back)edges fix up against this.
    Frozen(BlockTemplate),
}

impl Default for EntryState {
    fn default() -> Self {
        EntryState::Pending {
            params: SmallVec::new(),
            inherited: None,
            deferred: Vec::new(),
        }
    }
}

#[derive(Clone, Default)]
struct Entry {
    kind: EntryKind,
    state: EntryState,
}

/// Which record path a terminator edge takes, carrying the path-specific data.
pub(super) enum RecordEdge<'a> {
    /// Unconditional jump: may defer (forward merge), inherit (forward single-pred), or fix up now
    /// (frozen dest / planned-early block).
    Jump {
        inst: InstId,
        free_slots: &'a FreeSlotPools,
        action_start: usize,
    },
    /// Conditional branch / `br_table` edge. Critical edges are pre-split, so the target is
    /// single-pred and always inherits; a frozen target means an unsplit in-cycle multiway edge.
    /// `label` ("branch" / "br_table") only feeds the assert messages.
    Multiway { label: &'static str },
}

/// What [`EntryTable::record_edge`] tells the caller to do at the terminator.
pub(super) enum EdgeDisposition {
    /// Forward edge recorded for later (opaque no-op, single-pred inherit): caller emits the exit +
    /// jump trace itself.
    Recorded,
    /// Forward merge edge deferred; its exit + jump trace was captured synchronously here, so the
    /// caller emits nothing further.
    Deferred,
    /// Dest already frozen (backedge / planned-early): normalize to this template now.
    FixupNow(BlockTemplate),
}

/// What [`EntryTable::freeze_entry`] hands back to the driver so it can finish planning the entry
/// (run deferred-edge fixups, the inherited prologue, and build the initial stack). Transfer
/// selection and the `Pending -> Frozen` transition have already happened.
pub(super) enum ResolvedEntry {
    /// Terminal chain: opaque entry stack, no normalization.
    Opaque,
    /// Function entry: the seeded ABI stack, used unchanged.
    Entry { stack: SymStack },
    /// Single predecessor arrived: inherit its exit stack (with a prologue fixup if the block has
    /// phi params).
    Inherited { pred: BlockId, stack: SymStack },
    /// Nothing arrived before the block's RPO visit (irreducible / planned-early merge or
    /// single-pred): the template was frozen from the canonical fallback; build the stack from it.
    Fallback,
    /// Merge with `>= 1` arrived edges: fix each deferred edge up to the frozen template, then build
    /// the stack from it.
    Merge { deferred: Vec<DeferredEdge> },
}

pub(super) struct EntryTable {
    entries: SecondaryMap<BlockId, Entry>,
}

impl EntryTable {
    /// Classify every block and seed the function entry's ABI stack. Runs once per fixed-point
    /// iteration, after the terminal-chain analysis it consumes.
    pub(super) fn classify(
        ctx: &StackifyContext<'_>,
        interfaces: &BlockInterfaces,
        terminal_chain: &BitSet<BlockId>,
        entry_stack: SymStack,
    ) -> Self {
        let mut entries: SecondaryMap<BlockId, Entry> = SecondaryMap::new();
        for block in ctx.func.layout.iter_block() {
            let kind = if block == ctx.entry {
                EntryKind::FunctionEntry
            } else if terminal_chain.contains(block) {
                EntryKind::Opaque
            } else if ctx.cfg.pred_num_of(block) > 1 {
                EntryKind::Merge
            } else {
                EntryKind::Inherited
            };
            entries[block] = Entry {
                kind,
                state: EntryState::Pending {
                    params: interfaces.params[block].clone(),
                    inherited: None,
                    deferred: Vec::new(),
                },
            };
        }

        // Seed the entry block's ABI stack as its (single) inherited predecessor stack.
        if let EntryState::Pending { inherited, .. } = &mut entries[ctx.entry].state {
            *inherited = Some((ctx.entry, entry_stack));
        }

        Self { entries }
    }

    pub(super) fn kind(&self, block: BlockId) -> EntryKind {
        self.entries[block].kind
    }

    pub(super) fn is_frozen(&self, block: BlockId) -> bool {
        matches!(self.entries[block].state, EntryState::Frozen(_))
    }

    /// The frozen template for `block`. Panics if the block has not been planned yet.
    pub(super) fn template(&self, block: BlockId) -> &BlockTemplate {
        match &self.entries[block].state {
            EntryState::Frozen(tmpl) => tmpl,
            EntryState::Pending { .. } => panic!("block template is not frozen"),
        }
    }

    /// Record one successor edge at a terminator; see [`EdgeDisposition`].
    pub(super) fn record_edge<O: StackifyObserver>(
        &mut self,
        ctx: &StackifyContext<'_>,
        observer: &mut O,
        edge: RecordEdge<'_>,
        pred: BlockId,
        dest: BlockId,
        stack: &SymStack,
    ) -> EdgeDisposition {
        match edge {
            RecordEdge::Multiway { label } => {
                // Critical edges are pre-split, so every multiway successor is single-pred and only
                // ever inherits. An already-frozen (planned) target is an in-cycle multiway edge
                // that `StackifyEdgeSplitter` should have split.
                assert!(
                    !self.is_frozen(dest),
                    "multiway {label} edge to already-planned block {dest:?}: run \
                     StackifyEdgeSplitter before stackify to split in-cycle multiway edges"
                );
                debug_assert_eq!(
                    ctx.cfg.pred_num_of(dest),
                    1,
                    "no critical edges: {label} target must be single-pred"
                );
                self.set_inherited(dest, pred, stack);
                EdgeDisposition::Recorded
            }
            RecordEdge::Jump {
                inst,
                free_slots,
                action_start,
            } => match self.kind(dest) {
                // Terminal-chain dest: no normalization on any edge.
                EntryKind::Opaque => EdgeDisposition::Recorded,
                // Forward merge edge: defer the fixup until the merge template is frozen.
                EntryKind::Merge if !self.is_frozen(dest) => {
                    debug_assert!(
                        ctx.scc.is_reachable(dest),
                        "pending edge target must be reachable"
                    );
                    let trace_token = observer.on_deferred_inst_jump(inst, dest);
                    self.push_deferred(
                        dest,
                        DeferredEdge {
                            pred,
                            inst,
                            stack: stack.clone(),
                            free_slots: free_slots.clone(),
                            action_start,
                            trace_token,
                        },
                    );
                    EdgeDisposition::Deferred
                }
                // Forward single-pred edge: the successor inherits this exit stack.
                EntryKind::Inherited if !self.is_frozen(dest) => {
                    self.set_inherited(dest, pred, stack);
                    EdgeDisposition::Recorded
                }
                // Frozen `Merge`/`Inherited` (backedge / planned-early), or the function entry
                // (always frozen by the time an edge reaches it): fix up against the frozen template.
                EntryKind::FunctionEntry | EntryKind::Merge | EntryKind::Inherited => {
                    EdgeDisposition::FixupNow(self.template(dest).clone())
                }
            },
        }
    }

    /// Store a single-pred block's inherited predecessor stack. First writer wins: with split
    /// critical edges a single-pred block receives exactly one edge, except the degenerate
    /// `br c b b` double edge whose two stacks are identical, so keeping the first is correct.
    fn set_inherited(&mut self, block: BlockId, pred: BlockId, stack: &SymStack) {
        match &mut self.entries[block].state {
            EntryState::Pending { inherited, .. } => {
                inherited.get_or_insert_with(|| (pred, stack.clone()));
            }
            EntryState::Frozen(_) => unreachable!("inherit into already-frozen block {block:?}"),
        }
    }

    fn push_deferred(&mut self, block: BlockId, edge: DeferredEdge) {
        match &mut self.entries[block].state {
            EntryState::Pending { deferred, .. } => deferred.push(edge),
            EntryState::Frozen(_) => unreachable!("defer edge to already-frozen block {block:?}"),
        }
    }

    /// Consume `block`'s pending state, select its transfer region, freeze its template, and return
    /// the payload the driver needs to finish planning the entry. This is the single place transfer
    /// selection happens (`project_transfer` / `choose_transfer` / `canonical_transfer_order`).
    pub(super) fn freeze_entry(
        &mut self,
        ctx: &StackifyContext<'_>,
        carry_in: &BitSet<ValueId>,
        block: BlockId,
    ) -> ResolvedEntry {
        let kind = self.entries[block].kind;
        let EntryState::Pending {
            params,
            inherited,
            deferred,
        } = std::mem::take(&mut self.entries[block].state)
        else {
            panic!("block {block:?} entry already frozen");
        };

        let (transfer, resolved) = match kind {
            EntryKind::Opaque => (TransferOrder::new(), ResolvedEntry::Opaque),
            EntryKind::FunctionEntry => {
                let (_, stack) = inherited.expect("function entry stack seeded during classify");
                let transfer = project_transfer(&stack, carry_in);
                (transfer, ResolvedEntry::Entry { stack })
            }
            EntryKind::Inherited => match inherited {
                Some((pred, stack)) => {
                    let transfer = project_transfer(&stack, carry_in);
                    (transfer, ResolvedEntry::Inherited { pred, stack })
                }
                None => (
                    canonical_transfer_order(carry_in, &ctx.dom_depth, &ctx.def_info),
                    ResolvedEntry::Fallback,
                ),
            },
            EntryKind::Merge => {
                debug_assert!(
                    inherited.is_none(),
                    "pending merge edges cannot also inherit one stack"
                );
                if deferred.is_empty() {
                    (
                        canonical_transfer_order(carry_in, &ctx.dom_depth, &ctx.def_info),
                        ResolvedEntry::Fallback,
                    )
                } else {
                    let projected: Vec<(BlockId, TransferOrder)> = deferred
                        .iter()
                        .map(|edge| (edge.pred, project_transfer(&edge.stack, carry_in)))
                        .collect();
                    let transfer = choose_transfer(ctx, block, &projected);
                    (transfer, ResolvedEntry::Merge { deferred })
                }
            }
        };

        self.entries[block].state = EntryState::Frozen(BlockTemplate::new(params, transfer));
        resolved
    }

    /// After `plan_blocks`, every planned block is frozen and no pending block still holds deferred
    /// merge edges (the old "unresolved stackify edges remain" invariant).
    pub(super) fn debug_assert_no_pending_edges(&self) {
        debug_assert!(
            self.entries.values().all(|entry| match &entry.state {
                EntryState::Frozen(_) => true,
                EntryState::Pending { deferred, .. } => deferred.is_empty(),
            }),
            "unresolved stackify edges remain"
        );
    }
}
