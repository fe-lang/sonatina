//! The stores that may have written the word each load of a local slot reads.
//!
//! A slot is an `alloca` whose address the function uses only as the address of its own memory
//! accesses, so no object reference can name it. A forward dataflow tracks, for each location of
//! such a slot, the writes that may have last stored it on some path. A location that some path
//! leaves unwritten, or that a write the solver cannot place may have stored, has no entry, so a
//! load of it has no writes. As in load-store forwarding, a raw write to an unknown address, or a
//! call that may write memory, may store any location.

use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    AccessKind, BlockId, ControlFlowGraph, Function, InstId, ValueId, inst::data::Alloca,
};

use crate::{
    analysis::memory_access::{BaseObject, LinearLocKey, MemoryAccessAnalysis, TrackedLocKey},
    optim::load_store::{collect_alloca_visibility, forwardable_read_key, store_value_of_inst},
};

/// Each load of a local slot whose word a store of the load's type wrote on every path to it, and
/// the values those stores may have written.
pub(crate) fn local_slot_load_writes(func: &Function) -> FxHashMap<ValueId, Vec<ValueId>> {
    let mut analysis = MemoryAccessAnalysis::new();
    let local = collect_alloca_visibility(func, &mut analysis).local_only;
    if local.is_empty() {
        return FxHashMap::default();
    }

    let mut solver = Solver { analysis, local };
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(func);
    let order: Vec<BlockId> = cfg
        .post_order()
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .collect();
    let entry = func.layout.entry_block();

    let mut outs = SecondaryMap::<BlockId, Option<SlotState>>::new();
    let mut ins = SecondaryMap::<BlockId, Option<SlotState>>::new();
    let mut changed = true;
    while changed {
        changed = false;
        for &block in &order {
            let state = if Some(block) == entry {
                Some(SlotState::default())
            } else {
                cfg.preds_of(block)
                    .filter_map(|&pred| outs[pred].as_ref())
                    .fold(None, |acc: Option<SlotState>, pred| {
                        Some(acc.map_or_else(|| pred.clone(), |acc| acc.meet(pred)))
                    })
            };
            let Some(mut state) = state else {
                continue;
            };
            ins[block] = Some(state.clone());
            for inst in func.layout.iter_inst(block) {
                solver.transfer(func, inst, &mut state, None);
            }
            if outs[block].as_ref() != Some(&state) {
                outs[block] = Some(state);
                changed = true;
            }
        }
    }

    let mut loads = FxHashMap::default();
    for &block in &order {
        let Some(mut state) = ins[block].take() else {
            continue;
        };
        for inst in func.layout.iter_inst(block) {
            solver.transfer(func, inst, &mut state, Some(&mut loads));
        }
    }
    loads
}

/// The writes that may have last stored each location of a local slot.
#[derive(Clone, Debug, Default)]
struct SlotState {
    cells: FxHashMap<LinearLocKey, Vec<ValueId>>,
}

/// Write lists compare as sets, so the solver's fixpoint does not depend on the order a meet
/// lists them in. A list holds each write once.
impl PartialEq for SlotState {
    fn eq(&self, other: &Self) -> bool {
        self.cells.len() == other.cells.len()
            && self.cells.iter().all(|(key, writes)| {
                other.cells.get(key).is_some_and(|others| {
                    writes.len() == others.len() && writes.iter().all(|w| others.contains(w))
                })
            })
    }
}

impl Eq for SlotState {}

impl SlotState {
    /// The state after either of two paths: a location written on both may hold either's write.
    fn meet(mut self, other: &Self) -> Self {
        self.cells.retain(|key, writes| {
            let Some(others) = other.cells.get(key) else {
                return false;
            };
            for write in others {
                if !writes.contains(write) {
                    writes.push(*write);
                }
            }
            true
        });
        self
    }
}

struct Solver {
    analysis: MemoryAccessAnalysis,
    local: FxHashSet<InstId>,
}

impl Solver {
    fn transfer(
        &mut self,
        func: &Function,
        inst: InstId,
        state: &mut SlotState,
        loads: Option<&mut FxHashMap<ValueId, Vec<ValueId>>>,
    ) {
        // A slot an `alloca` makes again holds nothing an earlier one stored.
        if func.dfg.downcast::<&Alloca>(inst).is_some() {
            state
                .cells
                .retain(|key, _| key.base != BaseObject::Alloca(inst));
            return;
        }

        let effects = func.dfg.effects(inst);
        if let Some(loads) = loads
            && let Some(TrackedLocKey::Linear(key)) =
                forwardable_read_key(func, inst, &mut self.analysis, &effects)
            && let Some(writes) = state.cells.get(&key)
            && let Some(result) = func.dfg.inst_result(inst)
        {
            loads.insert(result, writes.clone());
        }

        let Self { analysis, local } = self;
        let is_local = |base: &BaseObject| matches!(base, BaseObject::Alloca(alloca) if local.contains(alloca));
        for access in effects
            .accesses
            .iter()
            .filter(|a| a.kind == AccessKind::Write)
        {
            state.cells.retain(|key, _| {
                !analysis.access_may_alias_key(func, access, &TrackedLocKey::Linear(key.clone()))
            });
            if access.must_happen
                && let Some(TrackedLocKey::Linear(key)) = analysis.trackable_exact_loc(func, access)
                && is_local(&key.base)
                && let Some(value) =
                    store_value_of_inst(func, inst, &TrackedLocKey::Linear(key.clone()))
            {
                state.cells.insert(key, vec![value]);
            }
        }
    }
}
