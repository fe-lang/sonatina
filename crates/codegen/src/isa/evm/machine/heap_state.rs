//! Shared forward-dataflow engine for tracking the state of the free-memory
//! pointer (`memory[0x40]`).
//!
//! Two passes instantiate this engine with different lattices:
//! - the *exactness* pass (here): "does 0x40 still hold its function-entry
//!   value?" — a bool with all-preds-must-agree meet, computed before malloc
//!   placements are decided and consumed by the Fixed-vs-Heap rules;
//! - the *floor* pass (`free_ptr_floor`): a numeric lower bound on 0x40,
//!   computed after placements exist (its transfer reads `MallocPlacement`).
//!
//! A single fixpoint cannot serve both: floors depend on placements, which
//! depend on exactness. One engine, two passes.

use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use sonatina_ir::{
    AccessKind, BlockId, Function, InstId, InstSetExt, ValueId,
    cfg::ControlFlowGraph,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
};

use crate::isa::evm::{
    memory_plan::FuncMemPlan, prepare::memory_access_may_touch_free_ptr_slot,
    ptr_provenance::Provenance,
};

/// Per-block fixpoint states of a forward heap dataflow.
pub(crate) struct HeapDataflowStates<S: Copy + Default> {
    pub(crate) block_in: SecondaryMap<BlockId, S>,
    pub(crate) block_out: SecondaryMap<BlockId, S>,
}

/// Runs a forward dataflow over `function`: every block is seeded with
/// `seed`, block entries are computed by `block_entry` from predecessor
/// exits, and `transfer_inst` advances the state across each instruction.
/// Iterates to fixpoint in layout order.
pub(crate) fn run_forward_heap_dataflow<S: Copy + PartialEq + Default>(
    function: &Function,
    seed: S,
    block_entry: impl Fn(BlockId, &SecondaryMap<BlockId, S>) -> S,
    transfer_inst: impl Fn(InstId, S) -> S,
) -> HeapDataflowStates<S> {
    let mut block_in: SecondaryMap<BlockId, S> = SecondaryMap::new();
    let mut block_out: SecondaryMap<BlockId, S> = SecondaryMap::new();
    for block in function.layout.iter_block() {
        block_in[block] = seed;
        block_out[block] = seed;
    }

    let mut changed = true;
    while changed {
        changed = false;
        for block in function.layout.iter_block() {
            let entry = block_entry(block, &block_out);
            let mut exit = entry;
            for inst in function.layout.iter_inst(block) {
                exit = transfer_inst(inst, exit);
            }
            changed |= block_in[block] != entry || block_out[block] != exit;
            block_in[block] = entry;
            block_out[block] = exit;
        }
    }

    HeapDataflowStates {
        block_in,
        block_out,
    }
}

impl<S: Copy + Default> HeapDataflowStates<S> {
    /// Replays every block from its fixpoint entry state, calling `visit`
    /// with the state *before* each instruction.
    pub(crate) fn for_each_inst_state(
        &self,
        function: &Function,
        transfer_inst: impl Fn(InstId, S) -> S,
        mut visit: impl FnMut(InstId, S),
    ) {
        for block in function.layout.iter_block() {
            let mut state = self.block_in[block];
            for inst in function.layout.iter_inst(block) {
                visit(inst, state);
                state = transfer_inst(inst, state);
            }
        }
    }
}

/// Whether `inst` may write the free-pointer slot (`memory[0x40]`), judged
/// from its declared memory effects and pointer provenance.
pub(crate) fn inst_writes_free_ptr_slot(
    function: &Function,
    inst: InstId,
    prov: &SecondaryMap<ValueId, Provenance>,
) -> bool {
    function.dfg.effects(inst).accesses.iter().any(|access| {
        access.kind == AccessKind::Write
            && memory_access_may_touch_free_ptr_slot(function, access, prov)
    })
}

/// The exactness pass: for each malloc, whether `memory[0x40]` provably still
/// holds its function-entry value at that point. Persistent mallocs, internal
/// calls, and any possible 0x40 write kill exactness; transient mallocs
/// preserve it (their lowering never touches the slot).
///
/// PARITY: internal calls kill exactness unconditionally, even though the
/// floor pass consults callee write summaries. Relaxing this would let more
/// mallocs become Fixed and needs its own snapshot-reviewed change.
pub(crate) fn compute_exact_heap_base_before_malloc(
    function: &Function,
    isa: &Evm,
    cfg: &ControlFlowGraph,
    func_plan: &FuncMemPlan,
    prov: &SecondaryMap<ValueId, Provenance>,
    entry_heap_base_is_exact: bool,
) -> FxHashMap<InstId, bool> {
    let transfer =
        |inst: InstId, exact: bool| match isa.inst_set().resolve_inst(function.dfg.inst(inst)) {
            EvmInstKind::EvmMalloc(_) => exact && func_plan.transient_mallocs.contains(&inst),
            EvmInstKind::Call(_) => false,
            _ => exact && !inst_writes_free_ptr_slot(function, inst, prov),
        };

    let states = run_forward_heap_dataflow(
        function,
        entry_heap_base_is_exact,
        |block, block_out| {
            let mut preds = cfg.preds_of(block);
            match preds.next() {
                None => entry_heap_base_is_exact,
                Some(first) => block_out[*first] && preds.all(|pred| block_out[*pred]),
            }
        },
        transfer,
    );

    let mut exact_before_malloc = FxHashMap::default();
    states.for_each_inst_state(function, transfer, |inst, exact| {
        if matches!(
            isa.inst_set().resolve_inst(function.dfg.inst(inst)),
            EvmInstKind::EvmMalloc(_)
        ) {
            exact_before_malloc.insert(inst, exact);
        }
    });
    exact_before_malloc
}
