use crate::{
    analysis::memory_access::MemoryAccessAnalysis,
    bitset::BitSet,
    cfg_scc::CfgSccAnalysis,
    domtree::DomTree,
    isa::evm::{
        immediate_materialization_code_len, immediate_materialization_plan,
        static_arena_alloc::StackObjId,
    },
    liveness::Liveness,
    stackalloc::{Action, normalize_value_alias_map},
};
use cranelift_entity::{EntityRef, SecondaryMap};
use rustc_hash::FxHashSet;
use smallvec::SmallVec;
use sonatina_ir::{
    BlockId, Function, I256, InstDowncast, ValueId, cfg::ControlFlowGraph,
    inst::evm::EvmCalldataLoad,
};

use super::{
    alloc::{SpillStorage, StackifyAlloc},
    block::operand_order_for_stackify,
    driver::FunctionPlanner,
    entry::EntryTable,
    planner::{MemState, NormalizeSearchScratch, StackifySearchCache, must_use_object_storage},
    slots::{FreeSlotPools, SpillSlotInterference, SpillSlotPools},
    spill::SpillSet,
    sym_stack::SymStack,
    templates::{
        DefInfo, compute_block_interfaces, compute_def_info, compute_dom_depth,
        compute_merge_separated, compute_phi_out_sources, compute_phi_results,
        function_has_internal_return,
    },
    terminal_chain::compute_terminal_chain_blocks,
    trace::{NullObserver, StackifyObserver},
};
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug)]
pub(super) struct StackifyReachability {
    pub(super) dup_max: usize,
    pub(super) swap_max: usize,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum StackifySearchProfile {
    Fast,
    GreedyWide,
    #[default]
    Exact,
}

/// Operand-prep beam search depth slack: either a fixed amount or "as deep as `SWAP*` reach".
#[derive(Clone, Copy, Debug)]
pub(super) enum BeamSlack {
    Fixed(usize),
    SwapMax,
}

impl BeamSlack {
    pub(super) fn resolve(self, swap_max: usize) -> usize {
        match self {
            BeamSlack::Fixed(n) => n,
            BeamSlack::SwapMax => swap_max,
        }
    }
}

/// Search-effort knobs for a `StackifySearchProfile`, expressed as data instead of code.
pub(super) struct SearchBudgets {
    pub(super) exact_operand_prep: bool,
    pub(super) exact_expansions: usize,
    pub(super) operand_prep_exact_expansions: usize,
    /// `(with incumbent, without incumbent)`.
    normalize_max_states: (usize, usize),
    pub(super) operand_prep_max_states: usize,
    pub(super) operand_prep_beam_width: usize,
    pub(super) operand_prep_beam_depth_slack: BeamSlack,
}

impl SearchBudgets {
    pub(super) fn normalize_max_states(&self, have_incumbent: bool) -> usize {
        if have_incumbent {
            self.normalize_max_states.0
        } else {
            self.normalize_max_states.1
        }
    }
}

const FAST_BUDGETS: SearchBudgets = SearchBudgets {
    exact_operand_prep: false,
    exact_expansions: 0,
    operand_prep_exact_expansions: 0,
    normalize_max_states: (0, 0),
    operand_prep_max_states: 0,
    operand_prep_beam_width: 16,
    operand_prep_beam_depth_slack: BeamSlack::Fixed(4),
};

const GREEDY_WIDE_BUDGETS: SearchBudgets = SearchBudgets {
    exact_operand_prep: true,
    exact_expansions: 1_000,
    operand_prep_exact_expansions: 250,
    normalize_max_states: (25_000, 50_000),
    operand_prep_max_states: 25_000,
    operand_prep_beam_width: 64,
    operand_prep_beam_depth_slack: BeamSlack::SwapMax,
};

const EXACT_BUDGETS: SearchBudgets = SearchBudgets {
    exact_operand_prep: true,
    exact_expansions: 50_000,
    operand_prep_exact_expansions: 50_000,
    normalize_max_states: (200_000, 500_000),
    operand_prep_max_states: 150_000,
    operand_prep_beam_width: 192,
    operand_prep_beam_depth_slack: BeamSlack::SwapMax,
};

impl StackifySearchProfile {
    pub(super) fn budgets(self) -> &'static SearchBudgets {
        match self {
            Self::Fast => &FAST_BUDGETS,
            Self::GreedyWide => &GREEDY_WIDE_BUDGETS,
            Self::Exact => &EXACT_BUDGETS,
        }
    }
}

impl StackifyReachability {
    pub(super) fn new(reach_depth: u8) -> Self {
        assert!(
            (1..=super::DUP_MAX as u8).contains(&reach_depth),
            "stackify reach_depth must be in 1..={}",
            super::DUP_MAX
        );

        let dup_max = reach_depth as usize;
        let swap_max = (dup_max + 1).min(super::SWAP_WINDOW_MAX);

        Self { dup_max, swap_max }
    }
}

/// The plan of one fixed-point iteration, and what it asks of the next.
struct IterationPlan {
    alloc: StackifyAlloc,
    /// The stack object of each stored value the plan may keep in one.
    spill_obj: SecondaryMap<ValueId, Option<StackObjId>>,
    /// The values the plan could not reach on the stack and are not spilled yet.
    spill_requests: BitSet<ValueId>,
    /// The values the plan loads from memory.
    reloaded: BitSet<ValueId>,
    /// The stored values the plan found no free scratch slot for.
    object_spills: BitSet<ValueId>,
}

pub struct StackifyBuilder<'a> {
    func: &'a Function,
    cfg: &'a ControlFlowGraph,
    dom: &'a DomTree,
    liveness: &'a Liveness,
    reach: StackifyReachability,
    search_profile: StackifySearchProfile,
    scratch_barred: Vec<BitSet<ValueId>>,
    value_aliases_override: Option<&'a SecondaryMap<ValueId, Option<ValueId>>>,
    stack_cached_immediates: FxHashSet<I256>,
    cache_hot_immediates: bool,
    hot_immediate_min_block_uses: u32,
    hot_immediate_min_materialization_bytes: usize,
    record_entry_stacks: bool,
}

pub(super) struct StackifyContext<'a> {
    pub(super) func: &'a Function,
    pub(super) cfg: &'a ControlFlowGraph,
    pub(super) dom: &'a DomTree,
    pub(super) liveness: &'a Liveness,
    /// The values each scratch spill slot cannot hold, one entry per slot.
    pub(super) scratch_barred: Vec<BitSet<ValueId>>,
    pub(super) entry: BlockId,
    pub(super) scc: CfgSccAnalysis,
    pub(super) dom_depth: SecondaryMap<BlockId, u32>,
    pub(super) def_info: SecondaryMap<ValueId, Option<DefInfo>>,
    pub(super) phi_results: SecondaryMap<BlockId, SmallVec<[ValueId; 4]>>,
    pub(super) phi_out_sources: SecondaryMap<BlockId, BitSet<ValueId>>,
    /// The values whose stack copy no instruction can use once they are defined
    /// (`compute_merge_separated`); a store of one moves it off the stack.
    pub(super) merge_separated: BitSet<ValueId>,
    pub(super) spill_slot_interference: SpillSlotInterference,
    pub(super) has_internal_return: bool,
    pub(super) reach: StackifyReachability,
    pub(super) search_profile: StackifySearchProfile,
    pub(super) value_aliases: SecondaryMap<ValueId, Option<ValueId>>,
    pub(super) remat_actions: SecondaryMap<ValueId, Option<Action>>,
    pub(super) stack_cached_immediates: FxHashSet<I256>,
    pub(super) record_entry_stacks: bool,
}

impl StackifyContext<'_> {
    pub(super) fn canonicalize_value(&self, value: ValueId) -> ValueId {
        self.value_aliases[value].unwrap_or(value)
    }

    /// The value is pinned to the stack: losing its last copy costs a spill/reload, so operand
    /// preparation must preserve it. Immediates are never pinned — they can always be re-pushed.
    pub(super) fn retains_value(&self, value: ValueId) -> bool {
        !self.func.dfg.value_is_imm(value)
    }

    /// The value is a hot cached immediate: rematerializable, but expensive enough to push that
    /// planning prefers `DUP`ing an existing stack copy over re-pushing it.
    pub(super) fn stack_caches_immediate(&self, value: ValueId) -> bool {
        self.func
            .dfg
            .value_imm(value)
            .is_some_and(|imm| self.stack_cached_immediates.contains(&imm.as_i256()))
    }

    /// The value participates in per-block use counting (`UseTracker`): pinned values and cached
    /// immediates alike are counted so they stay in `live_future` until their last in-block use.
    pub(super) fn is_use_tracked(&self, value: ValueId) -> bool {
        self.retains_value(value) || self.stack_caches_immediate(value)
    }
}

impl<'a> StackifyBuilder<'a> {
    pub fn new(
        func: &'a Function,
        cfg: &'a ControlFlowGraph,
        dom: &'a DomTree,
        liveness: &'a Liveness,
        reach_depth: u8,
    ) -> Self {
        Self {
            func,
            cfg,
            dom,
            liveness,
            reach: StackifyReachability::new(reach_depth),
            search_profile: StackifySearchProfile::default(),
            scratch_barred: Vec::new(),
            value_aliases_override: None,
            stack_cached_immediates: FxHashSet::default(),
            cache_hot_immediates: false,
            hot_immediate_min_block_uses: HOT_IMMEDIATE_DEFAULT_MIN_BLOCK_USES,
            hot_immediate_min_materialization_bytes:
                HOT_IMMEDIATE_DEFAULT_MIN_MATERIALIZATION_BYTES,
            record_entry_stacks: false,
        }
    }

    pub fn with_search_profile(mut self, profile: StackifySearchProfile) -> Self {
        self.search_profile = profile;
        self
    }

    /// Provides a scratch spill slot per entry of `barred`, the values the slot cannot hold.
    pub(crate) fn with_scratch_slots(mut self, barred: Vec<BitSet<ValueId>>) -> Self {
        self.scratch_barred = barred;
        self
    }

    pub fn with_value_aliases(
        mut self,
        value_aliases: &'a SecondaryMap<ValueId, Option<ValueId>>,
    ) -> Self {
        self.value_aliases_override = Some(value_aliases);
        self
    }

    pub(crate) fn with_hot_immediate_caching(mut self) -> Self {
        self.cache_hot_immediates = true;
        self
    }

    /// Record the stack each block is planned to start with
    /// (`StackifyAlloc::entry_stacks`).
    pub(crate) fn with_entry_stack_record(mut self, record: bool) -> Self {
        self.record_entry_stacks = record;
        self
    }

    pub(crate) fn with_hot_immediate_min_materialization_bytes(mut self, bytes: usize) -> Self {
        self.hot_immediate_min_materialization_bytes = bytes;
        self
    }

    pub(crate) fn with_hot_immediate_min_block_uses(mut self, uses: u32) -> Self {
        self.hot_immediate_min_block_uses = uses;
        self
    }

    pub fn compute(self) -> StackifyAlloc {
        let mut observer = NullObserver;
        self.compute_with_observer(&mut observer)
    }

    pub fn compute_with_trace(self) -> (StackifyAlloc, String) {
        let func = self.func;
        let (alloc, trace) = self.compute_with_trace_capture();
        let trace = trace.render(func, &alloc);
        (alloc, trace)
    }

    pub(crate) fn compute_with_trace_capture(self) -> (StackifyAlloc, super::trace::StackifyTrace) {
        let mut trace = super::trace::StackifyTrace::default();
        let alloc = self.compute_with_observer(&mut trace);
        (alloc, trace)
    }

    pub(super) fn compute_with_observer<O: StackifyObserver>(
        self,
        observer: &mut O,
    ) -> StackifyAlloc {
        self.compute_with_observer_and_cache(observer, &mut StackifySearchCache::default())
    }

    pub(crate) fn compute_with_search_cache(
        self,
        cache: &mut StackifySearchCache,
    ) -> StackifyAlloc {
        self.compute_with_observer_and_cache(&mut NullObserver, cache)
    }

    pub(crate) fn compute_with_trace_and_search_cache(
        self,
        cache: &mut StackifySearchCache,
    ) -> (StackifyAlloc, super::trace::StackifyTrace) {
        let mut trace = super::trace::StackifyTrace::default();
        let alloc = self.compute_with_observer_and_cache(&mut trace, cache);
        (alloc, trace)
    }

    fn compute_with_observer_and_cache<O: StackifyObserver>(
        self,
        observer: &mut O,
        cache: &mut StackifySearchCache,
    ) -> StackifyAlloc {
        let entry = match self.cfg.entry() {
            Some(b) => b,
            None => return StackifyAlloc::default(),
        };

        let mut scc = CfgSccAnalysis::new();
        scc.compute(self.cfg);

        let mut value_aliases = if let Some(value_aliases) = self.value_aliases_override {
            value_aliases.clone()
        } else {
            let mut aliases: SecondaryMap<ValueId, Option<ValueId>> = SecondaryMap::new();
            for value in self.func.dfg.value_ids() {
                aliases[value] = Some(value);
            }
            aliases
        };
        normalize_value_alias_map(self.func, &mut value_aliases);
        // Collapse numerically-equal immediates onto one representative ValueId, then re-normalize.
        // The imm pass keeps the map one-hop canonical, so re-running is idempotent; it re-validates
        // the invariant in debug builds over the post-canonicalization map.
        canonicalize_immediate_aliases(self.func, &mut value_aliases);
        normalize_value_alias_map(self.func, &mut value_aliases);

        let mut stack_cached_immediates = self.stack_cached_immediates;
        if self.cache_hot_immediates {
            stack_cached_immediates.extend(compute_hot_stack_cached_immediates(
                self.func,
                &value_aliases,
                self.hot_immediate_min_block_uses,
                self.hot_immediate_min_materialization_bytes,
            ));
        }

        let remat_actions = compute_remat_actions(self.func, &value_aliases);
        let phi_results = compute_phi_results(self.func, &value_aliases);
        let phi_out_sources = compute_phi_out_sources(self.func, self.cfg, &value_aliases);
        let def_info = compute_def_info(self.func, entry, &value_aliases);
        let merge_separated = compute_merge_separated(
            self.func,
            self.cfg,
            self.dom,
            &def_info,
            &value_aliases,
            &phi_out_sources,
        );
        let spill_slot_interference = SpillSlotInterference::compute(
            self.func,
            self.cfg,
            self.liveness,
            &phi_results,
            &value_aliases,
        );

        let ctx = StackifyContext {
            func: self.func,
            cfg: self.cfg,
            dom: self.dom,
            liveness: self.liveness,
            scratch_barred: self.scratch_barred,
            entry,
            scc,
            dom_depth: compute_dom_depth(self.dom, entry),
            def_info,
            phi_results,
            phi_out_sources,
            merge_separated,
            spill_slot_interference,
            // Internal-return functions expect a caller-provided return address below their args.
            has_internal_return: function_has_internal_return(self.func),
            reach: self.reach,
            search_profile: self.search_profile,
            value_aliases,
            remat_actions,
            stack_cached_immediates,
            record_entry_stacks: self.record_entry_stacks,
        };

        // `spill_set` is discovered via a monotone fixed point:
        // - planning may demand a `MemLoadFrameSlot(v)` when `v` is unreachable by `DUP16`
        // - or when a flush/rebuild needs to reconstruct a stack template
        // In that case we add `v` to `spill_requests`, discard this iteration's plan, and retry.
        //
        // Once `v ∈ spill_set`, we remove it from transfer regions (`T(B)` excludes `spill_set`).
        // A later plan may then reach every use of `v` on the stack, so only the values the last
        // plan reloaded are stored (`stored`): at their definition, on their phi's incoming edges,
        // or at entry for an argument, each of which dominates the loads. The plan is final once
        // it reloads exactly the values it stores.
        //
        // Dropping a store can change the rest of the plan: an edge no longer stages a phi's
        // source for it, and a store that took its value off the stack leaves the value there
        // instead. If that makes a plan reload a value whose stores were dropped, the value stays
        // stored from then on, which bounds the iterations.
        let mut spill_set: BitSet<ValueId> = BitSet::default();
        let mut stored: BitSet<ValueId> = BitSet::default();
        let mut dropped: BitSet<ValueId> = BitSet::default();
        let mut pinned: BitSet<ValueId> = BitSet::default();
        let mut search_scratch = NormalizeSearchScratch::with_cache(std::mem::take(cache));
        loop {
            let checkpoint = observer.checkpoint();
            let mut slots: SpillSlotPools = SpillSlotPools::default();

            let spill = SpillSet::new(&spill_set, &stored);
            let IterationPlan {
                mut alloc,
                spill_obj,
                spill_requests,
                reloaded,
                object_spills,
            } = Self::plan_iteration(&ctx, observer, spill, &mut slots, &mut search_scratch);

            let mut next_stored = BitSet::difference(&stored, &reloaded);
            next_stored.intersect_with(&pinned);
            next_stored.union_with(&reloaded);
            if spill_requests.is_subset(&spill_set) && next_stored == stored {
                Self::finalize_spill_storage(
                    &ctx,
                    spill,
                    &object_spills,
                    &mut slots,
                    &mut alloc,
                    &spill_obj,
                );
                alloc.validate_spill_storage();
                *cache = search_scratch.into_cache();
                return alloc;
            }

            observer.rollback(checkpoint);
            spill_set.union_with(&spill_requests);
            let mut reloaded_after_drop = BitSet::difference(&reloaded, &stored);
            reloaded_after_drop.intersect_with(&dropped);
            pinned.union_with(&reloaded_after_drop);
            dropped.union_with(&BitSet::difference(&stored, &next_stored));
            stored = next_stored;
        }
    }

    fn plan_iteration<O: StackifyObserver>(
        ctx: &StackifyContext<'_>,
        observer: &mut O,
        spill: SpillSet<'_>,
        slots: &mut SpillSlotPools,
        search_scratch: &mut NormalizeSearchScratch,
    ) -> IterationPlan {
        let mut object_spills: BitSet<ValueId> = BitSet::default();
        let mut arg_free_slots: FreeSlotPools = FreeSlotPools::default();
        for &arg in ctx.func.arg_values.iter() {
            let arg = ctx.canonicalize_value(arg);
            if let Some(spilled) = spill.stored(arg)
                && ctx.remat_actions[arg].is_none()
                && !must_use_object_storage(&ctx.scratch_barred, &object_spills, arg)
                && slots
                    .scratch
                    .try_ensure_slot(
                        spilled,
                        &ctx.spill_slot_interference,
                        &mut arg_free_slots.scratch,
                        &ctx.scratch_barred,
                    )
                    .is_none()
            {
                object_spills.insert(arg);
            }
        }

        let spill_obj = assign_spill_obj_ids(ctx.func, spill, &ctx.remat_actions);
        let interfaces = compute_block_interfaces(ctx, spill);

        let mut alloc = StackifyAlloc {
            pre_actions: SecondaryMap::new(),
            post_actions: SecondaryMap::new(),
            brtable_actions: SecondaryMap::new(),
            spill_storage: SecondaryMap::new(),
            remat_actions: ctx.remat_actions.clone(),
            entry_stacks: SecondaryMap::new(),
        };

        let mut spill_requests: BitSet<ValueId> = BitSet::default();
        let mut reloaded: BitSet<ValueId> = BitSet::default();
        let terminal_chain_blocks = compute_terminal_chain_blocks(ctx, &interfaces);

        // The entry block enters with its ABI stack (function args ++ optional return address); the
        // entry-state machine seeds this as the entry's inherited predecessor stack.
        let mut entry_stack = SymStack::entry_stack(ctx.func, ctx.has_internal_return);
        for (idx, &arg) in ctx.func.arg_values.iter().enumerate() {
            entry_stack.rename_value_at_depth(idx, ctx.canonicalize_value(arg));
        }
        let entries = EntryTable::classify(ctx, &interfaces, &terminal_chain_blocks, entry_stack);

        let mem = MemState {
            spill,
            spill_obj: &spill_obj,
            spill_requests: &mut spill_requests,
            reloaded: &mut reloaded,
            object_spills: &mut object_spills,
            slots,
        };
        let mut planner = FunctionPlanner::new(
            ctx,
            mem,
            &interfaces.carry_in,
            &mut alloc,
            entries,
            search_scratch,
            observer,
        );
        planner.plan_blocks();

        IterationPlan {
            alloc,
            spill_obj,
            spill_requests,
            reloaded,
            object_spills,
        }
    }

    fn finalize_spill_storage(
        ctx: &StackifyContext<'_>,
        spill: SpillSet<'_>,
        object_spills: &BitSet<ValueId>,
        slots: &mut SpillSlotPools,
        alloc: &mut StackifyAlloc,
        spill_obj: &SecondaryMap<ValueId, Option<StackObjId>>,
    ) {
        let scratch_slots = slots.scratch.take_slot_map();
        let mut spill_storage: SecondaryMap<ValueId, Option<SpillStorage>> = SecondaryMap::new();
        for value in ctx.func.dfg.value_ids() {
            let _ = &mut spill_storage[value];
        }

        for value in spill.stored_bitset().iter() {
            if ctx.remat_actions[value].is_some() {
                spill_storage[value] = Some(SpillStorage::Rematerialized);
            } else if must_use_object_storage(&ctx.scratch_barred, object_spills, value) {
                let obj = spill_obj[value].expect("object spill missing stack object id");
                spill_storage[value] = Some(SpillStorage::Object(obj));
            } else if let Some(slot) = scratch_slots[value] {
                debug_assert!(
                    !ctx.scratch_barred[slot as usize].contains(value),
                    "spilled value {} holds scratch slot {slot}, which bars it",
                    value.as_u32()
                );
                spill_storage[value] = Some(SpillStorage::Scratch(slot));
            } else {
                panic!(
                    "spilled value {} has no stable scratch slot or object storage",
                    value.as_u32()
                );
            }
        }

        alloc.spill_storage = spill_storage;
    }
}

const HOT_IMMEDIATE_DEFAULT_MIN_BLOCK_USES: u32 = 4;
pub(crate) const HOT_IMMEDIATE_SIZE_MIN_BLOCK_USES: u32 = 3;
const HOT_IMMEDIATE_DEFAULT_MIN_MATERIALIZATION_BYTES: usize = 17;
pub(crate) const HOT_IMMEDIATE_SIZE_MIN_MATERIALIZATION_BYTES: usize = 3;

fn compute_hot_stack_cached_immediates(
    func: &Function,
    value_aliases: &SecondaryMap<ValueId, Option<ValueId>>,
    min_block_uses: u32,
    min_materialization_bytes: usize,
) -> FxHashSet<I256> {
    let mut hot = FxHashSet::default();

    for block in func.layout.iter_block() {
        let mut counts: BTreeMap<I256, (u32, usize)> = BTreeMap::new();
        for inst in func.layout.iter_inst(block) {
            if func.dfg.is_phi(inst) {
                continue;
            }

            for value in operand_order_for_stackify(func, inst, value_aliases) {
                let Some(imm) = func.dfg.value_imm(value) else {
                    continue;
                };

                let entry = counts.entry(imm.as_i256()).or_insert((0, 0));
                entry.0 += 1;
                entry.1 = entry.1.max(immediate_materialization_code_len(imm));
            }
        }

        hot.extend(
            counts
                .into_iter()
                .filter(|(_, (uses, materialization_bytes))| {
                    *uses >= min_block_uses && *materialization_bytes >= min_materialization_bytes
                })
                .map(|(imm, _)| imm),
        );
    }

    hot
}

/// Aliases every immediate value to one canonical representative `ValueId` per distinct materialized
/// 256-bit word.
///
/// Numerically equal immediates are interchangeable on the EVM stack: equal `as_i256()` means an
/// identical stack word (types like `I8(-1)` and `I256(-1)` sign-extend to the same word), which the
/// materialization/rename machinery already relies on. Giving them one identity lets ordinary
/// `ValueId` equality subsume the semantic-equality checks scattered across stackify.
///
/// The representative is the class member with the cheapest materialization, then the lowest id —
/// deterministic, and the whole class is pushed via `Action::Push(rep's Immediate)`, so it never
/// materializes worse than its best member (equal-word plans can differ across immediate types,
/// e.g. `I256(-1)` gets a compact `NOT`-based plan that `I8(-1)` does not). The canonical `c` is
/// read first, and imm-ness is keyed off `c`, so pre-existing (e.g. GVN-provided) aliases are
/// respected and folded through.
///
/// Assumes `value_aliases` is already one-hop canonical (post `normalize_value_alias_map`). The pass
/// preserves that: each re-aliased `v` points to `rep`, which is the canonical of some value and is
/// itself never re-aliased (it is its own word's representative), hence self-canonical.
fn canonicalize_immediate_aliases(
    func: &Function,
    value_aliases: &mut SecondaryMap<ValueId, Option<ValueId>>,
) {
    let mut rep_of: BTreeMap<I256, (usize, ValueId)> = BTreeMap::new();
    for v in func.dfg.value_ids() {
        let c = value_aliases[v].unwrap_or(v);
        if let Some(imm) = func.dfg.value_imm(c) {
            let key = (immediate_materialization_code_len(imm), c);
            let entry = rep_of.entry(imm.as_i256()).or_insert(key);
            *entry = key.min(*entry);
        }
    }

    for v in func.dfg.value_ids() {
        let c = value_aliases[v].unwrap_or(v);
        if let Some(imm) = func.dfg.value_imm(c) {
            let (_, rep) = rep_of[&imm.as_i256()];
            if rep != c {
                value_aliases[v] = Some(rep);
            }
        }
    }
}

fn assign_spill_obj_ids(
    func: &Function,
    spill: SpillSet<'_>,
    remat_actions: &SecondaryMap<ValueId, Option<Action>>,
) -> SecondaryMap<ValueId, Option<StackObjId>> {
    let mut map: SecondaryMap<ValueId, Option<StackObjId>> = SecondaryMap::new();
    for v in func.dfg.value_ids() {
        let _ = &mut map[v];
    }

    let mut stored: Vec<ValueId> = spill.stored_bitset().iter().collect();
    stored.sort_unstable_by_key(|v| v.as_u32());

    let mut next_idx = 0usize;
    for v in stored {
        if remat_actions[v].is_some() {
            continue;
        }
        map[v] = Some(StackObjId::new(next_idx));
        next_idx += 1;
    }
    map
}

pub(super) fn compute_remat_actions(
    func: &Function,
    value_aliases: &SecondaryMap<ValueId, Option<ValueId>>,
) -> SecondaryMap<ValueId, Option<Action>> {
    let mut analysis = MemoryAccessAnalysis::new();
    let mut map: SecondaryMap<ValueId, Option<Action>> = SecondaryMap::new();
    for value in func.dfg.value_ids() {
        let canonical = value_aliases[value].unwrap_or(value);
        map[value] = analysis
            .exact_local_addr(func, canonical)
            .map(|exact| Action::MaterializeLocalAddr {
                alloca: exact.root_alloca,
                offset_bytes: exact.offset_bytes,
            })
            .or_else(|| {
                let inst = func.dfg.value_inst(canonical)?;
                let load = <&EvmCalldataLoad>::downcast(func.inst_set(), func.dfg.inst(inst))?;
                let offset = func.dfg.value_imm(*load.data_offset())?;
                let cost = immediate_materialization_plan(offset).cost();
                // An absolute arena reload commonly costs PUSH2 + MLOAD (4 bytes / 6 gas).
                // Match that reload budget, avoiding the spill store and reservation. Keep
                // the original Immediate: large or negative offsets must never truncate.
                // Calldata is immutable across calls, and out-of-range loads zero-pad.
                (cost.bytes <= 3 && cost.gas <= 3).then_some(Action::LoadCalldata(offset))
            });
    }
    map
}

#[cfg(test)]
mod tests {
    use crate::{
        domtree::DomTree,
        liveness::Liveness,
        stackalloc::{Action, StackifyBuilder, normalize_value_alias_map},
    };
    use cranelift_entity::SecondaryMap;
    use sonatina_ir::cfg::ControlFlowGraph;
    use sonatina_parser::parse_module;

    #[test]
    fn rematerialization_preserves_offset_width_and_excludes_mutable_reads() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"
func public %reads(v0.i256) -> i256 {
block0:
    v1.i256 = evm_calldata_load 65535.i256;
    v2.i256 = evm_calldata_load 65536.i256;
    v3.i256 = evm_calldata_load 18446744073709551648.i256;
    v4.i256 = evm_calldata_load -1.i256;
    v5.i256 = evm_calldata_load v0;
    v6.i256 = evm_gas;
    v7.i256 = mload 32.i256 i256;
    v8.i256 = evm_sload 32.i256;
    return v1;
}
"#,
        )
        .unwrap();
        let fref = parsed.module.funcs()[0];
        parsed.module.func_store.view(fref, |func| {
            let mut aliases = SecondaryMap::new();
            for value in func.dfg.value_ids() {
                aliases[value] = Some(value);
            }
            let actions = super::compute_remat_actions(func, &aliases);
            let value = parsed.debug.value(fref, "v1").unwrap();
            let Some(Action::LoadCalldata(offset)) = actions[value] else {
                panic!("short constant calldata read should rematerialize");
            };
            assert_eq!(offset.as_i256(), 65535.into());
            for name in ["v0", "v2", "v3", "v4", "v5", "v6", "v7", "v8"] {
                let value = parsed.debug.value(fref, name).unwrap();
                assert_eq!(actions[value], None, "{name} must not rematerialize");
            }
        });
    }

    #[test]
    fn normalize_value_aliases_keeps_cycle_paths_self_canonical() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256) -> i256 {
block0:
    v1.i256 = add v0 1.i256;
    v2.i256 = add v1 1.i256;
    v3.i256 = add v2 1.i256;
    return v3;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func_ref = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&f| parsed.module.ctx.func_sig(f, |sig| sig.name() == "f"))
            .expect("function exists");

        let v0 = parsed.debug.value(func_ref, "v0").expect("v0 exists");
        let v1 = parsed.debug.value(func_ref, "v1").expect("v1 exists");
        let v2 = parsed.debug.value(func_ref, "v2").expect("v2 exists");
        let v3 = parsed.debug.value(func_ref, "v3").expect("v3 exists");

        parsed.module.func_store.view(func_ref, |func| {
            let mut aliases: SecondaryMap<_, Option<_>> = SecondaryMap::new();
            for value in func.dfg.value_ids() {
                aliases[value] = Some(value);
            }

            // v0 -> v1 -> v2 -> v3 -> v2 (cycle entered from outside).
            aliases[v0] = Some(v1);
            aliases[v1] = Some(v2);
            aliases[v2] = Some(v3);
            aliases[v3] = Some(v2);

            normalize_value_alias_map(func, &mut aliases);

            for value in [v0, v1, v2, v3] {
                assert_eq!(aliases[value], Some(value));
            }
        });
    }

    #[test]
    fn hot_immediate_caching_preserves_repeated_large_immediate() {
        const BIG: &str =
            "21888242871839275222246405745257275088548364400416034343698204186575808495617";
        let src = format!(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256) -> i256 {{
block0:
    v1.i256 = add v0 {BIG}.i256;
    v2.i256 = add v1 {BIG}.i256;
    v3.i256 = add v2 {BIG}.i256;
    v4.i256 = add v3 {BIG}.i256;
    return v4;
}}
"#
        );

        let parsed = parse_module(&src).expect("module parses");
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.view(func_ref, |func| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let alloc = StackifyBuilder::new(func, &cfg, &dom, &liveness, 16)
                .with_hot_immediate_caching()
                .compute();

            let mut large_pushes = 0;
            let mut dup_count = 0;
            alloc.for_each_action(|action| match action {
                Action::Push(imm) if super::immediate_materialization_code_len(*imm) >= 17 => {
                    large_pushes += 1;
                }
                Action::StackDup(_) => {
                    dup_count += 1;
                }
                _ => {}
            });

            assert_eq!(large_pushes, 1);
            assert!(dup_count >= 3);
        });
    }

    #[test]
    fn hot_immediate_caching_can_preserve_repeated_push2_immediate() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256) -> i256 {
block0:
    v1.i256 = add v0 256.i256;
    v2.i256 = add v1 256.i256;
    v3.i256 = add v2 256.i256;
    v4.i256 = add v3 256.i256;
    return v4;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.view(func_ref, |func| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let alloc = StackifyBuilder::new(func, &cfg, &dom, &liveness, 16)
                .with_hot_immediate_caching()
                .with_hot_immediate_min_materialization_bytes(
                    super::HOT_IMMEDIATE_SIZE_MIN_MATERIALIZATION_BYTES,
                )
                .compute();

            let mut push2_count = 0;
            let mut dup_count = 0;
            alloc.for_each_action(|action| match action {
                Action::Push(imm) if super::immediate_materialization_code_len(*imm) == 3 => {
                    push2_count += 1;
                }
                Action::StackDup(_) => {
                    dup_count += 1;
                }
                _ => {}
            });

            assert_eq!(push2_count, 1);
            assert!(dup_count >= 3);
        });
    }

    #[test]
    fn canonicalize_immediates_collapses_numerically_equal_differently_typed_immediates() {
        use sonatina_ir::I256;

        // The DFG interns immediates per `Immediate` (type-inclusive), so `1.i8` and `1.i256` become
        // distinct ValueIds that share `as_i256() == 1`. Stage-1 canonicalization must collapse them
        // onto one representative, and the resulting map must stay one-hop canonical.
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256, v1.i8) -> i256 {
block0:
    v2.i8 = add v1 1.i8;
    v3.i256 = zext v2 i256;
    v4.i256 = add v0 1.i256;
    v5.i256 = add v3 v4;
    return v5;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.view(func_ref, |func| {
            // Collect the immediate value ids whose 256-bit word is 1, lowest id first.
            let mut imm_ones: Vec<_> = func
                .dfg
                .value_ids()
                .filter(|&v| {
                    func.dfg
                        .value_imm(v)
                        .is_some_and(|imm| imm.as_i256() == I256::one())
                })
                .collect();
            imm_ones.sort_unstable_by_key(|v| v.as_u32());

            // The scenario is real: two distinct ValueIds, equal word, different types.
            assert_eq!(
                imm_ones.len(),
                2,
                "parser should intern 1.i8 and 1.i256 as distinct value ids"
            );
            let ty0 = func.dfg.value_imm(imm_ones[0]).unwrap().ty();
            let ty1 = func.dfg.value_imm(imm_ones[1]).unwrap().ty();
            assert_ne!(ty0, ty1, "the two immediates must have different types");

            let mut aliases: SecondaryMap<_, Option<_>> = SecondaryMap::new();
            for value in func.dfg.value_ids() {
                aliases[value] = Some(value);
            }
            normalize_value_alias_map(func, &mut aliases);
            super::canonicalize_immediate_aliases(func, &mut aliases);

            // Both immediates canonicalize to the lowest-id representative.
            let rep = imm_ones[0];
            for &v in &imm_ones {
                assert_eq!(aliases[v].unwrap_or(v), rep);
            }

            // The map remains one-hop canonical: re-running normalization is a no-op.
            let before = aliases.clone();
            normalize_value_alias_map(func, &mut aliases);
            for value in func.dfg.value_ids() {
                assert_eq!(aliases[value], before[value]);
            }

            // compute() integrates the canonicalization end-to-end without panicking.
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);
            let mut dom = DomTree::new();
            dom.compute(&cfg);
            let _ = StackifyBuilder::new(func, &cfg, &dom, &liveness, 16).compute();
        });
    }

    #[test]
    fn hot_immediate_caching_can_use_size_mode_use_threshold() {
        const BIG: &str = "340282366920938463463374607431768211454";
        let src = format!(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256, v1.i256, v2.i256) -> i256 {{
block0:
    v3.i256 = and v0 {BIG}.i256;
    v4.i256 = and v1 {BIG}.i256;
    v5.i256 = and v2 {BIG}.i256;
    return v5;
}}
"#
        );

        let parsed = parse_module(&src).expect("module parses");
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.view(func_ref, |func| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let alloc = StackifyBuilder::new(func, &cfg, &dom, &liveness, 16)
                .with_hot_immediate_caching()
                .with_hot_immediate_min_block_uses(super::HOT_IMMEDIATE_SIZE_MIN_BLOCK_USES)
                .with_hot_immediate_min_materialization_bytes(
                    super::HOT_IMMEDIATE_SIZE_MIN_MATERIALIZATION_BYTES,
                )
                .compute();

            let mut large_pushes = 0;
            let mut dup_count = 0;
            alloc.for_each_action(|action| match action {
                Action::Push(imm) if super::immediate_materialization_code_len(*imm) >= 17 => {
                    large_pushes += 1;
                }
                Action::StackDup(_) => {
                    dup_count += 1;
                }
                _ => {}
            });

            assert_eq!(large_pushes, 1);
            assert!(dup_count >= 2);
        });
    }
}
