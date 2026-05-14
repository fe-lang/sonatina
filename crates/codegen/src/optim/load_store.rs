use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    AccessKind, AccessLoc, AddressSpaceId, ControlFlowGraph, Function, InstDowncast, InstId, Type,
    ValueId,
    bitset::BitSet,
    inst::{
        control_flow,
        data::{Alloca, Mload, Mstore},
        evm::{
            EvmCalldataLoad, EvmInvalid, EvmMstore8, EvmReturn, EvmRevert, EvmSelfDestruct,
            EvmSload, EvmSstore, EvmStop, EvmTload, EvmTstore,
        },
    },
};

use crate::analysis::memory_access::{
    AliasResult, BaseObject, KeyExpr, KeyedLocKey, LinearLocKey, LinearRangeKey,
    MemoryAccessAnalysis, RangeCoverage, TrackedLocKey, ValueKey,
};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct AvailState {
    exact: ExactAvailState,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct LiveState {
    exact_live: FxHashSet<TrackedLocKey>,
    exit_live: FxHashSet<TrackedLocKey>,
    range_live: FxHashSet<LinearRangeKey>,
    whole_space_live: BitSet<AddressSpaceId>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct AllocaVisibility {
    local_only: FxHashSet<InstId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct LinearBaseKey {
    space: AddressSpaceId,
    base: BaseObject,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct ExactAvailState {
    linear_disjoint: FxHashMap<LinearBaseKey, FxHashMap<LinearLocKey, ValueId>>,
    linear_ambiguous: FxHashMap<LinearBaseKey, FxHashMap<LinearLocKey, ValueId>>,
    keyed: FxHashMap<KeyedLocKey, ValueId>,
}

impl ExactAvailState {
    fn get(&self, key: &TrackedLocKey) -> Option<&ValueId> {
        match key {
            TrackedLocKey::Linear(key) => {
                let base = LinearBaseKey::new(key.space, key.base.clone());
                linear_map_for_base(self, &key.base)
                    .get(&base)
                    .and_then(|bucket| bucket.get(key))
            }
            TrackedLocKey::Keyed(key) => self.keyed.get(key),
        }
    }

    fn insert(&mut self, key: TrackedLocKey, value: ValueId) {
        match key {
            TrackedLocKey::Linear(key) => {
                let base = LinearBaseKey::new(key.space, key.base.clone());
                linear_map_for_base_mut(self, &key.base)
                    .entry(base)
                    .or_default()
                    .insert(key, value);
            }
            TrackedLocKey::Keyed(key) => {
                self.keyed.insert(key, value);
            }
        }
    }

    fn retain<F>(&mut self, mut keep: F)
    where
        F: FnMut(&TrackedLocKey, &mut ValueId) -> bool,
    {
        retain_linear_map(&mut self.linear_disjoint, &mut keep);
        retain_linear_map(&mut self.linear_ambiguous, &mut keep);
        self.keyed.retain(|key, value| {
            let tracked = TrackedLocKey::Keyed(key.clone());
            keep(&tracked, value)
        });
    }

    fn retain_no_alias_key(&mut self, analysis: &MemoryAccessAnalysis, key: &TrackedLocKey) {
        match key {
            TrackedLocKey::Linear(key) => {
                let tracked = TrackedLocKey::Linear(key.clone());
                self.retain_linear_candidates(key.space, &key.base, |other, _| {
                    analysis.alias(&TrackedLocKey::Linear(other.clone()), &tracked)
                        == AliasResult::NoAlias
                });
            }
            TrackedLocKey::Keyed(key) => {
                let tracked = TrackedLocKey::Keyed(key.clone());
                self.keyed.retain(|other, _| {
                    analysis.alias(&TrackedLocKey::Keyed(other.clone()), &tracked)
                        == AliasResult::NoAlias
                });
            }
        }
    }

    fn retain_no_alias_range(&mut self, analysis: &MemoryAccessAnalysis, range: &LinearRangeKey) {
        self.retain_linear_candidates(range.space, &range.base, |key, _| {
            !analysis.range_may_alias_key(range, &TrackedLocKey::Linear(key.clone()))
        });
    }

    fn retain_linear_candidates<F>(&mut self, space: AddressSpaceId, base: &BaseObject, mut keep: F)
    where
        F: FnMut(&LinearLocKey, &mut ValueId) -> bool,
    {
        match base {
            BaseObject::Alloca(_) | BaseObject::Malloc(_) | BaseObject::Global(_) => {
                let base_key = LinearBaseKey::new(space, base.clone());
                let remove_bucket = if let Some(bucket) = self.linear_disjoint.get_mut(&base_key) {
                    bucket.retain(|key, value| keep(key, value));
                    bucket.is_empty()
                } else {
                    false
                };
                if remove_bucket {
                    self.linear_disjoint.remove(&base_key);
                }
                retain_linear_map_in_space(&mut self.linear_ambiguous, space, &mut keep);
            }
            BaseObject::Arg(_) | BaseObject::Absolute(_) | BaseObject::Unknown(_) => {
                retain_linear_map_in_space(&mut self.linear_disjoint, space, &mut keep);
                retain_linear_map_in_space(&mut self.linear_ambiguous, space, &mut keep);
            }
        }
    }
}

impl LinearBaseKey {
    fn new(space: AddressSpaceId, base: BaseObject) -> Self {
        Self { space, base }
    }
}

fn linear_map_for_base<'a>(
    state: &'a ExactAvailState,
    base: &BaseObject,
) -> &'a FxHashMap<LinearBaseKey, FxHashMap<LinearLocKey, ValueId>> {
    match base {
        BaseObject::Alloca(_) | BaseObject::Malloc(_) | BaseObject::Global(_) => {
            &state.linear_disjoint
        }
        BaseObject::Arg(_) | BaseObject::Absolute(_) | BaseObject::Unknown(_) => {
            &state.linear_ambiguous
        }
    }
}

fn linear_map_for_base_mut<'a>(
    state: &'a mut ExactAvailState,
    base: &BaseObject,
) -> &'a mut FxHashMap<LinearBaseKey, FxHashMap<LinearLocKey, ValueId>> {
    match base {
        BaseObject::Alloca(_) | BaseObject::Malloc(_) | BaseObject::Global(_) => {
            &mut state.linear_disjoint
        }
        BaseObject::Arg(_) | BaseObject::Absolute(_) | BaseObject::Unknown(_) => {
            &mut state.linear_ambiguous
        }
    }
}

fn retain_linear_map<F>(
    map: &mut FxHashMap<LinearBaseKey, FxHashMap<LinearLocKey, ValueId>>,
    keep: &mut F,
) where
    F: FnMut(&TrackedLocKey, &mut ValueId) -> bool,
{
    map.retain(|_, bucket| {
        bucket.retain(|key, value| keep(&TrackedLocKey::Linear(key.clone()), value));
        !bucket.is_empty()
    });
}

fn retain_linear_map_in_space<F>(
    map: &mut FxHashMap<LinearBaseKey, FxHashMap<LinearLocKey, ValueId>>,
    space: AddressSpaceId,
    keep: &mut F,
) where
    F: FnMut(&LinearLocKey, &mut ValueId) -> bool,
{
    map.retain(|base, bucket| {
        if base.space == space {
            bucket.retain(|key, value| keep(key, value));
        }
        !bucket.is_empty()
    });
}

#[derive(Debug, Default)]
pub struct LoadStoreSolver;

impl LoadStoreSolver {
    pub fn new() -> Self {
        Self
    }

    pub fn run(&mut self, func: &mut Function, cfg: &mut ControlFlowGraph) -> bool {
        let mut changed_any = false;
        let mut analysis = MemoryAccessAnalysis::new();

        loop {
            cfg.compute(func);

            let mut changed = self.run_forward(func, cfg, &mut analysis);
            cfg.compute(func);
            changed |= self.run_backward(func, cfg, &mut analysis);

            if !changed {
                return changed_any;
            }

            changed_any = true;
        }
    }

    fn run_forward(
        &mut self,
        func: &mut Function,
        cfg: &ControlFlowGraph,
        analysis: &mut MemoryAccessAnalysis,
    ) -> bool {
        let reachable = cfg.reachable_blocks();
        let order: Vec<_> = cfg
            .post_order()
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect();

        let mut in_states = SecondaryMap::<sonatina_ir::BlockId, AvailState>::new();
        let mut out_states = SecondaryMap::<sonatina_ir::BlockId, AvailState>::new();
        let mut in_valid = SecondaryMap::<sonatina_ir::BlockId, bool>::new();
        let mut out_valid = SecondaryMap::<sonatina_ir::BlockId, bool>::new();
        let entry = func.layout.entry_block();
        let mut dataflow_changed = true;

        while dataflow_changed {
            dataflow_changed = false;
            for &block in &order {
                if !reachable[block] {
                    continue;
                }

                let maybe_in_state = if Some(block) == entry {
                    Some(AvailState::default())
                } else {
                    let pred_states: Vec<_> = cfg
                        .preds_of(block)
                        .copied()
                        .filter(|pred| reachable[*pred])
                        .filter(|pred| out_valid[*pred])
                        .map(|pred| out_states[pred].clone())
                        .collect();
                    (!pred_states.is_empty()).then(|| meet_forward(pred_states.into_iter()))
                };

                let Some(in_state) = maybe_in_state else {
                    if in_valid[block] {
                        in_valid[block] = false;
                        dataflow_changed = true;
                    }
                    if out_valid[block] {
                        out_valid[block] = false;
                        dataflow_changed = true;
                    }
                    continue;
                };

                if !in_valid[block] || in_states[block] != in_state {
                    in_states[block] = in_state.clone();
                    in_valid[block] = true;
                    dataflow_changed = true;
                }

                let mut state = in_state;
                let insts: Vec<_> = func.layout.iter_inst(block).collect();
                for inst in insts {
                    if !func.layout.is_inst_inserted(inst) {
                        continue;
                    }
                    transfer_forward(func, inst, analysis, &mut state, false);
                }

                if !out_valid[block] || state != out_states[block] {
                    out_states[block] = state;
                    out_valid[block] = true;
                    dataflow_changed = true;
                }
            }
        }

        let mut changed = false;
        for &block in &order {
            if !reachable[block] || !in_valid[block] {
                continue;
            }

            let mut state = in_states[block].clone();
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                if transfer_forward(func, inst, analysis, &mut state, true) {
                    changed = true;
                }
            }
        }

        changed
    }

    fn run_backward(
        &mut self,
        func: &mut Function,
        cfg: &ControlFlowGraph,
        analysis: &mut MemoryAccessAnalysis,
    ) -> bool {
        let reachable = cfg.reachable_blocks();
        let committing_exit_reachable = blocks_reaching_committing_exit(func, cfg, &reachable);
        let order: Vec<_> = cfg.post_order().collect();
        func.rebuild_users();
        analysis.clear();
        let alloca_visibility = collect_alloca_visibility(func, analysis);

        let mut in_states = SecondaryMap::<sonatina_ir::BlockId, LiveState>::new();
        let mut out_states = SecondaryMap::<sonatina_ir::BlockId, LiveState>::new();
        let mut dataflow_changed = true;

        while dataflow_changed {
            dataflow_changed = false;
            for &block in &order {
                if !reachable[block] {
                    continue;
                }

                let out_state = meet_live(
                    cfg.succs_of(block)
                        .copied()
                        .filter(|succ| reachable[*succ])
                        .map(|succ| (in_states[succ].clone(), committing_exit_reachable[succ])),
                );
                if out_state != out_states[block] {
                    out_states[block] = out_state.clone();
                    dataflow_changed = true;
                }

                let mut live = out_state;
                let insts: Vec<_> = func.layout.iter_inst(block).collect();
                for inst in insts.into_iter().rev() {
                    if !func.layout.is_inst_inserted(inst) {
                        continue;
                    }
                    transfer_backward(
                        func,
                        inst,
                        analysis,
                        &mut live,
                        committing_exit_reachable[block],
                        &alloca_visibility,
                        false,
                    );
                }

                if live != in_states[block] {
                    in_states[block] = live;
                    dataflow_changed = true;
                }
            }
        }

        let mut changed = false;
        for &block in &order {
            if !reachable[block] {
                continue;
            }

            let mut live = out_states[block].clone();
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts.into_iter().rev() {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                if transfer_backward(
                    func,
                    inst,
                    analysis,
                    &mut live,
                    committing_exit_reachable[block],
                    &alloca_visibility,
                    true,
                ) {
                    changed = true;
                }
            }
        }

        changed
    }
}

fn meet_forward(states: impl Iterator<Item = AvailState>) -> AvailState {
    let states: Vec<_> = states.collect();
    let Some(mut out) = states.first().cloned() else {
        return AvailState::default();
    };

    out.exact.retain(|loc, value| {
        states[1..]
            .iter()
            .all(|state| state.exact.get(loc).copied() == Some(*value))
    });
    out
}

fn meet_live(states: impl Iterator<Item = (LiveState, bool)>) -> LiveState {
    let mut out = LiveState::default();
    let mut exit_states = Vec::new();

    for (state, committing_exit_reachable) in states {
        out.whole_space_live.union_with(&state.whole_space_live);
        out.exact_live.extend(state.exact_live);
        out.range_live.extend(state.range_live);
        if committing_exit_reachable {
            exit_states.push(state.exit_live);
        }
    }

    let Some(mut exit_live) = exit_states.first().cloned() else {
        return out;
    };
    exit_live.retain(|key| exit_states[1..].iter().all(|state| state.contains(key)));
    out.exit_live = exit_live;

    out
}

fn collect_alloca_visibility(
    func: &Function,
    analysis: &mut MemoryAccessAnalysis,
) -> AllocaVisibility {
    let mut local_only = FxHashSet::default();

    for block in func.layout.iter_block() {
        for inst in func.layout.iter_inst(block) {
            if <&Alloca as InstDowncast>::downcast(func.inst_set(), func.dfg.inst(inst)).is_some()
                && let Some(root) = func.dfg.inst_result(inst)
                && alloca_stays_local(func, inst, root, analysis)
            {
                local_only.insert(inst);
            }
        }
    }

    AllocaVisibility { local_only }
}

fn alloca_stays_local(
    func: &Function,
    root_alloca: InstId,
    root: ValueId,
    analysis: &mut MemoryAccessAnalysis,
) -> bool {
    let mut seen = FxHashSet::default();
    let mut worklist = vec![root];

    while let Some(value) = worklist.pop() {
        if !seen.insert(value) {
            continue;
        }

        for &user in func.dfg.users(value) {
            if !func.layout.is_inst_inserted(user) {
                continue;
            }
            if let Some(result) = transparent_local_addr_result(func, root_alloca, user, analysis) {
                worklist.push(result);
            } else if !uses_value_only_as_local_memory_addr(
                func,
                root_alloca,
                user,
                value,
                analysis,
            ) {
                return false;
            }
        }
    }

    true
}

fn transparent_local_addr_result(
    func: &Function,
    root_alloca: InstId,
    inst: InstId,
    analysis: &mut MemoryAccessAnalysis,
) -> Option<ValueId> {
    let [result] = func.dfg.try_inst_results(inst)? else {
        return None;
    };
    let result = *result;
    let exact = analysis.exact_local_addr(func, result)?;
    (exact.root_alloca == root_alloca).then_some(result)
}

fn uses_value_only_as_local_memory_addr(
    func: &Function,
    root_alloca: InstId,
    inst: InstId,
    value: ValueId,
    analysis: &mut MemoryAccessAnalysis,
) -> bool {
    let mut use_count = 0;
    func.dfg.inst(inst).for_each_value(&mut |operand| {
        use_count += usize::from(operand == value);
    });
    let allowed = func
        .dfg
        .effects(inst)
        .accesses
        .iter()
        .filter(|access| access_uses_local_alloca_addr(func, root_alloca, access, value, analysis))
        .count();
    use_count == allowed
}

fn access_uses_local_alloca_addr(
    func: &Function,
    root_alloca: InstId,
    access: &sonatina_ir::MemoryAccess,
    value: ValueId,
    analysis: &mut MemoryAccessAnalysis,
) -> bool {
    if access.space != func.ctx().address_spaces().default_space() {
        return false;
    }

    match access.loc {
        AccessLoc::LinearExact { addr, .. } if addr == value => {
            matches!(
                analysis.trackable_exact_loc(func, access),
                Some(TrackedLocKey::Linear(key)) if key.base == BaseObject::Alloca(root_alloca)
            )
        }
        AccessLoc::LinearRange { addr, len } if addr == value && len != value => {
            matches!(
                analysis.trackable_linear_range(func, access),
                Some(range) if range.base == BaseObject::Alloca(root_alloca)
            )
        }
        _ => false,
    }
}

fn transfer_forward(
    func: &mut Function,
    inst: InstId,
    analysis: &mut MemoryAccessAnalysis,
    state: &mut AvailState,
    rewrite: bool,
) -> bool {
    prune_dead_avail_state(func, state);
    let effects = func.dfg.effects(inst);

    if let Some(key) = forwardable_read_key(func, inst, analysis, &effects) {
        if let Some(&known) = state.exact.get(&key) {
            if rewrite {
                let result = func
                    .dfg
                    .inst_result(inst)
                    .expect("forwardable reads must produce a result");
                func.dfg.change_to_alias(result, known);
                remove_inst(func, inst);
                analysis.clear();
                return true;
            }
            return false;
        }

        let result = func
            .dfg
            .inst_result(inst)
            .expect("forwardable reads must produce a result");
        state.exact.insert(key, result);
    }

    for access in effects
        .accesses
        .iter()
        .filter(|access| access.kind == AccessKind::Write && !access.must_happen)
    {
        kill_aliasing_access(func, state, analysis, access);
    }

    for access in effects
        .accesses
        .iter()
        .filter(|access| access.kind == AccessKind::Write && access.must_happen)
    {
        let Some(key) = analysis.trackable_exact_loc(func, access) else {
            kill_aliasing_access(func, state, analysis, access);
            continue;
        };

        let Some(stored_value) = store_value_of_inst(func, inst, &key) else {
            kill_aliasing_key(state, analysis, &key);
            continue;
        };

        if state.exact.get(&key) == Some(&stored_value) && store_is_removable(func, inst) {
            if rewrite {
                remove_inst(func, inst);
                analysis.clear();
                return true;
            }
            return false;
        }

        kill_aliasing_key(state, analysis, &key);
        state.exact.insert(key, stored_value);
    }

    false
}

fn transfer_backward(
    func: &mut Function,
    inst: InstId,
    analysis: &mut MemoryAccessAnalysis,
    live: &mut LiveState,
    committing_exit_reachable: bool,
    alloca_visibility: &AllocaVisibility,
    rewrite: bool,
) -> bool {
    prune_dead_live_state(func, live);
    let effects = func.dfg.effects(inst);

    for access in effects.accesses.iter().rev() {
        match access.kind {
            AccessKind::Read => {
                if let Some(key) = analysis.trackable_exact_loc(func, access) {
                    live.exact_live.insert(key);
                } else if let Some(range) = analysis.trackable_linear_range(func, access) {
                    live.range_live.insert(range);
                } else {
                    live.whole_space_live.insert(access.space);
                }
            }
            AccessKind::Write => {
                let Some(key) = analysis.trackable_exact_loc(func, access) else {
                    live.whole_space_live.insert(access.space);
                    continue;
                };

                let has_whole_space_live =
                    whole_space_liveness_may_observe_key(func, live, &key, alloca_visibility);
                let has_exact_live = has_may_alias_live(&live.exact_live, &key, analysis);
                let has_range_live = has_may_alias_live_range(&live.range_live, &key, analysis);
                let live_at_exit = committing_exit_reachable
                    && write_visible_at_committing_exit(func, &key)
                    && !has_must_alias_live(&live.exit_live, &key, analysis);
                let dead =
                    !has_whole_space_live && !has_exact_live && !has_range_live && !live_at_exit;

                if dead && store_is_removable(func, inst) {
                    if rewrite {
                        remove_inst(func, inst);
                        analysis.clear();
                        return true;
                    }
                    return false;
                }

                kill_must_alias_live(&mut live.exact_live, &key, analysis);
                discharge_live_ranges(&mut live.range_live, &key, analysis);
                if live_at_exit {
                    kill_must_alias_live(&mut live.exit_live, &key, analysis);
                    live.exit_live.insert(key);
                }
            }
        }
    }

    false
}

fn kill_aliasing_access(
    func: &Function,
    state: &mut AvailState,
    analysis: &mut MemoryAccessAnalysis,
    access: &sonatina_ir::MemoryAccess,
) {
    if let Some(range) = analysis.trackable_linear_range(func, access) {
        state.exact.retain_no_alias_range(analysis, &range);
        return;
    }
    if let Some(key) = analysis.trackable_exact_loc(func, access) {
        state.exact.retain_no_alias_key(analysis, &key);
        return;
    }

    state
        .exact
        .retain(|key, _| !analysis.access_may_alias_key(func, access, key));
}

fn kill_aliasing_key(state: &mut AvailState, analysis: &MemoryAccessAnalysis, key: &TrackedLocKey) {
    state.exact.retain_no_alias_key(analysis, key);
}

fn prune_dead_avail_state(func: &Function, state: &mut AvailState) {
    state
        .exact
        .retain(|key, value| func.dfg.has_value(*value) && tracked_key_is_live(func, key));
}

fn prune_dead_live_state(func: &Function, live: &mut LiveState) {
    live.exact_live.retain(|key| tracked_key_is_live(func, key));
    live.exit_live.retain(|key| tracked_key_is_live(func, key));
    live.range_live
        .retain(|range| linear_range_is_live(func, range));
}

fn tracked_key_is_live(func: &Function, key: &TrackedLocKey) -> bool {
    match key {
        TrackedLocKey::Linear(key) => base_object_is_live(func, &key.base),
        TrackedLocKey::Keyed(key) => value_key_is_live(func, &key.key),
    }
}

fn linear_range_is_live(func: &Function, range: &LinearRangeKey) -> bool {
    base_object_is_live(func, &range.base)
}

fn base_object_is_live(func: &Function, base: &BaseObject) -> bool {
    match base {
        BaseObject::Alloca(inst) | BaseObject::Malloc(inst) => func.dfg.has_inst(*inst),
        BaseObject::Arg(value) | BaseObject::Unknown(value) => func.dfg.has_value(*value),
        BaseObject::Global(_) | BaseObject::Absolute(_) => true,
    }
}

fn value_key_is_live(func: &Function, key: &ValueKey) -> bool {
    match key {
        ValueKey::Imm(_) => true,
        ValueKey::Arg(value) => func.dfg.has_value(*value),
        ValueKey::Expr(expr) => match expr.as_ref() {
            KeyExpr::Unary { arg, .. } | KeyExpr::Cast { arg, .. } => value_key_is_live(func, arg),
            KeyExpr::Binary { lhs, rhs, .. } => {
                value_key_is_live(func, lhs) && value_key_is_live(func, rhs)
            }
        },
    }
}

fn has_may_alias_live(
    live: &FxHashSet<TrackedLocKey>,
    key: &TrackedLocKey,
    analysis: &MemoryAccessAnalysis,
) -> bool {
    live.iter()
        .any(|other| analysis.alias(other, key) != AliasResult::NoAlias)
}

fn has_must_alias_live(
    live: &FxHashSet<TrackedLocKey>,
    key: &TrackedLocKey,
    analysis: &MemoryAccessAnalysis,
) -> bool {
    live.iter()
        .any(|other| analysis.alias(other, key) == AliasResult::MustAlias)
}

fn has_may_alias_live_range(
    live: &FxHashSet<LinearRangeKey>,
    key: &TrackedLocKey,
    analysis: &MemoryAccessAnalysis,
) -> bool {
    live.iter()
        .any(|range| analysis.range_may_alias_key(range, key))
}

fn whole_space_liveness_may_observe_key(
    func: &Function,
    live: &LiveState,
    key: &TrackedLocKey,
    alloca_visibility: &AllocaVisibility,
) -> bool {
    let space = match key {
        TrackedLocKey::Linear(key) => key.space,
        TrackedLocKey::Keyed(key) => key.space,
    };
    if !live.whole_space_live.contains(space) {
        return false;
    }

    !matches!(
        key,
        TrackedLocKey::Linear(LinearLocKey {
            space,
            base: BaseObject::Alloca(alloca),
            ..
        }) if *space == func.ctx().address_spaces().default_space()
            && alloca_visibility.local_only.contains(alloca)
    )
}

fn kill_must_alias_live(
    live: &mut FxHashSet<TrackedLocKey>,
    key: &TrackedLocKey,
    analysis: &MemoryAccessAnalysis,
) {
    live.retain(|other| analysis.alias(other, key) != AliasResult::MustAlias);
}

fn discharge_live_ranges(
    live: &mut FxHashSet<LinearRangeKey>,
    key: &TrackedLocKey,
    analysis: &MemoryAccessAnalysis,
) {
    let TrackedLocKey::Linear(key) = key else {
        return;
    };

    let ranges: Vec<_> = live.drain().collect();
    for range in ranges {
        match analysis.exact_write_coverage(&range, key) {
            RangeCoverage::NoOverlap | RangeCoverage::Unknown => {
                live.insert(range);
            }
            RangeCoverage::FullyCovered => {}
            RangeCoverage::PartiallyCovered { before, after } => {
                if let Some(before) = before {
                    live.insert(before);
                }
                if let Some(after) = after {
                    live.insert(after);
                }
            }
        }
    }
}

fn store_value_of_inst(func: &Function, inst: InstId, key: &TrackedLocKey) -> Option<ValueId> {
    let inst_data = func.dfg.inst(inst);
    let is = func.inst_set();

    if let Some(store) = <&Mstore as InstDowncast>::downcast(is, inst_data) {
        return forwardable_store_value(func, *store.value(), key);
    }
    if let Some(store) = <&EvmMstore8 as InstDowncast>::downcast(is, inst_data) {
        return forwardable_store_value(func, *store.val(), key);
    }
    if let Some(store) = <&EvmSstore as InstDowncast>::downcast(is, inst_data) {
        return forwardable_store_value(func, *store.val(), key);
    }
    if let Some(store) = <&EvmTstore as InstDowncast>::downcast(is, inst_data) {
        return forwardable_store_value(func, *store.val(), key);
    }

    None
}

fn forwardable_store_value(
    func: &Function,
    value: ValueId,
    key: &TrackedLocKey,
) -> Option<ValueId> {
    if !func.dfg.has_value(value) {
        return None;
    }
    if func.dfg.value_ty(value) != expected_loaded_value_type(key) {
        return None;
    }

    Some(value)
}

fn expected_loaded_value_type(key: &TrackedLocKey) -> Type {
    match key {
        TrackedLocKey::Linear(key) => key.ty,
        TrackedLocKey::Keyed(_) => Type::I256,
    }
}

fn forwardable_read_key(
    func: &Function,
    inst: InstId,
    analysis: &mut MemoryAccessAnalysis,
    effects: &sonatina_ir::InstEffects,
) -> Option<TrackedLocKey> {
    let inst_data = func.dfg.inst(inst);
    let is = func.inst_set();

    if <&Mload as InstDowncast>::downcast(is, inst_data).is_none()
        && <&EvmSload as InstDowncast>::downcast(is, inst_data).is_none()
        && <&EvmTload as InstDowncast>::downcast(is, inst_data).is_none()
        && <&EvmCalldataLoad as InstDowncast>::downcast(is, inst_data).is_none()
    {
        return None;
    }

    effects
        .accesses
        .iter()
        .find(|access| access.kind == AccessKind::Read && access.must_happen)
        .and_then(|access| analysis.trackable_exact_loc(func, access))
}

fn store_is_removable(func: &Function, inst: InstId) -> bool {
    let inst_data = func.dfg.inst(inst);
    let is = func.inst_set();

    <&Mstore as InstDowncast>::downcast(is, inst_data).is_some()
        || <&EvmMstore8 as InstDowncast>::downcast(is, inst_data).is_some()
        || <&EvmSstore as InstDowncast>::downcast(is, inst_data).is_some()
        || <&EvmTstore as InstDowncast>::downcast(is, inst_data).is_some()
}

fn blocks_reaching_committing_exit(
    func: &Function,
    cfg: &ControlFlowGraph,
    reachable: &SecondaryMap<sonatina_ir::BlockId, bool>,
) -> SecondaryMap<sonatina_ir::BlockId, bool> {
    let mut reaches_commit = SecondaryMap::new();
    let mut worklist = Vec::new();

    for &exit in &cfg.exits {
        if !reachable[exit] || !exit_commits_visible_writes(func, exit) {
            continue;
        }

        reaches_commit[exit] = true;
        worklist.push(exit);
    }

    while let Some(block) = worklist.pop() {
        for pred in cfg.preds_of(block).copied().filter(|pred| reachable[*pred]) {
            if reaches_commit[pred] {
                continue;
            }

            reaches_commit[pred] = true;
            worklist.push(pred);
        }
    }

    reaches_commit
}

fn exit_commits_visible_writes(func: &Function, block: sonatina_ir::BlockId) -> bool {
    let Some(term) = func.layout.last_inst_of(block) else {
        return false;
    };
    if !func.dfg.is_exit(term) {
        return false;
    }

    let inst = func.dfg.inst(term);
    let is = func.inst_set();

    if <&EvmRevert as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmInvalid as InstDowncast>::downcast(is, inst).is_some()
    {
        return false;
    }

    if <&control_flow::Unreachable as InstDowncast>::downcast(is, inst).is_some() {
        return preceding_terminal_call(func, term).is_some_and(|call| {
            func.ctx()
                .func_effects(call.callee())
                .is_committing_noreturn()
        });
    }

    if <&control_flow::Return as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmReturn as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmSelfDestruct as InstDowncast>::downcast(is, inst).is_some()
        || <&EvmStop as InstDowncast>::downcast(is, inst).is_some()
    {
        return true;
    }

    true
}

fn preceding_terminal_call(func: &Function, term: InstId) -> Option<&dyn control_flow::CallInfo> {
    let prev = func.layout.prev_inst_of(term)?;
    func.dfg.call_info(prev)
}

fn write_visible_at_committing_exit(func: &Function, key: &TrackedLocKey) -> bool {
    let default_space = func.ctx().address_spaces().default_space();
    match key {
        TrackedLocKey::Keyed(_) => true,
        TrackedLocKey::Linear(key) if key.space != default_space => true,
        TrackedLocKey::Linear(key) => !matches!(key.base, BaseObject::Alloca(_)),
    }
}

fn remove_inst(func: &mut Function, inst: InstId) {
    func.layout.remove_inst(inst);
    func.erase_inst(inst);
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::{
        Type,
        builder::test_util::*,
        inst::{
            control_flow::Return,
            data::{Alloca, Mload},
        },
        isa::Isa,
    };

    #[test]
    fn rewrite_ignores_deleted_available_values() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let ptr_ty = builder.ptr_type(Type::I256);
        let addr = builder.insert_inst_with(|| Alloca::new(is, Type::I256), ptr_ty);
        let dead_load = builder.insert_inst_with(|| Mload::new(is, addr, Type::I256), Type::I256);
        let live_load = builder.insert_inst_with(|| Mload::new(is, addr, Type::I256), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, live_load));
        builder.seal_all();

        let dead_inst = builder
            .func
            .dfg
            .value_inst(dead_load)
            .expect("dead load should come from an instruction");
        builder.func.layout.remove_inst(dead_inst);
        builder.func.erase_inst(dead_inst);

        let live_inst = builder
            .func
            .dfg
            .value_inst(live_load)
            .expect("live load should come from an instruction");
        let mut analysis = MemoryAccessAnalysis::new();
        let effects = builder.func.dfg.effects(live_inst);
        let key = forwardable_read_key(&builder.func, live_inst, &mut analysis, &effects)
            .expect("live load should be forwardable");

        let mut state = AvailState::default();
        state.exact.insert(key.clone(), dead_load);

        assert!(!transfer_forward(
            &mut builder.func,
            live_inst,
            &mut analysis,
            &mut state,
            true,
        ));
        assert!(builder.func.layout.is_inst_inserted(live_inst));
        assert_eq!(state.exact.get(&key), Some(&live_load));
    }
}
