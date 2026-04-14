use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    AccessKind, AddressSpaceId, ControlFlowGraph, Function, InstDowncast, InstId, Type, ValueId,
    bitset::BitSet,
    inst::{
        control_flow,
        data::{Mload, Mstore},
        evm::{
            EvmCalldataLoad, EvmInvalid, EvmMstore8, EvmReturn, EvmRevert, EvmSelfDestruct,
            EvmSload, EvmSstore, EvmStop, EvmTload, EvmTstore,
        },
    },
};

use crate::analysis::memory_access::{
    AliasResult, BaseObject, KeyExpr, LinearRangeKey, MemoryAccessAnalysis, RangeCoverage,
    TrackedLocKey, ValueKey,
};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct AvailState {
    exact: FxHashMap<TrackedLocKey, ValueId>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct LiveState {
    exact_live: FxHashSet<TrackedLocKey>,
    exit_live: FxHashSet<TrackedLocKey>,
    range_live: FxHashSet<LinearRangeKey>,
    whole_space_live: BitSet<AddressSpaceId>,
}

#[derive(Debug, Default)]
pub struct LoadStoreSolver;

impl LoadStoreSolver {
    pub fn new() -> Self {
        Self
    }

    pub fn run(&mut self, func: &mut Function, cfg: &mut ControlFlowGraph) -> bool {
        let mut changed_any = false;
        let analysis = MemoryAccessAnalysis::new();

        loop {
            cfg.compute(func);

            let mut changed = self.run_forward(func, cfg, &analysis);
            cfg.compute(func);
            changed |= self.run_backward(func, cfg, &analysis);

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
        analysis: &MemoryAccessAnalysis,
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
        analysis: &MemoryAccessAnalysis,
    ) -> bool {
        let reachable = cfg.reachable_blocks();
        let committing_exit_reachable = blocks_reaching_committing_exit(func, cfg, &reachable);
        let order: Vec<_> = cfg.post_order().collect();

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
            .all(|state| state.exact.get(loc) == Some(value))
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

fn transfer_forward(
    func: &mut Function,
    inst: InstId,
    analysis: &MemoryAccessAnalysis,
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
    analysis: &MemoryAccessAnalysis,
    live: &mut LiveState,
    committing_exit_reachable: bool,
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

                let has_whole_space_live = live.whole_space_live.contains(access.space);
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
    analysis: &MemoryAccessAnalysis,
    access: &sonatina_ir::MemoryAccess,
) {
    state
        .exact
        .retain(|key, _| !analysis.access_may_alias_key(func, access, key));
}

fn kill_aliasing_key(state: &mut AvailState, analysis: &MemoryAccessAnalysis, key: &TrackedLocKey) {
    state
        .exact
        .retain(|other, _| analysis.alias(other, key) == AliasResult::NoAlias);
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
    analysis: &MemoryAccessAnalysis,
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
        I256, Immediate, InstSetBase, Linkage, Signature, Type,
        builder::test_util::*,
        effects::FuncEffectSummary,
        inst::{
            arith::Add,
            control_flow::{Br, Jump, Return},
            data::{Alloca, Mload},
            evm::{
                EvmCalldataLoad, EvmCreate, EvmCreate2, EvmKeccak256, EvmMalloc, EvmReturn,
                EvmRevert, EvmSelfDestruct, EvmSload, EvmSstore, EvmStaticCall, EvmStop, EvmTload,
            },
        },
        ir_writer::FuncWriter,
        isa::Isa,
    };

    fn run_solver(func: &mut Function) -> bool {
        let mut cfg = ControlFlowGraph::default();
        LoadStoreSolver::new().run(func, &mut cfg)
    }

    fn count_insts<T>(func: &Function) -> usize
    where
        for<'a> &'a T: InstDowncast<'a>,
    {
        let is = func.inst_set();
        func.layout
            .iter_block()
            .flat_map(|block| func.layout.iter_inst(block))
            .filter(|&inst| <&T as InstDowncast>::downcast(is, func.dfg.inst(inst)).is_some())
            .count()
    }

    #[test]
    fn forwards_local_mload_from_prior_store() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let ptr_ty = builder.ptr_type(Type::I256);
        let addr = builder.insert_inst_with(|| Alloca::new(is, Type::I256), ptr_ty);
        let value = builder.make_imm_value(I256::from(7));
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, value, Type::I256));
        let loaded = builder.insert_inst_with(|| Mload::new(is, addr, Type::I256), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, loaded));
        builder.seal_all();

        assert!(run_solver(&mut builder.func));
        assert_eq!(count_insts::<Mload>(&builder.func), 0);

        let ret = builder
            .func
            .layout
            .last_inst_of(block)
            .and_then(|inst| builder.func.dfg.return_args(inst))
            .expect("return args");
        assert_eq!(
            builder.func.dfg.value_imm(ret[0]),
            Some(Immediate::I256(I256::from(7)))
        );
    }

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
        let analysis = MemoryAccessAnalysis::new();
        let effects = builder.func.dfg.effects(live_inst);
        let key = forwardable_read_key(&builder.func, live_inst, &analysis, &effects)
            .expect("live load should be forwardable");

        let mut state = AvailState::default();
        state.exact.insert(key.clone(), dead_load);

        assert!(!transfer_forward(
            &mut builder.func,
            live_inst,
            &analysis,
            &mut state,
            true,
        ));
        assert!(builder.func.layout.is_inst_inserted(live_inst));
        assert_eq!(state.exact.get(&key), Some(&live_load));
    }

    #[test]
    fn forwards_loop_invariant_load_with_initially_unsolved_backedge() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I1], Type::I256);
        let is = evm.inst_set();
        let carried = builder.declare_var(Type::I256);

        let entry = builder.append_block();
        let header = builder.append_block();
        let body = builder.append_block();
        let exit = builder.append_block();

        builder.switch_to_block(entry);
        let ptr_ty = builder.ptr_type(Type::I256);
        let addr = builder.insert_inst_with(|| Alloca::new(is, Type::I256), ptr_ty);
        let seven = builder.make_imm_value(I256::from(7));
        let zero = builder.make_imm_value(I256::from(0));
        let one = builder.make_imm_value(I256::from(1));
        let cond = builder.args()[0];
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, seven, Type::I256));
        builder.def_var(carried, zero);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));

        builder.switch_to_block(header);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, exit, body));

        builder.switch_to_block(body);
        let loop_load = builder.insert_inst_with(|| Mload::new(is, addr, Type::I256), Type::I256);
        let loop_sum = builder.insert_inst_with(|| Add::new(is, loop_load, one), Type::I256);
        builder.def_var(carried, loop_sum);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));

        builder.switch_to_block(exit);
        let result = builder.use_var(carried);
        builder.insert_inst_no_result_with(|| Return::new_single(is, result));
        builder.seal_all();

        assert!(run_solver(&mut builder.func));
        assert_eq!(count_insts::<Mload>(&builder.func), 0);

        let add_inst = builder
            .func
            .dfg
            .value_inst(loop_sum)
            .expect("loop sum should stay defined by an add");
        let add = <&Add as InstDowncast>::downcast(is, builder.func.dfg.inst(add_inst))
            .expect("loop use should stay as an add");
        assert_eq!(
            builder.func.dfg.value_imm(*add.lhs()),
            Some(Immediate::I256(I256::from(7)))
        );
        assert_eq!(
            builder.func.dfg.value_imm(*add.rhs()),
            Some(Immediate::I256(I256::from(1)))
        );
    }

    #[test]
    fn forwards_loop_invariant_sload_with_initially_unsolved_backedge() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I1, Type::I256], Type::I256);
        let is = evm.inst_set();
        let carried = builder.declare_var(Type::I256);

        let entry = builder.append_block();
        let header = builder.append_block();
        let body = builder.append_block();
        let exit = builder.append_block();

        builder.switch_to_block(entry);
        let cond = builder.args()[0];
        let base = builder.args()[1];
        let zero = builder.make_imm_value(I256::from(0));
        let one = builder.make_imm_value(I256::from(1));
        let seven = builder.make_imm_value(I256::from(7));
        let slot = builder.insert_inst_with(|| Add::new(is, base, one), Type::I256);
        builder.insert_inst_no_result_with(|| EvmSstore::new(is, slot, seven));
        builder.def_var(carried, zero);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));

        builder.switch_to_block(header);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, exit, body));

        builder.switch_to_block(body);
        let loop_load = builder.insert_inst_with(|| EvmSload::new(is, slot), Type::I256);
        let loop_sum = builder.insert_inst_with(|| Add::new(is, loop_load, one), Type::I256);
        builder.def_var(carried, loop_sum);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));

        builder.switch_to_block(exit);
        let result = builder.use_var(carried);
        builder.insert_inst_no_result_with(|| Return::new_single(is, result));
        builder.seal_all();

        assert!(run_solver(&mut builder.func));
        assert_eq!(count_insts::<EvmSload>(&builder.func), 0);

        let add_inst = builder
            .func
            .dfg
            .value_inst(loop_sum)
            .expect("loop sum should stay defined by an add");
        let add = <&Add as InstDowncast>::downcast(is, builder.func.dfg.inst(add_inst))
            .expect("loop use should stay as an add");
        assert_eq!(
            builder.func.dfg.value_imm(*add.lhs()),
            Some(Immediate::I256(I256::from(7)))
        );
        assert_eq!(
            builder.func.dfg.value_imm(*add.rhs()),
            Some(Immediate::I256(I256::from(1)))
        );
    }

    #[test]
    fn loop_backedge_write_prevents_header_forwarding() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();
        let done_var = builder.declare_var(Type::I1);

        let entry = builder.append_block();
        let header = builder.append_block();
        let body = builder.append_block();
        let exit = builder.append_block();

        builder.switch_to_block(entry);
        let ptr_ty = builder.ptr_type(Type::I256);
        let addr = builder.insert_inst_with(|| Alloca::new(is, Type::I256), ptr_ty);
        let seven = builder.make_imm_value(I256::from(7));
        let eight = builder.make_imm_value(I256::from(8));
        let one = builder.make_imm_value(I256::from(1));
        let done_false = builder.make_imm_value(false);
        let done_true = builder.make_imm_value(true);
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, seven, Type::I256));
        builder.def_var(done_var, done_false);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));

        builder.switch_to_block(header);
        let cond = builder.use_var(done_var);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, exit, body));

        builder.switch_to_block(body);
        let loop_load = builder.insert_inst_with(|| Mload::new(is, addr, Type::I256), Type::I256);
        builder.insert_inst_with(|| Add::new(is, loop_load, one), Type::I256);
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, eight, Type::I256));
        builder.def_var(done_var, done_true);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));

        builder.switch_to_block(exit);
        let exit_load = builder.insert_inst_with(|| Mload::new(is, addr, Type::I256), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, exit_load));
        builder.seal_all();

        run_solver(&mut builder.func);
        let dumped = FuncWriter::new(builder.func_ref, &builder.func).dump_string();
        assert_eq!(
            count_insts::<Mload>(&builder.func),
            2,
            "both loop and exit loads must remain when the backedge disagrees:\n{dumped}"
        );
    }

    #[test]
    fn join_with_disagreeing_predecessor_values_does_not_forward() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I1], Type::I256);
        let is = evm.inst_set();

        let entry = builder.append_block();
        let left = builder.append_block();
        let right = builder.append_block();
        let join = builder.append_block();

        builder.switch_to_block(entry);
        let ptr_ty = builder.ptr_type(Type::I256);
        let addr = builder.insert_inst_with(|| Alloca::new(is, Type::I256), ptr_ty);
        let seven = builder.make_imm_value(I256::from(7));
        let eight = builder.make_imm_value(I256::from(8));
        let cond = builder.args()[0];
        builder.insert_inst_no_result_with(|| Br::new(is, cond, left, right));

        builder.switch_to_block(left);
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, seven, Type::I256));
        builder.insert_inst_no_result_with(|| Jump::new(is, join));

        builder.switch_to_block(right);
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, eight, Type::I256));
        builder.insert_inst_no_result_with(|| Jump::new(is, join));

        builder.switch_to_block(join);
        let load = builder.insert_inst_with(|| Mload::new(is, addr, Type::I256), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, load));
        builder.seal_all();

        assert!(!run_solver(&mut builder.func));
        assert_eq!(count_insts::<Mload>(&builder.func), 1);
    }

    #[test]
    fn removes_overwritten_local_store() {
        let mb = test_module_builder();
        let word_ptr_ty = mb.ptr_type(Type::I256);
        let (evm, mut builder) = test_func_builder(&mb, &[], word_ptr_ty);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let ptr_ty = builder.ptr_type(Type::I256);
        let addr = builder.insert_inst_with(|| Alloca::new(is, Type::I256), ptr_ty);
        let v1 = builder.make_imm_value(I256::from(1));
        let v2 = builder.make_imm_value(I256::from(2));
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, v1, Type::I256));
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, v2, Type::I256));
        let loaded = builder.insert_inst_with(|| Mload::new(is, addr, word_ptr_ty), word_ptr_ty);
        builder.insert_inst_no_result_with(|| Return::new_single(is, loaded));
        builder.seal_all();

        assert!(run_solver(&mut builder.func));
        assert_eq!(count_insts::<Mstore>(&builder.func), 1);
        assert_eq!(count_insts::<Mload>(&builder.func), 1);
    }

    #[test]
    fn does_not_forward_keccak_result_from_memory_contents() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let ptr_ty = builder.ptr_type(Type::I256);
        let addr = builder.insert_inst_with(|| Alloca::new(is, Type::I256), ptr_ty);
        let seven = builder.make_imm_value(I256::from(7));
        let len = builder.make_imm_value(I256::from(32));
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, seven, Type::I256));
        let hash = builder.insert_inst_with(|| EvmKeccak256::new(is, addr, len), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, hash));
        builder.seal_all();

        assert!(!run_solver(&mut builder.func));
        assert_eq!(count_insts::<Mstore>(&builder.func), 1);
        assert_eq!(count_insts::<EvmKeccak256>(&builder.func), 1);
    }

    #[test]
    fn storage_write_survives_staticcall_read_barrier_while_sload_forwards() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let ptr_ty = builder.ptr_type(Type::I256);
        let scratch = builder.insert_inst_with(|| Alloca::new(is, Type::I256), ptr_ty);
        let zero = builder.make_imm_value(I256::from(0));
        let one = builder.make_imm_value(I256::from(1));

        builder.insert_inst_no_result_with(|| EvmSstore::new(is, one, one));
        let _ok = builder.insert_inst_with(
            || EvmStaticCall::new(is, zero, zero, scratch, zero, scratch, zero),
            Type::I1,
        );
        let load = builder.insert_inst_with(|| EvmSload::new(is, one), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, load));
        builder.seal_all();

        assert!(run_solver(&mut builder.func));
        assert_eq!(count_insts::<EvmSstore>(&builder.func), 1);
        assert_eq!(count_insts::<EvmSload>(&builder.func), 0);
    }

    #[test]
    fn storage_barrier_does_not_kill_memory_fact() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let ptr_ty = builder.ptr_type(Type::I256);
        let addr = builder.insert_inst_with(|| Alloca::new(is, Type::I256), ptr_ty);
        let seven = builder.make_imm_value(I256::from(7));
        let slot = builder.make_imm_value(I256::from(1));
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, seven, Type::I256));
        builder.insert_inst_no_result_with(|| EvmSstore::new(is, slot, seven));
        let load = builder.insert_inst_with(|| Mload::new(is, addr, Type::I256), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, load));
        builder.seal_all();

        assert!(run_solver(&mut builder.func));
        assert_eq!(count_insts::<Mload>(&builder.func), 0);
    }

    #[test]
    fn mload_does_not_forward_across_malloc_free_ptr_barrier() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let addr = builder.make_imm_value(I256::from(64));
        let size = builder.make_imm_value(I256::from(32));
        let ptr_ty = builder.ptr_type(Type::I8);
        let _first = builder.insert_inst_with(|| Mload::new(is, addr, Type::I256), Type::I256);
        let _malloc = builder.insert_inst_with(|| EvmMalloc::new(is, size), ptr_ty);
        let second = builder.insert_inst_with(|| Mload::new(is, addr, Type::I256), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, second));
        builder.seal_all();

        assert!(!run_solver(&mut builder.func));
        assert_eq!(count_insts::<Mload>(&builder.func), 2);
    }

    #[test]
    fn malloc_read_keeps_prior_free_ptr_store_live() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let addr = builder.make_imm_value(I256::from(64));
        let size = builder.make_imm_value(I256::from(32));
        let ptr_ty = builder.ptr_type(Type::I8);
        let v1 = builder.make_imm_value(I256::from(7));
        let v2 = builder.make_imm_value(I256::from(8));
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, v1, Type::I256));
        let _malloc = builder.insert_inst_with(|| EvmMalloc::new(is, size), ptr_ty);
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, v2, Type::I256));
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        assert!(!run_solver(&mut builder.func));
        assert_eq!(count_insts::<Mstore>(&builder.func), 2);
    }

    #[test]
    fn malloc_free_ptr_barrier_does_not_kill_unrelated_malloc_fact() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let size = builder.make_imm_value(I256::from(32));
        let value = builder.make_imm_value(I256::from(7));
        let ptr_ty = builder.ptr_type(Type::I8);
        let addr = builder.insert_inst_with(|| EvmMalloc::new(is, size), ptr_ty);
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, value, Type::I256));
        let _malloc = builder.insert_inst_with(|| EvmMalloc::new(is, size), ptr_ty);
        let loaded = builder.insert_inst_with(|| Mload::new(is, addr, Type::I256), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, loaded));
        builder.seal_all();

        assert!(run_solver(&mut builder.func));
        assert_eq!(count_insts::<Mload>(&builder.func), 0);

        let ret = builder
            .func
            .layout
            .last_inst_of(block)
            .and_then(|inst| builder.func.dfg.return_args(inst))
            .expect("return args");
        assert_eq!(
            builder.func.dfg.value_imm(ret[0]),
            Some(Immediate::I256(I256::from(7)))
        );
    }

    #[test]
    fn sload_does_not_forward_across_create_barrier() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let ptr_ty = builder.ptr_type(Type::I256);
        let scratch = builder.insert_inst_with(|| Alloca::new(is, Type::I256), ptr_ty);
        let zero = builder.make_imm_value(I256::from(0));
        let one = builder.make_imm_value(I256::from(1));

        builder.insert_inst_no_result_with(|| EvmSstore::new(is, one, one));
        let _created =
            builder.insert_inst_with(|| EvmCreate::new(is, zero, scratch, zero), Type::I256);
        let load = builder.insert_inst_with(|| EvmSload::new(is, one), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, load));
        builder.seal_all();

        assert!(!run_solver(&mut builder.func));
        assert_eq!(count_insts::<EvmSstore>(&builder.func), 1);
        assert_eq!(count_insts::<EvmSload>(&builder.func), 1);
    }

    #[test]
    fn create_barrier_keeps_overwritten_sstore_live() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let ptr_ty = builder.ptr_type(Type::I256);
        let scratch = builder.insert_inst_with(|| Alloca::new(is, Type::I256), ptr_ty);
        let zero = builder.make_imm_value(I256::from(0));
        let slot = builder.make_imm_value(I256::from(1));
        let v1 = builder.make_imm_value(I256::from(7));
        let v2 = builder.make_imm_value(I256::from(8));

        builder.insert_inst_no_result_with(|| EvmSstore::new(is, slot, v1));
        let _created =
            builder.insert_inst_with(|| EvmCreate::new(is, zero, scratch, zero), Type::I256);
        builder.insert_inst_no_result_with(|| EvmSstore::new(is, slot, v2));
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        assert!(!run_solver(&mut builder.func));
        assert_eq!(count_insts::<EvmSstore>(&builder.func), 2);
    }

    #[test]
    fn tload_does_not_forward_across_create2_barrier() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let ptr_ty = builder.ptr_type(Type::I256);
        let scratch = builder.insert_inst_with(|| Alloca::new(is, Type::I256), ptr_ty);
        let zero = builder.make_imm_value(I256::from(0));
        let one = builder.make_imm_value(I256::from(1));

        builder.insert_inst_no_result_with(|| EvmTstore::new(is, one, one));
        let _created = builder.insert_inst_with(
            || EvmCreate2::new(is, zero, scratch, zero, zero),
            Type::I256,
        );
        let load = builder.insert_inst_with(|| EvmTload::new(is, one), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, load));
        builder.seal_all();

        assert!(!run_solver(&mut builder.func));
        assert_eq!(count_insts::<EvmTstore>(&builder.func), 1);
        assert_eq!(count_insts::<EvmTload>(&builder.func), 1);
    }

    #[test]
    fn keeps_final_sstore_at_function_exit() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let slot = builder.make_imm_value(I256::from(1));
        let value = builder.make_imm_value(I256::from(7));
        builder.insert_inst_no_result_with(|| EvmSstore::new(is, slot, value));
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        assert!(!run_solver(&mut builder.func));
        assert_eq!(count_insts::<EvmSstore>(&builder.func), 1);
    }

    #[test]
    fn keeps_final_sstore_before_noreturn_call_exit() {
        let mb = test_module_builder();
        let callee = mb
            .declare_function(Signature::new_unit(
                "noreturn_helper",
                Linkage::Private,
                &[],
            ))
            .unwrap();
        mb.ctx.set_func_effects(
            callee,
            FuncEffectSummary {
                noreturn: true,
                may_commit_visible_writes: true,
                will_return: false,
                will_terminate: true,
                ..FuncEffectSummary::default()
            },
        );

        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();
        let has_call = is.has_call().expect("target ISA must support `call`");

        let block = builder.append_block();
        builder.switch_to_block(block);

        let slot = builder.make_imm_value(I256::from(1));
        let value = builder.make_imm_value(I256::from(7));
        builder.insert_inst_no_result_with(|| EvmSstore::new(is, slot, value));
        builder.insert_inst_no_result_with(|| {
            control_flow::Call::new(has_call, callee, smallvec::smallvec![])
        });
        builder.insert_inst_no_result_with(|| control_flow::Unreachable::new_unchecked(is));
        builder.seal_all();

        assert!(!run_solver(&mut builder.func));
        assert_eq!(count_insts::<EvmSstore>(&builder.func), 1);
    }

    #[test]
    fn removes_final_sstore_before_reverting_noreturn_call_exit() {
        let mb = test_module_builder();
        let callee = mb
            .declare_function(Signature::new_unit("revert_helper", Linkage::Private, &[]))
            .unwrap();
        mb.ctx.set_func_effects(
            callee,
            FuncEffectSummary {
                noreturn: true,
                may_commit_visible_writes: false,
                will_return: false,
                will_terminate: true,
                ..FuncEffectSummary::default()
            },
        );

        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();
        let has_call = is.has_call().expect("target ISA must support `call`");

        let block = builder.append_block();
        builder.switch_to_block(block);

        let slot = builder.make_imm_value(I256::from(1));
        let value = builder.make_imm_value(I256::from(7));
        builder.insert_inst_no_result_with(|| EvmSstore::new(is, slot, value));
        builder.insert_inst_no_result_with(|| {
            control_flow::Call::new(has_call, callee, smallvec::smallvec![])
        });
        builder.insert_inst_no_result_with(|| control_flow::Unreachable::new_unchecked(is));
        builder.seal_all();

        assert!(run_solver(&mut builder.func));
        assert_eq!(count_insts::<EvmSstore>(&builder.func), 0);
    }

    #[test]
    fn keeps_final_absolute_memory_store_at_function_exit() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let addr = builder.make_imm_value(I256::from(64));
        let value = builder.make_imm_value(I256::from(7));
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, value, Type::I256));
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        assert!(!run_solver(&mut builder.func));
        assert_eq!(count_insts::<Mstore>(&builder.func), 1);
    }

    #[test]
    fn removes_overwritten_absolute_memory_store_before_function_exit() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let addr = builder.make_imm_value(I256::from(64));
        let v1 = builder.make_imm_value(I256::from(7));
        let v2 = builder.make_imm_value(I256::from(8));
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, v1, Type::I256));
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, v2, Type::I256));
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        assert!(run_solver(&mut builder.func));
        assert_eq!(count_insts::<Mstore>(&builder.func), 1);
    }

    #[test]
    fn keeps_store_when_only_one_commit_path_overwrites_exit_visible_value() {
        use sonatina_ir::inst::control_flow::Br;

        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I1], Type::Unit);
        let is = evm.inst_set();

        let entry = builder.append_block();
        let overwrite = builder.append_block();
        let passthrough = builder.append_block();

        builder.switch_to_block(entry);
        let cond = builder.args()[0];
        let addr = builder.make_imm_value(I256::from(64));
        let v1 = builder.make_imm_value(I256::from(7));
        let v2 = builder.make_imm_value(I256::from(8));
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, v1, Type::I256));
        builder.insert_inst_no_result_with(|| Br::new(is, cond, overwrite, passthrough));

        builder.switch_to_block(overwrite);
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, v2, Type::I256));
        builder.insert_inst_no_result_with(|| Return::new_unit(is));

        builder.switch_to_block(passthrough);
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();

        assert!(!run_solver(&mut builder.func));
        assert_eq!(count_insts::<Mstore>(&builder.func), 2);
    }

    #[test]
    fn removes_disjoint_absolute_memory_store_on_revert_exit() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let zero = builder.make_imm_value(I256::from(0));
        let len = builder.make_imm_value(I256::from(32));
        let addr = builder.make_imm_value(I256::from(64));
        let value = builder.make_imm_value(I256::from(7));
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, value, Type::I256));
        builder.insert_inst_no_result_with(|| EvmRevert::new(is, zero, len));
        builder.seal_all();

        assert!(run_solver(&mut builder.func));
        assert_eq!(count_insts::<Mstore>(&builder.func), 0);
    }

    #[test]
    fn removes_zero_length_absolute_memory_store_on_revert_exit() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let zero = builder.make_imm_value(I256::from(0));
        let addr = builder.make_imm_value(I256::from(64));
        let value = builder.make_imm_value(I256::from(7));
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, value, Type::I256));
        builder.insert_inst_no_result_with(|| EvmRevert::new(is, zero, zero));
        builder.seal_all();

        assert!(run_solver(&mut builder.func));
        assert_eq!(count_insts::<Mstore>(&builder.func), 0);
    }

    #[test]
    fn keeps_absolute_memory_store_when_revert_payload_reads_it() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let addr = builder.make_imm_value(I256::from(64));
        let len = builder.make_imm_value(I256::from(32));
        let value = builder.make_imm_value(I256::from(7));
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, value, Type::I256));
        builder.insert_inst_no_result_with(|| EvmRevert::new(is, addr, len));
        builder.seal_all();

        assert!(!run_solver(&mut builder.func));
        assert_eq!(count_insts::<Mstore>(&builder.func), 1);
    }

    #[test]
    fn removes_overwritten_absolute_memory_store_before_revert_payload() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let addr = builder.make_imm_value(I256::from(64));
        let len = builder.make_imm_value(I256::from(32));
        let v1 = builder.make_imm_value(I256::from(7));
        let v2 = builder.make_imm_value(I256::from(8));
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, v1, Type::I256));
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, v2, Type::I256));
        builder.insert_inst_no_result_with(|| EvmRevert::new(is, addr, len));
        builder.seal_all();

        assert!(run_solver(&mut builder.func));
        assert_eq!(count_insts::<Mstore>(&builder.func), 1);
    }

    #[test]
    fn removes_overwritten_absolute_memory_store_before_return_payload() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let addr = builder.make_imm_value(I256::from(64));
        let len = builder.make_imm_value(I256::from(32));
        let v1 = builder.make_imm_value(I256::from(7));
        let v2 = builder.make_imm_value(I256::from(8));
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, v1, Type::I256));
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, v2, Type::I256));
        builder.insert_inst_no_result_with(|| EvmReturn::new(is, addr, len));
        builder.seal_all();

        assert!(run_solver(&mut builder.func));
        assert_eq!(count_insts::<Mstore>(&builder.func), 1);
    }

    #[test]
    fn keeps_partially_overwritten_absolute_memory_store_before_revert_payload() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let range_addr = builder.make_imm_value(I256::from(64));
        let overwrite_addr = builder.make_imm_value(I256::from(80));
        let len = builder.make_imm_value(I256::from(32));
        let v1 = builder.make_imm_value(I256::from(7));
        let v2 = builder.make_imm_value(I256::from(8));
        builder.insert_inst_no_result_with(|| Mstore::new(is, range_addr, v1, Type::I256));
        builder.insert_inst_no_result_with(|| Mstore::new(is, overwrite_addr, v2, Type::I256));
        builder.insert_inst_no_result_with(|| EvmRevert::new(is, range_addr, len));
        builder.seal_all();

        assert!(!run_solver(&mut builder.func));
        assert_eq!(count_insts::<Mstore>(&builder.func), 2);
    }

    #[test]
    fn removes_final_sstore_on_revert_exit() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let zero = builder.make_imm_value(I256::from(0));
        let slot = builder.make_imm_value(I256::from(1));
        let value = builder.make_imm_value(I256::from(7));
        builder.insert_inst_no_result_with(|| EvmSstore::new(is, slot, value));
        builder.insert_inst_no_result_with(|| EvmRevert::new(is, zero, zero));
        builder.seal_all();

        assert!(run_solver(&mut builder.func));
        assert_eq!(count_insts::<EvmSstore>(&builder.func), 0);
    }

    #[test]
    fn keeps_final_sstore_on_selfdestruct_exit() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let zero = builder.make_imm_value(I256::from(0));
        let slot = builder.make_imm_value(I256::from(1));
        let value = builder.make_imm_value(I256::from(7));
        builder.insert_inst_no_result_with(|| EvmSstore::new(is, slot, value));
        builder.insert_inst_no_result_with(|| EvmSelfDestruct::new(is, zero));
        builder.seal_all();

        assert!(!run_solver(&mut builder.func));
        assert_eq!(count_insts::<EvmSstore>(&builder.func), 1);
    }

    #[test]
    fn keeps_final_sstore_when_any_exit_commits() {
        use sonatina_ir::inst::control_flow::Br;

        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I1], Type::Unit);
        let is = evm.inst_set();

        let entry = builder.append_block();
        let revert_block = builder.append_block();
        let stop_block = builder.append_block();

        builder.switch_to_block(entry);
        let cond = builder.args()[0];
        let zero = builder.make_imm_value(I256::from(0));
        let slot = builder.make_imm_value(I256::from(1));
        let value = builder.make_imm_value(I256::from(7));
        builder.insert_inst_no_result_with(|| EvmSstore::new(is, slot, value));
        builder.insert_inst_no_result_with(|| Br::new(is, cond, revert_block, stop_block));

        builder.switch_to_block(revert_block);
        builder.insert_inst_no_result_with(|| EvmRevert::new(is, zero, zero));

        builder.switch_to_block(stop_block);
        builder.insert_inst_no_result_with(|| EvmStop::new(is));

        builder.seal_all();

        assert!(!run_solver(&mut builder.func));
        assert_eq!(count_insts::<EvmSstore>(&builder.func), 1);
    }

    #[test]
    fn repeated_calldata_loads_cse() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let zero = builder.make_imm_value(0i32);
        let _first = builder.insert_inst_with(|| EvmCalldataLoad::new(is, zero), Type::I256);
        let second = builder.insert_inst_with(|| EvmCalldataLoad::new(is, zero), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, second));
        builder.seal_all();

        assert!(run_solver(&mut builder.func));
        assert_eq!(count_insts::<EvmCalldataLoad>(&builder.func), 1);
    }

    #[test]
    fn repeated_sloads_from_same_dynamic_key_forward_across_branch_and_join() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I1, Type::I256], Type::I256);
        let is = evm.inst_set();

        let entry = builder.append_block();
        let taken = builder.append_block();
        let join = builder.append_block();

        builder.switch_to_block(entry);
        let cond = builder.args()[0];
        let base = builder.args()[1];
        let one = builder.make_imm_value(I256::from(1));
        let key = builder.insert_inst_with(|| Add::new(is, one, base), Type::I256);
        let _first = builder.insert_inst_with(|| EvmSload::new(is, key), Type::I256);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, taken, join));

        builder.switch_to_block(taken);
        let _second = builder.insert_inst_with(|| EvmSload::new(is, key), Type::I256);
        builder.insert_inst_no_result_with(|| Jump::new(is, join));

        builder.switch_to_block(join);
        let third = builder.insert_inst_with(|| EvmSload::new(is, key), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, third));
        builder.seal_all();

        assert!(run_solver(&mut builder.func));
        assert_eq!(count_insts::<EvmSload>(&builder.func), 1);
    }

    #[test]
    fn does_not_forward_loop_variant_sload_across_backedge() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I1, Type::I256], Type::I256);
        let is = evm.inst_set();
        let carried = builder.declare_var(Type::I256);

        let entry = builder.append_block();
        let header = builder.append_block();
        let body = builder.append_block();
        let exit = builder.append_block();

        builder.switch_to_block(entry);
        let cond = builder.args()[0];
        let base = builder.args()[1];
        let zero = builder.make_imm_value(I256::from(0));
        let one = builder.make_imm_value(I256::from(1));
        builder.def_var(carried, zero);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));

        builder.switch_to_block(header);
        let idx = builder.use_var(carried);
        let slot = builder.insert_inst_with(|| Add::new(is, base, idx), Type::I256);
        let loaded = builder.insert_inst_with(|| EvmSload::new(is, slot), Type::I256);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, exit, body));

        builder.switch_to_block(body);
        let next = builder.insert_inst_with(|| Add::new(is, idx, one), Type::I256);
        builder.def_var(carried, next);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));

        builder.switch_to_block(exit);
        builder.insert_inst_no_result_with(|| Return::new_single(is, loaded));
        builder.seal_all();

        assert!(!run_solver(&mut builder.func));
        assert_eq!(count_insts::<EvmSload>(&builder.func), 1);
    }

    #[test]
    fn forwards_sload_from_equivalent_dynamic_key_expression() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I256], Type::I256);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let base = builder.args()[0];
        let one = builder.make_imm_value(I256::from(1));
        let seven = builder.make_imm_value(I256::from(7));
        let store_key = builder.insert_inst_with(|| Add::new(is, one, base), Type::I256);
        let load_key = builder.insert_inst_with(|| Add::new(is, one, base), Type::I256);
        builder.insert_inst_no_result_with(|| EvmSstore::new(is, store_key, seven));
        let loaded = builder.insert_inst_with(|| EvmSload::new(is, load_key), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, loaded));
        builder.seal_all();

        assert!(run_solver(&mut builder.func));
        assert_eq!(count_insts::<EvmSload>(&builder.func), 0);

        let ret = builder
            .func
            .layout
            .last_inst_of(block)
            .and_then(|inst| builder.func.dfg.return_args(inst))
            .expect("return args");
        assert_eq!(
            builder.func.dfg.value_imm(ret[0]),
            Some(Immediate::I256(I256::from(7)))
        );
    }

    #[test]
    fn does_not_forward_mstore8_from_wide_value() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I8);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let ptr_ty = builder.ptr_type(Type::I8);
        let addr = builder.insert_inst_with(|| Alloca::new(is, Type::I8), ptr_ty);
        let wide = builder.make_imm_value(I256::from(0x1ff));
        builder.insert_inst_no_result_with(|| EvmMstore8::new(is, addr, wide));
        let loaded = builder.insert_inst_with(|| Mload::new(is, addr, Type::I8), Type::I8);
        builder.insert_inst_no_result_with(|| Return::new_single(is, loaded));
        builder.seal_all();

        assert!(!run_solver(&mut builder.func));
        assert_eq!(count_insts::<EvmMstore8>(&builder.func), 1);
        assert_eq!(count_insts::<Mload>(&builder.func), 1);

        let ret = builder
            .func
            .layout
            .last_inst_of(block)
            .and_then(|inst| builder.func.dfg.return_args(inst))
            .expect("return args");
        assert_eq!(builder.func.dfg.value_ty(ret[0]), Type::I8);
    }

    #[test]
    fn does_not_forward_sload_from_narrow_stored_value() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let slot = builder.make_imm_value(I256::from(1));
        let narrow = builder.make_imm_value(7i32);
        builder.insert_inst_no_result_with(|| EvmSstore::new(is, slot, narrow));
        let loaded = builder.insert_inst_with(|| EvmSload::new(is, slot), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, loaded));
        builder.seal_all();

        assert!(!run_solver(&mut builder.func));
        assert_eq!(count_insts::<EvmSstore>(&builder.func), 1);
        assert_eq!(count_insts::<EvmSload>(&builder.func), 1);
    }
}
