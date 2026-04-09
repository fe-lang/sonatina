use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    BlockId, Function, InstId, Module, Type, Value, ValueId,
    cfg::ControlFlowGraph,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{control_flow, data, downcast},
    module::{FuncRef, ModuleCtx},
    types::CompoundType,
};

use super::{
    ObjectEffectSummaryMap, ObjectReturnEffect, collect_root_provenance,
    compute_object_effect_summaries,
    object_locality::{self, LocalObjectArgInfo, LocalObjectArgMap, RootInit},
    private_abi::{self, PrivateAbiPlan},
    provenance::{CompleteProvenance, CompleteRootSet, RootValue},
    shape,
};
use crate::cfg_scc::CfgSccAnalysis;

#[derive(Clone, Copy)]
enum RewriteRoot {
    LocalAlloc {
        inst: InstId,
        value: ValueId,
    },
    FreshCall {
        inst: InstId,
        value: ValueId,
        callee: FuncRef,
    },
}

impl RewriteRoot {
    fn value(&self) -> ValueId {
        match *self {
            Self::LocalAlloc { value, .. } | Self::FreshCall { value, .. } => value,
        }
    }

    fn inst(&self) -> InstId {
        match *self {
            Self::LocalAlloc { inst, .. } | Self::FreshCall { inst, .. } => inst,
        }
    }

    fn dependent_callee(&self) -> Option<FuncRef> {
        match *self {
            Self::LocalAlloc { .. } => None,
            Self::FreshCall { callee, .. } => Some(callee),
        }
    }

    fn is_forwarded_call_inst(&self, inst: InstId) -> bool {
        matches!(*self, Self::FreshCall { inst: root_inst, .. } if root_inst == inst)
    }
}

#[derive(Clone)]
struct FuncPlan {
    out_ty: Type,
    out_elem_ty: Type,
    roots: SmallVec<[RewriteRoot; 4]>,
    new_arg_tys: SmallVec<[Type; 8]>,
    new_ret_tys: SmallVec<[Type; 2]>,
}

impl PrivateAbiPlan for FuncPlan {
    fn new_arg_tys(&self) -> &[Type] {
        &self.new_arg_tys
    }

    fn new_ret_tys(&self) -> &[Type] {
        &self.new_ret_tys
    }
}

impl FuncPlan {
    fn forwards_caller_out_at(&self, inst: InstId) -> bool {
        self.roots
            .iter()
            .any(|root| root.is_forwarded_call_inst(inst))
    }

    fn dependent_callees(&self) -> impl Iterator<Item = FuncRef> + '_ {
        self.roots.iter().filter_map(RewriteRoot::dependent_callee)
    }
}

#[derive(Default)]
pub struct ObjectReturnOutParam;

impl ObjectReturnOutParam {
    pub fn run(&mut self, module: &Module) -> bool {
        !self.run_with_synthetic_out_args(module).is_empty()
    }

    pub(crate) fn run_with_synthetic_out_args(&mut self, module: &Module) -> LocalObjectArgMap {
        let mut synthetic_out_args = LocalObjectArgMap::default();

        loop {
            let object_effects = compute_object_effect_summaries(module);
            let plans = self.collect_plans(module, &object_effects);
            if plans.is_empty() {
                return synthetic_out_args;
            }
            let old_sigs = private_abi::rewrite_declared_signatures(module, &plans);

            for &func in plans.keys() {
                synthetic_out_args.entry(func).or_default().insert(
                    0,
                    LocalObjectArgInfo {
                        init: RootInit::UndefFresh,
                        fresh_result_out: true,
                    },
                );
            }

            for (&func, plan) in &plans {
                module.func_store.modify(func, |function| {
                    self.rewrite_function(function, plan);
                    function.rebuild_users();
                });
            }

            for func in module.funcs() {
                let caller_plan = plans.get(&func).cloned();
                module.func_store.modify(func, |function| {
                    if self.rewrite_calls(function, caller_plan.as_ref(), &plans) {
                        function.rebuild_users();
                    }
                });
            }

            private_abi::propagate_private_abi_types(module, &old_sigs);
        }
    }

    fn collect_plans(
        &self,
        module: &Module,
        object_effects: &ObjectEffectSummaryMap,
    ) -> FxHashMap<FuncRef, FuncPlan> {
        let mut plans = self.collect_candidate_plans(module, object_effects);

        loop {
            let before_len = plans.len();
            let live: FxHashSet<_> = plans.keys().copied().collect();
            let to_remove: Vec<_> = plans
                .iter()
                .filter_map(|(&func, plan)| {
                    plan.dependent_callees()
                        .any(|callee| !live.contains(&callee))
                        .then_some(func)
                })
                .collect();
            for func in to_remove {
                plans.remove(&func);
            }
            private_abi::retain_higher_order_safe_plans(module, &mut plans);
            if plans.len() == before_len {
                break;
            }
        }

        debug_assert!(plans.iter().all(|(_, plan)| {
            plan.dependent_callees()
                .all(|callee| plans.contains_key(&callee))
        }));

        plans
    }

    fn collect_candidate_plans(
        &self,
        module: &Module,
        object_effects: &ObjectEffectSummaryMap,
    ) -> FxHashMap<FuncRef, FuncPlan> {
        let mut plans = FxHashMap::default();

        for func in module.funcs() {
            let Some(sig) = module.ctx.get_sig(func) else {
                continue;
            };
            if !private_abi::is_owned_private_abi_func(&sig) || !sig.returns_single() {
                continue;
            }

            let Some(out_ty) = sig.single_ret_ty() else {
                continue;
            };
            let Some(out_elem_ty) = objref_element_ty(&module.ctx, out_ty) else {
                continue;
            };

            let Some(roots) = module.func_store.view(func, |function| {
                self.analyze_return_root(function, out_ty, out_elem_ty, object_effects)
            }) else {
                continue;
            };

            let new_arg_tys = std::iter::once(out_ty)
                .chain(sig.args().iter().copied())
                .collect();
            let new_ret_tys = SmallVec::new();
            plans.insert(
                func,
                FuncPlan {
                    out_ty,
                    out_elem_ty,
                    roots,
                    new_arg_tys,
                    new_ret_tys,
                },
            );
        }

        plans
    }

    fn analyze_return_root(
        &self,
        function: &Function,
        out_ty: Type,
        out_elem_ty: Type,
        object_effects: &ObjectEffectSummaryMap,
    ) -> Option<SmallVec<[RewriteRoot; 4]>> {
        let root_slices = self.collect_candidate_return_root_slices(
            function,
            out_ty,
            out_elem_ty,
            object_effects,
        );
        if root_slices.is_empty() {
            return None;
        }
        let mut layout_cache = shape::AggregateLayoutCache::default();
        let provenance_facts = collect_root_provenance(
            function,
            function.ctx(),
            &root_slices,
            &mut layout_cache,
            Some(object_effects),
        );
        let provenance = provenance_facts.complete();
        let root_slice = whole_object_slice(&mut layout_cache, function.ctx(), out_elem_ty);
        let mut return_roots = SmallVec::<[ValueId; 4]>::new();
        let mut seen_roots = FxHashSet::default();
        let mut saw_return = false;

        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                let Some(ret) =
                    downcast::<&control_flow::Return>(function.inst_set(), function.dfg.inst(inst))
                else {
                    continue;
                };
                saw_return = true;
                if !ret.returns_single() {
                    return None;
                }

                let root = *ret.arg()?;
                if function.dfg.value_ty(root) != out_ty {
                    return None;
                }

                for root in self.returned_whole_roots(root, root_slice, &root_slices, provenance)? {
                    if !seen_roots.insert(root) {
                        continue;
                    }
                    return_roots.push(root);
                }
            }
        }

        if !saw_return || return_roots.is_empty() {
            return None;
        }

        return_roots.sort_unstable_by_key(|root| root.as_u32());
        if !self.return_roots_are_rewritable(function, &return_roots) {
            return None;
        }

        let allowed_roots: FxHashSet<_> = return_roots.iter().copied().collect();
        let mut roots = SmallVec::with_capacity(return_roots.len());
        for root in return_roots {
            let rewrite_root =
                self.classify_rewrite_root(function, root, out_ty, out_elem_ty, object_effects)?;
            if !self.root_is_rewritable(
                function,
                root,
                &root_slices,
                provenance,
                object_effects,
                &allowed_roots,
            ) {
                return None;
            }
            roots.push(rewrite_root);
        }

        Some(roots)
    }

    fn returned_whole_roots(
        &self,
        value: ValueId,
        root_slice: shape::AggregateSlice,
        root_slices: &FxHashMap<ValueId, shape::AggregateSlice>,
        provenance: CompleteProvenance<'_>,
    ) -> Option<SmallVec<[ValueId; 4]>> {
        if let Some(projection) = provenance.exact_projection(value) {
            return (root_slices.get(&projection.root_value.value()) == Some(&projection.slice)
                && projection.slice == root_slice)
                .then_some(smallvec![projection.root_value.value()]);
        }

        match provenance.complete_roots(value)? {
            CompleteRootSet::Single(root) => (root_slices.get(&root.value()) == Some(&root_slice))
                .then_some(smallvec![root.value()]),
            CompleteRootSet::Multiple(roots) => {
                let mut returned_roots = SmallVec::<[ValueId; 4]>::new();
                for root in roots.iter() {
                    if root_slices.get(&root.value()) != Some(&root_slice) {
                        return None;
                    }
                    returned_roots.push(root.value());
                }
                returned_roots.sort_unstable_by_key(|root| root.as_u32());
                (!returned_roots.is_empty()).then_some(returned_roots)
            }
        }
    }

    fn return_roots_are_rewritable(&self, function: &Function, roots: &[ValueId]) -> bool {
        fresh_root_blocks_are_pairwise_unreachable(function, roots)
    }

    fn root_value_is_allowed(
        &self,
        function: &Function,
        value: ValueId,
        root: ValueId,
        root_slice: shape::AggregateSlice,
        provenance: CompleteProvenance<'_>,
        allowed_roots: &FxHashSet<ValueId>,
    ) -> bool {
        if provenance
            .exact_projection(value)
            .is_some_and(|projection| {
                projection.root_value == RootValue::new(root) && projection.slice == root_slice
            })
        {
            return true;
        }

        if function.dfg.value_ty(value) != function.dfg.value_ty(root) {
            return false;
        }

        match provenance.complete_roots(value) {
            Some(CompleteRootSet::Single(provenance_root)) => {
                provenance_root == RootValue::new(root)
            }
            Some(CompleteRootSet::Multiple(roots)) => {
                roots.contains(RootValue::new(root))
                    && roots
                        .iter()
                        .all(|candidate| allowed_roots.contains(&candidate.value()))
            }
            None => false,
        }
    }

    fn root_is_rewritable(
        &self,
        function: &Function,
        root: ValueId,
        root_slices: &FxHashMap<ValueId, shape::AggregateSlice>,
        provenance: CompleteProvenance<'_>,
        object_effects: &ObjectEffectSummaryMap,
        allowed_roots: &FxHashSet<ValueId>,
    ) -> bool {
        let Some(&root_slice) = root_slices.get(&root) else {
            return false;
        };
        let root_ty = function.dfg.value_ty(root);
        object_locality::object_root_stays_local_with_effects(
            function,
            root,
            root_ty,
            object_effects,
            |value| {
                self.root_value_is_allowed(
                    function,
                    value,
                    root,
                    root_slice,
                    provenance,
                    allowed_roots,
                )
            },
            true,
        )
    }

    fn rewrite_function(&self, function: &mut Function, plan: &FuncPlan) {
        self.prepend_out_arg(function, plan.out_ty);
        // Alias all planned returned roots to the synthetic out-param now.
        // Only local alloc roots are erased here; FreshCall roots stay in place until
        // rewrite_calls decides whether each exact callsite forwards caller storage.
        for root in &plan.roots {
            function
                .dfg
                .change_to_alias(root.value(), function.arg_values[0]);
        }
        for root in &plan.roots {
            if matches!(root, RewriteRoot::LocalAlloc { .. }) {
                function.layout.remove_inst(root.inst());
                function.erase_inst(root.inst());
            }
        }
        self.rewrite_returns(function);
    }

    fn is_fresh_return_call_candidate(
        &self,
        function: &Function,
        call: &control_flow::Call,
        result: ValueId,
        out_ty: Type,
        out_elem_ty: Type,
        object_effects: &ObjectEffectSummaryMap,
    ) -> bool {
        if function.dfg.value_ty(result) != out_ty
            || objref_element_ty(function.ctx(), function.dfg.value_ty(result)) != Some(out_elem_ty)
        {
            return false;
        }

        let Some(sig) = function.ctx().get_sig(*call.callee()) else {
            return false;
        };
        if !private_abi::is_owned_private_abi_func(&sig)
            || !sig.returns_single()
            || sig.single_ret_ty() != Some(out_ty)
        {
            return false;
        }

        object_effects
            .get(call.callee())
            .is_some_and(|summary| summary.ret_effect == ObjectReturnEffect::FreshObject)
    }

    fn classify_rewrite_root(
        &self,
        function: &Function,
        root: ValueId,
        out_ty: Type,
        out_elem_ty: Type,
        object_effects: &ObjectEffectSummaryMap,
    ) -> Option<RewriteRoot> {
        let inst = function.dfg.value_inst(root)?;
        if !function.layout.is_inst_inserted(inst) {
            return None;
        }

        if let Some(obj_alloc) =
            downcast::<&data::ObjAlloc>(function.inst_set(), function.dfg.inst(inst))
        {
            return (*obj_alloc.ty() == out_elem_ty)
                .then_some(RewriteRoot::LocalAlloc { inst, value: root });
        }

        let call = downcast::<&control_flow::Call>(function.inst_set(), function.dfg.inst(inst))?;
        let [result] = function.dfg.inst_results(inst) else {
            return None;
        };
        if *result != root
            || !self.is_fresh_return_call_candidate(
                function,
                call,
                root,
                out_ty,
                out_elem_ty,
                object_effects,
            )
        {
            return None;
        }

        Some(RewriteRoot::FreshCall {
            inst,
            value: root,
            callee: *call.callee(),
        })
    }

    fn collect_candidate_return_root_slices(
        &self,
        function: &Function,
        out_ty: Type,
        out_elem_ty: Type,
        object_effects: &ObjectEffectSummaryMap,
    ) -> FxHashMap<ValueId, shape::AggregateSlice> {
        let mut layout_cache = shape::AggregateLayoutCache::default();
        let root_slice = whole_object_slice(&mut layout_cache, function.ctx(), out_elem_ty);
        let mut root_slices = FxHashMap::default();

        // Seed provenance with both local alloc roots and fresh returned call results.
        // The final returned-root producers are resolved later through provenance.
        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                if let Some(obj_alloc) =
                    downcast::<&data::ObjAlloc>(function.inst_set(), function.dfg.inst(inst))
                {
                    if let Some(result) = function.dfg.inst_result(inst)
                        && *obj_alloc.ty() == out_elem_ty
                    {
                        root_slices.insert(result, root_slice);
                    }
                    continue;
                }

                let Some(call) =
                    downcast::<&control_flow::Call>(function.inst_set(), function.dfg.inst(inst))
                else {
                    continue;
                };
                let [result] = function.dfg.inst_results(inst) else {
                    continue;
                };
                if self.is_fresh_return_call_candidate(
                    function,
                    call,
                    *result,
                    out_ty,
                    out_elem_ty,
                    object_effects,
                ) {
                    root_slices.insert(*result, root_slice);
                }
            }
        }

        root_slices
    }

    fn prepend_out_arg(&self, function: &mut Function, out_ty: Type) {
        let old_args = function.arg_values.clone();
        let out_arg = function.dfg.make_value(Value::Arg { ty: out_ty, idx: 0 });
        let mut new_args = SmallVec::with_capacity(old_args.len() + 1);
        new_args.push(out_arg);

        for (idx, arg) in old_args.into_iter().enumerate() {
            let ty = function.dfg.value_ty(arg);
            function.dfg.values[arg] = Value::Arg { ty, idx: idx + 1 };
            new_args.push(arg);
        }

        function.arg_values = new_args;
    }

    fn rewrite_returns(&self, function: &mut Function) {
        let blocks: Vec<_> = function.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = function.layout.iter_inst(block).collect();
            for inst in insts {
                if downcast::<&control_flow::Return>(function.inst_set(), function.dfg.inst(inst))
                    .is_none()
                {
                    continue;
                }
                function.dfg.replace_inst(
                    inst,
                    Box::new(control_flow::Return::new_unit(
                        function
                            .inst_set()
                            .has_return()
                            .expect("target ISA must support `return`"),
                    )),
                );
            }
        }
    }

    fn rewrite_calls(
        &self,
        function: &mut Function,
        caller_plan: Option<&FuncPlan>,
        plans: &FxHashMap<FuncRef, FuncPlan>,
    ) -> bool {
        let mut changed = false;
        let blocks: Vec<_> = function.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = function.layout.iter_inst(block).collect();
            for inst in insts {
                if !function.layout.is_inst_inserted(inst) {
                    continue;
                }
                let Some(call) =
                    downcast::<&control_flow::Call>(function.inst_set(), function.dfg.inst(inst))
                        .cloned()
                else {
                    continue;
                };
                let Some(plan) = plans.get(call.callee()) else {
                    continue;
                };
                self.rewrite_call(function, inst, &call, plan, caller_plan);
                changed = true;
            }
        }
        changed
    }

    fn rewrite_call(
        &self,
        function: &mut Function,
        inst: InstId,
        call: &control_flow::Call,
        callee_plan: &FuncPlan,
        caller_plan: Option<&FuncPlan>,
    ) {
        let original_loc = function.layout.prev_inst_of(inst).map_or(
            CursorLocation::BlockTop(function.layout.inst_block(inst)),
            CursorLocation::At,
        );
        let forward_to_caller_out =
            caller_plan.is_some_and(|plan| plan.forwards_caller_out_at(inst));

        let (out_arg, call_loc) = if forward_to_caller_out {
            assert!(
                !function.arg_values.is_empty(),
                "forwarded returned-call rewrite requires caller out-param"
            );
            assert_eq!(
                function.dfg.value_ty(function.arg_values[0]),
                callee_plan.out_ty,
                "forwarded returned-call rewrite must match callee out type"
            );
            (function.arg_values[0], original_loc)
        } else {
            let mut cursor = InstInserter::at_location(original_loc);
            let out_alloc = cursor.insert_inst_data(
                function,
                data::ObjAlloc::new_unchecked(function.inst_set(), callee_plan.out_elem_ty),
            );
            let out_arg = cursor.make_result(function, out_alloc, callee_plan.out_ty);
            cursor.attach_result(function, out_alloc, out_arg);
            (out_arg, CursorLocation::At(out_alloc))
        };

        let mut cursor = InstInserter::at_location(call_loc);
        let new_args = std::iter::once(out_arg)
            .chain(call.args().iter().copied())
            .collect();
        let new_call = cursor.insert_inst_data(
            function,
            control_flow::Call::new(
                function
                    .inst_set()
                    .has_call()
                    .expect("target ISA must support `call`"),
                *call.callee(),
                new_args,
            ),
        );
        cursor.attach_results(function, new_call, &[]);

        let [old_result] = function.dfg.inst_results(inst) else {
            panic!("planned object-return call should have exactly one result");
        };
        function.dfg.change_to_alias(*old_result, out_arg);
        function.layout.remove_inst(inst);
        function.erase_inst(inst);
    }
}

fn objref_element_ty(ctx: &ModuleCtx, ty: Type) -> Option<Type> {
    let CompoundType::ObjRef(elem) = ty.resolve_compound(ctx)? else {
        return None;
    };
    Some(elem)
}

fn whole_object_slice(
    layout_cache: &mut shape::AggregateLayoutCache,
    ctx: &ModuleCtx,
    ty: Type,
) -> shape::AggregateSlice {
    let leaf_count = if ty == Type::Unit {
        0
    } else {
        layout_cache
            .shape(ctx, ty)
            .map_or(1, |shape| shape.leaves.len())
    };
    shape::AggregateSlice {
        ty,
        first_leaf: 0,
        leaf_count,
    }
}

fn fresh_root_blocks_are_pairwise_unreachable(function: &Function, roots: &[ValueId]) -> bool {
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(function);
    let mut scc = CfgSccAnalysis::new();
    scc.compute(&cfg);

    let mut root_blocks = SmallVec::<[BlockId; 4]>::new();
    for &root in roots {
        let Some(inst) = function.dfg.value_inst(root) else {
            return false;
        };
        let block = function.layout.inst_block(inst);
        let Some(block_scc) = scc.scc_of(block) else {
            return false;
        };
        if scc.scc_data(block_scc).is_cycle {
            return false;
        }
        if root_blocks.contains(&block) {
            return false;
        }
        root_blocks.push(block);
    }

    for idx in 0..root_blocks.len() {
        for &other in &root_blocks[idx + 1..] {
            if block_reaches(&cfg, root_blocks[idx], other)
                || block_reaches(&cfg, other, root_blocks[idx])
            {
                return false;
            }
        }
    }

    true
}

fn block_reaches(cfg: &ControlFlowGraph, from: BlockId, to: BlockId) -> bool {
    if from == to {
        return true;
    }

    let mut worklist = vec![from];
    let mut seen = FxHashSet::default();
    while let Some(block) = worklist.pop() {
        if !seen.insert(block) {
            continue;
        }
        for succ in cfg.succs_as_slice(block).iter().copied() {
            if succ == to {
                return true;
            }
            if !seen.contains(&succ) {
                worklist.push(succ);
            }
        }
    }

    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::{Module, ir_writer::FuncWriter, module::FuncRef};
    use sonatina_parser::parse_module;
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

    fn parse_test_module(src: &str) -> Module {
        parse_module(src).expect("parse should succeed").module
    }

    fn lookup_func(module: &Module, name: &str) -> FuncRef {
        module
            .funcs()
            .into_iter()
            .find(|&func_ref| module.ctx.func_sig(func_ref, |sig| sig.name() == name))
            .expect("function should exist")
    }

    fn dump_func(module: &Module, func_ref: FuncRef) -> String {
        module.func_store.view(func_ref, |func| {
            FuncWriter::new(func_ref, func).dump_string()
        })
    }

    fn verify_rewritten_module(module: &Module) {
        let report = verify_module(
            module,
            &VerifierConfig::for_level(VerificationLevel::Standard),
        );
        assert!(
            !report.has_errors(),
            "object ABI rewriting should preserve verifier invariants:\n{report}"
        );
    }

    fn pair_ty(module: &Module) -> Type {
        module.ctx.with_ty_store(|store| {
            Type::Compound(store.lookup_struct("pair").expect("pair type should exist"))
        })
    }

    fn count_obj_allocs(func: &Function, ty: Type) -> usize {
        let mut count = 0;
        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                if downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst))
                    .is_some_and(|obj_alloc| *obj_alloc.ty() == ty)
                {
                    count += 1;
                }
            }
        }
        count
    }

    fn call_insts(func: &Function, callee: FuncRef) -> Vec<InstId> {
        let mut calls = Vec::new();
        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                if downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst))
                    .is_some_and(|call| *call.callee() == callee)
                {
                    calls.push(inst);
                }
            }
        }
        calls
    }

    #[test]
    fn forwards_nested_returned_call_root_to_caller_out_param_through_phi() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %make_pair(v0.i256, v1.i256) -> objref<@pair> {
block0:
    v2.objref<@pair> = obj.alloc @pair;
    v3.objref<i256> = obj.proj v2 0.i8;
    obj.store v3 v0;
    v4.objref<i256> = obj.proj v2 1.i8;
    obj.store v4 v1;
    return v2;
}

func private %wrap(v0.i1, v1.i256, v2.i256, v3.i256) -> objref<@pair> {
block0:
    br v0 block1 block2;

block1:
    v4.objref<@pair> = call %make_pair v1 v2;
    jump block3;

block2:
    v5.objref<@pair> = obj.alloc @pair;
    v6.objref<i256> = obj.proj v5 0.i8;
    obj.store v6 v3;
    jump block3;

block3:
    v7.objref<@pair> = phi (v4 block1) (v5 block2);
    return v7;
}
"#,
        );
        let make_pair = lookup_func(&module, "make_pair");
        let wrap = lookup_func(&module, "wrap");

        ObjectReturnOutParam.run(&module);
        verify_rewritten_module(&module);

        let pair = pair_ty(&module);
        let wrap_sig = module.ctx.get_sig(wrap).expect("signature should exist");
        assert_eq!(wrap_sig.args().len(), 5);
        assert_eq!(
            objref_element_ty(&module.ctx, wrap_sig.args()[0]),
            Some(pair)
        );
        assert_eq!(wrap_sig.ret_tys(), &[]);

        module.func_store.view(wrap, |func| {
            let dumped = dump_func(&module, wrap);
            let calls = call_insts(func, make_pair);
            assert_eq!(
                calls.len(),
                1,
                "expected one rewritten nested call:\n{dumped}"
            );

            let call = downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(calls[0]))
                .expect("call should remain present");
            assert_eq!(
                call.args()[0],
                func.arg_values[0],
                "returned nested call should forward the caller out-param:\n{dumped}"
            );
            assert_eq!(
                count_obj_allocs(func, pair),
                0,
                "returned nested call should not allocate a temporary out slot:\n{dumped}"
            );
        });
    }

    #[test]
    fn forwards_nested_multi_root_fresh_call_to_caller_out_param() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %pick(v0.i1, v1.i256, v2.i256) -> objref<@pair> {
block0:
    br v0 block1 block2;

block1:
    v3.objref<@pair> = obj.alloc @pair;
    v4.objref<i256> = obj.proj v3 0.i8;
    obj.store v4 v1;
    jump block3;

block2:
    v5.objref<@pair> = obj.alloc @pair;
    v6.objref<i256> = obj.proj v5 0.i8;
    obj.store v6 v2;
    jump block3;

block3:
    v7.objref<@pair> = phi (v3 block1) (v5 block2);
    return v7;
}

func private %wrap(v0.i1, v1.i1, v2.i256, v3.i256, v4.i256) -> objref<@pair> {
block0:
    br v0 block1 block2;

block1:
    v5.objref<@pair> = call %pick v1 v2 v3;
    jump block3;

block2:
    v6.objref<@pair> = obj.alloc @pair;
    v7.objref<i256> = obj.proj v6 0.i8;
    obj.store v7 v4;
    jump block3;

block3:
    v8.objref<@pair> = phi (v5 block1) (v6 block2);
    return v8;
}
"#,
        );
        let pick = lookup_func(&module, "pick");
        let wrap = lookup_func(&module, "wrap");

        ObjectReturnOutParam.run(&module);
        verify_rewritten_module(&module);

        let pair = pair_ty(&module);
        let wrap_sig = module.ctx.get_sig(wrap).expect("signature should exist");
        assert_eq!(wrap_sig.args().len(), 6);
        assert_eq!(
            objref_element_ty(&module.ctx, wrap_sig.args()[0]),
            Some(pair)
        );
        assert_eq!(wrap_sig.ret_tys(), &[]);

        module.func_store.view(wrap, |func| {
            let dumped = dump_func(&module, wrap);
            let calls = call_insts(func, pick);
            let [call_inst] = calls.as_slice() else {
                panic!("expected one rewritten nested call:\n{dumped}");
            };
            let call = downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(*call_inst))
                .expect("call should remain present");
            assert_eq!(
                call.args()[0],
                func.arg_values[0],
                "multi-root fresh nested call should forward the caller out-param:\n{dumped}"
            );
            assert_eq!(
                count_obj_allocs(func, pair),
                0,
                "returned nested call should not allocate a temporary out slot:\n{dumped}"
            );
        });
    }

    #[test]
    fn leaves_unrelated_same_typed_helper_calls_on_distinct_temporaries() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %helper(v0.i256) -> objref<@pair> {
block0:
    v1.objref<@pair> = obj.alloc @pair;
    v2.objref<i256> = obj.proj v1 0.i8;
    obj.store v2 v0;
    return v1;
}

func private %caller(v0.i256, v1.i256) -> objref<@pair> {
block0:
    v2.objref<@pair> = call %helper v0;
    v3.objref<@pair> = call %helper v1;
    v4.objref<i256> = obj.proj v2 0.i8;
    v5.i256 = obj.load v4;
    v6.objref<i256> = obj.proj v3 0.i8;
    v7.i256 = obj.load v6;
    v8.objref<@pair> = obj.alloc @pair;
    v9.objref<i256> = obj.proj v8 0.i8;
    obj.store v9 v5;
    v10.objref<i256> = obj.proj v8 1.i8;
    obj.store v10 v7;
    return v8;
}
"#,
        );
        let helper = lookup_func(&module, "helper");
        let caller = lookup_func(&module, "caller");

        ObjectReturnOutParam.run(&module);
        verify_rewritten_module(&module);

        let pair = pair_ty(&module);
        let caller_sig = module.ctx.get_sig(caller).expect("signature should exist");
        assert_eq!(caller_sig.args().len(), 3);
        assert_eq!(
            objref_element_ty(&module.ctx, caller_sig.args()[0]),
            Some(pair)
        );
        assert_eq!(caller_sig.ret_tys(), &[]);

        module.func_store.view(caller, |func| {
            let dumped = dump_func(&module, caller);
            let calls = call_insts(func, helper);
            assert_eq!(
                calls.len(),
                2,
                "expected both helper calls to remain after rewriting:\n{dumped}"
            );
            assert_eq!(
                count_obj_allocs(func, pair),
                2,
                "only helper temporaries should remain allocated:\n{dumped}"
            );

            let mut temp_outs = FxHashSet::default();
            for inst in calls {
                let call = downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst))
                    .expect("call should remain present");
                let temp_out = call.args()[0];
                assert_ne!(
                    temp_out, func.arg_values[0],
                    "unrelated helper calls must not forward the caller out-param:\n{dumped}"
                );
                let temp_inst = func
                    .dfg
                    .value_inst(temp_out)
                    .expect("helper out arg should come from an instruction");
                assert!(
                    downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(temp_inst))
                        .is_some_and(|obj_alloc| *obj_alloc.ty() == pair),
                    "helper call should receive a fresh local out allocation:\n{dumped}"
                );
                assert!(
                    temp_outs.insert(temp_out),
                    "helper calls should not alias the same temporary out slot:\n{dumped}"
                );
            }
        });
    }

    #[test]
    fn inserts_temporary_alloc_before_non_forwarded_rewritten_call() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %helper(v0.i256) -> objref<@pair> {
block0:
    v1.objref<@pair> = obj.alloc @pair;
    v2.objref<i256> = obj.proj v1 0.i8;
    obj.store v2 v0;
    return v1;
}

func private %caller(v0.i256) -> objref<@pair> {
block0:
    v1.objref<@pair> = call %helper v0;
    v2.objref<i256> = obj.proj v1 0.i8;
    v3.i256 = obj.load v2;
    v4.objref<@pair> = obj.alloc @pair;
    v5.objref<i256> = obj.proj v4 0.i8;
    obj.store v5 v3;
    return v4;
}
"#,
        );
        let helper = lookup_func(&module, "helper");
        let caller = lookup_func(&module, "caller");

        ObjectReturnOutParam.run(&module);
        verify_rewritten_module(&module);

        module.func_store.view(caller, |func| {
            let dumped = dump_func(&module, caller);
            let calls = call_insts(func, helper);
            let [call_inst] = calls.as_slice() else {
                panic!("expected exactly one helper call:\n{dumped}");
            };
            let call = downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(*call_inst))
                .expect("call should remain present");
            let temp_out = call.args()[0];
            assert_ne!(
                temp_out, func.arg_values[0],
                "temporary helper result should not use the caller out-param:\n{dumped}"
            );

            let alloc_inst = func
                .dfg
                .value_inst(temp_out)
                .expect("helper out arg should come from an instruction");
            assert!(
                downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(alloc_inst)).is_some(),
                "helper out arg should come from an obj.alloc:\n{dumped}"
            );

            let order: Vec<_> = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .collect();
            let alloc_pos = order
                .iter()
                .position(|&inst| inst == alloc_inst)
                .expect("alloc should be inserted");
            let call_pos = order
                .iter()
                .position(|&inst| inst == *call_inst)
                .expect("call should be inserted");
            assert!(
                alloc_pos < call_pos,
                "temporary out alloc must dominate the rewritten call:\n{dumped}"
            );
        });
    }

    #[test]
    fn forwards_only_exact_returned_call_roots_in_mixed_same_typed_callers() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %helper(v0.i256) -> objref<@pair> {
block0:
    v1.objref<@pair> = obj.alloc @pair;
    v2.objref<i256> = obj.proj v1 0.i8;
    obj.store v2 v0;
    return v1;
}

func private %caller(v0.i1, v1.i256, v2.i256, v3.i256) -> objref<@pair> {
block0:
    v4.objref<@pair> = call %helper v1;
    v5.objref<i256> = obj.proj v4 0.i8;
    v6.i256 = obj.load v5;
    br v0 block1 block2;

block1:
    v7.objref<@pair> = call %helper v2;
    jump block3;

block2:
    v8.objref<@pair> = obj.alloc @pair;
    v9.objref<i256> = obj.proj v8 0.i8;
    obj.store v9 v3;
    v10.objref<i256> = obj.proj v8 1.i8;
    obj.store v10 v6;
    jump block3;

block3:
    v11.objref<@pair> = phi (v7 block1) (v8 block2);
    return v11;
}
"#,
        );
        let helper = lookup_func(&module, "helper");
        let caller = lookup_func(&module, "caller");

        ObjectReturnOutParam.run(&module);
        verify_rewritten_module(&module);

        module.func_store.view(caller, |func| {
            let dumped = dump_func(&module, caller);
            let calls = call_insts(func, helper);
            assert_eq!(calls.len(), 2, "expected both helper calls:\n{dumped}");

            let mut saw_temporary_call = false;
            let mut saw_forwarded_call = false;
            for inst in calls {
                let call = downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst))
                    .expect("call should remain present");
                let out_arg = call.args()[0];
                let payload_arg = call.args()[1];
                if payload_arg == func.arg_values[2] {
                    saw_temporary_call = true;
                    assert_ne!(
                        out_arg, func.arg_values[0],
                        "temporary helper call must not forward the caller out-param:\n{dumped}"
                    );
                } else if payload_arg == func.arg_values[3] {
                    saw_forwarded_call = true;
                    assert_eq!(
                        out_arg, func.arg_values[0],
                        "returned helper call should forward the caller out-param:\n{dumped}"
                    );
                } else {
                    panic!("unexpected helper payload arg in rewritten caller:\n{dumped}");
                }
            }

            assert!(
                saw_temporary_call,
                "expected one helper temporary callsite:\n{dumped}"
            );
            assert!(
                saw_forwarded_call,
                "expected one forwarded returned helper callsite:\n{dumped}"
            );
        });
    }

    #[test]
    fn drops_wrapper_plan_when_returned_call_root_callee_is_not_final() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %make_pair(v0.i256) -> objref<@pair> {
block0:
    v1.objref<@pair> = obj.alloc @pair;
    v2.objref<i256> = obj.proj v1 0.i8;
    obj.store v2 v0;
    return v1;
}

func private %ambiguous_pair(v0.i256) -> objref<@pair> {
block0:
    jump block1;

block1:
    v1.objref<@pair> = obj.alloc @pair;
    v2.objref<i256> = obj.proj v1 0.i8;
    obj.store v2 v0;
    v3.i1 = is_zero v0;
    br v3 block1 block2;

block2:
    return v1;
}

func private %use_maker(v0.*(i256) -> objref<@pair>) {
block0:
    return;
}

func private %register_maker() {
block0:
    v0.*(i256) -> objref<@pair> = get_function_ptr %make_pair;
    call %use_maker v0;
    return;
}

func private %wrapper(v0.i1, v1.i256, v2.i256) -> objref<@pair> {
block0:
    br v0 block1 block2;

block1:
    v3.objref<@pair> = call %make_pair v1;
    jump block3;

block2:
    v4.objref<@pair> = obj.alloc @pair;
    v5.objref<i256> = obj.proj v4 0.i8;
    obj.store v5 v2;
    jump block3;

block3:
    v6.objref<@pair> = phi (v3 block1) (v4 block2);
    return v6;
}
"#,
        );
        let make_pair = lookup_func(&module, "make_pair");
        let wrapper = lookup_func(&module, "wrapper");
        let mut pass = ObjectReturnOutParam;
        let object_effects = compute_object_effect_summaries(&module);

        let candidates = pass.collect_candidate_plans(&module, &object_effects);
        assert!(candidates.contains_key(&make_pair));
        assert!(candidates.contains_key(&wrapper));

        let mut after_higher_order = pass.collect_candidate_plans(&module, &object_effects);
        private_abi::retain_higher_order_safe_plans(&module, &mut after_higher_order);
        assert!(
            !after_higher_order.contains_key(&make_pair),
            "callee should be removed by higher-order safety"
        );
        assert!(
            after_higher_order.contains_key(&wrapper),
            "wrapper should survive higher-order filtering because its own signature class is distinct"
        );

        let final_plans = pass.collect_plans(&module, &object_effects);
        assert!(
            !final_plans.contains_key(&wrapper),
            "dependency pruning should remove the wrapper after its returned-call callee disappears"
        );

        assert!(
            !pass.run(&module),
            "dependency pruning should reject the wrapper when the callee is not final"
        );
        verify_rewritten_module(&module);

        let make_pair_sig = module
            .ctx
            .get_sig(make_pair)
            .expect("signature should exist");
        assert_eq!(make_pair_sig.args().len(), 1);
        assert_eq!(make_pair_sig.ret_tys().len(), 1);

        let wrapper_sig = module.ctx.get_sig(wrapper).expect("signature should exist");
        assert_eq!(wrapper_sig.args().len(), 3);
        assert_eq!(wrapper_sig.ret_tys().len(), 1);

        module.func_store.view(wrapper, |func| {
            let dumped = dump_func(&module, wrapper);
            let calls = call_insts(func, make_pair);
            let [call_inst] = calls.as_slice() else {
                panic!("wrapper should still contain the original call:\n{dumped}");
            };
            let call = downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(*call_inst))
                .expect("call should remain present");
            assert_eq!(
                call.args()[0],
                func.arg_values[1],
                "wrapper callsite should still use its original payload argument:\n{dumped}"
            );
            assert_eq!(
                call.args().len(),
                1,
                "wrapper callsite should remain unchanged:\n{dumped}"
            );
            assert_eq!(
                func.dfg.inst_results(*call_inst).len(),
                1,
                "wrapper callsite should still produce its original result:\n{dumped}"
            );
        });
    }
}
