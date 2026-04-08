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
    ObjectEffectSummaryMap, collect_root_provenance, compute_object_effect_summaries,
    object_locality::{self, LocalObjectArgInfo, LocalObjectArgMap, RootInit},
    private_abi::{self, PrivateAbiPlan},
    shape,
};
use crate::cfg_scc::CfgSccAnalysis;

#[derive(Clone)]
struct RewriteRoot {
    alloc_inst: InstId,
    value: ValueId,
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
            let mut plans = self.collect_plans(module, &object_effects);
            private_abi::retain_higher_order_safe_plans(module, &mut plans);
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
                module.func_store.modify(func, |function| {
                    if self.rewrite_calls(function, func, &plans) {
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
        let root_slices = self.collect_return_root_slices(function, out_elem_ty, object_effects);
        if root_slices.is_empty() {
            return None;
        }
        let mut layout_cache = shape::AggregateLayoutCache::default();
        let provenance = collect_root_provenance(
            function,
            function.ctx(),
            &root_slices,
            &mut layout_cache,
            Some(object_effects),
        );
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

                for root in
                    self.returned_whole_roots(root, root_slice, &root_slices, &provenance)?
                {
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
            let root_alloc_inst = function.dfg.value_inst(root)?;
            if !function.layout.is_inst_inserted(root_alloc_inst)
                || downcast::<&data::ObjAlloc>(
                    function.inst_set(),
                    function.dfg.inst(root_alloc_inst),
                )
                .is_none()
                || !self.root_is_rewritable(
                    function,
                    root,
                    &root_slices,
                    &provenance,
                    object_effects,
                    &allowed_roots,
                )
            {
                return None;
            }
            roots.push(RewriteRoot {
                alloc_inst: root_alloc_inst,
                value: root,
            });
        }

        Some(roots)
    }

    fn returned_whole_roots(
        &self,
        value: ValueId,
        root_slice: shape::AggregateSlice,
        root_slices: &FxHashMap<ValueId, shape::AggregateSlice>,
        provenance: &super::provenance::RootProvenanceMap,
    ) -> Option<SmallVec<[ValueId; 4]>> {
        if let Some(projection) = provenance.exact_projection(value) {
            return (root_slices.get(&projection.root_value) == Some(&projection.slice)
                && projection.slice == root_slice)
                .then_some(smallvec![projection.root_value]);
        }

        match provenance.provenance(value) {
            super::RootProvenance::SameRoot(root) => {
                (root_slices.get(&root) == Some(&root_slice)).then_some(smallvec![root])
            }
            super::RootProvenance::Maybe(roots) => {
                let mut returned_roots = SmallVec::<[ValueId; 4]>::new();
                for root in roots {
                    if root_slices.get(&root) != Some(&root_slice) {
                        return None;
                    }
                    returned_roots.push(root);
                }
                returned_roots.sort_unstable_by_key(|root| root.as_u32());
                (!returned_roots.is_empty()).then_some(returned_roots)
            }
            super::RootProvenance::Exact(_) | super::RootProvenance::Unknown => None,
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
        provenance: &super::provenance::RootProvenanceMap,
        allowed_roots: &FxHashSet<ValueId>,
    ) -> bool {
        if provenance
            .exact_projection(value)
            .is_some_and(|projection| {
                projection.root_value == root && projection.slice == root_slice
            })
        {
            return true;
        }

        if function.dfg.value_ty(value) != function.dfg.value_ty(root) {
            return false;
        }

        match provenance.provenance(value) {
            super::RootProvenance::SameRoot(provenance_root) => provenance_root == root,
            super::RootProvenance::Maybe(roots) => {
                roots.contains(&root)
                    && roots
                        .iter()
                        .all(|candidate| allowed_roots.contains(candidate))
            }
            super::RootProvenance::Exact(projection) => {
                projection.root_value == root && projection.slice == root_slice
            }
            super::RootProvenance::Unknown => false,
        }
    }

    fn root_is_rewritable(
        &self,
        function: &Function,
        root: ValueId,
        root_slices: &FxHashMap<ValueId, shape::AggregateSlice>,
        provenance: &super::provenance::RootProvenanceMap,
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
        for root in &plan.roots {
            function
                .dfg
                .change_to_alias(root.value, function.arg_values[0]);
        }
        for root in &plan.roots {
            function.layout.remove_inst(root.alloc_inst);
            function.erase_inst(root.alloc_inst);
        }
        self.rewrite_returns(function);
    }

    fn collect_return_root_slices(
        &self,
        function: &Function,
        out_elem_ty: Type,
        object_effects: &ObjectEffectSummaryMap,
    ) -> FxHashMap<ValueId, shape::AggregateSlice> {
        let mut layout_cache = shape::AggregateLayoutCache::default();
        let root_slice = whole_object_slice(&mut layout_cache, function.ctx(), out_elem_ty);
        let mut root_slices = FxHashMap::default();

        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                let Some(obj_alloc) =
                    downcast::<&data::ObjAlloc>(function.inst_set(), function.dfg.inst(inst))
                else {
                    continue;
                };
                let Some(result) = function.dfg.inst_result(inst) else {
                    continue;
                };
                if *obj_alloc.ty() == out_elem_ty {
                    root_slices.insert(result, root_slice);
                }
            }
        }

        let _ = object_effects;
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
        caller_func: FuncRef,
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
                self.rewrite_call(function, inst, &call, plan, caller_func, plans);
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
        plan: &FuncPlan,
        caller_func: FuncRef,
        plans: &FxHashMap<FuncRef, FuncPlan>,
    ) {
        // If the calling function was itself planned for out-param rewriting,
        // and the call result type matches the caller's out-param type, forward
        // the caller's out-param to the callee instead of allocating a fresh local.
        // This handles the case where a call result flows through a phi to the
        // caller's return (e.g. `and_then` calling `Step::call`).
        let caller_out_param = if plans.contains_key(&caller_func)
            && !function.arg_values.is_empty()
            && function.dfg.value_ty(function.arg_values[0]) == plan.out_ty
        {
            Some(function.arg_values[0])
        } else {
            None
        };

        let out_arg = if let Some(caller_out) = caller_out_param {
            caller_out
        } else {
            let loc = function.layout.prev_inst_of(inst).map_or(
                CursorLocation::BlockTop(function.layout.inst_block(inst)),
                CursorLocation::At,
            );
            let mut cursor = InstInserter::at_location(loc);
            let out_alloc = cursor.insert_inst_data(
                function,
                data::ObjAlloc::new_unchecked(function.inst_set(), plan.out_elem_ty),
            );
            let out_arg = cursor.make_result(function, out_alloc, plan.out_ty);
            cursor.attach_result(function, out_alloc, out_arg);
            out_arg
        };

        let loc = function.layout.prev_inst_of(inst).map_or(
            CursorLocation::BlockTop(function.layout.inst_block(inst)),
            CursorLocation::At,
        );
        let mut cursor = InstInserter::at_location(loc);
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
