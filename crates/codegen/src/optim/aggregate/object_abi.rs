use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use sonatina_ir::{
    Function, InstId, Module, Type, Value, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{control_flow, data, downcast},
    module::{FuncRef, ModuleCtx},
    types::CompoundType,
};

use super::{
    collect_root_provenance,
    object_locality::{self, LocalObjectArgInfo, LocalObjectArgMap, RootInit},
    private_abi::{self, PrivateAbiPlan},
    shape,
};

#[derive(Clone)]
struct FuncPlan {
    out_ty: Type,
    out_elem_ty: Type,
    root_alloc_inst: InstId,
    root_value: ValueId,
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
            let local_object_args = object_locality::collect_local_object_arg_info(module);
            let mut plans = self.collect_plans(module, &local_object_args);
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
                    if self.rewrite_calls(function, &plans) {
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
        local_object_args: &LocalObjectArgMap,
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

            let Some((root_alloc_inst, root_value)) = module.func_store.view(func, |function| {
                self.analyze_return_root(function, out_ty, out_elem_ty, local_object_args)
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
                    root_alloc_inst,
                    root_value,
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
        local_object_args: &LocalObjectArgMap,
    ) -> Option<(InstId, ValueId)> {
        let root_slices = self.collect_return_root_slices(function, out_elem_ty);
        if root_slices.is_empty() {
            return None;
        }
        let mut layout_cache = shape::AggregateLayoutCache::default();
        let provenance =
            collect_root_provenance(function, function.ctx(), &root_slices, &mut layout_cache);
        let mut return_root = None;
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

                let projection = provenance.exact_projection(root)?;
                if root_slices.get(&projection.root_value) != Some(&projection.slice) {
                    return None;
                }

                if let Some(existing) = return_root {
                    if existing != projection.root_value {
                        return None;
                    }
                } else {
                    return_root = Some(projection.root_value);
                }
            }
        }

        if !saw_return {
            return None;
        }

        let root_value = return_root?;
        let root_alloc_inst = function.dfg.value_inst(root_value)?;
        if !function.layout.is_inst_inserted(root_alloc_inst)
            || downcast::<&data::ObjAlloc>(function.inst_set(), function.dfg.inst(root_alloc_inst))
                .is_none()
            || !self.root_is_rewritable(
                function,
                root_value,
                out_ty,
                local_object_args,
                &root_slices,
                &provenance,
            )
        {
            return None;
        }

        Some((root_alloc_inst, root_value))
    }

    fn root_is_rewritable(
        &self,
        function: &Function,
        root: ValueId,
        root_ty: Type,
        local_object_args: &LocalObjectArgMap,
        root_slices: &FxHashMap<ValueId, shape::AggregateSlice>,
        provenance: &super::provenance::RootProvenanceMap,
    ) -> bool {
        let Some(&root_slice) = root_slices.get(&root) else {
            return false;
        };
        object_locality::object_root_stays_local_with(
            function,
            root,
            root_ty,
            local_object_args,
            |value| {
                provenance
                    .exact_projection(value)
                    .is_some_and(|projection| {
                        projection.root_value == root && projection.slice == root_slice
                    })
            },
            true,
        )
    }

    fn collect_return_root_slices(
        &self,
        function: &Function,
        out_elem_ty: Type,
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

        root_slices
    }

    fn rewrite_function(&self, function: &mut Function, plan: &FuncPlan) {
        self.prepend_out_arg(function, plan.out_ty);
        function
            .dfg
            .change_to_alias(plan.root_value, function.arg_values[0]);
        function.layout.remove_inst(plan.root_alloc_inst);
        function.erase_inst(plan.root_alloc_inst);
        self.rewrite_returns(function);
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

    fn rewrite_calls(&self, function: &mut Function, plans: &FxHashMap<FuncRef, FuncPlan>) -> bool {
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
                self.rewrite_call(function, inst, &call, plan);
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
    ) {
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
        cursor.set_location(CursorLocation::At(out_alloc));

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
