use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    Function, InstId, Module, Type, Value, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{control_flow, data, downcast},
    module::{FuncRef, ModuleCtx},
    types::CompoundType,
};

use super::private_abi::{self, PrivateAbiPlan};

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
        let entry_funcs = private_abi::collect_entry_funcs(module);
        let mut changed = false;

        loop {
            let in_place_helpers = collect_in_place_object_helpers(module);
            let mut plans = self.collect_plans(module, &entry_funcs, &in_place_helpers);
            private_abi::retain_higher_order_safe_plans(module, &mut plans);
            if plans.is_empty() {
                return changed;
            }
            changed = true;
            let old_sigs = private_abi::rewrite_declared_signatures(module, &plans);

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
        entry_funcs: &FxHashSet<FuncRef>,
        in_place_helpers: &FxHashSet<FuncRef>,
    ) -> FxHashMap<FuncRef, FuncPlan> {
        let mut plans = FxHashMap::default();

        for func in module.funcs() {
            if entry_funcs.contains(&func) {
                continue;
            }

            let Some(sig) = module.ctx.get_sig(func) else {
                continue;
            };
            if !sig.linkage().is_private()
                || !sig.linkage().has_definition()
                || !sig.returns_single()
            {
                continue;
            }

            let Some(out_ty) = sig.single_ret_ty() else {
                continue;
            };
            let Some(out_elem_ty) = objref_element_ty(&module.ctx, out_ty) else {
                continue;
            };

            let Some((root_alloc_inst, root_value)) = module.func_store.view(func, |function| {
                self.analyze_return_root(function, out_ty, in_place_helpers)
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
        in_place_helpers: &FxHashSet<FuncRef>,
    ) -> Option<(InstId, ValueId)> {
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

                if let Some(existing) = return_root {
                    if existing != root {
                        return None;
                    }
                } else {
                    return_root = Some(root);
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
            || !self.root_is_rewritable(function, root_value, out_ty, in_place_helpers)
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
        in_place_helpers: &FxHashSet<FuncRef>,
    ) -> bool {
        object_root_stays_local(function, root, root_ty, in_place_helpers, true)
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

pub(crate) fn collect_in_place_object_helpers(module: &Module) -> FxHashSet<FuncRef> {
    let mut helpers = FxHashSet::default();

    loop {
        let mut changed = false;

        for func in module.funcs() {
            if helpers.contains(&func) || !is_in_place_object_helper(module, func, &helpers) {
                continue;
            }
            helpers.insert(func);
            changed = true;
        }

        if !changed {
            return helpers;
        }
    }
}

pub(crate) fn call_passes_object_to_in_place_helper(
    ctx: &ModuleCtx,
    call: &control_flow::Call,
    value: ValueId,
    value_ty: Type,
    helpers: &FxHashSet<FuncRef>,
) -> bool {
    helpers.contains(call.callee())
        && call.args().first() == Some(&value)
        && call.args().iter().filter(|&&arg| arg == value).count() == 1
        && ctx
            .get_sig(*call.callee())
            .is_some_and(|sig| sig.returns_unit() && sig.args().first() == Some(&value_ty))
}

fn is_in_place_object_helper(module: &Module, func: FuncRef, helpers: &FxHashSet<FuncRef>) -> bool {
    let Some(sig) = module.ctx.get_sig(func) else {
        return false;
    };
    let Some(&root_ty) = sig.args().first() else {
        return false;
    };
    if !sig.linkage().has_definition() || !sig.returns_unit() || !root_ty.is_obj_ref(&module.ctx) {
        return false;
    }

    module.func_store.view(func, |function| {
        let Some(&root) = function.arg_values.first() else {
            return false;
        };
        function.dfg.value_ty(root) == root_ty
            && object_root_stays_local(function, root, root_ty, helpers, false)
    })
}

fn object_root_stays_local(
    function: &Function,
    root: ValueId,
    root_ty: Type,
    in_place_helpers: &FxHashSet<FuncRef>,
    allow_return_root: bool,
) -> bool {
    let mut worklist = vec![root];
    let mut seen = FxHashSet::default();

    while let Some(value) = worklist.pop() {
        if !seen.insert(value) {
            continue;
        }

        for &user in function.dfg.users(value) {
            if !function.layout.is_inst_inserted(user) {
                continue;
            }

            if let Some(proj) =
                downcast::<&data::ObjProj>(function.inst_set(), function.dfg.inst(user))
                && proj.values().first() == Some(&value)
            {
                if let Some(result) = function.dfg.inst_result(user) {
                    worklist.push(result);
                }
                continue;
            }

            if let Some(index) =
                downcast::<&data::ObjIndex>(function.inst_set(), function.dfg.inst(user))
                && *index.object() == value
            {
                if let Some(result) = function.dfg.inst_result(user) {
                    worklist.push(result);
                }
                continue;
            }

            if let Some(load) =
                downcast::<&data::ObjLoad>(function.inst_set(), function.dfg.inst(user))
                && *load.object() == value
            {
                continue;
            }

            if let Some(store) =
                downcast::<&data::ObjStore>(function.inst_set(), function.dfg.inst(user))
                && *store.object() == value
            {
                continue;
            }

            if let Some(ret) =
                downcast::<&control_flow::Return>(function.inst_set(), function.dfg.inst(user))
                && allow_return_root
                && value == root
                && ret.returns_single()
                && ret.arg() == Some(&value)
            {
                continue;
            }

            if let Some(call) =
                downcast::<&control_flow::Call>(function.inst_set(), function.dfg.inst(user))
                && function.dfg.inst_results(user).is_empty()
                && value == root
                && call_passes_object_to_in_place_helper(
                    function.ctx(),
                    call,
                    value,
                    root_ty,
                    in_place_helpers,
                )
            {
                continue;
            }

            return false;
        }
    }

    true
}

fn objref_element_ty(ctx: &ModuleCtx, ty: Type) -> Option<Type> {
    let CompoundType::ObjRef(elem) = ty.resolve_compound(ctx)? else {
        return None;
    };
    Some(elem)
}
