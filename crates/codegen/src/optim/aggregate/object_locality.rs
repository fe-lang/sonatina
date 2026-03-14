use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    Function, Module, Type, ValueId,
    inst::{cast, control_flow, data, downcast},
    module::{FuncRef, ModuleCtx},
};
use std::ops::ControlFlow;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RootInit {
    UndefFresh,
    LoadLiveIn,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LocalObjectArgInfo {
    pub init: RootInit,
    pub fresh_result_out: bool,
}

pub(crate) type LocalObjectArgMap = FxHashMap<FuncRef, FxHashMap<usize, LocalObjectArgInfo>>;
pub(crate) type LocalObjectArgs = FxHashMap<FuncRef, FxHashSet<usize>>;

pub(crate) enum SpecialObjectUse<'a> {
    MaterializeStack(Option<ValueId>),
    MaterializeHeap,
    Call {
        value: ValueId,
        call: &'a control_flow::Call,
    },
    Return {
        value: ValueId,
        ret: &'a control_flow::Return,
    },
    Unknown,
}

// This walks the full module and must run before any `func_store.modify(...)` loop.
pub(crate) fn collect_local_object_arg_info(module: &Module) -> LocalObjectArgMap {
    let mut local_object_args = LocalObjectArgMap::default();

    loop {
        let mut changed = false;

        for func in module.funcs() {
            let Some(sig) = module.ctx.get_sig(func) else {
                continue;
            };
            if !sig.linkage().has_definition() {
                continue;
            }

            for (idx, &root_ty) in sig.args().iter().enumerate() {
                if !root_ty.is_obj_ref(&module.ctx)
                    || local_object_args
                        .get(&func)
                        .is_some_and(|local_args| local_args.contains_key(&idx))
                {
                    continue;
                }

                let stays_local = module.func_store.view(func, |function| {
                    let Some(&root) = function.arg_values.get(idx) else {
                        return false;
                    };
                    function.dfg.value_ty(root) == root_ty
                        && object_root_stays_local(
                            function,
                            root,
                            root_ty,
                            &local_object_args,
                            false,
                        )
                });
                if stays_local {
                    local_object_args.entry(func).or_default().insert(
                        idx,
                        LocalObjectArgInfo {
                            init: RootInit::LoadLiveIn,
                            fresh_result_out: false,
                        },
                    );
                    changed = true;
                }
            }
        }

        if !changed {
            return local_object_args;
        }
    }
}

pub(crate) fn collect_local_object_args(module: &Module) -> LocalObjectArgs {
    info_to_local_object_args(&collect_local_object_arg_info(module))
}

pub(crate) fn info_to_local_object_args(local_object_args: &LocalObjectArgMap) -> LocalObjectArgs {
    local_object_args
        .iter()
        .map(|(&func, args)| (func, args.keys().copied().collect()))
        .collect()
}

pub(crate) fn merge_local_object_arg_info(
    local_object_args: &mut LocalObjectArgMap,
    extra: &LocalObjectArgMap,
) {
    for (&func, args) in extra {
        local_object_args
            .entry(func)
            .or_default()
            .extend(args.iter().map(|(&idx, &info)| (idx, info)));
    }
}

pub(crate) fn call_passes_object_to_local_args(
    ctx: &ModuleCtx,
    call: &control_flow::Call,
    value: ValueId,
    value_ty: Type,
    local_object_args: &LocalObjectArgs,
) -> bool {
    let Some(sig) = ctx.get_sig(*call.callee()) else {
        return false;
    };
    let Some(local_args) = local_object_args.get(call.callee()) else {
        return false;
    };

    let mut saw_value = false;
    for (idx, &arg) in call.args().iter().enumerate() {
        if arg != value {
            continue;
        }
        saw_value = true;
        if sig.args().get(idx) != Some(&value_ty) || !local_args.contains(&idx) {
            return false;
        }
    }

    saw_value
}

fn call_passes_object_to_local_arg_info(
    ctx: &ModuleCtx,
    call: &control_flow::Call,
    value: ValueId,
    value_ty: Type,
    local_object_args: &LocalObjectArgMap,
) -> bool {
    let Some(sig) = ctx.get_sig(*call.callee()) else {
        return false;
    };
    let Some(local_args) = local_object_args.get(call.callee()) else {
        return false;
    };

    let mut saw_value = false;
    for (idx, &arg) in call.args().iter().enumerate() {
        if arg != value {
            continue;
        }
        saw_value = true;
        if sig.args().get(idx) != Some(&value_ty) || !local_args.contains_key(&idx) {
            return false;
        }
    }

    saw_value
}

pub(crate) fn object_root_stays_local(
    function: &Function,
    root: ValueId,
    root_ty: Type,
    local_object_args: &LocalObjectArgMap,
    allow_return_root: bool,
) -> bool {
    object_root_stays_local_with(
        function,
        root,
        root_ty,
        local_object_args,
        |value| value == root,
        allow_return_root,
    )
}

pub(crate) fn object_root_stays_local_with(
    function: &Function,
    root: ValueId,
    root_ty: Type,
    local_object_args: &LocalObjectArgMap,
    mut is_allowed_root_value: impl FnMut(ValueId) -> bool,
    allow_return_root: bool,
) -> bool {
    walk_object_root_uses(function, root, |special| match special {
        SpecialObjectUse::MaterializeStack(Some(ptr)) if raw_pointer_stays_local(function, ptr) => {
            ControlFlow::Continue(())
        }
        SpecialObjectUse::Return { value, ret }
            if allow_return_root
                && is_allowed_root_value(value)
                && ret.returns_single()
                && ret.arg() == Some(&value) =>
        {
            ControlFlow::Continue(())
        }
        SpecialObjectUse::Call { value, call }
            if is_allowed_root_value(value)
                && call_passes_object_to_local_arg_info(
                    function.ctx(),
                    call,
                    value,
                    root_ty,
                    local_object_args,
                ) =>
        {
            ControlFlow::Continue(())
        }
        _ => ControlFlow::Break(()),
    })
    .is_none()
}

pub(crate) fn raw_pointer_stays_local(function: &Function, root: ValueId) -> bool {
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

            if let Some(gep) = downcast::<&data::Gep>(function.inst_set(), function.dfg.inst(user))
                && gep.values().first() == Some(&value)
            {
                if let Some(result) = function.dfg.inst_result(user) {
                    worklist.push(result);
                }
                continue;
            }

            if let Some(bitcast) =
                downcast::<&cast::Bitcast>(function.inst_set(), function.dfg.inst(user))
                && *bitcast.from() == value
            {
                if let Some(result) = function.dfg.inst_result(user) {
                    worklist.push(result);
                }
                continue;
            }

            if let Some(phi) =
                downcast::<&control_flow::Phi>(function.inst_set(), function.dfg.inst(user))
                && phi.args().iter().any(|(arg, _)| *arg == value)
            {
                if let Some(result) = function.dfg.inst_result(user) {
                    worklist.push(result);
                }
                continue;
            }

            if let Some(load) =
                downcast::<&data::Mload>(function.inst_set(), function.dfg.inst(user))
                && *load.addr() == value
            {
                continue;
            }

            if let Some(store) =
                downcast::<&data::Mstore>(function.inst_set(), function.dfg.inst(user))
            {
                if *store.addr() == value {
                    continue;
                }
                if *store.value() == value {
                    return false;
                }
            }

            if downcast::<&control_flow::Call>(function.inst_set(), function.dfg.inst(user))
                .is_some()
                || downcast::<&control_flow::Return>(function.inst_set(), function.dfg.inst(user))
                    .is_some_and(|ret| ret.args().iter().any(|arg| *arg == value))
                || downcast::<&cast::PtrToInt>(function.inst_set(), function.dfg.inst(user))
                    .is_some_and(|ptr_to_int| *ptr_to_int.from() == value)
            {
                return false;
            }

            return false;
        }
    }

    true
}

pub(crate) fn walk_object_root_uses<T>(
    function: &Function,
    root: ValueId,
    mut on_special: impl FnMut(SpecialObjectUse<'_>) -> ControlFlow<T>,
) -> Option<T> {
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

            if let Some(phi) =
                downcast::<&control_flow::Phi>(function.inst_set(), function.dfg.inst(user))
                && phi.args().iter().any(|(arg, _)| *arg == value)
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

            if let Some(mat_stack) =
                downcast::<&data::ObjMaterializeStack>(function.inst_set(), function.dfg.inst(user))
                && *mat_stack.object() == value
            {
                if let ControlFlow::Break(result) = on_special(SpecialObjectUse::MaterializeStack(
                    function.dfg.inst_result(user),
                )) {
                    return Some(result);
                }
                continue;
            }

            if let Some(mat_heap) =
                downcast::<&data::ObjMaterializeHeap>(function.inst_set(), function.dfg.inst(user))
                && *mat_heap.object() == value
            {
                if let ControlFlow::Break(result) = on_special(SpecialObjectUse::MaterializeHeap) {
                    return Some(result);
                }
                continue;
            }

            if let Some(call) =
                downcast::<&control_flow::Call>(function.inst_set(), function.dfg.inst(user))
                && call.args().contains(&value)
            {
                if let ControlFlow::Break(result) =
                    on_special(SpecialObjectUse::Call { value, call })
                {
                    return Some(result);
                }
                continue;
            }

            if let Some(ret) =
                downcast::<&control_flow::Return>(function.inst_set(), function.dfg.inst(user))
                && ret.args().iter().copied().any(|arg| arg == value)
            {
                if let ControlFlow::Break(result) =
                    on_special(SpecialObjectUse::Return { value, ret })
                {
                    return Some(result);
                }
                continue;
            }

            if let ControlFlow::Break(result) = on_special(SpecialObjectUse::Unknown) {
                return Some(result);
            }
        }
    }

    None
}
