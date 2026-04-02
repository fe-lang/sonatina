use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    Function, Signature, Type, Value,
    inst::{data, downcast},
    module::{FuncRef, Module, ModuleCtx},
    types::{CompoundType, CompoundTypeRef, StructData},
    visitor::VisitorMut,
};

pub(crate) trait SignatureRewritePlan {
    fn new_arg_tys(&self) -> &[Type];
    fn new_ret_tys(&self) -> &[Type];

    fn is_higher_order_compatible(&self, other: &Self) -> bool {
        self.new_arg_tys() == other.new_arg_tys() && self.new_ret_tys() == other.new_ret_tys()
    }
}

pub(crate) fn is_owned_private_signature_func(sig: &Signature) -> bool {
    sig.linkage().is_private()
}

pub(crate) fn rewrite_declared_signatures<P: SignatureRewritePlan>(
    module: &Module,
    plans: &FxHashMap<FuncRef, P>,
) -> FxHashMap<FuncRef, Signature> {
    let mut old_sigs = FxHashMap::default();

    for (&func, plan) in plans {
        let sig = module
            .ctx
            .get_sig(func)
            .expect("planned function should have signature");
        old_sigs.insert(func, sig.clone());
        module
            .ctx
            .declared_funcs
            .get_mut(&func)
            .expect("planned function signature should exist")
            .clone_from(&Signature::new(
                sig.name(),
                sig.linkage(),
                plan.new_arg_tys(),
                plan.new_ret_tys(),
            ));
    }

    old_sigs
}

pub(crate) fn retain_higher_order_safe_plans<P: SignatureRewritePlan>(
    module: &Module,
    plans: &mut FxHashMap<FuncRef, P>,
) {
    if plans.is_empty() {
        return;
    }

    let ctx = &module.ctx;
    let planned_types = collect_planned_func_types(ctx, plans);
    let live_get_fn_uses = collect_live_get_function_ptr_uses(module, &planned_types);
    if live_get_fn_uses.is_empty() {
        return;
    }

    let exposed_types = collect_non_owned_exposed_func_types(module, &planned_types);
    let class_info = collect_rewrite_class_info(ctx, plans);
    let mut blocked_types = FxHashSet::default();

    for old_ty in live_get_fn_uses {
        let Some(info) = class_info.get(&old_ty) else {
            continue;
        };
        if !info.fully_rewritten || !info.consistent_new_shape || exposed_types.contains(&old_ty) {
            blocked_types.insert(old_ty);
        }
    }

    if blocked_types.is_empty() {
        return;
    }

    plans.retain(|&func, _| {
        let Some(old_sig) = ctx.get_sig(func) else {
            return false;
        };
        !blocked_types.contains(&make_func_ty(ctx, old_sig.args(), old_sig.ret_tys()))
    });
}

pub(crate) fn propagate_signature_rewrite_types(
    module: &Module,
    old_sigs: &FxHashMap<FuncRef, Signature>,
) {
    if old_sigs.is_empty() {
        return;
    }

    let mut types = SignatureRewriteTypeRewriter::new(module, old_sigs);
    rewrite_signature_types(module, old_sigs, &mut types);
    rewrite_global_types(module, &mut types);

    for func in module.funcs() {
        module.func_store.modify(func, |function| {
            rewrite_function_types(function, old_sigs, &mut types);
        });
    }
}

#[derive(Default)]
struct SignatureRewriteTypeRewriter {
    sig_func_map: FxHashMap<CompoundTypeRef, FuncRef>,
    compound_map: FxHashMap<CompoundTypeRef, CompoundTypeRef>,
}

impl SignatureRewriteTypeRewriter {
    fn new(module: &Module, old_sigs: &FxHashMap<FuncRef, Signature>) -> Self {
        Self {
            sig_func_map: collect_safe_structural_rewrite_classes(&module.ctx, old_sigs),
            compound_map: FxHashMap::default(),
        }
    }

    fn rewrite_type(&mut self, ctx: &ModuleCtx, ty: Type) -> Type {
        match ty {
            Type::Compound(compound) => Type::Compound(self.rewrite_compound(ctx, compound)),
            _ => ty,
        }
    }

    fn rewrite_compound(&mut self, ctx: &ModuleCtx, compound: CompoundTypeRef) -> CompoundTypeRef {
        if let Some(&mapped) = self.compound_map.get(&compound) {
            return mapped;
        }

        if let Some(&func) = self.sig_func_map.get(&compound) {
            self.compound_map.insert(compound, compound);
            let mapped = ctx
                .get_sig(func)
                .map(|sig| {
                    let args: Vec<_> = sig
                        .args()
                        .iter()
                        .map(|&arg| self.rewrite_type(ctx, arg))
                        .collect();
                    let ret_tys: Vec<_> = sig
                        .ret_tys()
                        .iter()
                        .map(|&ret| self.rewrite_type(ctx, ret))
                        .collect();
                    make_func_ty(ctx, &args, &ret_tys)
                })
                .unwrap_or(compound);
            self.compound_map.insert(compound, mapped);
            return mapped;
        }

        let current = ctx.with_ty_store(|store| store.resolve_compound(compound).clone());
        self.compound_map.insert(compound, compound);

        match current {
            CompoundType::Array { elem, len } => {
                let elem = self.rewrite_type(ctx, elem);
                let mapped = ctx.with_ty_store_mut(|store| match store.make_array(elem, len) {
                    Type::Compound(mapped) => mapped,
                    _ => unreachable!(),
                });
                self.compound_map.insert(compound, mapped);
                mapped
            }
            CompoundType::Ptr(elem) => {
                let elem = self.rewrite_type(ctx, elem);
                let mapped = ctx.with_ty_store_mut(|store| match store.make_ptr(elem) {
                    Type::Compound(mapped) => mapped,
                    _ => unreachable!(),
                });
                self.compound_map.insert(compound, mapped);
                mapped
            }
            CompoundType::ObjRef(elem) => {
                let elem = self.rewrite_type(ctx, elem);
                let mapped = ctx.with_ty_store_mut(|store| match store.make_obj_ref(elem) {
                    Type::Compound(mapped) => mapped,
                    _ => unreachable!(),
                });
                self.compound_map.insert(compound, mapped);
                mapped
            }
            CompoundType::ConstRef(elem) => {
                let elem = self.rewrite_type(ctx, elem);
                let mapped = ctx.with_ty_store_mut(|store| match store.make_const_ref(elem) {
                    Type::Compound(mapped) => mapped,
                    _ => unreachable!(),
                });
                self.compound_map.insert(compound, mapped);
                mapped
            }
            CompoundType::Enum(data) => {
                let new_variants: Vec<_> = data
                    .variants
                    .iter()
                    .map(|variant| sonatina_ir::types::VariantData {
                        name: variant.name.clone(),
                        explicit_discriminant: variant.explicit_discriminant,
                        fields: variant
                            .fields
                            .iter()
                            .map(|&field| self.rewrite_type(ctx, field))
                            .collect(),
                    })
                    .collect();
                if new_variants != data.variants {
                    ctx.with_ty_store_mut(|store| {
                        store.update_enum_variants(&data.name, &new_variants, data.repr)
                    });
                }
                compound
            }
            CompoundType::Func { args, ret_tys } => {
                let args: Vec<_> = args
                    .iter()
                    .map(|&arg| self.rewrite_type(ctx, arg))
                    .collect();
                let ret_tys: Vec<_> = ret_tys
                    .iter()
                    .map(|&ret| self.rewrite_type(ctx, ret))
                    .collect();
                let mapped =
                    ctx.with_ty_store_mut(|store| match store.make_func(&args, &ret_tys) {
                        Type::Compound(mapped) => mapped,
                        _ => unreachable!(),
                    });
                self.compound_map.insert(compound, mapped);
                mapped
            }
            CompoundType::Struct(StructData { name, fields, .. }) => {
                let fields: Vec<_> = fields
                    .iter()
                    .map(|&field| self.rewrite_type(ctx, field))
                    .collect();
                ctx.with_ty_store_mut(|store| store.update_struct_fields(&name, &fields));
                compound
            }
        }
    }
}

fn make_func_ty(ctx: &ModuleCtx, args: &[Type], ret_tys: &[Type]) -> CompoundTypeRef {
    let Type::Compound(cmpd) = ctx.with_ty_store_mut(|store| store.make_func(args, ret_tys)) else {
        unreachable!();
    };
    cmpd
}

fn rewrite_signature_types(
    module: &Module,
    old_sigs: &FxHashMap<FuncRef, Signature>,
    types: &mut SignatureRewriteTypeRewriter,
) {
    let funcs: Vec<_> = module
        .ctx
        .declared_funcs
        .iter()
        .map(|entry| *entry.key())
        .collect();

    for func in funcs {
        let Some(sig) = module.ctx.get_sig(func) else {
            continue;
        };
        if !old_sigs.contains_key(&func) && !is_owned_private_signature_func(&sig) {
            continue;
        }

        let args: Vec<_> = sig
            .args()
            .iter()
            .map(|&arg| types.rewrite_type(&module.ctx, arg))
            .collect();
        let ret_tys: Vec<_> = sig
            .ret_tys()
            .iter()
            .map(|&ret| types.rewrite_type(&module.ctx, ret))
            .collect();
        if args.as_slice() == sig.args() && ret_tys.as_slice() == sig.ret_tys() {
            continue;
        }

        module
            .ctx
            .declared_funcs
            .get_mut(&func)
            .expect("declared function should exist")
            .clone_from(&Signature::new(sig.name(), sig.linkage(), &args, &ret_tys));
    }
}

fn rewrite_global_types(module: &Module, types: &mut SignatureRewriteTypeRewriter) {
    let globals: Vec<_> = module
        .ctx
        .with_gv_store(|store| store.all_gv_refs().collect());

    module.ctx.with_gv_store_mut(|store| {
        for gv in globals {
            let Some(gv_data) = store.get(gv).cloned() else {
                continue;
            };
            if !gv_data.linkage.is_private() {
                continue;
            }
            let old_ty = gv_data.ty;
            let new_ty = types.rewrite_type(&module.ctx, old_ty);
            if new_ty != old_ty {
                store.update_ty(gv, new_ty);
            }
        }
    });
}

fn rewrite_function_types(
    function: &mut Function,
    old_sigs: &FxHashMap<FuncRef, Signature>,
    types: &mut SignatureRewriteTypeRewriter,
) {
    let value_ids: Vec<_> = function.dfg.value_ids().collect();
    for value_id in value_ids {
        let old_ty = function.dfg.value_ty(value_id);
        let new_ty = direct_get_function_ptr_ty(function, value_id, old_sigs)
            .unwrap_or_else(|| types.rewrite_type(function.ctx(), old_ty));
        if new_ty == old_ty {
            continue;
        }

        function.dfg.values[value_id] = match function.dfg.value(value_id).clone() {
            Value::Immediate { imm, .. } => Value::Immediate { imm, ty: new_ty },
            Value::Inst {
                inst, result_idx, ..
            } => Value::Inst {
                inst,
                result_idx,
                ty: new_ty,
            },
            Value::Arg { idx, .. } => Value::Arg { idx, ty: new_ty },
            Value::Global { gv, .. } => Value::Global { gv, ty: new_ty },
            Value::Undef { .. } => Value::Undef { ty: new_ty },
        };
    }

    struct TypeVisitor<'a> {
        ctx: ModuleCtx,
        types: &'a mut SignatureRewriteTypeRewriter,
    }

    impl VisitorMut for TypeVisitor<'_> {
        fn visit_ty(&mut self, item: &mut Type) {
            *item = self.types.rewrite_type(&self.ctx, *item);
        }
    }

    let mut visitor = TypeVisitor {
        ctx: function.ctx().clone(),
        types,
    };
    let blocks: Vec<_> = function.layout.iter_block().collect();
    for block in blocks {
        let insts: Vec<_> = function.layout.iter_inst(block).collect();
        for inst in insts {
            if function.layout.is_inst_inserted(inst) {
                function.dfg.inst_mut(inst).accept_mut(&mut visitor);
            }
        }
    }
}

#[derive(Default)]
struct RewriteClassInfo {
    funcs: Vec<FuncRef>,
    fully_rewritten: bool,
    consistent_new_shape: bool,
    representative: Option<FuncRef>,
}

fn collect_safe_structural_rewrite_classes(
    ctx: &ModuleCtx,
    old_sigs: &FxHashMap<FuncRef, Signature>,
) -> FxHashMap<CompoundTypeRef, FuncRef> {
    let mut safe = FxHashMap::default();
    for (old_ty, info) in collect_rewrite_class_info_from_old_sigs(ctx, old_sigs) {
        if info.fully_rewritten
            && info.consistent_new_shape
            && let Some(func) = info.representative
        {
            safe.insert(old_ty, func);
        }
    }
    safe
}

fn collect_rewrite_class_info<P: SignatureRewritePlan>(
    ctx: &ModuleCtx,
    plans: &FxHashMap<FuncRef, P>,
) -> FxHashMap<CompoundTypeRef, RewriteClassInfo> {
    let mut info: FxHashMap<CompoundTypeRef, RewriteClassInfo> = FxHashMap::default();

    for entry in ctx.declared_funcs.iter() {
        let func = *entry.key();
        let sig = entry.value();
        let old_ty = make_func_ty(ctx, sig.args(), sig.ret_tys());
        info.entry(old_ty).or_default().funcs.push(func);
    }

    for class in info.values_mut() {
        class.funcs.sort_unstable_by_key(|func| func.as_u32());
        class.fully_rewritten = class.funcs.iter().all(|func| plans.contains_key(func));
        if !class.fully_rewritten {
            continue;
        }

        let mut reference = None::<FuncRef>;
        class.consistent_new_shape = true;
        for &func in &class.funcs {
            let Some(plan) = plans.get(&func) else {
                class.consistent_new_shape = false;
                break;
            };

            if let Some(reference_func) = reference {
                let reference_plan = plans
                    .get(&reference_func)
                    .expect("reference rewrite plan should exist");
                if !reference_plan.is_higher_order_compatible(plan) {
                    class.consistent_new_shape = false;
                    break;
                }
            } else {
                reference = Some(func);
            }
        }

        if class.consistent_new_shape {
            class.representative = reference;
        }
    }

    info
}

fn collect_rewrite_class_info_from_old_sigs(
    ctx: &ModuleCtx,
    old_sigs: &FxHashMap<FuncRef, Signature>,
) -> FxHashMap<CompoundTypeRef, RewriteClassInfo> {
    let mut info: FxHashMap<CompoundTypeRef, RewriteClassInfo> = FxHashMap::default();

    for entry in ctx.declared_funcs.iter() {
        let func = *entry.key();
        let old_sig = old_sigs.get(&func).unwrap_or_else(|| entry.value());
        let old_ty = make_func_ty(ctx, old_sig.args(), old_sig.ret_tys());
        info.entry(old_ty).or_default().funcs.push(func);
    }

    for class in info.values_mut() {
        class.funcs.sort_unstable_by_key(|func| func.as_u32());
        class.fully_rewritten = class.funcs.iter().all(|func| old_sigs.contains_key(func));
        if !class.fully_rewritten {
            continue;
        }

        let mut reference = None::<(Vec<Type>, Vec<Type>, FuncRef)>;
        class.consistent_new_shape = true;
        for &func in &class.funcs {
            let Some(sig) = ctx.get_sig(func) else {
                class.consistent_new_shape = false;
                break;
            };

            if let Some((ref_args, ref_rets, _)) = &reference {
                if ref_args.as_slice() != sig.args() || ref_rets.as_slice() != sig.ret_tys() {
                    class.consistent_new_shape = false;
                    break;
                }
            } else {
                reference = Some((sig.args().to_vec(), sig.ret_tys().to_vec(), func));
            }
        }

        if class.consistent_new_shape {
            class.representative = reference.map(|(_, _, func)| func);
        }
    }

    info
}

fn collect_planned_func_types<P: SignatureRewritePlan>(
    ctx: &ModuleCtx,
    plans: &FxHashMap<FuncRef, P>,
) -> FxHashSet<CompoundTypeRef> {
    plans
        .keys()
        .filter_map(|&func| {
            ctx.get_sig(func)
                .map(|sig| make_func_ty(ctx, sig.args(), sig.ret_tys()))
        })
        .collect()
}

fn collect_live_get_function_ptr_uses(
    module: &Module,
    planned_types: &FxHashSet<CompoundTypeRef>,
) -> FxHashSet<CompoundTypeRef> {
    let mut live = FxHashSet::default();

    for func in module.funcs() {
        module.func_store.view(func, |function| {
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    let Some(get_fn) = downcast::<&data::GetFunctionPtr>(
                        function.inst_set(),
                        function.dfg.inst(inst),
                    ) else {
                        continue;
                    };
                    let Some(sig) = module.ctx.get_sig(*get_fn.func()) else {
                        continue;
                    };
                    let old_ty = make_func_ty(&module.ctx, sig.args(), sig.ret_tys());
                    if !planned_types.contains(&old_ty) {
                        continue;
                    }
                    let Some(result) = function.dfg.inst_result(inst) else {
                        continue;
                    };
                    if function.dfg.users(result).next().is_some() {
                        live.insert(old_ty);
                    }
                }
            }
        });
    }

    live
}

fn collect_non_owned_exposed_func_types(
    module: &Module,
    planned_types: &FxHashSet<CompoundTypeRef>,
) -> FxHashSet<CompoundTypeRef> {
    let mut exposed = FxHashSet::default();

    for entry in module.ctx.declared_funcs.iter() {
        let sig = entry.value();
        if is_owned_private_signature_func(sig) {
            continue;
        }
        for &ty in sig.args().iter().chain(sig.ret_tys().iter()) {
            collect_nested_planned_func_types(&module.ctx, ty, planned_types, &mut exposed);
        }
    }

    module.ctx.with_gv_store(|store| {
        for gv in store.all_gv_refs() {
            let Some(gv_data) = store.get(gv) else {
                continue;
            };
            if gv_data.linkage.is_private() {
                continue;
            }
            collect_nested_planned_func_types(&module.ctx, gv_data.ty, planned_types, &mut exposed);
        }
    });

    exposed
}

fn collect_nested_planned_func_types(
    ctx: &ModuleCtx,
    ty: Type,
    planned_types: &FxHashSet<CompoundTypeRef>,
    found: &mut FxHashSet<CompoundTypeRef>,
) {
    let mut seen = FxHashSet::default();
    let mut stack = vec![ty];

    while let Some(current_ty) = stack.pop() {
        let Type::Compound(cmpd_ref) = current_ty else {
            continue;
        };
        if !seen.insert(cmpd_ref) {
            continue;
        }
        if planned_types.contains(&cmpd_ref) {
            found.insert(cmpd_ref);
        }

        let Some(cmpd) = ctx.with_ty_store(|store| store.get_compound(cmpd_ref).cloned()) else {
            continue;
        };
        match cmpd {
            CompoundType::Array { elem, .. }
            | CompoundType::Ptr(elem)
            | CompoundType::ConstRef(elem)
            | CompoundType::ObjRef(elem) => {
                stack.push(elem);
            }
            CompoundType::Enum(data) => stack.extend(
                data.variants
                    .into_iter()
                    .flat_map(|variant| variant.fields.into_iter()),
            ),
            CompoundType::Struct(data) => stack.extend(data.fields),
            CompoundType::Func { args, ret_tys } => {
                stack.extend(args);
                stack.extend(ret_tys);
            }
        }
    }
}

fn direct_get_function_ptr_ty(
    function: &Function,
    value: sonatina_ir::ValueId,
    old_sigs: &FxHashMap<FuncRef, Signature>,
) -> Option<Type> {
    let Value::Inst { inst, .. } = function.dfg.value(value) else {
        return None;
    };
    let get_fn = downcast::<&data::GetFunctionPtr>(function.inst_set(), function.dfg.inst(*inst))?;
    old_sigs.contains_key(get_fn.func()).then(|| {
        function
            .ctx()
            .func_sig(*get_fn.func(), |sig| sig.func_ptr_type(function.ctx()))
    })
}
