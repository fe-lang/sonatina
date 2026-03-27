use rustc_hash::FxHashMap;
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    Function, I256, Immediate, Module, Type, Value, ValueId,
    inst::{data, downcast, evm},
    module::{FuncRef, ModuleCtx},
    types::{CompoundType, CompoundTypeRef, StructData},
    visitor::VisitorMut,
};

use super::{
    object_locality::{self, LocalObjectArgs, SpecialObjectUse},
    private_abi::{self, PrivateAbiPlan},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Materialization {
    Stack,
    Heap,
}

#[derive(Clone)]
struct FuncPlan {
    new_arg_tys: SmallVec<[Type; 8]>,
    new_ret_tys: SmallVec<[Type; 8]>,
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
pub struct ObjectLowerToMemory;

impl ObjectLowerToMemory {
    pub fn run(&mut self, module: &Module) -> bool {
        let local_object_args = object_locality::collect_local_object_args(module);
        let mut type_lowerer = ObjRefTypeLowerer::default();
        let mut plans = self.collect_plans(module, &mut type_lowerer);
        private_abi::retain_higher_order_safe_plans(module, &mut plans);
        let mut changed = type_lowerer.changed || !plans.is_empty();
        let old_sigs = private_abi::rewrite_declared_signatures(module, &plans);
        changed |= rewrite_global_types(module, &mut type_lowerer);
        changed |= type_lowerer.changed;

        for func_ref in module.funcs() {
            changed |= module.func_store.modify(func_ref, |function| {
                self.rewrite_function(function, &local_object_args, &mut type_lowerer)
            });
            changed |= type_lowerer.changed;
        }

        private_abi::propagate_private_abi_types(module, &old_sigs);
        changed
    }

    fn collect_plans(
        &self,
        module: &Module,
        type_lowerer: &mut ObjRefTypeLowerer,
    ) -> FxHashMap<FuncRef, FuncPlan> {
        let mut plans = FxHashMap::default();

        for func in module.funcs() {
            let Some(sig) = module.ctx.get_sig(func) else {
                continue;
            };

            let new_arg_tys: SmallVec<[Type; 8]> = sig
                .args()
                .iter()
                .copied()
                .map(|ty| type_lowerer.rewrite_type(&module.ctx, ty))
                .collect();
            let new_ret_tys: SmallVec<[Type; 8]> = sig
                .ret_tys()
                .iter()
                .copied()
                .map(|ty| type_lowerer.rewrite_type(&module.ctx, ty))
                .collect();

            if new_arg_tys.as_slice() == sig.args() && new_ret_tys.as_slice() == sig.ret_tys() {
                continue;
            }

            plans.insert(
                func,
                FuncPlan {
                    new_arg_tys,
                    new_ret_tys,
                },
            );
        }

        plans
    }

    fn rewrite_function(
        &mut self,
        func: &mut Function,
        local_object_args: &LocalObjectArgs,
        type_lowerer: &mut ObjRefTypeLowerer,
    ) -> bool {
        let mut changed = self.rewrite_types(func, type_lowerer);
        let alloc_kinds = self.collect_alloc_kinds(func, local_object_args);
        if alloc_kinds.is_empty() && !has_object_lowering_work(func) {
            if changed {
                func.rebuild_users();
            }
            return changed;
        }

        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                changed |= self.rewrite_inst(func, inst, &alloc_kinds);
            }
        }

        if changed {
            func.rebuild_users();
        }
        changed
    }

    fn rewrite_types(&self, func: &mut Function, type_lowerer: &mut ObjRefTypeLowerer) -> bool {
        let mut changed = false;
        for value in func.dfg.value_ids().collect::<Vec<_>>() {
            let old_ty = func.dfg.value_ty(value);
            let new_ty = type_lowerer.rewrite_type(func.ctx(), old_ty);
            if new_ty == old_ty {
                continue;
            }

            let replacement = match func.dfg.value(value).clone() {
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
            func.dfg.values[value] = replacement;
            changed = true;
        }

        struct TypeVisitor<'a> {
            ctx: ModuleCtx,
            type_lowerer: &'a mut ObjRefTypeLowerer,
            changed: bool,
        }

        impl VisitorMut for TypeVisitor<'_> {
            fn visit_ty(&mut self, item: &mut Type) {
                let new_ty = self.type_lowerer.rewrite_type(&self.ctx, *item);
                self.changed |= new_ty != *item;
                *item = new_ty;
            }
        }

        let mut visitor = TypeVisitor {
            ctx: func.ctx().clone(),
            type_lowerer,
            changed: false,
        };
        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                if func.layout.is_inst_inserted(inst) {
                    func.dfg.inst_mut(inst).accept_mut(&mut visitor);
                }
            }
        }

        changed || visitor.changed
    }

    fn collect_alloc_kinds(
        &self,
        func: &Function,
        local_object_args: &LocalObjectArgs,
    ) -> FxHashMap<sonatina_ir::InstId, Materialization> {
        let mut alloc_kinds = FxHashMap::default();

        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                if downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst)).is_none() {
                    continue;
                }
                let Some(result) = func.dfg.inst_result(inst) else {
                    continue;
                };
                alloc_kinds.insert(
                    inst,
                    self.choose_materialization(
                        func,
                        result,
                        func.dfg.value_ty(result),
                        local_object_args,
                    ),
                );
            }
        }

        alloc_kinds
    }

    fn choose_materialization(
        &self,
        func: &Function,
        root: ValueId,
        root_value_ty: Type,
        local_object_args: &LocalObjectArgs,
    ) -> Materialization {
        let mut kind = Materialization::Stack;
        if let Some(materialization) =
            object_locality::walk_object_root_uses(func, root, |special| match special {
                SpecialObjectUse::MaterializeStack(Some(ptr))
                    if object_locality::raw_pointer_stays_local(func, ptr) =>
                {
                    std::ops::ControlFlow::Continue(())
                }
                SpecialObjectUse::MaterializeStack(_) => {
                    std::ops::ControlFlow::Break(Materialization::Heap)
                }
                SpecialObjectUse::MaterializeHeap => {
                    kind = Materialization::Heap;
                    std::ops::ControlFlow::Continue(())
                }
                SpecialObjectUse::Call { value, call }
                    if value == root
                        && object_locality::call_passes_object_to_local_args(
                            func.ctx(),
                            call,
                            value,
                            root_value_ty,
                            local_object_args,
                        ) =>
                {
                    std::ops::ControlFlow::Continue(())
                }
                _ => std::ops::ControlFlow::Break(Materialization::Heap),
            })
        {
            return materialization;
        }

        kind
    }

    fn rewrite_inst(
        &mut self,
        func: &mut Function,
        inst: sonatina_ir::InstId,
        alloc_kinds: &FxHashMap<sonatina_ir::InstId, Materialization>,
    ) -> bool {
        if let Some(obj_alloc) =
            downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            let kind = alloc_kinds
                .get(&inst)
                .copied()
                .unwrap_or(Materialization::Stack);
            match kind {
                Materialization::Stack => {
                    func.dfg.replace_inst(
                        inst,
                        Box::new(data::Alloca::new_unchecked(
                            func.inst_set(),
                            *obj_alloc.ty(),
                        )),
                    );
                }
                Materialization::Heap => {
                    let size = func
                        .ctx()
                        .size_of(*obj_alloc.ty())
                        .expect("heap object type must have a concrete size");
                    let size = func
                        .dfg
                        .make_imm_value(Immediate::I256(I256::from(size as u64)));
                    func.dfg.replace_inst(
                        inst,
                        Box::new(evm::EvmMalloc::new_unchecked(func.inst_set(), size)),
                    );
                }
            }
            return true;
        }

        if let Some(obj_proj) =
            downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            let (&base, rest) = obj_proj
                .values()
                .split_first()
                .expect("obj.proj requires a base operand");
            let zero = func.dfg.make_imm_value(0i64);
            let mut values = SmallVec::<[ValueId; 8]>::new();
            values.push(base);
            values.push(zero);
            values.extend(rest.iter().copied());
            func.dfg.replace_inst(
                inst,
                Box::new(data::Gep::new_unchecked(func.inst_set(), values)),
            );
            return true;
        }

        if let Some(obj_index) =
            downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            let zero = func.dfg.make_imm_value(0i64);
            let values = smallvec![*obj_index.object(), zero, *obj_index.index()];
            func.dfg.replace_inst(
                inst,
                Box::new(data::Gep::new_unchecked(func.inst_set(), values)),
            );
            return true;
        }

        if let Some(obj_load) =
            downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            let pointee_ty = pointer_elem_ty(func, *obj_load.object())
                .expect("obj.load requires pointer-typed operand after object lowering");
            func.dfg.replace_inst(
                inst,
                Box::new(data::Mload::new_unchecked(
                    func.inst_set(),
                    *obj_load.object(),
                    pointee_ty,
                )),
            );
            return true;
        }

        if let Some(obj_store) =
            downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            let pointee_ty = pointer_elem_ty(func, *obj_store.object())
                .expect("obj.store requires pointer-typed operand after object lowering");
            func.dfg.replace_inst(
                inst,
                Box::new(data::Mstore::new_unchecked(
                    func.inst_set(),
                    *obj_store.object(),
                    *obj_store.value(),
                    pointee_ty,
                )),
            );
            return true;
        }

        if let Some(mat_stack) =
            downcast::<&data::ObjMaterializeStack>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            return alias_and_remove_object_materialize(func, inst, *mat_stack.object());
        }

        if let Some(mat_heap) =
            downcast::<&data::ObjMaterializeHeap>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            return alias_and_remove_object_materialize(func, inst, *mat_heap.object());
        }

        if let Some(mem_alloc) =
            downcast::<&data::MemAllocDynamic>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            func.dfg.replace_inst(
                inst,
                Box::new(evm::EvmMalloc::new_unchecked(
                    func.inst_set(),
                    *mem_alloc.size(),
                )),
            );
            return true;
        }

        false
    }
}

fn alias_and_remove_object_materialize(
    func: &mut Function,
    inst: sonatina_ir::InstId,
    replacement: ValueId,
) -> bool {
    if let Some(result) = func.dfg.inst_result(inst) {
        func.dfg.change_to_alias(result, replacement);
    }
    func.layout.remove_inst(inst);
    func.erase_inst(inst);
    true
}

fn has_object_lowering_work(func: &Function) -> bool {
    for block in func.layout.iter_block() {
        for inst in func.layout.iter_inst(block) {
            if downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst)).is_some()
                || downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(inst)).is_some()
                || downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(inst)).is_some()
                || downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst)).is_some()
                || downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst)).is_some()
                || downcast::<&data::ObjMaterializeStack>(func.inst_set(), func.dfg.inst(inst))
                    .is_some()
                || downcast::<&data::ObjMaterializeHeap>(func.inst_set(), func.dfg.inst(inst))
                    .is_some()
                || downcast::<&data::MemAllocDynamic>(func.inst_set(), func.dfg.inst(inst))
                    .is_some()
            {
                return true;
            }
        }
    }

    false
}

#[derive(Default)]
struct ObjRefTypeLowerer {
    changed: bool,
    compound_map: FxHashMap<CompoundTypeRef, CompoundTypeRef>,
}

impl ObjRefTypeLowerer {
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

        let current = ctx.with_ty_store(|store| store.resolve_compound(compound).clone());
        self.compound_map.insert(compound, compound);

        let mapped = match current {
            CompoundType::Array { elem, len } => {
                let elem = self.rewrite_type(ctx, elem);
                ctx.with_ty_store_mut(|store| {
                    let Type::Compound(mapped) = store.make_array(elem, len) else {
                        unreachable!();
                    };
                    mapped
                })
            }
            CompoundType::Ptr(elem) => {
                let elem = self.rewrite_type(ctx, elem);
                ctx.with_ty_store_mut(|store| {
                    let Type::Compound(mapped) = store.make_ptr(elem) else {
                        unreachable!();
                    };
                    mapped
                })
            }
            CompoundType::ObjRef(elem) => {
                let elem = self.rewrite_type(ctx, elem);
                let mapped = ctx.with_ty_store_mut(|store| {
                    let Type::Compound(mapped) = store.make_ptr(elem) else {
                        unreachable!();
                    };
                    mapped
                });
                self.changed = true;
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
                    self.changed = true;
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
                ctx.with_ty_store_mut(|store| {
                    let Type::Compound(mapped) = store.make_func(&args, &ret_tys) else {
                        unreachable!();
                    };
                    mapped
                })
            }
            CompoundType::Struct(StructData { name, fields, .. }) => {
                let new_fields: Vec<_> = fields
                    .iter()
                    .map(|&field| self.rewrite_type(ctx, field))
                    .collect();
                if new_fields != fields {
                    ctx.with_ty_store_mut(|store| store.update_struct_fields(&name, &new_fields));
                    self.changed = true;
                }
                compound
            }
        };

        if mapped != compound {
            self.changed = true;
        }
        self.compound_map.insert(compound, mapped);
        mapped
    }
}

fn rewrite_global_types(module: &Module, type_lowerer: &mut ObjRefTypeLowerer) -> bool {
    let globals: Vec<_> = module
        .ctx
        .with_gv_store(|store| store.all_gv_refs().collect());
    let mut changed = false;

    module.ctx.with_gv_store_mut(|store| {
        for gv in globals {
            let Some(gv_data) = store.get(gv).cloned() else {
                continue;
            };
            let new_ty = type_lowerer.rewrite_type(&module.ctx, gv_data.ty);
            if new_ty != gv_data.ty {
                store.update_ty(gv, new_ty);
                changed = true;
            }
        }
    });

    changed
}

fn pointer_elem_ty(func: &Function, value: ValueId) -> Option<Type> {
    let ty = func.dfg.value_ty(value);
    func.ctx().with_ty_store(|store| store.deref(ty))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        isa::evm::{EvmBackend, PushWidthPolicy},
        object::{CompileOptions, compile_all_objects},
    };
    use rustc_hash::FxHashSet;
    use sonatina_ir::{
        Module,
        inst::{control_flow, data, evm},
        isa::evm::Evm,
    };
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};
    use sonatina_verifier::{VerificationLevel, VerifierConfig};

    fn has_nested_objref(ctx: &ModuleCtx, ty: Type) -> bool {
        let mut visited = FxHashSet::default();
        let mut worklist = vec![ty];

        while let Some(current) = worklist.pop() {
            let Type::Compound(compound) = current else {
                continue;
            };
            if !visited.insert(compound) {
                continue;
            }

            match ctx.with_ty_store(|store| store.resolve_compound(compound).clone()) {
                CompoundType::Array { elem, .. } | CompoundType::Ptr(elem) => worklist.push(elem),
                CompoundType::ObjRef(_) => return true,
                CompoundType::Struct(data) => worklist.extend(data.fields),
                CompoundType::Enum(data) => {
                    for variant in data.variants {
                        worklist.extend(variant.fields);
                    }
                }
                CompoundType::Func { args, ret_tys } => {
                    worklist.extend(args);
                    worklist.extend(ret_tys);
                }
            }
        }

        false
    }

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

    fn test_backend() -> EvmBackend {
        let triple = TargetTriple::new(
            Architecture::Evm,
            Vendor::Ethereum,
            OperatingSystem::Evm(EvmVersion::Osaka),
        );
        EvmBackend::new(Evm::new(triple))
    }

    fn assert_no_object_ir(module: &Module) {
        for func_ref in module.funcs() {
            let sig = module
                .ctx
                .get_sig(func_ref)
                .expect("signature should exist");
            assert!(
                sig.args()
                    .iter()
                    .all(|&ty| !has_nested_objref(&module.ctx, ty)),
                "object refs should be removed from args of {}",
                sig.name()
            );
            assert!(
                sig.ret_tys()
                    .iter()
                    .all(|&ty| !has_nested_objref(&module.ctx, ty)),
                "object refs should be removed from returns of {}",
                sig.name()
            );

            module.func_store.view(func_ref, |func| {
                for value in func.dfg.value_ids() {
                    assert!(
                        !has_nested_objref(&module.ctx, func.dfg.value_ty(value)),
                        "value {value:?} in {} still has objref type",
                        sig.name()
                    );
                }

                for block in func.layout.iter_block() {
                    for inst in func.layout.iter_inst(block) {
                        assert!(
                            downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst))
                                .is_none(),
                            "obj.alloc remained in {}",
                            sig.name()
                        );
                        assert!(
                            downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(inst))
                                .is_none(),
                            "obj.proj remained in {}",
                            sig.name()
                        );
                        assert!(
                            downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(inst))
                                .is_none(),
                            "obj.index remained in {}",
                            sig.name()
                        );
                        assert!(
                            downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                                .is_none(),
                            "obj.load remained in {}",
                            sig.name()
                        );
                        assert!(
                            downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst))
                                .is_none(),
                            "obj.store remained in {}",
                            sig.name()
                        );
                        assert!(
                            downcast::<&data::ObjMaterializeStack>(
                                func.inst_set(),
                                func.dfg.inst(inst)
                            )
                            .is_none(),
                            "obj.materialize.stack remained in {}",
                            sig.name()
                        );
                        assert!(
                            downcast::<&data::ObjMaterializeHeap>(
                                func.inst_set(),
                                func.dfg.inst(inst)
                            )
                            .is_none(),
                            "obj.materialize.heap remained in {}",
                            sig.name()
                        );
                        assert!(
                            downcast::<&data::MemAllocDynamic>(
                                func.inst_set(),
                                func.dfg.inst(inst)
                            )
                            .is_none(),
                            "mem.alloc_dynamic remained in {}",
                            sig.name()
                        );
                    }
                }
            });
        }
    }

    #[test]
    fn objref_helper_chain_compiles_through_evm() {
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

func private %forward_pair(v0.i256, v1.i256) -> objref<@pair> {
block0:
    v2.objref<@pair> = call %make_pair v0 v1;
    return v2;
}

func public %entry(v0.i256, v1.i256) -> i256 {
block0:
    v2.objref<@pair> = call %forward_pair v0 v1;
    v3.objref<i256> = obj.proj v2 0.i8;
    v4.i256 = obj.load v3;
    v5.objref<i256> = obj.proj v2 1.i8;
    v6.i256 = obj.load v5;
    v7.i256 = add v4 v6;
    return v7;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
        );

        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::MinimalRelax,
            emit_symtab: false,
            emit_observability: false,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Fast),
        };
        compile_all_objects(&module, &test_backend(), &opts).expect("compile should succeed");

        assert_no_object_ir(&module);
        let entry = lookup_func(&module, "entry");
        let make_pair = lookup_func(&module, "make_pair");
        let forward_pair = lookup_func(&module, "forward_pair");
        let make_pair_sig = module
            .ctx
            .get_sig(make_pair)
            .expect("make_pair signature should exist");
        assert_eq!(make_pair_sig.args().len(), 3);
        assert!(make_pair_sig.returns_unit());
        let forward_pair_sig = module
            .ctx
            .get_sig(forward_pair)
            .expect("forward_pair signature should exist");
        assert_eq!(forward_pair_sig.args().len(), 3);
        assert!(forward_pair_sig.returns_unit());

        module.func_store.view(make_pair, |func| {
            assert!(
                func.layout
                    .iter_block()
                    .flat_map(|block| func.layout.iter_inst(block))
                    .all(
                        |inst| downcast::<&evm::EvmMalloc>(func.inst_set(), func.dfg.inst(inst))
                            .is_none()
                    ),
                "make_pair should initialize the caller-provided object in place"
            );
        });
        module.func_store.view(forward_pair, |func| {
            assert!(
                func.layout
                    .iter_block()
                    .flat_map(|block| func.layout.iter_inst(block))
                    .all(
                        |inst| downcast::<&evm::EvmMalloc>(func.inst_set(), func.dfg.inst(inst))
                            .is_none()
                    ),
                "forward_pair should forward the caller-provided object without heap allocation"
            );
        });
        module.func_store.view(entry, |func| {
            let mut saw_forward_pair = false;
            assert!(
                func.layout
                    .iter_block()
                    .flat_map(|block| func.layout.iter_inst(block))
                    .all(|inst| {
                        assert!(
                            downcast::<&evm::EvmMalloc>(func.inst_set(), func.dfg.inst(inst))
                                .is_none(),
                            "entry should keep the returned object caller-local"
                        );
                        let Some(call) =
                            downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst))
                        else {
                            return true;
                        };
                        if *call.callee() == forward_pair {
                            saw_forward_pair = true;
                            assert!(
                                func.dfg.inst_results(inst).is_empty(),
                                "rewritten forward_pair call should return through the out arg"
                            );
                        }
                        true
                    }),
                "entry should still contain lowered calls"
            );
            assert!(saw_forward_pair, "entry should still call forward_pair");
        });
    }

    #[test]
    fn materialize_stack_return_escapes_to_heap() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func public %entry(v0.i256) -> i256 {
block0:
    v1.objref<@pair> = obj.alloc @pair;
    v2.objref<i256> = obj.proj v1 0.i8;
    obj.store v2 v0;
    v3.*@pair = obj.materialize.stack v1;
    v4.i256 = call %sum_ptr v3;
    return v4;
}

func private %sum_ptr(v0.*@pair) -> i256 {
block0:
    v1.*i256 = gep v0 0.i64 0.i8;
    v2.i256 = mload v1 i256;
    return v2;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
        );

        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::MinimalRelax,
            emit_symtab: false,
            emit_observability: false,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Fast),
        };
        compile_all_objects(&module, &test_backend(), &opts).expect("compile should succeed");

        let entry = lookup_func(&module, "entry");
        module.func_store.view(entry, |func| {
            assert!(
                func.layout
                    .iter_block()
                    .flat_map(|block| func.layout.iter_inst(block))
                    .any(
                        |inst| downcast::<&evm::EvmMalloc>(func.inst_set(), func.dfg.inst(inst))
                            .is_some()
                    ),
                "escaping stack materialization must force heap allocation"
            );
        });
    }

    #[test]
    fn nested_objref_compound_arg_compiles_through_evm() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };
type @wrapper = { objref<@pair> };

func private %sum_wrapper(v0.@wrapper) -> i256 {
block0:
    v1.objref<@pair> = extract_value v0 0.i8;
    v2.objref<i256> = obj.proj v1 0.i8;
    v3.i256 = obj.load v2;
    return v3;
}

func public %entry(v0.i256, v1.i256) -> i256 {
block0:
    v2.objref<@pair> = obj.alloc @pair;
    v3.objref<i256> = obj.proj v2 0.i8;
    obj.store v3 v0;
    v4.objref<i256> = obj.proj v2 1.i8;
    obj.store v4 v1;
    v5.@wrapper = insert_value undef.@wrapper 0.i8 v2;
    v6.i256 = call %sum_wrapper v5;
    return v6;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
        );

        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::MinimalRelax,
            emit_symtab: false,
            emit_observability: false,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Fast),
        };
        compile_all_objects(&module, &test_backend(), &opts).expect("compile should succeed");

        assert_no_object_ir(&module);
    }

    #[test]
    fn local_object_return_can_capture_and_reuse_pointer_arg() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @wrapper = { objref<i256> };

func private %make_wrapper(v0.objref<i256>) -> objref<@wrapper> {
block0:
    v1.objref<@wrapper> = obj.alloc @wrapper;
    v2.objref<objref<i256>> = obj.proj v1 0.i8;
    obj.store v2 v0;
    return v1;
}

func private %read_wrapper(v0.objref<@wrapper>) -> i256 {
block0:
    v1.objref<objref<i256>> = obj.proj v0 0.i8;
    v2.objref<i256> = obj.load v1;
    v3.i256 = obj.load v2;
    return v3;
}

func public %entry(v0.i256) -> i256 {
block0:
    v1.objref<i256> = obj.alloc i256;
    obj.store v1 v0;
    v2.objref<@wrapper> = call %make_wrapper v1;
    v3.i256 = call %read_wrapper v2;
    return v3;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
        );

        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::MinimalRelax,
            emit_symtab: false,
            emit_observability: false,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Fast),
        };
        compile_all_objects(&module, &test_backend(), &opts).expect("compile should succeed");

        assert_no_object_ir(&module);
    }
}
