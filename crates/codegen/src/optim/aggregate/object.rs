use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    Function, I256, Immediate, Module, Type, Value, ValueId,
    inst::{control_flow, data, downcast, evm},
    module::FuncRef,
};

use super::{
    object_abi,
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
        let in_place_helpers = object_abi::collect_in_place_object_helpers(module);
        let mut plans = self.collect_plans(module);
        private_abi::retain_higher_order_safe_plans(module, &mut plans);
        let mut changed = !plans.is_empty();
        let old_sigs = private_abi::rewrite_declared_signatures(module, &plans);

        for func_ref in module.funcs() {
            changed |= module.func_store.modify(func_ref, |function| {
                self.rewrite_function(function, &in_place_helpers)
            });
        }

        private_abi::propagate_private_abi_types(module, &old_sigs);
        changed
    }

    fn collect_plans(&self, module: &Module) -> FxHashMap<FuncRef, FuncPlan> {
        let mut plans = FxHashMap::default();

        for func in module.funcs() {
            let Some(sig) = module.ctx.get_sig(func) else {
                continue;
            };

            let new_arg_tys: SmallVec<[Type; 8]> = sig
                .args()
                .iter()
                .copied()
                .map(|ty| lower_objref_ty(&module.ctx, ty))
                .collect();
            let new_ret_tys: SmallVec<[Type; 8]> = sig
                .ret_tys()
                .iter()
                .copied()
                .map(|ty| lower_objref_ty(&module.ctx, ty))
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
        in_place_helpers: &FxHashSet<FuncRef>,
    ) -> bool {
        let mut changed = self.rewrite_value_types(func);
        let alloc_kinds = self.collect_alloc_kinds(func, in_place_helpers);
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

    fn rewrite_value_types(&self, func: &mut Function) -> bool {
        let mut changed = false;
        for value in func.dfg.value_ids().collect::<Vec<_>>() {
            let old_ty = func.dfg.value_ty(value);
            let new_ty = lower_objref_ty(func.ctx(), old_ty);
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
        changed
    }

    fn collect_alloc_kinds(
        &self,
        func: &Function,
        in_place_helpers: &FxHashSet<FuncRef>,
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
                        in_place_helpers,
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
        in_place_helpers: &FxHashSet<FuncRef>,
    ) -> Materialization {
        let mut worklist = vec![root];
        let mut seen = FxHashSet::default();
        let mut kind = Materialization::Stack;

        while let Some(value) = worklist.pop() {
            if !seen.insert(value) {
                continue;
            }

            for &user in func.dfg.users(value) {
                if !func.layout.is_inst_inserted(user) {
                    continue;
                }

                if let Some(proj) = downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(user))
                    && proj.values().first() == Some(&value)
                {
                    if let Some(result) = func.dfg.inst_result(user) {
                        worklist.push(result);
                    }
                    continue;
                }

                if let Some(index) =
                    downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(user))
                    && *index.object() == value
                {
                    if let Some(result) = func.dfg.inst_result(user) {
                        worklist.push(result);
                    }
                    continue;
                }

                if let Some(phi) =
                    downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(user))
                    && phi.args().iter().any(|(arg, _)| *arg == value)
                {
                    if let Some(result) = func.dfg.inst_result(user) {
                        worklist.push(result);
                    }
                    continue;
                }

                if let Some(load) = downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(user))
                    && *load.object() == value
                {
                    continue;
                }

                if let Some(store) =
                    downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(user))
                    && *store.object() == value
                {
                    continue;
                }

                if let Some(mat_stack) =
                    downcast::<&data::ObjMaterializeStack>(func.inst_set(), func.dfg.inst(user))
                    && *mat_stack.object() == value
                {
                    continue;
                }

                if let Some(mat_heap) =
                    downcast::<&data::ObjMaterializeHeap>(func.inst_set(), func.dfg.inst(user))
                    && *mat_heap.object() == value
                {
                    kind = Materialization::Heap;
                    continue;
                }

                if let Some(call) =
                    downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(user))
                    && call.args().contains(&value)
                {
                    if value == root
                        && func.dfg.inst_results(user).is_empty()
                        && object_abi::call_passes_object_to_in_place_helper(
                            func.ctx(),
                            call,
                            value,
                            root_value_ty,
                            in_place_helpers,
                        )
                    {
                        continue;
                    }
                    return Materialization::Heap;
                }

                if let Some(ret) =
                    downcast::<&control_flow::Return>(func.inst_set(), func.dfg.inst(user))
                    && ret.args().iter().copied().any(|arg| arg == value)
                {
                    return Materialization::Heap;
                }

                return Materialization::Heap;
            }
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

fn lower_objref_ty(ctx: &sonatina_ir::module::ModuleCtx, ty: Type) -> Type {
    let Some(cmpd) = ty.resolve_compound(ctx) else {
        return ty;
    };
    let sonatina_ir::types::CompoundType::ObjRef(elem) = cmpd else {
        return ty;
    };
    elem.to_ptr(ctx)
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
    use sonatina_ir::{
        Module,
        inst::{control_flow, data, evm},
        isa::evm::Evm,
    };
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};
    use sonatina_verifier::{VerificationLevel, VerifierConfig};

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
                sig.args().iter().all(|&ty| !ty.is_obj_ref(&module.ctx)),
                "object refs should be removed from args of {}",
                sig.name()
            );
            assert!(
                sig.ret_tys().iter().all(|&ty| !ty.is_obj_ref(&module.ctx)),
                "object refs should be removed from returns of {}",
                sig.name()
            );

            module.func_store.view(func_ref, |func| {
                for value in func.dfg.value_ids() {
                    assert!(
                        !func.dfg.value_ty(value).is_obj_ref(&module.ctx),
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
}
