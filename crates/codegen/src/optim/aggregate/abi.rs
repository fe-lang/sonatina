use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use sonatina_ir::{
    Function, Type, Value, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{control_flow, data, downcast},
    module::{FuncRef, Module},
};

use super::{
    private_abi::{self, PrivateAbiPlan},
    reconstruct::AggregateValueReconstructor,
    shape,
};

#[derive(Clone)]
struct TypeExpansion {
    original_ty: Type,
    is_aggregate: bool,
    scalar_tys: SmallVec<[Type; 4]>,
}

#[derive(Clone)]
struct FuncPlan {
    args: Vec<TypeExpansion>,
    rets: Vec<TypeExpansion>,
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
pub struct AggregateExpandAbi {
    layout_cache: shape::AggregateLayoutCache,
}

impl AggregateExpandAbi {
    pub fn run(&mut self, module: &Module) -> bool {
        self.layout_cache.clear();

        let mut plans = self.collect_plans(module);
        private_abi::retain_higher_order_safe_plans(module, &mut plans);
        if plans.is_empty() {
            return false;
        }

        let old_sigs = private_abi::rewrite_declared_signatures(module, &plans);

        for &func in plans.keys() {
            let plan = plans
                .get(&func)
                .cloned()
                .expect("aggregate ABI plan should exist");
            module.func_store.modify(func, |function| {
                self.rewrite_function(function, &plan);
            });
        }

        for func in module.funcs() {
            module.func_store.modify(func, |function| {
                self.rewrite_calls(function, &plans);
                function.rebuild_users();
            });
        }

        private_abi::propagate_private_abi_types(module, &old_sigs);
        true
    }

    fn collect_plans(&mut self, module: &Module) -> FxHashMap<FuncRef, FuncPlan> {
        let mut plans = FxHashMap::default();

        for func in module.funcs() {
            let Some(sig) = module.ctx.get_sig(func) else {
                continue;
            };
            if !private_abi::is_owned_private_abi_func(&sig) {
                continue;
            }

            let args: Vec<_> = sig
                .args()
                .iter()
                .copied()
                .map(|ty| self.expand_type(module, ty))
                .collect();
            let rets: Vec<_> = sig
                .ret_tys()
                .iter()
                .copied()
                .map(|ty| self.expand_type(module, ty))
                .collect();
            if !args.iter().chain(&rets).any(|exp| exp.is_aggregate) {
                continue;
            }

            let new_arg_tys = args
                .iter()
                .flat_map(|exp| exp.scalar_tys.iter().copied())
                .collect();
            let new_ret_tys = rets
                .iter()
                .flat_map(|exp| exp.scalar_tys.iter().copied())
                .collect();

            plans.insert(
                func,
                FuncPlan {
                    args,
                    rets,
                    new_arg_tys,
                    new_ret_tys,
                },
            );
        }

        plans
    }

    fn expand_type(&mut self, module: &Module, ty: Type) -> TypeExpansion {
        let is_aggregate = shape::is_supported_aggregate_ty(&module.ctx, ty);
        let scalar_tys = if is_aggregate {
            self.layout_cache
                .runtime_leaves(&module.ctx, ty)
                .expect("supported aggregate type should have shape")
                .into_iter()
                .map(|leaf| leaf.ty)
                .collect()
        } else {
            SmallVec::from_slice(&[ty])
        };

        TypeExpansion {
            original_ty: ty,
            is_aggregate,
            scalar_tys,
        }
    }

    fn rewrite_function(&mut self, func: &mut Function, plan: &FuncPlan) {
        self.rewrite_args(func, plan);
        self.rewrite_returns(func, plan);
    }

    fn rewrite_args(&mut self, func: &mut Function, plan: &FuncPlan) {
        let Some(entry) = func.layout.entry_block() else {
            return;
        };
        let anchor = func
            .layout
            .first_inst_of(entry)
            .expect("aggregate ABI expansion requires non-empty entry block");
        let old_args = func.arg_values.clone();
        let mut new_args = SmallVec::new();

        for (&old_arg, expansion) in old_args.iter().zip(&plan.args) {
            if !expansion.is_aggregate {
                let idx = new_args.len();
                func.dfg.values[old_arg] = Value::Arg {
                    ty: expansion.original_ty,
                    idx,
                };
                new_args.push(old_arg);
                continue;
            }

            if expansion.scalar_tys.is_empty() {
                let undef = func.dfg.make_undef_value(expansion.original_ty);
                func.dfg.change_to_alias(old_arg, undef);
                func.dfg.values[old_arg] = Value::Undef {
                    ty: expansion.original_ty,
                };
                continue;
            }

            let scalar_args = self.append_scalar_args(func, &mut new_args, &expansion.scalar_tys);
            let rebuilt = self.rebuild_aggregate_from_leaves(
                func,
                anchor,
                expansion.original_ty,
                &scalar_args,
            );
            func.dfg.change_to_alias(old_arg, rebuilt);
            func.dfg.values[old_arg] = Value::Undef {
                ty: expansion.original_ty,
            };
        }

        func.arg_values = new_args;
    }

    fn append_scalar_args(
        &self,
        func: &mut Function,
        new_args: &mut SmallVec<[ValueId; 8]>,
        scalar_tys: &[Type],
    ) -> SmallVec<[ValueId; 4]> {
        let mut appended = SmallVec::new();
        for &ty in scalar_tys {
            let idx = new_args.len();
            let value = func.dfg.make_value(Value::Arg { ty, idx });
            new_args.push(value);
            appended.push(value);
        }
        appended
    }

    fn rewrite_returns(&mut self, func: &mut Function, plan: &FuncPlan) {
        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                let Some(ret) =
                    downcast::<&control_flow::Return>(func.inst_set(), func.dfg.inst(inst))
                        .cloned()
                else {
                    continue;
                };

                let mut new_args = SmallVec::new();
                for (&value, expansion) in ret.args().iter().zip(&plan.rets) {
                    new_args
                        .extend(self.expand_value_to_scalar_leaves(func, inst, value, expansion));
                }

                func.dfg.replace_inst(
                    inst,
                    Box::new(control_flow::Return::new(
                        func.inst_set()
                            .has_return()
                            .expect("target ISA must support `return`"),
                        new_args.into(),
                    )),
                );
            }
        }
    }

    fn rewrite_calls(&mut self, func: &mut Function, plans: &FxHashMap<FuncRef, FuncPlan>) {
        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                let Some(call) =
                    downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst)).cloned()
                else {
                    continue;
                };
                let Some(plan) = plans.get(call.callee()).cloned() else {
                    continue;
                };
                self.rewrite_call(func, inst, &call, &plan);
            }
        }
    }

    fn rewrite_call(
        &mut self,
        func: &mut Function,
        inst: sonatina_ir::InstId,
        call: &control_flow::Call,
        plan: &FuncPlan,
    ) {
        let mut new_args = SmallVec::new();
        for (&arg, expansion) in call.args().iter().zip(&plan.args) {
            new_args.extend(self.expand_value_to_scalar_leaves(func, inst, arg, expansion));
        }

        let loc = func.layout.prev_inst_of(inst).map_or(
            CursorLocation::BlockTop(func.layout.inst_block(inst)),
            CursorLocation::At,
        );
        let mut cursor = InstInserter::at_location(loc);
        let new_call = cursor.insert_inst_data(
            func,
            control_flow::Call::new(
                func.inst_set()
                    .has_call()
                    .expect("target ISA must support `call`"),
                *call.callee(),
                new_args,
            ),
        );
        let new_results = cursor.make_results(func, new_call, &plan.new_ret_tys);
        cursor.attach_results(func, new_call, &new_results);

        let old_results = func.dfg.inst_results(inst).to_vec();
        let mut next_scalar_result = 0usize;
        for (&old_result, expansion) in old_results.iter().zip(&plan.rets) {
            let replacement = if expansion.is_aggregate {
                let leaf_count = expansion.scalar_tys.len();
                let replacement = if leaf_count == 0 {
                    func.dfg.make_undef_value(expansion.original_ty)
                } else {
                    self.rebuild_aggregate_from_leaves(
                        func,
                        inst,
                        expansion.original_ty,
                        &new_results[next_scalar_result..next_scalar_result + leaf_count],
                    )
                };
                next_scalar_result += leaf_count;
                replacement
            } else {
                let replacement = new_results[next_scalar_result];
                next_scalar_result += 1;
                replacement
            };
            func.dfg.change_to_alias(old_result, replacement);
        }

        assert_eq!(
            next_scalar_result,
            new_results.len(),
            "aggregate ABI expansion result mapping should consume all scalar results"
        );

        func.layout.remove_inst(inst);
        func.erase_inst(inst);
    }

    fn expand_value_to_scalar_leaves(
        &mut self,
        func: &mut Function,
        inst: sonatina_ir::InstId,
        value: ValueId,
        expansion: &TypeExpansion,
    ) -> SmallVec<[ValueId; 4]> {
        if !expansion.is_aggregate {
            return SmallVec::from_slice(&[value]);
        }
        if expansion.scalar_tys.is_empty() {
            return SmallVec::new();
        }

        let leaves = self
            .layout_cache
            .runtime_leaves(func.ctx(), expansion.original_ty)
            .expect("aggregate expansion should have runtime leaves");
        let mut reconstructor = AggregateValueReconstructor::new(&mut self.layout_cache);
        let mut expanded = SmallVec::new();
        for leaf in leaves {
            let slice =
                shape::aggregate_slice_for_path(func.ctx(), expansion.original_ty, &leaf.path)
                    .expect("aggregate leaf path should be valid");
            let scalar = reconstructor
                .rebuild_slice(func, inst, value, expansion.original_ty, slice, leaf.ty)
                .expect("aggregate leaf slice should rebuild");
            expanded.push(scalar);
        }
        expanded
    }

    fn rebuild_aggregate_from_leaves(
        &mut self,
        func: &mut Function,
        inst: sonatina_ir::InstId,
        agg_ty: Type,
        scalar_leaves: &[ValueId],
    ) -> ValueId {
        if scalar_leaves.is_empty() {
            return func.dfg.make_undef_value(agg_ty);
        }

        let child_count = shape::aggregate_child_count(func.ctx(), agg_ty)
            .expect("aggregate reconstruction requires struct or array type");
        let mut aggregate = func.dfg.make_undef_value(agg_ty);
        for idx in 0..child_count {
            let idx = u32::try_from(idx).expect("aggregate child index overflow");
            let child = shape::aggregate_slice_for_index(func.ctx(), agg_ty, idx)
                .expect("aggregate child slice should exist");
            let child_value = if child.leaf_count == 0 {
                func.dfg.make_undef_value(child.ty)
            } else if shape::is_supported_aggregate_ty(func.ctx(), child.ty) {
                self.rebuild_aggregate_from_leaves(
                    func,
                    inst,
                    child.ty,
                    &scalar_leaves[child.first_leaf..child.first_leaf + child.leaf_count],
                )
            } else {
                scalar_leaves[child.first_leaf]
            };
            aggregate = insert_value_before_inst(func, inst, aggregate, idx, child_value, agg_ty);
        }
        aggregate
    }
}

fn insert_value_before_inst(
    func: &mut Function,
    inst: sonatina_ir::InstId,
    dest: ValueId,
    idx: u32,
    value: ValueId,
    ty: Type,
) -> ValueId {
    let idx_value = func.dfg.make_imm_value(i64::from(idx));
    let loc = func.layout.prev_inst_of(inst).map_or(
        CursorLocation::BlockTop(func.layout.inst_block(inst)),
        CursorLocation::At,
    );
    let mut cursor = InstInserter::at_location(loc);
    let insert_inst = cursor.insert_inst_data(
        func,
        data::InsertValue::new_unchecked(func.inst_set(), dest, idx_value, value),
    );
    let insert_value = func.dfg.make_value(Value::Inst {
        inst: insert_inst,
        result_idx: 0,
        ty,
    });
    cursor.attach_result(func, insert_inst, insert_value);
    insert_value
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        isa::evm::{EvmBackend, PushWidthPolicy},
        object::{CompileOptions, compile_all_objects},
    };
    use sonatina_ir::{Module, isa::evm::Evm, types::CompoundType};
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};
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

    fn lookup_declared_func(module: &Module, name: &str) -> FuncRef {
        module
            .ctx
            .declared_funcs
            .iter()
            .find_map(|entry| (entry.value().name() == name).then_some(*entry.key()))
            .expect("declared function should exist")
    }

    fn test_backend() -> EvmBackend {
        let triple = TargetTriple::new(
            Architecture::Evm,
            Vendor::Ethereum,
            OperatingSystem::Evm(EvmVersion::Osaka),
        );
        EvmBackend::new(Evm::new(triple))
    }

    #[test]
    fn expands_internal_aggregate_abi_and_keeps_ir_verifiable() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @inner = { i256, i256 };
type @pair = { @inner, i256 };

func private %twist(v0.@pair) -> @pair {
block0:
    v1.@inner = extract_value v0 0.i8;
    v2.i256 = extract_value v1 0.i8;
    v3.i256 = extract_value v1 1.i8;
    v4.i256 = extract_value v0 1.i8;
    v5.@inner = insert_value undef.@inner 0.i8 v3;
    v6.@inner = insert_value v5 1.i8 v2;
    v7.@pair = insert_value undef.@pair 0.i8 v6;
    v8.@pair = insert_value v7 1.i8 v4;
    return v8;
}

func public %entry(v0.i256, v1.i256, v2.i256) -> i256 {
block0:
    v3.@inner = insert_value undef.@inner 0.i8 v0;
    v4.@inner = insert_value v3 1.i8 v1;
    v5.@pair = insert_value undef.@pair 0.i8 v4;
    v6.@pair = insert_value v5 1.i8 v2;
    v7.@pair = call %twist v6;
    v8.@inner = extract_value v7 0.i8;
    v9.i256 = extract_value v8 0.i8;
    return v9;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
        );

        AggregateExpandAbi::default().run(&module);

        let report = verify_module(
            &module,
            &VerifierConfig::for_level(VerificationLevel::Standard),
        );
        assert!(
            !report.has_errors(),
            "aggregate ABI expansion should preserve verifier invariants:\n{report}"
        );

        let twist = lookup_func(&module, "twist");
        module.func_store.view(twist, |func| {
            let sig = module.ctx.get_sig(twist).expect("signature should exist");
            assert_eq!(sig.args(), &[Type::I256, Type::I256, Type::I256]);
            assert_eq!(sig.ret_tys(), &[Type::I256, Type::I256, Type::I256]);

            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    if let Some(call) =
                        downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst))
                    {
                        assert_eq!(call.args().len(), 3);
                        assert_eq!(func.dfg.inst_results(inst).len(), 3);
                    }
                }
            }
        });
    }

    #[test]
    fn expanded_internal_aggregate_calls_compile_through_evm() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %swap(v0.@pair) -> @pair {
block0:
    v1.i256 = extract_value v0 0.i8;
    v2.i256 = extract_value v0 1.i8;
    v3.@pair = insert_value undef.@pair 0.i8 v2;
    v4.@pair = insert_value v3 1.i8 v1;
    return v4;
}

func public %entry(v0.i256, v1.i256) -> i256 {
block0:
    v2.@pair = insert_value undef.@pair 0.i8 v0;
    v3.@pair = insert_value v2 1.i8 v1;
    v4.@pair = call %swap v3;
    v5.i256 = extract_value v4 0.i8;
    return v5;
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

        let swap = lookup_func(&module, "swap");
        let sig = module.ctx.get_sig(swap).expect("signature should exist");
        assert_eq!(sig.args(), &[Type::I256, Type::I256]);
        assert_eq!(sig.ret_tys(), &[Type::I256, Type::I256]);
    }

    #[test]
    fn higher_order_aggregate_callback_on_external_surface_blocks_rewrite() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

declare external %takes_swap(*(@pair) -> @pair);

func private %swap(v0.@pair) -> @pair {
block0:
    v1.i256 = extract_value v0 0.i8;
    v2.i256 = extract_value v0 1.i8;
    v3.@pair = insert_value undef.@pair 0.i8 v2;
    v4.@pair = insert_value v3 1.i8 v1;
    return v4;
}

func private %register_swap() {
block0:
    v0.*(@pair) -> @pair = get_function_ptr %swap;
    call %takes_swap v0;
    return;
}
"#,
        );

        AggregateExpandAbi::default().run(&module);

        let report = verify_module(
            &module,
            &VerifierConfig::for_level(VerificationLevel::Standard),
        );
        assert!(
            !report.has_errors(),
            "aggregate ABI expansion should stay verifiable around external callback surfaces:\n{report}"
        );

        let swap = lookup_func(&module, "swap");
        let sig = module.ctx.get_sig(swap).expect("signature should exist");
        let pair = sig.args()[0];
        assert_eq!(sig.args(), &[pair]);
        assert_eq!(sig.ret_tys(), &[pair]);

        let takes_swap = lookup_declared_func(&module, "takes_swap");
        let takes_swap_sig = module
            .ctx
            .get_sig(takes_swap)
            .expect("signature should exist");
        let expected_cb = module.ctx.with_ty_store_mut(|store| {
            let Type::Compound(func_ty) = store.make_func(&[pair], &[pair]) else {
                unreachable!();
            };
            store.make_ptr(Type::Compound(func_ty))
        });
        assert_eq!(takes_swap_sig.args(), &[expected_cb]);
        assert_eq!(takes_swap_sig.ret_tys(), &[]);
    }

    #[test]
    fn higher_order_aggregate_callback_on_public_non_entry_surface_blocks_rewrite() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };
type @swap_box = { *(@pair) -> @pair };

func public %consume_swap(v0.@swap_box) {
block0:
    return;
}

func private %swap(v0.@pair) -> @pair {
block0:
    v1.i256 = extract_value v0 0.i8;
    v2.i256 = extract_value v0 1.i8;
    v3.@pair = insert_value undef.@pair 0.i8 v2;
    v4.@pair = insert_value v3 1.i8 v1;
    return v4;
}

func private %register_swap() {
block0:
    v0.*(@pair) -> @pair = get_function_ptr %swap;
    v1.@swap_box = insert_value undef.@swap_box 0.i8 v0;
    call %consume_swap v1;
    return;
}
"#,
        );

        AggregateExpandAbi::default().run(&module);

        let report = verify_module(
            &module,
            &VerifierConfig::for_level(VerificationLevel::Standard),
        );
        assert!(
            !report.has_errors(),
            "aggregate ABI expansion should preserve public non-entry callback surfaces:\n{report}"
        );

        let swap = lookup_func(&module, "swap");
        let sig = module.ctx.get_sig(swap).expect("signature should exist");
        let pair = sig.args()[0];
        assert_eq!(sig.args(), &[pair]);
        assert_eq!(sig.ret_tys(), &[pair]);

        let consume_swap = lookup_func(&module, "consume_swap");
        let consume_swap_sig = module
            .ctx
            .get_sig(consume_swap)
            .expect("signature should exist");
        let Type::Compound(swap_box) = consume_swap_sig.args()[0] else {
            panic!("swap box should be compound");
        };
        let field_tys = module.ctx.with_ty_store(|store| {
            let CompoundType::Struct(data) = store.resolve_compound(swap_box) else {
                panic!("swap box should be a struct");
            };
            data.fields.clone()
        });
        let expected_cb = module.ctx.with_ty_store_mut(|store| {
            let Type::Compound(func_ty) = store.make_func(&[pair], &[pair]) else {
                unreachable!();
            };
            store.make_ptr(Type::Compound(func_ty))
        });
        assert_eq!(field_tys, vec![expected_cb]);
    }
}
