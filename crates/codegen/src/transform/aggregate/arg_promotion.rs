//! Pass private object arguments as a bounded set of scalars read at callee entry.

use std::{cmp::Reverse, collections::BTreeMap, slice};

use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    Function, InstId, Module, Type, Value, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{control_flow, data, downcast},
    module::FuncRef,
};

use crate::{
    analysis::func_behavior,
    optim::{
        aggregate::compute_object_effect_summaries,
        dead_func::{collect_object_roots, non_call_func_ref},
        signature_rewrite::{SignatureRewritePlan, rewrite_declared_signatures},
    },
};

use super::{
    ObjectAggregateAbi, ObjectAggregateAbiConfig, ObjectReturnOutParam,
    abi::abi_arg_operand_count,
    objref_element_ty,
    promotion::{ReadPrefixRequirement, unconditional_read_prefix},
    reconstruct::rebuild_scalar_shape_from_leaf_values,
    scalarize::insert_object_child_ref,
    shape::{self, AggregateLayoutCache, FieldPath},
};

#[derive(Default, Debug)]
pub struct ObjectArgPromotionStats {
    pub promoted_args: usize,
    pub rewritten_calls: usize,
}

struct Field {
    path: FieldPath,
    ty: Type,
}

struct Load {
    inst: InstId,
    ty: Type,
    paths: Vec<FieldPath>,
}

struct Reads {
    fields: Vec<Field>,
    loads: Vec<Load>,
    projections: Vec<InstId>,
}

struct Plan {
    arg_index: usize,
    root_ty: Type,
    reads: Reads,
    new_arg_tys: SmallVec<[Type; 8]>,
    ret_tys: SmallVec<[Type; 2]>,
}

impl SignatureRewritePlan for Plan {
    fn new_arg_tys(&self) -> &[Type] {
        &self.new_arg_tys
    }

    fn new_ret_tys(&self) -> &[Type] {
        &self.ret_tys
    }
}

#[derive(Default)]
pub struct ObjectArgPromotion {
    layouts: AggregateLayoutCache,
}

impl ObjectArgPromotion {
    pub fn run(&mut self, module: &Module) -> ObjectArgPromotionStats {
        self.layouts.clear();
        let mut blocked: FxHashSet<_> = collect_object_roots(module).into_iter().collect();
        for func_ref in module.funcs() {
            module.func_store.view(func_ref, |func| {
                for block in func.layout.iter_block() {
                    for inst in func.layout.iter_inst(block) {
                        blocked.extend(non_call_func_ref(func, inst));
                    }
                }
            });
        }
        let mut stats = ObjectArgPromotionStats::default();
        loop {
            // Complete each signature/call cutover before rebuilding any facts.
            func_behavior::analyze_module(module);
            let object_effects = compute_object_effect_summaries(module);
            // Promotion can split an exposed signature class and enable a
            // previously blocked output rewrite. Reserve candidate outputs
            // before filtering plans against the current signature classes.
            let synthetic_outputs =
                ObjectReturnOutParam.collect_candidate_plans(module, &object_effects);
            let mut plans = FxHashMap::default();
            for func_ref in module.funcs() {
                if blocked.contains(&func_ref) || !module.ctx.func_linkage(func_ref).is_private() {
                    continue;
                }
                module.func_store.modify(func_ref, Function::rebuild_users);
                let ret_tys = module.ctx.func_sig(func_ref, |sig| sig.ret_tys().to_vec());
                let plan = module.func_store.view(func_ref, |func| {
                    self.plan(func, &ret_tys, synthetic_outputs.contains_key(&func_ref))
                });
                if let Some(plan) = plan {
                    plans.insert(func_ref, plan);
                }
            }
            if plans.is_empty() {
                break;
            }
            stats.promoted_args += plans.len();
            // No function pointer or symbol uses survive the eligibility gate.
            // Leave structurally equal function types belonging to other functions alone.
            rewrite_declared_signatures(module, &plans);
            for (&func_ref, plan) in &plans {
                module
                    .func_store
                    .modify(func_ref, |func| rewrite_function(func, plan));
            }
            for func_ref in module.funcs() {
                stats.rewritten_calls += module
                    .func_store
                    .modify(func_ref, |func| rewrite_calls(func, &plans));
            }
        }
        stats
    }

    fn plan(&mut self, func: &Function, ret_tys: &[Type], synthetic_output: bool) -> Option<Plan> {
        let limits = ObjectAggregateAbiConfig::default();
        let hidden_returns = ObjectAggregateAbi::new(limits)
            .hidden_return_arg_count(func.ctx(), ret_tys)?
            + usize::from(synthetic_output);
        for (arg_index, &argument) in func.arg_values.iter().enumerate() {
            let Some(root_ty) = objref_element_ty(func.ctx(), func.dfg.value_ty(argument)) else {
                continue;
            };
            let Some(shape) = self.layouts.shape(func.ctx(), root_ty) else {
                continue;
            };
            if !shape.leaves.iter().all(|leaf| leaf.ty.is_integral()) {
                continue;
            }
            let Some(reads) = collect_reads(
                func,
                argument,
                root_ty,
                &mut self.layouts,
                limits.inline_leaf_limit,
            ) else {
                continue;
            };
            let loads: FxHashSet<_> = reads.loads.iter().map(|load| load.inst).collect();
            // All reads of this argument must execute in the unchanged entry
            // prefix. Other memory accesses, calls, allocations and branches are
            // barriers, so this needs no no-alias or all-callers initialization assumption.
            if reads.fields.is_empty()
                || unconditional_read_prefix(func, ReadPrefixRequirement::SingleExecution, |inst| {
                    loads.contains(&inst)
                })
                .len()
                    != loads.len()
            {
                continue;
            }
            let mut new_arg_tys = SmallVec::new();
            for (index, &arg) in func.arg_values.iter().enumerate() {
                if index == arg_index {
                    new_arg_tys.extend(reads.fields.iter().map(|field| field.ty));
                } else {
                    new_arg_tys.push(func.dfg.value_ty(arg));
                }
            }
            let operands = new_arg_tys
                .iter()
                .try_fold(hidden_returns, |operands, &ty| {
                    abi_arg_operand_count(func.ctx(), ty)
                        .and_then(|count| operands.checked_add(count))
                });
            if !operands.is_some_and(|operands| operands <= limits.max_direct_arg_words) {
                continue;
            }
            return Some(Plan {
                arg_index,
                root_ty,
                reads,
                new_arg_tys,
                ret_tys: SmallVec::from_slice(ret_tys),
            });
        }
        None
    }
}

fn collect_reads(
    func: &Function,
    argument: ValueId,
    root_ty: Type,
    layouts: &mut AggregateLayoutCache,
    leaf_limit: usize,
) -> Option<Reads> {
    let mut fields = BTreeMap::<FieldPath, Field>::new();
    let mut loads = Vec::new();
    let mut projections = Vec::new();
    let mut pending = vec![(argument, FieldPath::new())];
    let mut seen = FxHashSet::default();
    while let Some((object, path)) = pending.pop() {
        if !seen.insert(object) {
            continue;
        }
        for &inst in func.dfg.users(object) {
            if !func.layout.is_inst_inserted(inst) {
                continue;
            }
            if let Some(load) = downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                && *load.object() == object
            {
                let result = func.dfg.inst_result(inst)?;
                let ty = func.dfg.value_ty(result);
                let leaves = if ty.is_integral() {
                    vec![(path.clone(), ty)]
                } else {
                    if !shape::is_leaf_reifiable_ty(func.ctx(), ty) {
                        return None;
                    }
                    let loaded_shape = layouts.shape(func.ctx(), ty)?;
                    if loaded_shape.leaves.len() > leaf_limit {
                        return None;
                    }
                    loaded_shape
                        .leaves
                        .iter()
                        .map(|leaf| {
                            let mut leaf_path = path.clone();
                            leaf_path.extend_from_slice(&leaf.path);
                            (leaf_path, leaf.ty)
                        })
                        .collect()
                };
                let mut paths = Vec::new();
                for (path, ty) in leaves {
                    if !ty.is_integral() {
                        return None;
                    }
                    paths.push(path.clone());
                    fields.entry(path.clone()).or_insert(Field { path, ty });
                    if fields.len() > leaf_limit {
                        return None;
                    }
                }
                loads.push(Load { inst, ty, paths });
                continue;
            }
            let indices = if let Some(projection) =
                downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(inst))
                && projection.values().first() == Some(&object)
            {
                &projection.values()[1..]
            } else if let Some(index) =
                downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(inst))
                && *index.object() == object
            {
                slice::from_ref(index.index())
            } else {
                return None;
            };
            let mut child_path = path.clone();
            for &index in indices {
                child_path.push(shape::const_u32(&func.dfg, index)?);
            }
            shape::aggregate_slice_for_path(func.ctx(), root_ty, &child_path)?;
            projections.push((inst, child_path.len()));
            pending.push((func.dfg.inst_result(inst)?, child_path));
        }
    }
    projections.sort_unstable_by_key(|&(inst, depth)| (Reverse(depth), inst));
    Some(Reads {
        fields: fields.into_values().collect(),
        loads,
        projections: projections.into_iter().map(|(inst, _)| inst).collect(),
    })
}

fn rewrite_function(func: &mut Function, plan: &Plan) {
    let old_args = func.arg_values.clone();
    let mut args = SmallVec::new();
    let mut field_values = BTreeMap::new();
    for (index, &argument) in old_args.iter().enumerate() {
        if index == plan.arg_index {
            for field in &plan.reads.fields {
                let value = func.dfg.make_value(Value::Arg {
                    ty: field.ty,
                    idx: args.len(),
                });
                args.push(value);
                field_values.insert(field.path.clone(), value);
            }
        } else {
            func.dfg.values[argument] = Value::Arg {
                ty: func.dfg.value_ty(argument),
                idx: args.len(),
            };
            args.push(argument);
        }
    }
    let module = func.ctx().clone();
    for load in &plan.reads.loads {
        let values: Vec<_> = load.paths.iter().map(|path| field_values[path]).collect();
        let value = if load.ty.is_integral() {
            values[0]
        } else {
            rebuild_scalar_shape_from_leaf_values(func, load.inst, &module, load.ty, &values)
                .expect("planned leaf-reifiable load")
        };
        let result = func.dfg.inst_result(load.inst).expect("planned load");
        func.dfg.change_to_alias(result, value);
        InstInserter::at_location(CursorLocation::At(load.inst)).remove_inst(func);
    }
    for &projection in &plan.reads.projections {
        InstInserter::at_location(CursorLocation::At(projection)).remove_inst(func);
    }
    let old_arg = old_args[plan.arg_index];
    func.dfg.values[old_arg] = Value::Undef {
        ty: func.dfg.value_ty(old_arg),
    };
    func.arg_values = args;
}

fn rewrite_calls(func: &mut Function, plans: &FxHashMap<FuncRef, Plan>) -> usize {
    let calls: Vec<_> = func
        .layout
        .iter_block()
        .flat_map(|block| func.layout.iter_inst(block))
        .filter(|&inst| func.dfg.is_call(inst))
        .collect();
    let mut rewritten = 0;
    let module = func.ctx().clone();
    for inst in calls {
        let call = func.dfg.cast_call(inst).unwrap().clone();
        let Some(plan) = plans.get(call.callee()) else {
            continue;
        };
        let location = func.layout.prev_inst_of(inst).map_or(
            CursorLocation::BlockTop(func.layout.inst_block(inst)),
            CursorLocation::At,
        );
        let mut cursor = InstInserter::at_location(location);
        let mut args = SmallVec::new();
        for (index, &arg) in call.args().iter().enumerate() {
            if index != plan.arg_index {
                args.push(arg);
                continue;
            }
            for field in &plan.reads.fields {
                let mut object = arg;
                let mut ty = plan.root_ty;
                for &index in &field.path {
                    let child_ty = shape::aggregate_child_ty(&module, ty, index)
                        .expect("validated field path");
                    object = insert_object_child_ref(
                        func,
                        &mut cursor,
                        &module,
                        object,
                        ty,
                        index,
                        child_ty,
                    );
                    let projection = func.dfg.value_inst(object).unwrap();
                    func.apply_inst_attribution(projection, &func.inst_attribution(inst));
                    ty = child_ty;
                }
                let load = cursor.insert_inst_data_from(
                    func,
                    inst,
                    data::ObjLoad::new_unchecked(func.inst_set(), object),
                );
                let value = cursor.make_result(func, load, field.ty);
                cursor.attach_result(func, load, value);
                cursor.set_location(CursorLocation::At(load));
                args.push(value);
            }
        }
        func.dfg.replace_inst_preserving_results(
            inst,
            Box::new(control_flow::Call::new_unchecked(
                func.inst_set(),
                *call.callee(),
                args,
            )),
        );
        rewritten += 1;
    }
    rewritten
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transform::aggregate::AggregateExpandAbi;
    use sonatina_parser::parse_module;
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module_or_panic};

    #[test]
    fn reserves_fresh_object_outputs_and_counts_unit_operands() {
        for (extra_ty, extra_count, fresh_return, exposed_sibling, promoted) in [
            ("i256", 11, true, false, 1),
            ("i256", 12, true, false, 0),
            ("unit", 12, false, false, 1),
            ("unit", 13, false, false, 0),
            ("i256", 11, true, true, 1),
            ("i256", 12, true, true, 0),
        ] {
            let extra_args = (20..20 + extra_count)
                .map(|index| format!(", v{index}.{extra_ty}"))
                .collect::<String>();
            let (declaration, keep_args) = if extra_ty == "unit" {
                let types = vec!["unit"; extra_count].join(", ");
                let values = (20..20 + extra_count)
                    .map(|index| format!("v{index}"))
                    .collect::<Vec<_>>()
                    .join(" ");
                (
                    format!("declare external %consume_units({types});"),
                    format!("call %consume_units {values};"),
                )
            } else {
                (
                    String::new(),
                    (20..20 + extra_count)
                        .map(|index| format!("evm_sstore {index}.i256 v{index};\n"))
                        .collect::<String>(),
                )
            };
            let sibling = if exposed_sibling {
                let pointer_args =
                    format!("objref<@Four>, {}", vec![extra_ty; extra_count].join(", "));
                format!(
                    r#"
func private %borrow(v0.objref<@Four>{extra_args}) -> objref<i256> {{
block0:
    v1.objref<i256> = obj.proj v0 0.i8;
    return v1;
}}
func private %consume(v0.*({pointer_args}) -> objref<i256>) {{
block0:
    return;
}}
func private %register() {{
block0:
    v0.*({pointer_args}) -> objref<i256> = get_function_ptr %borrow;
    call %consume v0;
    return;
}}
"#
                )
            } else {
                String::new()
            };
            let (ret_ty, tail) = if fresh_return {
                (
                    "objref<i256>",
                    "v12.objref<i256> = obj.alloc i256;\n    obj.store v12 v11;\n    return v12;",
                )
            } else {
                ("i256", "return v11;")
            };
            let source = format!(
                r#"
target = "evm-ethereum-osaka"
type @Four = {{ i256, i256, i256, i256 }};
{declaration}
{sibling}
func private %read(v0.objref<@Four>{extra_args}) -> {ret_ty} {{
block0:
    v1.objref<i256> = obj.proj v0 0.i8;
    v2.i256 = obj.load v1;
    v3.objref<i256> = obj.proj v0 1.i8;
    v4.i256 = obj.load v3;
    v5.objref<i256> = obj.proj v0 2.i8;
    v6.i256 = obj.load v5;
    v7.objref<i256> = obj.proj v0 3.i8;
    v8.i256 = obj.load v7;
    v9.i256 = add v2 v4;
    v10.i256 = add v6 v8;
    v11.i256 = add v9 v10;
    {keep_args}
    {tail}
}}
"#
            );
            let module = parse_module(&source).unwrap().module;
            let config = VerifierConfig::for_level(VerificationLevel::Full);
            verify_module_or_panic(&module, &config);
            assert_eq!(
                ObjectArgPromotion::default().run(&module).promoted_args,
                promoted,
                "{extra_count} {extra_ty}, fresh_return={fresh_return}, exposed_sibling={exposed_sibling}"
            );
            verify_module_or_panic(&module, &config);
            ObjectAggregateAbi::new(ObjectAggregateAbiConfig::default())
                .lower_to_memory(&module, false)
                .unwrap();
            AggregateExpandAbi::default().run(&module);
            verify_module_or_panic(&module, &config);
            let read = module
                .funcs()
                .into_iter()
                .find(|&function| module.ctx.func_sig(function, |sig| sig.name() == "read"))
                .unwrap();
            let args = module.ctx.func_sig(read, |sig| sig.args().len());
            assert_eq!(
                args,
                extra_count
                    + if promoted == 1 { 4 } else { 1 }
                    + usize::from(fresh_return && (!exposed_sibling || promoted == 1))
            );
            assert!(args <= 16);
        }
    }

    #[test]
    fn reserves_hidden_return_arguments_at_the_direct_operand_limit() {
        for (hidden_returns, promoted) in [(12, 1), (13, 0)] {
            let ret_tys = vec!["[i256; 5]"; hidden_returns].join(", ");
            let returns = vec!["v13"; hidden_returns].join(", ");
            let source = format!(
                r#"
target = "evm-ethereum-osaka"
type @Four = {{ i256, i256, i256, i256 }};
func private %read(v0.objref<@Four>) -> ({ret_tys}) {{
block0:
    v1.objref<i256> = obj.proj v0 0.i8;
    v2.i256 = obj.load v1;
    v3.objref<i256> = obj.proj v0 1.i8;
    v4.i256 = obj.load v3;
    v5.objref<i256> = obj.proj v0 2.i8;
    v6.i256 = obj.load v5;
    v7.objref<i256> = obj.proj v0 3.i8;
    v8.i256 = obj.load v7;
    v9.[i256; 5] = insert_value undef.[i256; 5] 0.i8 v2;
    v10.[i256; 5] = insert_value v9 1.i8 v4;
    v11.[i256; 5] = insert_value v10 2.i8 v6;
    v12.[i256; 5] = insert_value v11 3.i8 v8;
    v13.[i256; 5] = insert_value v12 4.i8 0.i256;
    return ({returns});
}}
"#
            );
            let module = parse_module(&source).unwrap().module;
            let config = VerifierConfig::for_level(VerificationLevel::Full);
            verify_module_or_panic(&module, &config);
            assert_eq!(
                ObjectArgPromotion::default().run(&module).promoted_args,
                promoted
            );
            verify_module_or_panic(&module, &config);
            ObjectAggregateAbi::new(ObjectAggregateAbiConfig::default())
                .lower_to_memory(&module, false)
                .unwrap();
            verify_module_or_panic(&module, &config);
            let args = module
                .ctx
                .func_sig(module.funcs()[0], |sig| sig.args().len());
            assert_eq!(args, if promoted == 1 { 16 } else { 14 });
        }
    }
}
