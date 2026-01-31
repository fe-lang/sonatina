use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{BlockId, InstId, Module, ValueId, module::FuncRef};
use std::collections::{BTreeMap, BTreeSet};

use crate::{
    liveness::InstLiveness,
    module_analysis::{CallGraph, CallGraphSccs, SccBuilder, SccRef},
    stackalloc::StackifyAlloc,
};

use super::{
    ptr_escape::PtrEscapeSummary,
    static_arena_alloc::{
        FuncObjectLayout, FuncStackObjects, StackObjId, StaticArenaAllocCtx,
        build_func_object_layout, pack_objects_with_min_offsets, verify_object_packing,
    },
};
use sonatina_ir::isa::evm::Evm;

pub const WORD_BYTES: u32 = 32;
pub const FREE_PTR_SLOT: u8 = 0x40;
pub const DYN_SP_SLOT: u8 = 0x80;
pub const DYN_FP_SLOT: u8 = 0xa0;
pub const STATIC_BASE: u32 = 0xc0;

#[derive(Clone, Debug)]
pub struct ProgramMemoryPlan {
    pub dyn_base: u32,
    pub funcs: FxHashMap<FuncRef, FuncMemPlan>,
}

#[derive(Clone, Debug)]
pub struct FuncMemPlan {
    pub scheme: MemScheme,

    /// Word offsets for all stack objects in this function.
    ///
    /// For `StaticArena`, offsets are relative to `STATIC_BASE`.
    /// For `DynamicFrame`, offsets are relative to `fp`.
    pub obj_offset_words: FxHashMap<StackObjId, u32>,

    /// Convenience map for `Alloca` lowering.
    pub alloca_offset_words: FxHashMap<InstId, u32>,

    /// Convenience map for spill rewriting: ValueId -> obj id (non-scratch spills).
    pub spill_obj: SecondaryMap<ValueId, Option<StackObjId>>,

    /// Total local object extent (max offset + size), in words.
    pub locals_words: u32,

    pub malloc_future_static_words: FxHashMap<InstId, u32>,
    pub transient_mallocs: FxHashSet<InstId>,
}

#[derive(Clone, Debug)]
pub enum MemScheme {
    StaticArena(StaticArenaFuncPlan),
    DynamicFrame,
}

#[derive(Clone, Debug)]
pub struct StaticArenaFuncPlan {
    pub need_words: u32,

    /// Per-call preservation choice for calls to StaticArena callees with non-zero `need_words`.
    /// Only populated for StaticArena callers.
    pub call_choice: FxHashMap<InstId, CallPreserveChoice>,

    /// Save plans for calls chosen as `Save`/`ForcedSave` with a non-empty save set.
    pub call_saves: FxHashMap<InstId, CallSavePlan>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CallPreserveChoice {
    Layout,
    Save,
    ForcedSave,
}

#[derive(Clone, Debug)]
pub struct CallSavePlan {
    /// Word offsets (relative to STATIC_BASE) to save, in ascending order.
    pub save_word_offsets: Vec<u32>,

    /// Whether the call returns a value (IR: call has inst_result).
    pub has_return: bool,
}

#[derive(Clone, Copy, Debug)]
pub struct ArenaCostModel {
    pub w_mem: u64,
    pub w_save: u64,
    pub w_code: u64,
    pub w_stack: u64,
    pub max_save_words_per_call: u32,
}

impl Default for ArenaCostModel {
    fn default() -> Self {
        Self {
            w_mem: 1,
            w_save: 1,
            w_code: 200,
            w_stack: 0,
            max_save_words_per_call: 128,
        }
    }
}

pub(crate) struct FuncAnalysis {
    pub(crate) alloc: StackifyAlloc,
    pub(crate) inst_liveness: InstLiveness,
    pub(crate) block_order: Vec<BlockId>,
}

pub(crate) fn compute_program_memory_plan(
    module: &Module,
    funcs: &[FuncRef],
    analyses: &FxHashMap<FuncRef, FuncAnalysis>,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    isa: &Evm,
    cost_model: &ArenaCostModel,
) -> ProgramMemoryPlan {
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let call_graph = CallGraph::build_graph_subset(module, &funcs_set);
    let scc = SccBuilder::new().compute_scc(&call_graph);

    let topo = topo_sort_sccs(&funcs_set, &call_graph, &scc);

    let alloc_ctx = StaticArenaAllocCtx::new(&module.ctx, isa, ptr_escape);

    let mut need_words: FxHashMap<FuncRef, u32> = FxHashMap::default();
    let mut static_max_words: u32 = 0;
    let mut plans: FxHashMap<FuncRef, FuncMemPlan> = FxHashMap::default();

    for &scc_ref in topo.iter().rev() {
        let scc_info = scc.scc_info(scc_ref);
        let is_cyclic = scc_info.is_cycle;

        let mut component: Vec<FuncRef> = scc_info
            .components
            .iter()
            .copied()
            .filter(|f| funcs_set.contains(f))
            .collect();
        component.sort_unstable_by_key(|f| f.as_u32());

        let mut ext_need_max: u32 = 0;
        for &func in &component {
            for &callee in call_graph.callee_of(func) {
                if scc.scc_ref(callee) == scc_ref {
                    continue;
                }
                let need = *need_words.get(&callee).expect("callee missing need_words");
                ext_need_max = ext_need_max.max(need);
            }
        }

        struct PlannedFunc {
            layout: FuncObjectLayout,
            call_choice: FxHashMap<InstId, CallPreserveChoice>,
        }

        let mut stacks: FxHashMap<FuncRef, FuncStackObjects> = FxHashMap::default();
        for &func in &component {
            let analysis = analyses.get(&func).expect("missing FuncAnalysis");
            let stack: FuncStackObjects = module.func_store.view(func, |function| {
                alloc_ctx.compute_func_stack_objects(func, function, analysis)
            });
            stacks.insert(func, stack);
        }

        let mut planned: FxHashMap<FuncRef, PlannedFunc> = FxHashMap::default();
        let mut max_locals_words: u32;
        let mut fallback_dynamic: bool;
        let mut cap: u32 = ext_need_max;

        loop {
            planned.clear();
            max_locals_words = 0;
            fallback_dynamic = false;

            for &func in &component {
                let stack = stacks.get(&func).expect("missing stack");
                let Some((call_choice, layout)) = solve_call_preservation_for_func(
                    stack,
                    &need_words,
                    &scc,
                    scc_ref,
                    is_cyclic,
                    cost_model,
                    cap,
                ) else {
                    fallback_dynamic = true;
                    break;
                };

                max_locals_words = max_locals_words.max(layout.locals_words);
                planned.insert(
                    func,
                    PlannedFunc {
                        layout,
                        call_choice,
                    },
                );
            }

            if fallback_dynamic {
                break;
            }

            let new_cap = ext_need_max.max(max_locals_words);
            if new_cap == cap {
                break;
            }
            cap = new_cap;
        }

        if fallback_dynamic {
            for &func in &component {
                need_words.insert(func, 0);
            }

            for &func in &component {
                let stack = stacks.get(&func).expect("missing stack");
                let min_offset_words: FxHashMap<StackObjId, u32> = FxHashMap::default();
                let (obj_offset_words, locals_words) =
                    pack_objects_with_min_offsets(stack, &min_offset_words);
                let layout = build_func_object_layout(stack, obj_offset_words, locals_words);
                plans.insert(
                    func,
                    FuncMemPlan {
                        scheme: MemScheme::DynamicFrame,
                        obj_offset_words: layout.obj_offset_words,
                        alloca_offset_words: layout.alloca_offset_words,
                        spill_obj: layout.spill_obj,
                        locals_words: layout.locals_words,
                        malloc_future_static_words: FxHashMap::default(),
                        transient_mallocs: FxHashSet::default(),
                    },
                );
            }
            continue;
        }

        let need_scc = cap;
        for &func in &component {
            need_words.insert(func, need_scc);
            static_max_words = static_max_words.max(need_scc);
        }

        for &func in &component {
            let planned_func = planned.remove(&func).expect("missing planned func");
            let stack = stacks.get(&func).expect("missing stack");
            let call_saves = CallSavePlansForFuncCtx {
                stack,
                obj_offset_words: &planned_func.layout.obj_offset_words,
                call_choice: &planned_func.call_choice,
                need_words: &need_words,
                scc: &scc,
                scc_ref,
                need_scc,
            }
            .finalize_call_save_plans_for_func();

            plans.insert(
                func,
                FuncMemPlan {
                    scheme: MemScheme::StaticArena(StaticArenaFuncPlan {
                        need_words: need_scc,
                        call_choice: planned_func.call_choice,
                        call_saves,
                    }),
                    obj_offset_words: planned_func.layout.obj_offset_words,
                    alloca_offset_words: planned_func.layout.alloca_offset_words,
                    spill_obj: planned_func.layout.spill_obj,
                    locals_words: planned_func.layout.locals_words,
                    malloc_future_static_words: FxHashMap::default(),
                    transient_mallocs: FxHashSet::default(),
                },
            );
        }
    }

    let static_max_bytes = static_max_words
        .checked_mul(WORD_BYTES)
        .expect("static max bytes overflow");
    let dyn_base = STATIC_BASE
        .checked_add(static_max_bytes)
        .expect("dyn base overflow");

    let plan = ProgramMemoryPlan {
        dyn_base,
        funcs: plans,
    };

    #[cfg(debug_assertions)]
    if std::env::var_os("SONATINA_EVM_MEM_VERIFY").is_some() {
        verify_static_arena_plan(module, funcs, analyses, ptr_escape, isa, &scc, &plan);
    }

    plan
}

#[derive(Clone, Debug)]
struct CallMeta {
    inst: InstId,
    callee_need_words: u32,
    has_return: bool,
    is_internal_scc_call: bool,
    arg_count: u8,
    live_out_objs: Vec<StackObjId>,
    must_layout_objs: Vec<StackObjId>,
}

impl CallMeta {
    fn eligible_for_layout(&self) -> bool {
        !self.is_internal_scc_call && self.callee_need_words != 0
    }
}

fn solve_call_preservation_for_func(
    stack: &FuncStackObjects,
    need_words: &FxHashMap<FuncRef, u32>,
    scc: &CallGraphSccs,
    scc_ref: SccRef,
    is_cyclic_scc: bool,
    cost_model: &ArenaCostModel,
    mem_cost_cap_words: u32,
) -> Option<(FxHashMap<InstId, CallPreserveChoice>, FuncObjectLayout)> {
    if stack.requires_dynamic_frame {
        return None;
    }

    let mut calls: Vec<CallMeta> = Vec::new();
    for call in &stack.call_sites {
        let is_internal = is_cyclic_scc && scc.scc_ref(call.callee) == scc_ref;
        let callee_need_words = if is_internal {
            0
        } else {
            *need_words
                .get(&call.callee)
                .expect("callee missing need_words")
        };

        if !is_internal && callee_need_words == 0 {
            continue;
        }
        if is_internal && !call.must_layout_objs.is_empty() {
            return None;
        }

        calls.push(CallMeta {
            inst: call.inst,
            callee_need_words,
            has_return: call.has_return,
            is_internal_scc_call: is_internal,
            arg_count: call.arg_count,
            live_out_objs: call.live_out_objs.clone(),
            must_layout_objs: call.must_layout_objs.clone(),
        });
    }

    let child_need_max = calls
        .iter()
        .filter(|c| !c.is_internal_scc_call)
        .map(|c| c.callee_need_words)
        .max()
        .unwrap_or(0);

    fn mem_expansion_gas(words: u32) -> u64 {
        let w = u128::from(words);
        let lin = 3u128 * w;
        let quad = (w * w) / 512u128;
        u64::try_from(lin + quad).expect("mem gas overflow")
    }

    fn push_imm_len_u32(imm: u32) -> u64 {
        if imm == 0 {
            return 0;
        }
        let bits = 32 - imm.leading_zeros();
        u64::from(bits.div_ceil(8))
    }

    fn mem_load_abs_bytes(addr: u32) -> u64 {
        // PUSHn + imm + MLOAD, or PUSH0 + MLOAD.
        2 + push_imm_len_u32(addr)
    }

    fn mem_store_abs_bytes(addr: u32) -> u64 {
        // PUSHn + imm + MSTORE, or PUSH0 + MSTORE.
        2 + push_imm_len_u32(addr)
    }

    fn save_gas(k: u64, arg_count: u64, has_return: bool) -> u64 {
        let swap_chunks = if has_return && k != 0 {
            k.div_ceil(16)
        } else {
            0
        };
        k.checked_mul(12)
            .and_then(|g| g.checked_add(k.checked_mul(arg_count).and_then(|s| s.checked_mul(3))?))
            .and_then(|g| g.checked_add(swap_chunks.checked_mul(3)?))
            .expect("save gas overflow")
    }

    fn save_code_bytes(save_offsets: &[u32], arg_count: u64, has_return: bool) -> u64 {
        let mut bytes: u64 = 0;
        for &w in save_offsets {
            let addr = STATIC_BASE
                .checked_add(w.checked_mul(WORD_BYTES).expect("save addr overflow"))
                .expect("save addr overflow");
            bytes = bytes
                .checked_add(mem_load_abs_bytes(addr))
                .and_then(|b| b.checked_add(mem_store_abs_bytes(addr)))
                .expect("save bytes overflow");
        }

        let k = u64::try_from(save_offsets.len()).expect("save count overflow");
        bytes = bytes
            .checked_add(k.checked_mul(arg_count).expect("swap bytes overflow"))
            .expect("swap bytes overflow");

        if has_return && k != 0 {
            bytes = bytes
                .checked_add(k.div_ceil(16))
                .expect("swap bytes overflow");
        }

        bytes
    }

    fn save_set(
        stack: &FuncStackObjects,
        obj_offset_words: &FxHashMap<StackObjId, u32>,
        live_out_objs: &[StackObjId],
        must_layout_objs: &[StackObjId],
        callee_need_words: u32,
    ) -> Vec<u32> {
        if callee_need_words == 0 {
            return Vec::new();
        }

        let mut out: Vec<u32> = Vec::new();
        for &obj in live_out_objs {
            if must_layout_objs.binary_search(&obj).is_ok() {
                continue;
            }
            let Some(&off) = obj_offset_words.get(&obj) else {
                continue;
            };
            let Some(&size) = stack.obj_size_words.get(&obj) else {
                continue;
            };
            if size == 0 || off >= callee_need_words {
                continue;
            }
            let end = off.checked_add(size).expect("object end words overflow");
            let end = end.min(callee_need_words);
            for w in off..end {
                out.push(w);
            }
        }
        out.sort_unstable();
        out.dedup();
        out
    }

    fn evaluate(
        stack: &FuncStackObjects,
        calls: &[CallMeta],
        layout_calls: &FxHashSet<InstId>,
        child_need_max: u32,
        mem_cost_cap_words: u32,
        cost_model: &ArenaCostModel,
    ) -> Option<(u64, FuncObjectLayout)> {
        let mut min_offset_words: FxHashMap<StackObjId, u32> = FxHashMap::default();
        for call in calls {
            for &obj in &call.must_layout_objs {
                min_offset_words
                    .entry(obj)
                    .and_modify(|m| *m = (*m).max(call.callee_need_words))
                    .or_insert(call.callee_need_words);
            }

            if !call.eligible_for_layout() || !layout_calls.contains(&call.inst) {
                continue;
            }
            for &obj in &call.live_out_objs {
                min_offset_words
                    .entry(obj)
                    .and_modify(|m| *m = (*m).max(call.callee_need_words))
                    .or_insert(call.callee_need_words);
            }
        }

        let (obj_offset_words, locals_words) =
            pack_objects_with_min_offsets(stack, &min_offset_words);

        let need_est = locals_words.max(child_need_max);
        let need_for_cost = need_est.max(mem_cost_cap_words);
        let base_words = STATIC_BASE / WORD_BYTES;
        let mem_words = base_words
            .checked_add(need_for_cost)
            .expect("mem words overflow");
        let mut cost = cost_model
            .w_mem
            .checked_mul(mem_expansion_gas(mem_words))
            .expect("mem cost overflow");

        for call in calls {
            let is_save = call.is_internal_scc_call
                || (call.callee_need_words != 0 && !layout_calls.contains(&call.inst));
            if !is_save {
                continue;
            }

            let callee_need_words = if call.is_internal_scc_call {
                // Internal SCC calls use a clobber prefix that is >= locals_words, so the full
                // live object ranges overlap and need to be saved.
                locals_words
            } else {
                call.callee_need_words
            };

            let save_offsets = save_set(
                stack,
                &obj_offset_words,
                &call.live_out_objs,
                &call.must_layout_objs,
                callee_need_words,
            );

            let k = u64::try_from(save_offsets.len()).expect("save count overflow");
            if k > u64::from(cost_model.max_save_words_per_call) {
                if call.is_internal_scc_call {
                    return None;
                }

                cost = cost.saturating_add(u64::MAX / 4);
                continue;
            }

            let arg_count = u64::from(call.arg_count);
            let gas = save_gas(k, arg_count, call.has_return);
            let bytes = save_code_bytes(&save_offsets, arg_count, call.has_return);
            let stack_risk = k;

            cost = cost
                .checked_add(
                    cost_model
                        .w_save
                        .checked_mul(gas)
                        .expect("save cost overflow"),
                )
                .and_then(|c| {
                    c.checked_add(
                        cost_model
                            .w_code
                            .checked_mul(bytes)
                            .expect("code cost overflow"),
                    )
                })
                .and_then(|c| {
                    c.checked_add(
                        cost_model
                            .w_stack
                            .checked_mul(stack_risk)
                            .expect("stack cost overflow"),
                    )
                })
                .expect("total cost overflow");
        }

        let layout = build_func_object_layout(stack, obj_offset_words, locals_words);
        Some((cost, layout))
    }

    let mut layout_calls: FxHashSet<InstId> = FxHashSet::default();
    let (mut best_cost, mut best_layout) = evaluate(
        stack,
        &calls,
        &layout_calls,
        child_need_max,
        mem_cost_cap_words,
        cost_model,
    )?;

    let mut promotion_order: Vec<InstId> = Vec::new();
    loop {
        let mut best_improvement: u64 = 0;
        let mut best_call: Option<InstId> = None;
        let mut best_candidate: Option<(u64, FuncObjectLayout)> = None;

        let mut candidates: Vec<InstId> = calls
            .iter()
            .filter(|c| c.eligible_for_layout() && !layout_calls.contains(&c.inst))
            .map(|c| c.inst)
            .collect();
        candidates.sort_unstable_by_key(|i| i.as_u32());

        for inst in candidates {
            let mut candidate_layout_calls = layout_calls.clone();
            candidate_layout_calls.insert(inst);
            let Some((cost, layout)) = evaluate(
                stack,
                &calls,
                &candidate_layout_calls,
                child_need_max,
                mem_cost_cap_words,
                cost_model,
            ) else {
                continue;
            };

            if cost >= best_cost {
                continue;
            }

            let improvement = best_cost - cost;
            if improvement > best_improvement
                || (improvement == best_improvement
                    && best_call.is_some_and(|prev| inst.as_u32() < prev.as_u32()))
            {
                best_improvement = improvement;
                best_call = Some(inst);
                best_candidate = Some((cost, layout));
            }
        }

        let Some(call) = best_call else {
            break;
        };
        let Some((cost, layout)) = best_candidate else {
            break;
        };

        layout_calls.insert(call);
        promotion_order.push(call);
        best_cost = cost;
        best_layout = layout;
    }

    for &inst in promotion_order.iter().rev() {
        if !layout_calls.contains(&inst) {
            continue;
        }

        let mut candidate_layout_calls = layout_calls.clone();
        candidate_layout_calls.remove(&inst);

        let Some((cost, layout)) = evaluate(
            stack,
            &calls,
            &candidate_layout_calls,
            child_need_max,
            mem_cost_cap_words,
            cost_model,
        ) else {
            continue;
        };

        if cost < best_cost {
            layout_calls = candidate_layout_calls;
            best_cost = cost;
            best_layout = layout;
        }
    }

    let mut call_choice: FxHashMap<InstId, CallPreserveChoice> = FxHashMap::default();
    for call in calls {
        if call.is_internal_scc_call {
            call_choice.insert(call.inst, CallPreserveChoice::ForcedSave);
            continue;
        }

        if call.callee_need_words == 0 {
            continue;
        }

        let choice = if layout_calls.contains(&call.inst) {
            CallPreserveChoice::Layout
        } else {
            CallPreserveChoice::Save
        };
        call_choice.insert(call.inst, choice);
    }

    Some((call_choice, best_layout))
}

struct CallSavePlansForFuncCtx<'a> {
    stack: &'a FuncStackObjects,
    obj_offset_words: &'a FxHashMap<StackObjId, u32>,
    call_choice: &'a FxHashMap<InstId, CallPreserveChoice>,
    need_words: &'a FxHashMap<FuncRef, u32>,
    scc: &'a CallGraphSccs,
    scc_ref: SccRef,
    need_scc: u32,
}

impl CallSavePlansForFuncCtx<'_> {
    fn finalize_call_save_plans_for_func(&self) -> FxHashMap<InstId, CallSavePlan> {
        let is_cyclic_scc = self.scc.scc_info(self.scc_ref).is_cycle;
        let mut out: FxHashMap<InstId, CallSavePlan> = FxHashMap::default();

        for call in &self.stack.call_sites {
            let Some(choice) = self.call_choice.get(&call.inst).copied() else {
                continue;
            };
            if matches!(choice, CallPreserveChoice::Layout) {
                continue;
            }

            let callee_need_words =
                if is_cyclic_scc && self.scc.scc_ref(call.callee) == self.scc_ref {
                    self.need_scc
                } else {
                    *self
                        .need_words
                        .get(&call.callee)
                        .expect("callee missing need_words")
                };

            if callee_need_words == 0 {
                continue;
            }

            let mut save_offsets: Vec<u32> = Vec::new();
            for &obj in &call.live_out_objs {
                if call.must_layout_objs.binary_search(&obj).is_ok() {
                    continue;
                }
                let Some(&off) = self.obj_offset_words.get(&obj) else {
                    continue;
                };
                let Some(&size) = self.stack.obj_size_words.get(&obj) else {
                    continue;
                };
                if size == 0 || off >= callee_need_words {
                    continue;
                }
                let end = off
                    .checked_add(size)
                    .expect("object end words overflow")
                    .min(callee_need_words);
                for w in off..end {
                    save_offsets.push(w);
                }
            }
            save_offsets.sort_unstable();
            save_offsets.dedup();

            if save_offsets.is_empty() {
                continue;
            }

            out.insert(
                call.inst,
                CallSavePlan {
                    save_word_offsets: save_offsets,
                    has_return: call.has_return,
                },
            );
        }

        out
    }
}

#[cfg(debug_assertions)]
fn verify_static_arena_plan(
    module: &Module,
    funcs: &[FuncRef],
    analyses: &FxHashMap<FuncRef, FuncAnalysis>,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    isa: &Evm,
    scc: &CallGraphSccs,
    plan: &ProgramMemoryPlan,
) {
    let mut need_words: FxHashMap<FuncRef, u32> = FxHashMap::default();
    for (&f, p) in &plan.funcs {
        if let MemScheme::StaticArena(st) = &p.scheme {
            need_words.insert(f, st.need_words);
        }
    }

    let alloc_ctx = StaticArenaAllocCtx::new(&module.ctx, isa, ptr_escape);

    for &func in funcs {
        let Some(func_plan) = plan.funcs.get(&func) else {
            continue;
        };
        let MemScheme::StaticArena(st) = &func_plan.scheme else {
            continue;
        };
        let analysis = analyses.get(&func).expect("missing analysis");
        let scc_ref = scc.scc_ref(func);
        let is_cyclic_scc = scc.scc_info(scc_ref).is_cycle;

        module.func_store.view(func, |function| {
            let stack = alloc_ctx.compute_func_stack_objects(func, function, analysis);

            verify_object_packing(
                func,
                &stack,
                &func_plan.obj_offset_words,
                func_plan.locals_words,
            );

            let expected_saves = CallSavePlansForFuncCtx {
                stack: &stack,
                obj_offset_words: &func_plan.obj_offset_words,
                call_choice: &st.call_choice,
                need_words: &need_words,
                scc,
                scc_ref,
                need_scc: st.need_words,
            }
            .finalize_call_save_plans_for_func();

            if expected_saves.len() != st.call_saves.len() {
                panic!(
                    "StaticArena call_saves mismatch in func {}: expected {} entries, got {}",
                    func.as_u32(),
                    expected_saves.len(),
                    st.call_saves.len()
                );
            }

            for (inst, expected) in expected_saves {
                let actual = st
                    .call_saves
                    .get(&inst)
                    .unwrap_or_else(|| panic!("StaticArena missing call_saves entry for {inst:?}"));

                if actual.has_return != expected.has_return
                    || actual.save_word_offsets != expected.save_word_offsets
                {
                    panic!(
                        "StaticArena call_saves mismatch in func {} at inst {}",
                        func.as_u32(),
                        inst.as_u32()
                    );
                }
            }

            for call in &stack.call_sites {
                let callee = call.callee;
                let Some(callee_plan) = plan.funcs.get(&callee) else {
                    continue;
                };
                let MemScheme::StaticArena(callee_static) = &callee_plan.scheme else {
                    continue;
                };

                let is_internal = is_cyclic_scc && scc.scc_ref(callee) == scc_ref;
                let callee_need_words = if is_internal {
                    st.need_words
                } else {
                    callee_static.need_words
                };

                if callee_need_words == 0 && !is_internal {
                    continue;
                }

                let Some(choice) = st.call_choice.get(&call.inst).copied() else {
                    panic!(
                        "StaticArena missing call_choice in func {} at inst {}",
                        func.as_u32(),
                        call.inst.as_u32()
                    );
                };

                if is_internal && !matches!(choice, CallPreserveChoice::ForcedSave) {
                    panic!(
                        "StaticArena internal SCC call is not ForcedSave in func {} at inst {}",
                        func.as_u32(),
                        call.inst.as_u32()
                    );
                }

                if matches!(choice, CallPreserveChoice::Layout) {
                    for &obj in &call.live_out_objs {
                        let off = func_plan.obj_offset_words.get(&obj).copied().unwrap_or_else(|| {
                            panic!("missing offset for obj {} in func {}", obj.as_u32(), func.as_u32())
                        });
                        if off < callee_need_words {
                            panic!(
                                "StaticArena Layout violates min-offset in func {} at inst {}: obj {} at {off} < need_words={callee_need_words}",
                                func.as_u32(),
                                call.inst.as_u32(),
                                obj.as_u32(),
                            );
                        }
                    }
                }

                for &obj in &call.must_layout_objs {
                    let off = func_plan.obj_offset_words.get(&obj).copied().unwrap_or_else(|| {
                        panic!("missing offset for obj {} in func {}", obj.as_u32(), func.as_u32())
                    });
                    if off < callee_need_words {
                        panic!(
                            "StaticArena call violates must-layout in func {} at inst {}: obj {} at {off} < need_words={callee_need_words}",
                            func.as_u32(),
                            call.inst.as_u32(),
                            obj.as_u32(),
                        );
                    }
                }

                if !matches!(choice, CallPreserveChoice::Layout) {
                    let saved = st
                        .call_saves
                        .get(&call.inst)
                        .map(|p| p.save_word_offsets.as_slice())
                        .unwrap_or(&[]);

                    for &obj in &call.live_out_objs {
                        if call.must_layout_objs.binary_search(&obj).is_ok() {
                            continue;
                        }

                        let off =
                            func_plan.obj_offset_words.get(&obj).copied().unwrap_or_else(|| {
                                panic!(
                                    "missing offset for obj {} in func {}",
                                    obj.as_u32(),
                                    func.as_u32()
                                )
                            });
                        let size = stack.obj_size_words.get(&obj).copied().unwrap_or_else(|| {
                            panic!(
                                "missing size for obj {} in func {}",
                                obj.as_u32(),
                                func.as_u32()
                            )
                        });
                        if size == 0 || off >= callee_need_words {
                            continue;
                        }

                        let end = off
                            .checked_add(size)
                            .expect("obj end words overflow")
                            .min(callee_need_words);
                        for w in off..end {
                            if saved.binary_search(&w).is_err() {
                                panic!(
                                    "StaticArena save plan missing word {w} in func {} at inst {}",
                                    func.as_u32(),
                                    call.inst.as_u32()
                                );
                            }
                        }
                    }
                }
            }
        });
    }
}

fn topo_sort_sccs(
    funcs: &FxHashSet<FuncRef>,
    call_graph: &CallGraph,
    scc: &CallGraphSccs,
) -> Vec<SccRef> {
    let mut sccs: BTreeSet<SccRef> = BTreeSet::new();
    for &f in funcs {
        sccs.insert(scc.scc_ref(f));
    }

    let mut edges: BTreeMap<SccRef, BTreeSet<SccRef>> = BTreeMap::new();
    let mut indegree: BTreeMap<SccRef, usize> = BTreeMap::new();
    for &s in &sccs {
        edges.insert(s, BTreeSet::new());
        indegree.insert(s, 0);
    }

    for &f in funcs {
        let from = scc.scc_ref(f);
        for &callee in call_graph.callee_of(f) {
            let to = scc.scc_ref(callee);
            if from == to {
                continue;
            }

            let tos = edges.get_mut(&from).expect("missing scc");
            if tos.insert(to) {
                *indegree.get_mut(&to).expect("missing scc") += 1;
            }
        }
    }

    let mut ready: BTreeSet<SccRef> = BTreeSet::new();
    for (&s, &deg) in &indegree {
        if deg == 0 {
            ready.insert(s);
        }
    }

    let mut topo: Vec<SccRef> = Vec::with_capacity(sccs.len());
    while let Some(&s) = ready.first() {
        ready.remove(&s);
        topo.push(s);

        let tos: Vec<SccRef> = edges
            .get(&s)
            .expect("missing scc")
            .iter()
            .copied()
            .collect();
        for to in tos {
            let deg = indegree.get_mut(&to).expect("missing scc");
            *deg = deg.checked_sub(1).expect("indegree underflow");
            if *deg == 0 {
                ready.insert(to);
            }
        }
    }

    debug_assert_eq!(topo.len(), sccs.len(), "SCC topo sort incomplete");
    topo
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        critical_edge::CriticalEdgeSplitter, domtree::DomTree,
        isa::evm::ptr_escape::compute_ptr_escape_summaries, liveness::Liveness,
    };
    use sonatina_ir::cfg::ControlFlowGraph;
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    fn plan_from_src(src: &str) -> (Module, ProgramMemoryPlan, FxHashMap<String, FuncRef>) {
        plan_from_src_with_cost(src, &ArenaCostModel::default())
    }

    fn plan_from_src_with_cost(
        src: &str,
        cost_model: &ArenaCostModel,
    ) -> (Module, ProgramMemoryPlan, FxHashMap<String, FuncRef>) {
        let parsed = parse_module(src).unwrap();
        let funcs: Vec<FuncRef> = parsed.module.funcs();

        let isa = Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        });

        let mut analyses: FxHashMap<FuncRef, FuncAnalysis> = FxHashMap::default();
        for &func in &funcs {
            parsed.module.func_store.modify(func, |function| {
                let mut cfg = ControlFlowGraph::new();
                cfg.compute(function);

                let mut splitter = CriticalEdgeSplitter::new();
                splitter.run(function, &mut cfg);

                let mut liveness = Liveness::new();
                liveness.compute(function, &cfg);

                let mut inst_liveness = InstLiveness::new();
                inst_liveness.compute(function, &cfg, &liveness);

                let mut dom = DomTree::new();
                dom.compute(&cfg);

                let block_order = dom.rpo().to_owned();
                let alloc = StackifyAlloc::for_function(function, &cfg, &dom, &liveness, 16);

                analyses.insert(
                    func,
                    FuncAnalysis {
                        alloc,
                        inst_liveness,
                        block_order,
                    },
                );
            });
        }

        let ptr_escape = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);
        let plan = compute_program_memory_plan(
            &parsed.module,
            &funcs,
            &analyses,
            &ptr_escape,
            &isa,
            cost_model,
        );

        let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
        for f in funcs {
            let name = parsed.module.ctx.func_sig(f, |sig| sig.name().to_string());
            names.insert(name, f);
        }

        (parsed.module, plan, names)
    }

    #[test]
    fn static_arena_chain_has_no_base_stacking() {
        let (_module, plan, names) = plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %c() -> i256 {
block0:
    v0.*i256 = alloca i256;
    return 0.i256;
}

func public %b() -> i256 {
block0:
    v0.*i256 = alloca i256;
    v1.i256 = call %c;
    return v1;
}

func public %a() -> i256 {
block0:
    v0.*i256 = alloca i256;
    v1.i256 = call %b;
    return v1;
}
"#,
        );

        assert_eq!(plan.dyn_base, STATIC_BASE + WORD_BYTES);

        for name in ["a", "b", "c"] {
            let func = names[name];
            let MemScheme::StaticArena(p) = &plan.funcs[&func].scheme else {
                panic!("expected {name} to be StaticArena");
            };
            assert_eq!(p.need_words, 1);
        }
    }

    #[test]
    fn call_live_alloca_is_placed_above_callee_need() {
        let (module, plan, names) = plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %callee() -> i256 {
block0:
    v0.*i256 = alloca i256;
    v1.*i256 = alloca i256;
    v2.*i256 = alloca i256;
    v3.*i256 = alloca i256;
    v4.*i256 = alloca i256;
    mstore v0 0.i256 i256;
    mstore v1 0.i256 i256;
    mstore v2 0.i256 i256;
    mstore v3 0.i256 i256;
    mstore v4 0.i256 i256;
    v5.i256 = mload v0 i256;
    v6.i256 = mload v1 i256;
    v7.i256 = mload v2 i256;
    v8.i256 = mload v3 i256;
    v9.i256 = mload v4 i256;
    v10.i256 = add v5 v6;
    v11.i256 = add v10 v7;
    v12.i256 = add v11 v8;
    v13.i256 = add v12 v9;
    return v13;
}

func public %caller() -> i256 {
block0:
    v0.*i256 = alloca i256;
    mstore v0 1.i256 i256;
    v1.i256 = call %callee;
    mstore v0 v1 i256;
    v2.i256 = mload v0 i256;
    return v2;
}
"#,
        );

        let callee = names["callee"];
        let caller = names["caller"];

        let MemScheme::StaticArena(callee_plan) = &plan.funcs[&callee].scheme else {
            panic!("expected callee to be StaticArena");
        };
        let MemScheme::StaticArena(caller_plan) = &plan.funcs[&caller].scheme else {
            panic!("expected caller to be StaticArena");
        };

        let call_inst = module.func_store.view(caller, |function| {
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    if function.dfg.call_info(inst).is_some() {
                        return inst;
                    }
                }
            }
            panic!("missing call inst");
        });

        let mut allocas: Vec<InstId> = plan.funcs[&caller]
            .alloca_offset_words
            .keys()
            .copied()
            .collect();
        allocas.sort_unstable_by_key(|i| i.as_u32());
        assert_eq!(allocas.len(), 1);

        let off = plan.funcs[&caller].alloca_offset_words[&allocas[0]];
        match caller_plan.call_choice.get(&call_inst) {
            Some(CallPreserveChoice::Layout) => assert!(off >= callee_plan.need_words),
            Some(CallPreserveChoice::Save | CallPreserveChoice::ForcedSave) => {
                let save = caller_plan
                    .call_saves
                    .get(&call_inst)
                    .expect("missing call save plan");
                assert!(save.has_return);
                assert_eq!(save.save_word_offsets.as_slice(), &[off]);
            }
            None => panic!("missing call choice"),
        }
    }

    #[test]
    fn pointer_arg_alloca_is_layout_preserved_and_not_call_saved() {
        let cost_model = ArenaCostModel {
            w_save: 0,
            w_code: 0,
            ..ArenaCostModel::default()
        };
        let (module, plan, names) = plan_from_src_with_cost(
            r#"
target = "evm-ethereum-osaka"

func public %callee(v0.*i256) -> i256 {
block0:
    v1.*i256 = alloca i256;
    mstore v1 0.i256 i256;
    mstore v0 42.i256 i256;
    return 0.i256;
}

func public %caller() -> i256 {
block0:
    v0.*i256 = alloca i256;
    mstore v0 1.i256 i256;
    v1.i256 = call %callee v0;
    v2.i256 = mload v0 i256;
    return v2;
}
"#,
            &cost_model,
        );

        let callee = names["callee"];
        let caller = names["caller"];

        let MemScheme::StaticArena(callee_plan) = &plan.funcs[&callee].scheme else {
            panic!("expected callee to be StaticArena");
        };
        let MemScheme::StaticArena(caller_plan) = &plan.funcs[&caller].scheme else {
            panic!("expected caller to be StaticArena");
        };

        let call_inst = module.func_store.view(caller, |function| {
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    if function.dfg.call_info(inst).is_some() {
                        return inst;
                    }
                }
            }
            panic!("missing call inst");
        });

        let mut allocas: Vec<InstId> = plan.funcs[&caller]
            .alloca_offset_words
            .keys()
            .copied()
            .collect();
        allocas.sort_unstable_by_key(|i| i.as_u32());
        assert_eq!(allocas.len(), 1);

        let off = plan.funcs[&caller].alloca_offset_words[&allocas[0]];
        assert!(off >= callee_plan.need_words);
        if let Some(save) = caller_plan.call_saves.get(&call_inst) {
            assert!(!save.save_word_offsets.contains(&off));
        }
    }

    #[test]
    fn transitive_points_to_through_local_memory_is_must_layout() {
        let (_module, plan, names) = plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %callee(v0.**i256) -> i256 {
block0:
    v1.*i256 = alloca i256;
    mstore v1 0.i256 i256;
    v2.*i256 = mload v0 *i256;
    mstore v2 42.i256 i256;
    return 0.i256;
}

func public %caller() -> i256 {
block0:
    v0.*i256 = alloca i256;
    v1.**i256 = alloca *i256;
    mstore v0 1.i256 i256;
    mstore v1 v0 *i256;
    v2.i256 = call %callee v1;
    return v2;
}
"#,
        );

        let callee = names["callee"];
        let caller = names["caller"];

        let MemScheme::StaticArena(callee_plan) = &plan.funcs[&callee].scheme else {
            panic!("expected callee to be StaticArena");
        };
        let MemScheme::StaticArena(_) = &plan.funcs[&caller].scheme else {
            panic!("expected caller to be StaticArena");
        };

        let mut allocas: Vec<InstId> = plan.funcs[&caller]
            .alloca_offset_words
            .keys()
            .copied()
            .collect();
        allocas.sort_unstable_by_key(|i| i.as_u32());
        assert_eq!(allocas.len(), 2);

        for inst in allocas {
            let off = plan.funcs[&caller].alloca_offset_words[&inst];
            assert!(off >= callee_plan.need_words);
        }
    }

    #[test]
    fn self_recursion_uses_static_arena_with_forced_save() {
        let (_module, plan, names) = plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %f() -> i256 {
block0:
    v0.*i256 = alloca i256;
    v1.i256 = call %f;
    return v1;
}
"#,
        );

        let f = names["f"];
        let MemScheme::StaticArena(p) = &plan.funcs[&f].scheme else {
            panic!("expected f to be StaticArena");
        };
        assert_eq!(p.need_words, 1);
        assert_eq!(plan.dyn_base, STATIC_BASE + WORD_BYTES);
    }

    #[test]
    fn recursion_passing_local_alloca_pointer_falls_back_to_dynamic_frame() {
        let (_module, plan, names) = plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.*i256) -> i256 {
block0:
    v1.*i256 = alloca i256;
    mstore v1 0.i256 i256;
    v2.i256 = call %f v1;
    return v2;
}
"#,
        );

        let f = names["f"];
        assert!(matches!(plan.funcs[&f].scheme, MemScheme::DynamicFrame));
        assert_eq!(plan.dyn_base, STATIC_BASE);
    }
}
