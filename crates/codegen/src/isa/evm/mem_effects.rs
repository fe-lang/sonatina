use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    Function, InstSetExt, Module,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::FuncRef,
};

use crate::module_analysis::CallGraphSchedule;

use super::memory_plan::ProgramMemoryPlan;

#[derive(Clone, Copy, Default)]
pub(crate) struct FuncMemEffects {
    pub(crate) touches_static_arena: bool,
    pub(crate) touches_fixed_slots: bool,
    pub(crate) touches_dyn_frame: bool,
    pub(crate) touches_heap_meta: bool,
}

impl FuncMemEffects {
    fn union_with(&mut self, other: &FuncMemEffects) {
        self.touches_static_arena |= other.touches_static_arena;
        self.touches_fixed_slots |= other.touches_fixed_slots;
        self.touches_dyn_frame |= other.touches_dyn_frame;
        self.touches_heap_meta |= other.touches_heap_meta;
    }
}

/// Computes, for each function, which memory regions it transitively touches
/// (itself or through any callee).
pub(crate) fn compute_func_mem_effects(
    module: &Module,
    schedule: &CallGraphSchedule,
    plan: &ProgramMemoryPlan,
    fixed_slot_effects: &FxHashSet<FuncRef>,
    isa: &Evm,
) -> FxHashMap<FuncRef, FuncMemEffects> {
    let mut local_effect_results: Vec<_> = schedule
        .funcs()
        .par_iter()
        .copied()
        .map(|func| {
            let func_plan = plan.funcs.get(&func);
            let touches_static_arena = func_plan.is_some_and(|p| {
                p.scratch_words != 0 || p.stable_base_word().is_some() && p.stable_words != 0
            });
            let touches_dyn_frame = func_plan.is_some_and(|p| p.dynamic_frame_layout().is_some());
            let touches_heap_meta = module.func_store.view(func, |f| func_uses_malloc(f, isa));
            let touches_fixed_slots = fixed_slot_effects.contains(&func);
            (
                func,
                FuncMemEffects {
                    touches_static_arena,
                    touches_fixed_slots,
                    touches_dyn_frame,
                    touches_heap_meta,
                },
            )
        })
        .collect();
    local_effect_results.sort_unstable_by_key(|(func, _)| func.as_u32());
    let local_effects: FxHashMap<FuncRef, FuncMemEffects> =
        local_effect_results.into_iter().collect();

    schedule.join_over_callees(|func| local_effects[&func], FuncMemEffects::union_with)
}

fn func_uses_malloc(function: &Function, isa: &Evm) -> bool {
    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            if matches!(
                isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                EvmInstKind::EvmMalloc(_)
            ) {
                return true;
            }
        }
    }
    false
}
