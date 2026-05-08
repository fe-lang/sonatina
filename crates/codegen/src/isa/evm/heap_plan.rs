use cranelift_entity::SecondaryMap;
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::FxHashMap;
use sonatina_ir::{
    BlockId, Function, InstId, InstSetExt, Module,
    cfg::ControlFlowGraph,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::FuncRef,
};

use super::memory_plan::{FuncMemPlan, ProgramMemoryPlan, compute_abs_clobber_words};

pub(crate) fn compute_malloc_future_abs_words(
    module: &Module,
    funcs: &[FuncRef],
    plan: &ProgramMemoryPlan,
    isa: &Evm,
) -> FxHashMap<FuncRef, FxHashMap<InstId, u32>> {
    let abs_clobber_words = compute_abs_clobber_words(module, funcs, plan);
    let mut results: Vec<_> = funcs
        .par_iter()
        .copied()
        .map(|f| {
            let func_plan = plan
                .funcs
                .get(&f)
                .unwrap_or_else(|| panic!("missing memory plan for func {}", f.as_u32()));
            let map = module.func_store.view(f, |function| {
                let mut cfg = ControlFlowGraph::new();
                cfg.compute(function);
                let ctx = FutureBoundsCtx {
                    isa,
                    plan,
                    func_plan,
                    abs_clobber_words: &abs_clobber_words,
                };
                compute_future_bounds_for_func(function, &cfg, &ctx)
            });
            (f, map)
        })
        .collect();
    results.sort_unstable_by_key(|(func, _)| func.as_u32());

    let mut out: FxHashMap<FuncRef, FxHashMap<InstId, u32>> = FxHashMap::default();
    for (func, map) in results {
        out.insert(func, map);
    }
    out
}

struct FutureBoundsCtx<'a> {
    isa: &'a Evm,
    plan: &'a ProgramMemoryPlan,
    func_plan: &'a FuncMemPlan,
    abs_clobber_words: &'a FxHashMap<FuncRef, u32>,
}

fn compute_future_bounds_for_func(
    function: &Function,
    cfg: &ControlFlowGraph,
    ctx: &FutureBoundsCtx<'_>,
) -> FxHashMap<InstId, u32> {
    fn call_bound(ctx: &FutureBoundsCtx<'_>, function: &Function, inst: InstId) -> u32 {
        let Some(call) = function.dfg.call_info(inst) else {
            return 0;
        };
        let callee = call.callee();
        let callee_plan = ctx.plan.funcs.get(&callee).unwrap_or_else(|| {
            panic!(
                "missing memory plan for callee {} in heap bounds analysis",
                callee.as_u32()
            )
        });
        ctx.abs_clobber_words
            .get(&callee)
            .copied()
            .unwrap_or_else(|| callee_plan.abs_words_end())
    }

    let mut block_in: SecondaryMap<BlockId, u32> = SecondaryMap::new();
    let mut block_local: SecondaryMap<BlockId, u32> = SecondaryMap::new();
    for block in function.layout.iter_block() {
        let _ = &mut block_in[block];
        let _ = &mut block_local[block];
    }

    for block in function.layout.iter_block() {
        let mut bound = ctx.func_plan.active_abs_words();
        for inst in function.layout.iter_inst(block) {
            bound = bound.max(call_bound(ctx, function, inst));
        }
        block_local[block] = bound;
    }

    let blocks: Vec<BlockId> = cfg.post_order().collect();
    let mut changed = true;
    while changed {
        changed = false;

        for &block in &blocks {
            let out = cfg.succs_of(block).map(|b| block_in[*b]).max().unwrap_or(0);
            let bound = out.max(block_local[block]);

            if bound > block_in[block] {
                block_in[block] = bound;
                changed = true;
            }
        }
    }

    let mut malloc_bounds: FxHashMap<InstId, u32> = FxHashMap::default();
    for block in function.layout.iter_block() {
        let out = cfg.succs_of(block).map(|b| block_in[*b]).max().unwrap_or(0);
        let mut bound = out.max(ctx.func_plan.active_abs_words());

        let insts: Vec<InstId> = function.layout.iter_inst(block).collect();
        for inst in insts.into_iter().rev() {
            bound = bound.max(call_bound(ctx, function, inst));

            if matches!(
                ctx.isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                EvmInstKind::EvmMalloc(_)
            ) {
                malloc_bounds.insert(inst, bound);
            }
        }
    }

    malloc_bounds
}
