use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use sonatina_ir::{
    BlockId, Function, InstId, InstSetExt, Module, ValueId,
    cfg::ControlFlowGraph,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};

use super::{
    memory_plan::{
        FuncAnalysis, FuncMemPlan, ObjLoc, ProgramMemoryPlan, WORD_BYTES, compute_abs_clobber_words,
    },
    provenance::compute_value_provenance,
};

pub(crate) fn compute_malloc_future_abs_words(
    module: &Module,
    funcs: &[FuncRef],
    plan: &ProgramMemoryPlan,
    analyses: &FxHashMap<FuncRef, FuncAnalysis>,
    isa: &Evm,
) -> FxHashMap<FuncRef, FxHashMap<InstId, u32>> {
    let abs_clobber_words = compute_abs_clobber_words(module, funcs, plan);
    let mut out: FxHashMap<FuncRef, FxHashMap<InstId, u32>> = FxHashMap::default();
    for &f in funcs {
        let func_plan = plan
            .funcs
            .get(&f)
            .unwrap_or_else(|| panic!("missing memory plan for func {}", f.as_u32()));
        let analysis = analyses
            .get(&f)
            .unwrap_or_else(|| panic!("missing analysis for func {}", f.as_u32()));
        let map = module.func_store.view(f, |function| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);
            let ctx = FutureBoundsCtx {
                module: &module.ctx,
                isa,
                plan,
                func_plan,
                abs_clobber_words: &abs_clobber_words,
                analysis,
            };
            compute_future_bounds_for_func(function, &cfg, &ctx)
        });
        out.insert(f, map);
    }
    out
}

struct FutureBoundsCtx<'a> {
    module: &'a ModuleCtx,
    isa: &'a Evm,
    plan: &'a ProgramMemoryPlan,
    func_plan: &'a FuncMemPlan,
    abs_clobber_words: &'a FxHashMap<FuncRef, u32>,
    analysis: &'a FuncAnalysis,
}

fn compute_future_bounds_for_func(
    function: &Function,
    cfg: &ControlFlowGraph,
    ctx: &FutureBoundsCtx<'_>,
) -> FxHashMap<InstId, u32> {
    let prov = compute_value_provenance(function, ctx.module, ctx.isa, |callee| {
        let arg_count = ctx.module.func_sig(callee, |sig| sig.args().len());
        vec![true; arg_count]
    });

    let mut alloca_end_words: FxHashMap<InstId, u32> = FxHashMap::default();
    for (&inst, &loc) in &ctx.func_plan.alloca_loc {
        let data = ctx.isa.inst_set().resolve_inst(function.dfg.inst(inst));
        let EvmInstKind::Alloca(alloca) = data else {
            continue;
        };

        let Some(base_word) = absolute_base_word_for_loc(ctx.func_plan, loc) else {
            continue;
        };
        let size_bytes: u32 = ctx
            .isa
            .type_layout()
            .size_of(*alloca.ty(), ctx.module)
            .expect("alloca has invalid type") as u32;
        let size_words = size_bytes.div_ceil(WORD_BYTES);
        let end_words = base_word
            .checked_add(size_words)
            .expect("alloca end words overflow");
        alloca_end_words.insert(inst, end_words);
    }

    let mut value_alloca_bound: SecondaryMap<ValueId, u32> = SecondaryMap::new();
    let mut value_spill_bound: SecondaryMap<ValueId, u32> = SecondaryMap::new();
    for value in function.dfg.value_ids() {
        let _ = &mut value_alloca_bound[value];
        let _ = &mut value_spill_bound[value];
    }

    for value in function.dfg.value_ids() {
        let mut max_end: u32 = 0;
        for base in prov[value].alloca_insts() {
            if let Some(end) = alloca_end_words.get(&base) {
                max_end = max_end.max(*end);
            }
        }
        value_alloca_bound[value] = max_end;

        if let Some(obj) = ctx.func_plan.spill_obj[value]
            && let Some(loc) = ctx.func_plan.obj_loc.get(&obj).copied()
            && let Some(start_word) = absolute_base_word_for_loc(ctx.func_plan, loc)
        {
            value_spill_bound[value] = start_word.checked_add(1).expect("spill end overflow");
        }
    }

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

    fn live_bound(
        inst_liveness: &crate::liveness::InstLiveness,
        value_alloca_bound: &SecondaryMap<ValueId, u32>,
        value_spill_bound: &SecondaryMap<ValueId, u32>,
        inst: InstId,
    ) -> u32 {
        inst_liveness
            .live_out(inst)
            .iter()
            .map(|v| value_alloca_bound[v].max(value_spill_bound[v]))
            .max()
            .unwrap_or(0)
    }

    let mut block_in: SecondaryMap<BlockId, u32> = SecondaryMap::new();
    let mut block_local: SecondaryMap<BlockId, u32> = SecondaryMap::new();
    for block in function.layout.iter_block() {
        let _ = &mut block_in[block];
        let _ = &mut block_local[block];
    }

    for block in function.layout.iter_block() {
        let mut bound = ctx.func_plan.entry_abs_words;
        for inst in function.layout.iter_inst(block) {
            bound = bound.max(call_bound(ctx, function, inst));
            bound = bound.max(live_bound(
                &ctx.analysis.inst_liveness,
                &value_alloca_bound,
                &value_spill_bound,
                inst,
            ));
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
        let mut bound = out.max(ctx.func_plan.entry_abs_words);

        let insts: Vec<InstId> = function.layout.iter_inst(block).collect();
        for inst in insts.into_iter().rev() {
            bound = bound.max(call_bound(ctx, function, inst));
            bound = bound.max(live_bound(
                &ctx.analysis.inst_liveness,
                &value_alloca_bound,
                &value_spill_bound,
                inst,
            ));

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

fn absolute_base_word_for_loc(func_plan: &FuncMemPlan, loc: ObjLoc) -> Option<u32> {
    match loc {
        ObjLoc::ScratchAbs(off) => Some(off),
        ObjLoc::StableAbs(off) => func_plan
            .stable_base_word()
            .and_then(|base| base.checked_add(off)),
        ObjLoc::StableFrame(_) | ObjLoc::StackPinned(_) => None,
    }
}
