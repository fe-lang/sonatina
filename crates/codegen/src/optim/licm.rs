// TODO: Add control flow hoisting.
use rustc_hash::FxHashSet;
use sonatina_ir::{BlockId, ControlFlowGraph, Function, InstId, ValueId};

use crate::{
    cfg_edit::{CfgEditor, CleanupMode},
    domtree::DomTree,
    loop_analysis::{Loop, LoopTree},
    transform::aggregate::ObjectMemoryAnalysis,
};

#[derive(Debug)]
pub struct LicmSolver {
    invariants: Vec<InstId>,
}

#[derive(Clone, Copy)]
struct LoopInvariantCtx<'a> {
    cfg: &'a ControlFlowGraph,
    lpt: &'a LoopTree,
    lp: Loop,
    object_memory: Option<&'a ObjectMemoryAnalysis>,
}

impl LicmSolver {
    pub fn new() -> Self {
        Self {
            invariants: Vec::default(),
        }
    }

    pub fn clear(&mut self) {
        self.invariants.clear();
    }

    /// Run loop invariant code motion ont the function.
    /// This method also modifies `cfg` and `lpt` htt
    pub fn run(
        &mut self,
        func: &mut Function,
        cfg: &mut ControlFlowGraph,
        lpt: &mut LoopTree,
    ) -> bool {
        self.run_with_object_memory(func, cfg, lpt, None)
    }

    pub(crate) fn run_with_object_memory(
        &mut self,
        func: &mut Function,
        cfg: &mut ControlFlowGraph,
        lpt: &mut LoopTree,
        object_memory: Option<&ObjectMemoryAnalysis>,
    ) -> bool {
        self.clear();
        cfg.compute(func);
        let mut domtree = DomTree::new();
        domtree.compute(cfg);
        lpt.compute(cfg, &domtree);

        let mut changed = false;
        for lp in lpt.loops() {
            self.collect_invaliants(
                func,
                LoopInvariantCtx {
                    cfg,
                    lpt,
                    lp,
                    object_memory,
                },
            );

            if !self.invariants.is_empty() {
                if let Some(preheader) = self.create_preheader(func, cfg, lpt, lp) {
                    self.hoist_invariants(func, preheader);
                    changed = true;
                }
                self.invariants.clear();
            }
        }
        changed
    }

    /// Collect loop invariants int the `lp`.
    /// The found invariants are inserted to `Self::invariants`.
    fn collect_invaliants(&mut self, func: &Function, ctx: LoopInvariantCtx<'_>) {
        let mut block_in_loop_rpo: Vec<_> =
            ctx.lpt.iter_blocks_post_order(ctx.cfg, ctx.lp).collect();
        block_in_loop_rpo.reverse();

        let mut loop_var = FxHashSet::default();
        for block in block_in_loop_rpo {
            for inst in func.layout.iter_inst(block) {
                if self.is_invariant(func, ctx, &loop_var, inst) {
                    self.invariants.push(inst);
                } else {
                    loop_var.extend(func.dfg.inst_results(inst).iter().copied());
                }
            }
        }
    }

    /// Returns `true` if the inst is loop invariant.
    fn is_invariant(
        &self,
        func: &Function,
        ctx: LoopInvariantCtx<'_>,
        loop_var: &FxHashSet<ValueId>,
        inst_id: InstId,
    ) -> bool {
        if !self.is_safe_to_hoist(func, ctx, inst_id) {
            return false;
        }

        let mut invariant = true;
        let inst = func.dfg.inst(inst_id);
        inst.for_each_value(&mut |value| invariant &= !loop_var.contains(&value));
        invariant
    }

    /// Returns `true` if the `inst` is safe to hoist.
    fn is_safe_to_hoist(
        &self,
        func: &Function,
        ctx: LoopInvariantCtx<'_>,
        inst_id: InstId,
    ) -> bool {
        if ctx.object_memory.is_some_and(|object_memory| {
            object_memory.read_is_loop_invariant(func, ctx.cfg, ctx.lpt, ctx.lp, inst_id)
        }) {
            return true;
        }

        func.dfg.can_speculate(inst_id)
    }

    /// Returns preheader of the loop, if one can be used/created.
    /// 1. If there is natural preheader for the loop, then returns it without
    ///    any modification of function.
    /// 2. If no natural preheader for the loop, then create the preheader and
    ///    modify function layout, `cfg`, and `lpt`.
    fn create_preheader(
        &self,
        func: &mut Function,
        cfg: &mut ControlFlowGraph,
        lpt: &mut LoopTree,
        lp: Loop,
    ) -> Option<BlockId> {
        let lp_header = lpt.loop_header(lp);
        let original_preheaders: Vec<BlockId> = cfg
            .preds_of(lp_header)
            .copied()
            .filter(|block| !lpt.is_in_loop(*block, lp))
            .collect();
        let mut editor = CfgEditor::new(func, CleanupMode::Strict);
        let preheader = editor.create_or_reuse_loop_preheader(lp_header, &original_preheaders)?;
        *cfg = editor.cfg().clone();

        if !original_preheaders.contains(&preheader)
            && let Some(parent_lp) = lpt.parent_loop(lp)
        {
            lpt.map_block(preheader, parent_lp);
        }

        Some(preheader)
    }

    /// Hoist invariants to the preheader.
    fn hoist_invariants(&self, func: &mut Function, preheader: BlockId) {
        let last_inst = func.layout.last_inst_of(preheader).unwrap();
        for invariant in self.invariants.iter().copied() {
            func.layout.remove_inst(invariant);
            func.layout.insert_inst_before(invariant, last_inst);
        }
    }
}

impl Default for LicmSolver {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use smallvec::SmallVec;
    use sonatina_ir::{
        ControlFlowGraph, I256, Type,
        builder::test_util::*,
        inst::{
            arith::Add,
            cmp::{Lt, Slt},
            control_flow::{Br, Jump, Phi, Return},
            data::Mstore,
            evm::EvmKeccak256,
        },
        prelude::*,
    };

    use crate::{domtree::DomTree, loop_analysis::LoopTree};

    use super::LicmSolver;

    #[test]
    fn licm_skips_entry_loop_with_phi_and_no_preheader() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I32], Type::Unit);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();

        let arg0 = builder.args()[0];

        builder.switch_to_block(b0);
        let v0 = builder.insert_inst_with(|| Phi::new(is, SmallVec::new()), Type::I32);
        let c1 = builder.make_imm_value(1i32);
        let invariant = builder.insert_inst_with(|| Add::new(is, arg0, c1), Type::I32);
        builder.insert_inst_no_result_with(|| Jump::new(is, b1));

        builder.switch_to_block(b1);
        let v1 = builder.insert_inst_with(|| Add::new(is, v0, c1), Type::I32);
        let c10 = builder.make_imm_value(10i32);
        let cond = builder.insert_inst_with(|| Slt::new(is, v1, c10), Type::I1);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, b0, b2));
        builder.append_phi_arg(v0, v1, b1);

        builder.switch_to_block(b2);
        builder.insert_inst_no_result_with(|| Return::new_unit(is));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.modify(func_ref, |func| {
            let invariant_inst = func.dfg.value_inst(invariant).unwrap();
            assert_eq!(func.layout.entry_block(), Some(b0));
            assert_eq!(func.layout.inst_block(invariant_inst), b0);
            assert_eq!(func.layout.iter_block().count(), 3);

            let mut cfg = ControlFlowGraph::default();
            cfg.compute(func);
            let mut domtree = DomTree::default();
            domtree.compute(&cfg);
            let mut lpt = LoopTree::default();
            lpt.compute(&cfg, &domtree);

            let mut solver = LicmSolver::new();
            solver.run(func, &mut cfg, &mut lpt);

            assert_eq!(func.layout.entry_block(), Some(b0));
            assert_eq!(func.layout.inst_block(invariant_inst), b0);
            assert_eq!(func.layout.iter_block().count(), 3);
        });
    }

    #[test]
    fn licm_does_not_hoist_keccak256_across_memory_writes() {
        // Regression: `evm_keccak256` reads linear memory and must not be treated as a pure op.
        //
        // If `evm_keccak256` is considered pure, LICM may hoist it out of loops where the
        // pointer/length are loop-invariant, even though the hashed bytes are written inside
        // the loop (e.g. `mstore` + `keccak256(ptr, 64)` in Merkle hashing code).
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let preheader = builder.append_block();
        let header = builder.append_block();
        let body = builder.append_block();
        let exit = builder.append_block();

        builder.switch_to_block(preheader);
        let ptr = builder.make_imm_value(I256::from(0x2000u64));
        let len = builder.make_imm_value(I256::from(64u64));
        builder.insert_inst_no_result_with(|| Jump::new(is, header));

        builder.switch_to_block(header);
        let idx = builder.insert_inst_with(|| Phi::new(is, SmallVec::new()), Type::I256);
        let limit = builder.make_imm_value(I256::from(2u64));
        let cond = builder.insert_inst_with(|| Lt::new(is, idx, limit), Type::I1);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, body, exit));

        builder.switch_to_block(body);
        // A trivially loop-invariant pure op: should hoist.
        let pure_invariant = builder.insert_inst_with(|| Add::new(is, ptr, len), Type::I256);
        // A loop write to memory that `keccak256(ptr, len)` depends on.
        builder.insert_inst_no_result_with(|| Mstore::new(is, ptr, idx, Type::I256));
        // Must remain in the loop body (not safe to hoist).
        let keccak = builder.insert_inst_with(|| EvmKeccak256::new(is, ptr, len), Type::I256);

        let one = builder.make_imm_value(I256::from(1u64));
        let idx_next = builder.insert_inst_with(|| Add::new(is, idx, one), Type::I256);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));
        builder.append_phi_arg(idx, idx_next, body);

        builder.switch_to_block(exit);
        builder.insert_inst_no_result_with(|| Return::new_unit(is));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.modify(func_ref, |func| {
            let pure_invariant_inst = func.dfg.value_inst(pure_invariant).unwrap();
            let keccak_inst = func.dfg.value_inst(keccak).unwrap();
            assert_eq!(func.layout.inst_block(pure_invariant_inst), body);
            assert_eq!(func.layout.inst_block(keccak_inst), body);

            let mut cfg = ControlFlowGraph::default();
            cfg.compute(func);
            let mut domtree = DomTree::default();
            domtree.compute(&cfg);
            let mut lpt = LoopTree::default();
            lpt.compute(&cfg, &domtree);

            LicmSolver::new().run(func, &mut cfg, &mut lpt);

            // Sanity: LICM runs and hoists pure invariants.
            assert_eq!(func.layout.inst_block(pure_invariant_inst), preheader);
            // Regression: keccak must not be hoisted out of the loop.
            assert_eq!(func.layout.inst_block(keccak_inst), body);
        });
    }
}
