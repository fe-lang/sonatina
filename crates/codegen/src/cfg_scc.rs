use std::collections::BTreeSet;

use cranelift_entity::{
    EntityRef, PrimaryMap, SecondaryMap, entity_impl, packed_option::PackedOption,
};
use sonatina_ir::{BlockId, ControlFlowGraph};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct SccId(u32);
entity_impl!(SccId);

#[derive(Debug, Default)]
pub struct CfgSccAnalysis {
    block_to_scc: SecondaryMap<BlockId, PackedOption<SccId>>,
    sccs: PrimaryMap<SccId, SccData>,

    topo_order: Vec<SccId>,
    topo_index: SecondaryMap<SccId, u32>,

    cfg_rpo: Vec<BlockId>,
}

#[derive(Debug, Clone)]
pub struct SccData {
    pub blocks_rpo: Vec<BlockId>,
    pub entry_blocks: Vec<BlockId>,
    pub exit_blocks: Vec<BlockId>,
    pub succ_sccs: Vec<SccId>,
    pub pred_sccs: Vec<SccId>,
    pub is_cycle: bool,
}

impl Default for SccData {
    fn default() -> Self {
        Self::new()
    }
}

impl SccData {
    fn new() -> Self {
        Self {
            blocks_rpo: Vec::new(),
            entry_blocks: Vec::new(),
            exit_blocks: Vec::new(),
            succ_sccs: Vec::new(),
            pred_sccs: Vec::new(),
            is_cycle: false,
        }
    }

    pub fn is_multi_entry(&self) -> bool {
        self.entry_blocks.len() > 1
    }

    pub fn header(&self) -> Option<BlockId> {
        (self.entry_blocks.len() == 1).then(|| self.entry_blocks[0])
    }

    fn topo_tiebreak_key(&self) -> BlockId {
        debug_assert!(!self.blocks_rpo.is_empty());
        self.blocks_rpo[0]
    }
}

impl CfgSccAnalysis {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn clear(&mut self) {
        self.block_to_scc.clear();
        self.sccs.clear();
        self.topo_order.clear();
        self.topo_index.clear();
        self.cfg_rpo.clear();
    }

    /// Compute SCCs for the subgraph reachable from `cfg.entry()`.
    pub fn compute(&mut self, cfg: &ControlFlowGraph) {
        self.clear();

        let Some(entry) = cfg.entry() else {
            return;
        };

        self.cfg_rpo.extend(cfg.post_order());
        self.cfg_rpo.reverse();

        let mut reachable = SecondaryMap::<BlockId, bool>::default();
        for &block in &self.cfg_rpo {
            reachable[block] = true;
        }

        let mut visited = SecondaryMap::<BlockId, bool>::default();

        for &root in &self.cfg_rpo {
            if visited[root] {
                continue;
            }

            let scc = self.sccs.push(SccData::new());
            let mut stack = vec![root];
            visited[root] = true;

            while let Some(node) = stack.pop() {
                self.block_to_scc[node] = scc.into();

                for &pred in cfg.preds_of(node) {
                    if !reachable[pred] {
                        continue;
                    }

                    if !visited[pred] {
                        visited[pred] = true;
                        stack.push(pred);
                    }
                }
            }
        }

        for &block in &self.cfg_rpo {
            let scc = self.scc_of(block).unwrap();
            self.sccs[scc].blocks_rpo.push(block);
        }

        let scc_count = self.sccs.len();
        let mut succ_sets = vec![BTreeSet::<SccId>::new(); scc_count];
        let mut pred_sets = vec![BTreeSet::<SccId>::new(); scc_count];
        let mut entry_sets = vec![BTreeSet::<BlockId>::new(); scc_count];
        let mut exit_sets = vec![BTreeSet::<BlockId>::new(); scc_count];
        let mut has_self_loop = vec![false; scc_count];

        for &block in self.cfg_rpo.iter().rev() {
            let from_scc = self.scc_of(block).unwrap();
            let from_idx = from_scc.index();

            if block == entry
                || cfg
                    .preds_of(block)
                    .filter(|&&pred| reachable[pred])
                    .any(|&pred| self.scc_of(pred).unwrap() != from_scc)
            {
                entry_sets[from_idx].insert(block);
            }

            let mut is_exit = false;
            for &succ in cfg.succs_of(block) {
                if !reachable[succ] {
                    continue;
                }

                let to_scc = self.scc_of(succ).unwrap();
                if to_scc != from_scc {
                    is_exit = true;
                    succ_sets[from_idx].insert(to_scc);
                    pred_sets[to_scc.index()].insert(from_scc);
                } else if succ == block {
                    has_self_loop[from_idx] = true;
                }
            }

            if is_exit {
                exit_sets[from_idx].insert(block);
            }
        }

        for scc in self.sccs.keys() {
            let idx = scc.index();
            let data = &mut self.sccs[scc];

            data.entry_blocks = entry_sets[idx].iter().copied().collect();
            data.exit_blocks = exit_sets[idx].iter().copied().collect();
            data.succ_sccs = succ_sets[idx].iter().copied().collect();
            data.pred_sccs = pred_sets[idx].iter().copied().collect();

            data.is_cycle = data.blocks_rpo.len() > 1 || has_self_loop[idx];
        }

        self.compute_topo_order();
    }

    pub fn scc_of(&self, block: BlockId) -> Option<SccId> {
        self.block_to_scc[block].expand()
    }

    pub fn scc_data(&self, scc: SccId) -> &SccData {
        &self.sccs[scc]
    }

    pub fn scc_count(&self) -> usize {
        self.sccs.len()
    }

    pub fn topo_order(&self) -> &[SccId] {
        &self.topo_order
    }

    pub fn topo_index(&self, scc: SccId) -> u32 {
        self.topo_index[scc]
    }

    pub fn topo_before(&self, a: SccId, b: SccId) -> bool {
        self.topo_index(a) < self.topo_index(b)
    }

    pub fn entry_scc(&self, cfg: &ControlFlowGraph) -> Option<SccId> {
        cfg.entry().and_then(|entry| self.scc_of(entry))
    }

    pub fn is_reachable(&self, block: BlockId) -> bool {
        self.scc_of(block).is_some()
    }

    fn compute_topo_order(&mut self) {
        self.topo_order.clear();
        self.topo_index.clear();

        let scc_count = self.sccs.len();
        if scc_count == 0 {
            return;
        }

        let mut indegree = vec![0u32; scc_count];
        let mut ready = BTreeSet::<(BlockId, SccId)>::new();

        for scc in self.sccs.keys() {
            let idx = scc.index();
            indegree[idx] = self.sccs[scc].pred_sccs.len() as u32;
            if indegree[idx] == 0 {
                ready.insert((self.sccs[scc].topo_tiebreak_key(), scc));
            }
        }

        while let Some((_rep, scc)) = ready.pop_first() {
            self.topo_order.push(scc);

            for &succ in &self.sccs[scc].succ_sccs {
                let succ_idx = succ.index();
                indegree[succ_idx] -= 1;
                if indegree[succ_idx] == 0 {
                    ready.insert((self.sccs[succ].topo_tiebreak_key(), succ));
                }
            }
        }

        debug_assert_eq!(self.topo_order.len(), scc_count);

        for (index, &scc) in self.topo_order.iter().enumerate() {
            self.topo_index[scc] = index as u32;
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use sonatina_ir::{
        Function, Type,
        builder::test_util::*,
        inst::control_flow::{Br, Jump, Return},
        prelude::*,
    };

    use super::*;

    fn analyze_cfg(func: &Function) -> (ControlFlowGraph, CfgSccAnalysis) {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(func);
        let mut analysis = CfgSccAnalysis::new();
        analysis.compute(&cfg);
        (cfg, analysis)
    }

    fn assert_invariants(cfg: &ControlFlowGraph, analysis: &CfgSccAnalysis) {
        for from in cfg.post_order() {
            let from_scc = analysis.scc_of(from).unwrap();
            for succ in cfg.succs_of(from) {
                let Some(to_scc) = analysis.scc_of(*succ) else {
                    continue;
                };
                if from_scc != to_scc {
                    assert!(analysis.topo_before(from_scc, to_scc));
                }
            }
        }

        assert_eq!(analysis.topo_order().len(), analysis.scc_count());

        for &scc in analysis.topo_order() {
            let data = analysis.scc_data(scc);
            assert!(!data.blocks_rpo.is_empty());

            let block_set: BTreeSet<BlockId> = data.blocks_rpo.iter().copied().collect();
            assert_eq!(block_set.len(), data.blocks_rpo.len());

            assert!(data.blocks_rpo.iter().all(|b| block_set.contains(b)));

            assert!(data.entry_blocks.iter().all(|b| block_set.contains(b)));
            assert!(data.exit_blocks.iter().all(|b| block_set.contains(b)));

            assert!(data.succ_sccs.windows(2).all(|w| w[0] < w[1]));
            assert!(data.pred_sccs.windows(2).all(|w| w[0] < w[1]));
            assert!(!data.succ_sccs.contains(&scc));
            assert!(!data.pred_sccs.contains(&scc));

            assert_eq!(data.is_multi_entry(), data.entry_blocks.len() > 1);
            assert_eq!(
                data.header(),
                (data.entry_blocks.len() == 1).then(|| data.entry_blocks[0])
            );
        }
    }

    #[test]
    fn empty_cfg() {
        let cfg = ControlFlowGraph::new();
        let mut analysis = CfgSccAnalysis::new();
        analysis.compute(&cfg);
        assert_eq!(analysis.scc_count(), 0);
        assert!(analysis.topo_order().is_empty());
    }

    #[test]
    fn linear_chain() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();

        builder.switch_to_block(b0);
        builder.insert_inst_no_result_with(|| Jump::new(is, b1));

        builder.switch_to_block(b1);
        builder.insert_inst_no_result_with(|| Jump::new(is, b2));

        builder.switch_to_block(b2);
        builder.insert_inst_no_result_with(|| Return::new(is, None));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        let (cfg, analysis) = module.func_store.view(func_ref, analyze_cfg);

        assert_eq!(analysis.scc_count(), 3);
        assert_eq!(
            analysis
                .topo_order()
                .iter()
                .map(|&scc| analysis.scc_data(scc).topo_tiebreak_key())
                .collect::<Vec<_>>(),
            vec![b0, b1, b2]
        );

        assert_invariants(&cfg, &analysis);
    }

    #[test]
    fn diamond() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let entry = builder.append_block();
        let then_block = builder.append_block();
        let else_block = builder.append_block();
        let merge = builder.append_block();

        builder.switch_to_block(entry);
        let cond = builder.make_imm_value(true);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, else_block, then_block));

        builder.switch_to_block(then_block);
        builder.insert_inst_no_result_with(|| Jump::new(is, merge));

        builder.switch_to_block(else_block);
        builder.insert_inst_no_result_with(|| Jump::new(is, merge));

        builder.switch_to_block(merge);
        builder.insert_inst_no_result_with(|| Return::new(is, None));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        let (cfg, analysis) = module.func_store.view(func_ref, analyze_cfg);

        assert_eq!(analysis.scc_count(), 4);
        assert_eq!(
            analysis
                .topo_order()
                .iter()
                .map(|&scc| analysis.scc_data(scc).topo_tiebreak_key())
                .collect::<Vec<_>>(),
            vec![entry, then_block, else_block, merge]
        );

        assert_invariants(&cfg, &analysis);
    }

    #[test]
    fn simple_loop() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let entry = builder.append_block();
        let header = builder.append_block();
        let body = builder.append_block();
        let exit = builder.append_block();

        builder.switch_to_block(entry);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));

        builder.switch_to_block(header);
        let cond = builder.make_imm_value(true);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, exit, body));

        builder.switch_to_block(body);
        builder.insert_inst_no_result_with(|| Jump::new(is, header));

        builder.switch_to_block(exit);
        builder.insert_inst_no_result_with(|| Return::new(is, None));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        let (cfg, analysis) = module.func_store.view(func_ref, analyze_cfg);

        assert_eq!(analysis.scc_count(), 3);

        let loop_scc = analysis.scc_of(header).unwrap();
        assert_eq!(analysis.scc_of(body), Some(loop_scc));

        let loop_data = analysis.scc_data(loop_scc);
        assert!(loop_data.is_cycle);
        assert_eq!(loop_data.blocks_rpo, vec![header, body]);
        assert_eq!(loop_data.entry_blocks, vec![header]);
        assert_eq!(loop_data.header(), Some(header));
        assert_eq!(loop_data.exit_blocks, vec![header]);

        assert_invariants(&cfg, &analysis);
    }

    #[test]
    fn self_loop() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I1], Type::Unit);
        let is = evm.inst_set();

        let entry = builder.append_block();
        let loop_block = builder.append_block();
        let exit = builder.append_block();

        let arg = builder.args()[0];

        builder.switch_to_block(entry);
        builder.insert_inst_no_result_with(|| Jump::new(is, loop_block));

        builder.switch_to_block(loop_block);
        builder.insert_inst_no_result_with(|| Br::new(is, arg, loop_block, exit));

        builder.switch_to_block(exit);
        builder.insert_inst_no_result_with(|| Return::new(is, None));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        let (cfg, analysis) = module.func_store.view(func_ref, analyze_cfg);

        let scc = analysis.scc_of(loop_block).unwrap();
        let data = analysis.scc_data(scc);
        assert_eq!(data.blocks_rpo, vec![loop_block]);
        assert!(data.is_cycle);
        assert_eq!(data.entry_blocks, vec![loop_block]);
        assert_eq!(data.exit_blocks, vec![loop_block]);

        assert_invariants(&cfg, &analysis);
    }

    #[test]
    fn irreducible_multi_entry_scc() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let entry = builder.append_block();
        let a = builder.append_block();
        let b = builder.append_block();
        let c = builder.append_block();
        let d = builder.append_block();
        let exit = builder.append_block();

        builder.switch_to_block(entry);
        let cond = builder.make_imm_value(true);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, a, b));

        builder.switch_to_block(a);
        builder.insert_inst_no_result_with(|| Jump::new(is, c));

        builder.switch_to_block(b);
        builder.insert_inst_no_result_with(|| Jump::new(is, d));

        builder.switch_to_block(c);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, exit, d));

        builder.switch_to_block(d);
        builder.insert_inst_no_result_with(|| Jump::new(is, c));

        builder.switch_to_block(exit);
        builder.insert_inst_no_result_with(|| Return::new(is, None));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        let (cfg, analysis) = module.func_store.view(func_ref, analyze_cfg);

        let cycle_scc = analysis.scc_of(c).unwrap();
        assert_eq!(analysis.scc_of(d), Some(cycle_scc));

        let data = analysis.scc_data(cycle_scc);
        assert!(data.is_cycle);
        assert!(data.is_multi_entry());
        assert_eq!(data.header(), None);
        assert_eq!(data.entry_blocks, vec![c, d]);

        assert_invariants(&cfg, &analysis);
    }

    #[test]
    fn unreachable_subgraph_is_ignored() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let entry = builder.append_block();
        let exit = builder.append_block();

        let u0 = builder.append_block();
        let u1 = builder.append_block();

        builder.switch_to_block(entry);
        builder.insert_inst_no_result_with(|| Jump::new(is, exit));

        builder.switch_to_block(exit);
        builder.insert_inst_no_result_with(|| Return::new(is, None));

        builder.switch_to_block(u0);
        builder.insert_inst_no_result_with(|| Jump::new(is, u1));

        builder.switch_to_block(u1);
        builder.insert_inst_no_result_with(|| Jump::new(is, u0));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        let (cfg, analysis) = module.func_store.view(func_ref, analyze_cfg);

        assert_eq!(analysis.scc_count(), 2);
        assert_eq!(analysis.scc_of(u0), None);
        assert_eq!(analysis.scc_of(u1), None);

        assert_invariants(&cfg, &analysis);
    }
}
