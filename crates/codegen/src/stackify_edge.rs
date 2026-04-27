use std::collections::BTreeSet;

use sonatina_ir::{BlockId, ControlFlowGraph, Function};

use crate::{
    cfg_edit::{CfgEditor, CleanupMode},
    cfg_scc::CfgSccAnalysis,
    critical_edge::CriticalEdgeSplitter,
};

pub struct StackifyEdgeSplitter;

impl StackifyEdgeSplitter {
    pub fn run(func: &mut Function, cfg: &mut ControlFlowGraph) {
        CriticalEdgeSplitter::new().run(func, cfg);

        let mut scc = CfgSccAnalysis::new();
        scc.compute(cfg);

        let mut edges = BTreeSet::<(BlockId, BlockId)>::new();
        for from in func.layout.iter_block() {
            if cfg.succ_num_of(from) < 2 {
                continue;
            }

            let Some(from_scc) = scc.scc_of(from) else {
                continue;
            };
            if !scc.scc_data(from_scc).is_cycle {
                continue;
            }

            for &to in cfg.succs_of(from) {
                if scc.scc_of(to) == Some(from_scc) {
                    edges.insert((from, to));
                }
            }
        }

        if edges.is_empty() {
            return;
        }

        let mut editor = CfgEditor::new(func, CleanupMode::Strict);
        for (from, to) in edges {
            editor.split_edge(from, to);
        }
        cfg.compute(editor.func());
    }
}

#[cfg(test)]
mod tests {
    use sonatina_ir::cfg::ControlFlowGraph;
    use sonatina_parser::parse_module;

    use super::StackifyEdgeSplitter;

    #[test]
    fn splits_multiway_self_loop_edge() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f(v0.i1) {
block0:
    br v0 block0 block1;

block1:
    return;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func = parsed.module.funcs()[0];

        parsed.module.func_store.modify(func, |function| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);
            let entry = cfg.entry().expect("missing entry");
            assert!(cfg.succs_of(entry).any(|&succ| succ == entry));

            StackifyEdgeSplitter::run(function, &mut cfg);

            assert!(!cfg.succs_of(entry).any(|&succ| succ == entry));
            assert!(cfg.preds_of(entry).any(|&pred| cfg.succ_num_of(pred) == 1));
        });
    }
}
