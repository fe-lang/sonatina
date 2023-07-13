//! Compute the "liveness" of values in a control flow graph.
//!
//! This is an implementation of "Liveness Sets using Path Exploration",
//! as described in https://hal.inria.fr/hal-00761555/file/habilitation.pdf
//! Section 2.5.1:
//!
//! > a variable is live at a program point p, if p belongs to a path of the CFG
//! > leading from a definition of that variable to one of its uses without
//! > passing through the definition. Therefore, the live-range of a variable can
//! > be computed using a backward traversal starting at its uses and stopping
//! > when reaching its (unique) definition. This idea was first proposed by
//! > Appel in his “Tiger” book...
//! >
//! > Starting from a use of a variable, all paths where that variable is live
//! > are followed by traversing the CFG backwards until the variable’s
//! > definition is reached. Along the encountered paths, the variable is added
//! > to the live-in and live-out sets of the respective basic blocks.
//!
//!
//! Note that the arguments to a phi instruction are considered to be used by
//! their associated predecessor blocks, *not* by the block containing the phi.
//! The result of a phi instruction is live-in for the block containing the phi,
//! but *not* live-out for the predecessor blocks (so no block defines the result).
//!
//! This might change; it might make more sense to consider the result of a phi
//! to be defined by each of the predecessor blocks, or by the block containing the phi.

use std::collections::{btree_map::Entry, BTreeMap};

use crate::{bitset::BitSet, cfg::ControlFlowGraph};
use cranelift_entity::SecondaryMap;
use sonatina_ir::{Block, Function, InsnData, Value};

#[derive(Default)]
pub struct Liveness {
    /// block => (live_ins, live_outs)
    live_ins: SecondaryMap<Block, BitSet<Value>>,
    live_outs: SecondaryMap<Block, BitSet<Value>>,

    /// value => (defining block, is_defined_by_phi)
    defs: SecondaryMap<Value, Option<ValDef>>,
    pub val_live_blocks: SecondaryMap<Value, BitSet<Block>>,
    pub val_use_blocks: SecondaryMap<Value, BitSet<Block>>,
    pub val_use_count: SecondaryMap<Value, u32>,
}

impl Liveness {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn compute(&mut self, func: &Function, cfg: &ControlFlowGraph) {
        self.clear();

        for arg in &func.arg_values {
            self.defs[*arg] = Some(ValDef::FnArg);
        }
        for block in cfg.post_order() {
            for_each_def(func, block, |val, is_phi_def| {
                self.defs[val] = if is_phi_def {
                    Some(ValDef::Phi(block))
                } else {
                    Some(ValDef::Normal(block))
                }
            });
        }

        for block in cfg.post_order() {
            for_each_use(func, block, |val, phi_source_block| {
                if func.dfg.is_imm(val) {
                    self.mark_use(val, block);
                } else if let Some(pred_block) = phi_source_block {
                    // A phi input is considered to be a use by the associated
                    // predecessor block
                    self.mark_use(val, pred_block);
                    self.up_and_mark(cfg, pred_block, val);
                } else {
                    self.mark_use(val, block);
                    self.up_and_mark(cfg, block, val);
                }
            });
        }
    }

    // XXX better api
    pub fn block_live_ins(&self, block: Block) -> &BitSet<Value> {
        &self.live_ins[block]
    }
    pub fn block_live_outs(&self, block: Block) -> &BitSet<Value> {
        &self.live_outs[block]
    }

    /// Propagate liveness of `val` "upward" from its use in `block`
    fn up_and_mark(&mut self, cfg: &ControlFlowGraph, block: Block, val: Value) {
        let def = self.defs[val].unwrap();

        self.val_live_blocks[val].insert(block);

        // If `val` is defined in this block, there's nothing to do.
        if def == ValDef::Normal(block) {
            return;
        }

        if self.live_ins[block].contains(val) {
            // Already marked, so propagation to preds already done
            return;
        }
        self.live_ins[block].insert(val);

        // If `val` is the result of a phi, then it's live-in for the block
        // containing the phi, but not live-out for any predecessor block.
        if def == ValDef::Phi(block) {
            return;
        }

        for pred in cfg.preds_of(block) {
            self.live_outs[*pred].insert(val);
            self.up_and_mark(cfg, *pred, val);
        }
    }

    fn mark_use(&mut self, val: Value, block: Block) {
        self.val_use_blocks[val].insert(block);
        self.val_use_count[val] += 1;
    }

    /// Reset the `Liveness` struct so that it can be reused.
    pub fn clear(&mut self) {
        self.live_ins.clear();
        self.live_outs.clear();
        self.defs.clear();
        self.val_live_blocks.clear();
    }
}

// xxx remove?
#[derive(Default)]
pub struct EdgeLiveness {
    edges: BTreeMap<(Block, Block), BitSet<Value>>,
    // xxx store block var uses?
    /// value => (defining block, is_defined_by_phi)
    defs: SecondaryMap<Value, Option<ValDef>>,
}

impl EdgeLiveness {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn compute(&mut self, func: &Function, cfg: &ControlFlowGraph) {
        // Precompute `defs`
        for arg in &func.arg_values {
            self.defs[*arg] = Some(ValDef::FnArg);
        }
        for block in cfg.post_order() {
            for_each_def(func, block, |val, is_phi_def| {
                self.defs[val] = if is_phi_def {
                    Some(ValDef::Phi(block))
                } else {
                    Some(ValDef::Normal(block))
                }
            });
        }

        for block in cfg.post_order() {
            for_each_use(func, block, |val, phi_source_block| {
                if func.dfg.is_imm(val) {
                    // ignore
                } else if let Some(pred_block) = phi_source_block {
                    // A phi arg is considered to be a use by the associated
                    // predecessor block
                    self.up_and_mark(cfg, pred_block, val);
                } else {
                    self.up_and_mark(cfg, block, val);
                }
            });
        }
    }

    pub fn live_on_edge(&self, edge: (Block, Block)) -> &BitSet<Value> {
        &self.edges[&edge]
    }

    // xxx rename; only for testing?
    pub fn into_edges(self) -> BTreeMap<(Block, Block), BitSet<Value>> {
        self.edges
    }

    /// Propagate liveness of `val` "upward" from its use in `block`
    fn up_and_mark(&mut self, cfg: &ControlFlowGraph, block: Block, val: Value) {
        let def = self.defs[val].unwrap();

        // If `val` is defined in this block, there's nothing to do.
        if def == ValDef::Normal(block) {
            return;
        }

        for pred in cfg.preds_of(block) {
            let edge = (*pred, block);
            let liveset = match self.edges.entry(edge) {
                Entry::Occupied(entry) => entry.into_mut(),
                Entry::Vacant(entry) => entry.insert(BitSet::new()),
            };

            if liveset.contains(val) {
                // Already marked, so propagation to preds already done
                return;
            }
            liveset.insert(val);

            // If `val` is defined here by a phi, then it's considered to be
            // live on the incoming edges (ie defined by all pred blocks).
            if def == ValDef::Phi(block) {
                continue;
            }
            self.up_and_mark(cfg, *pred, val);
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum ValDef {
    FnArg,
    Normal(Block),
    Phi(Block),
}

fn for_each_use(func: &Function, block: Block, mut f: impl FnMut(Value, Option<Block>)) {
    for insn in func.layout.iter_insn(block) {
        match func.dfg.insn_data(insn) {
            InsnData::Phi { values, blocks, .. } => values
                .iter()
                .zip(blocks.iter())
                .for_each(|(v, b)| f(*v, Some(*b))),
            data => data.args().iter().for_each(|v| f(*v, None)),
        }
    }
}

fn for_each_def(func: &Function, block: Block, mut f: impl FnMut(Value, bool)) {
    for insn in func.layout.iter_insn(block) {
        if let Some(val) = func.dfg.insn_result(insn) {
            f(val, func.dfg.is_phi(insn))
        }
    }
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{Block, Module};
    use sonatina_parser::parser::Parser;

    use crate::cfg::ControlFlowGraph;

    use super::{EdgeLiveness, Liveness};

    fn parse_sona(content: &str) -> Module {
        let parser = Parser::default();
        parser.parse(content).unwrap().module
    }

    const SRC: &str = r#"
target = "evm-ethereum-london"
func public %complex_loop(v0.i8, v20.i8) -> i8:
    block1:
        v1.i8 = sub v0 1.i8;
        fallthrough block2;

    block2:
        v2.i8 = phi (v8 block7) (v0 block1);
        v3.i8 = phi (v9 block7) (v1 block1);
        v4.i1 = lt v3 100.i8;
        br v4 block3 block4;

    block3:
        v5.i1 = lt v2 20.i8;
        br v5 block5 block6;

    block4:
        return v2;

    block5:
        v6.i8 = add 1.i8 v3;
        jump block7;

    block6:
        v7.i8 = add v3 2.i8;
        fallthrough block7;

    block7:
        v8.i8 = phi (v0 block5) (v3 block6);
        v9.i8 = phi (v6 block5) (v7 block6);
        jump block2;
"#;

    #[test]
    fn test() {
        let module = parse_sona(SRC);
        let function = module.funcs.values().next().unwrap();
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(function);

        let mut live = Liveness::default();
        live.compute(function, &cfg);

        assert_eq!(live.block_live_ins(Block(1)), &[0].as_slice().into());
        assert_eq!(live.block_live_outs(Block(1)), &[0].as_slice().into());

        assert_eq!(live.block_live_ins(Block(2)), &[0, 2, 3].as_slice().into());
        assert_eq!(live.block_live_outs(Block(2)), &[0, 2, 3].as_slice().into());

        assert_eq!(live.block_live_ins(Block(3)), &[0, 2, 3].as_slice().into());
        assert_eq!(live.block_live_outs(Block(3)), &[0, 3].as_slice().into());

        assert_eq!(live.block_live_ins(Block(4)), &[2].as_slice().into());
        assert_eq!(live.block_live_outs(Block(4)), &[].as_slice().into());

        assert_eq!(live.block_live_ins(Block(5)), &[0, 3].as_slice().into());
        assert_eq!(live.block_live_outs(Block(5)), &[0].as_slice().into());

        assert_eq!(live.block_live_ins(Block(6)), &[0, 3].as_slice().into());
        assert_eq!(live.block_live_outs(Block(6)), &[0].as_slice().into());
    }

    #[test]
    fn test_edges() {
        let module = parse_sona(SRC);
        let function = module.funcs.values().next().unwrap();
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(function);

        let mut live = EdgeLiveness::default();
        live.compute(function, &cfg);

        let mut edges = live.into_edges();

        assert_eq!(
            edges.remove(&(Block(1), Block(2))).unwrap(),
            [0, 2, 3].as_slice().into(),
        );
        assert_eq!(
            edges.remove(&(Block(2), Block(3))).unwrap(),
            [0, 2, 3].as_slice().into()
        );
        assert_eq!(
            edges.remove(&(Block(2), Block(4))).unwrap(),
            [2].as_slice().into()
        );
        assert_eq!(
            edges.remove(&(Block(3), Block(5))).unwrap(),
            [0, 3].as_slice().into()
        );
        assert_eq!(
            edges.remove(&(Block(3), Block(6))).unwrap(),
            [0, 3].as_slice().into()
        );
        assert_eq!(
            edges.remove(&(Block(5), Block(7))).unwrap(),
            [0, 8, 9].as_slice().into()
        );
        assert_eq!(
            edges.remove(&(Block(6), Block(7))).unwrap(),
            [0, 8, 9].as_slice().into()
        );
        assert_eq!(
            edges.remove(&(Block(7), Block(2))).unwrap(),
            [0, 2, 3].as_slice().into()
        );
        assert!(edges.is_empty());
    }
}
