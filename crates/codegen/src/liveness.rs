//! Compute the "liveness" of values in a control flow graph.
//!
//! This is an implementation of "Liveness Sets using Path Exploration",
//! as described in <https://hal.inria.fr/hal-00761555/file/habilitation.pdf>
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

use std::collections::BTreeMap;

use crate::bitset::BitSet;
use cranelift_entity::SecondaryMap;
use sonatina_ir::{BlockId, Function, ValueId, cfg::ControlFlowGraph};

#[derive(Default)]
pub struct Liveness {
    /// block => (live_ins, live_outs)
    live_ins: SecondaryMap<BlockId, BitSet<ValueId>>,
    live_outs: SecondaryMap<BlockId, BitSet<ValueId>>,

    /// value => (defining block, is_defined_by_phi)
    defs: SecondaryMap<ValueId, Option<ValDef>>,
    pub val_live_blocks: SecondaryMap<ValueId, BitSet<BlockId>>,
    pub val_use_blocks: SecondaryMap<ValueId, BitSet<BlockId>>,
    pub val_use_count: SecondaryMap<ValueId, u32>,
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
                if func.dfg.value_is_imm(val) {
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
    pub fn block_live_ins(&self, block: BlockId) -> &BitSet<ValueId> {
        &self.live_ins[block]
    }
    pub fn block_live_outs(&self, block: BlockId) -> &BitSet<ValueId> {
        &self.live_outs[block]
    }

    /// Propagate liveness of `val` "upward" from its use in `block`
    fn up_and_mark(&mut self, cfg: &ControlFlowGraph, block: BlockId, val: ValueId) {
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

    fn mark_use(&mut self, val: ValueId, block: BlockId) {
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

#[derive(Copy, Clone, PartialEq, Eq)]
enum ValDef {
    FnArg,
    Normal(BlockId),
    Phi(BlockId),
}

pub fn value_uses_in_block_matching_predicate(
    func: &Function,
    block: BlockId,
    pred: impl Fn(ValueId) -> bool,
) -> BTreeMap<ValueId, u32> {
    let mut counts = BTreeMap::new();
    for_each_use(func, block, |val, _| {
        if pred(val) {
            counts.entry(val).and_modify(|n| *n += 1).or_insert(1);
        }
    });
    counts
}

fn for_each_use(func: &Function, block: BlockId, mut f: impl FnMut(ValueId, Option<BlockId>)) {
    for inst in func.layout.iter_inst(block) {
        if let Some(phi) = func.dfg.cast_phi(inst) {
            for (val, block) in phi.args().iter() {
                f(*val, Some(*block))
            }
        } else {
            func.dfg.inst(inst).for_each_value(&mut |v| f(v, None));
        }
    }
}

fn for_each_def(func: &Function, block: BlockId, mut f: impl FnMut(ValueId, bool)) {
    for inst in func.layout.iter_inst(block) {
        if let Some(val) = func.dfg.inst_result(inst) {
            f(val, func.dfg.is_phi(inst))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Liveness;
    use sonatina_ir::{BlockId, cfg::ControlFlowGraph};
    use sonatina_parser::parse_module;

    const SRC: &str = r#"
target = "evm-ethereum-london"
func public %complex_loop(v0.i8, v20.i8) -> i8 {
    block1:
        v1.i8 = sub v0 1.i8;
        jump block2;

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
        jump block7;

    block7:
        v8.i8 = phi (v0 block5) (v3 block6);
        v9.i8 = phi (v6 block5) (v7 block6);
        jump block2;
}
"#;

    #[test]
    fn test() {
        let parsed = parse_module(SRC).unwrap();
        let funcref = *parsed.module.funcs().first().unwrap();

        let live = parsed.module.func_store.view(funcref, |function| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);
            let mut live = Liveness::default();
            live.compute(function, &cfg);
            live
        });

        let v = |n: usize| parsed.debug.value(funcref, &format!("v{n}")).unwrap();

        assert_eq!(live.block_live_ins(BlockId(1)), &[v(0)].as_slice().into());
        assert_eq!(live.block_live_outs(BlockId(1)), &[v(0)].as_slice().into());

        assert_eq!(
            live.block_live_ins(BlockId(2)),
            &[v(0), v(2), v(3)].as_slice().into()
        );
        assert_eq!(
            live.block_live_outs(BlockId(2)),
            &[v(0), v(2), v(3)].as_slice().into()
        );

        assert_eq!(
            live.block_live_ins(BlockId(3)),
            &[v(0), v(2), v(3)].as_slice().into()
        );
        assert_eq!(
            live.block_live_outs(BlockId(3)),
            &[v(0), v(3)].as_slice().into()
        );

        assert_eq!(live.block_live_ins(BlockId(4)), &[v(2)].as_slice().into());
        assert_eq!(live.block_live_outs(BlockId(4)), &[].as_slice().into());

        assert_eq!(
            live.block_live_ins(BlockId(5)),
            &[v(0), v(3)].as_slice().into()
        );
        assert_eq!(live.block_live_outs(BlockId(5)), &[v(0)].as_slice().into());

        assert_eq!(
            live.block_live_ins(BlockId(6)),
            &[v(0), v(3)].as_slice().into()
        );
        assert_eq!(live.block_live_outs(BlockId(6)), &[v(0)].as_slice().into());
    }
}
