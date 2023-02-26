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

use crate::{cfg::ControlFlowGraph, stackalloc::Function};
use bit_set::BitSet;
use cranelift_entity::{EntityRef, SecondaryMap};
use sonatina_ir as ir;

pub struct Liveness<V: EntityRef> {
    /// block => (live_ins, live_outs)
    live_ins: SecondaryMap<ir::Block, BitSet>,
    live_outs: SecondaryMap<ir::Block, BitSet>,

    /// value => (defining block, is_defined_by_phi)
    defs: SecondaryMap<V, Option<(ir::Block, bool)>>,
}

impl<V: EntityRef> Liveness<V> {
    pub fn new() -> Self {
        Self {
            live_ins: SecondaryMap::default(),
            live_outs: SecondaryMap::default(),
            defs: SecondaryMap::default(),
        }
    }

    pub fn compute(&mut self, func: &impl Function<ValueType = V>, cfg: &ControlFlowGraph) {
        self.clear();

        // Precompute `defs`:
        // find defining block and is_phi_def for each value
        for block in cfg.post_order() {
            self.live_ins[block] = BitSet::new();
            self.live_ins[block] = BitSet::new();

            func.for_each_def(block, |val, is_phi_def| {
                self.defs[val] = Some((block, is_phi_def));
            });
        }

        for block in cfg.post_order() {
            func.for_each_use(block, |val, phi_source_block| {
                if let Some(pred_block) = phi_source_block {
                    // A phi input is considered to be a use by the associated
                    // predecessor block
                    self.up_and_mark(cfg, pred_block, val);
                } else {
                    self.up_and_mark(cfg, block, val);
                }
            });
        }
    }

    // XXX better api
    pub fn block_live_ins(&self, block: ir::Block) -> &BitSet {
        &self.live_ins[block]
    }
    pub fn block_live_outs(&self, block: ir::Block) -> &BitSet {
        &self.live_outs[block]
    }

    /// Propagate liveness of `val` "upward" from its use in `block`
    fn up_and_mark(&mut self, cfg: &ControlFlowGraph, block: ir::Block, val: V) {
        let Some((def_block, is_phi_def)) = self.defs[val] else {
            // `val` is never defined, so it must be an immediate
            // xxx maybe for_each_use should omit immediates
            return;
        };

        // If `val` is defined in this block, there's nothing to do.
        // If `val` is defined by a phi function, then we consider it live-in.
        if def_block == block && !is_phi_def {
            return;
        }

        if !self.live_ins[block].insert(val.index()) {
            // Already marked, so propagation to preds already done
            return;
        }

        // If `val` is the result of a phi, then it's live-in for the block
        // containing the phi, but not live-out for any predecessor block.
        if def_block == block && is_phi_def {
            return;
        }

        for pred in cfg.preds_of(block) {
            self.live_outs[*pred].insert(val.index());
            self.up_and_mark(cfg, *pred, val);
        }
    }

    /// Reset the `Liveness` struct so that it can be reused.
    pub fn clear(&mut self) {
        self.live_ins.clear();
        self.live_outs.clear();
        self.defs.clear();
    }
}

impl<V: EntityRef> Default for Liveness<V> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use bit_set::BitSet;
    use sonatina_ir::{Block, Module, Value};
    use sonatina_parser::{parser::Parser, ErrorKind};

    use crate::cfg::ControlFlowGraph;

    use super::Liveness;

    // xxx copied from evm.rs
    fn parse_sona(content: &str) -> Result<Module, String> {
        let parser = Parser::default();
        match parser.parse(content) {
            Ok(module) => Ok(module.module),
            Err(err) => match err.kind {
                ErrorKind::InvalidToken(msg) => Err(format!(
                    "failed to parse file: invalid token: {}. line: {}",
                    msg, err.line
                )),

                ErrorKind::SyntaxError(msg) => Err(format!(
                    "failed to parse file: invalid syntax: {}. line: {}",
                    msg, err.line
                )),

                ErrorKind::SemanticError(msg) => Err(format!(
                    "failed to parse file: invalid semantics: {}. line: {}",
                    msg, err.line
                )),
            },
        }
    }

    fn bitset(vals: &[usize]) -> BitSet {
        let mut set = BitSet::new();
        vals.iter().for_each(|v| {
            set.insert(*v);
        });
        set
    }

    #[test]
    fn test() {
        let src = r#"
target = "evm-ethereum-london"
func public %complex_loop() -> i8:
    block1:
        v0.i8 = add 1.i8 2.i8;
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

        let module = match parse_sona(src) {
            Ok(m) => m,
            Err(err) => panic!("{}", err),
        };
        let function = module.funcs.values().next().unwrap();
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(function);

        let mut live: Liveness<Value> = Liveness::default();
        live.compute(function, &cfg);

        assert_eq!(live.block_live_ins(Block(1)), &bitset(&[]));
        assert_eq!(live.block_live_outs(Block(1)), &bitset(&[0]));

        assert_eq!(live.block_live_ins(Block(2)), &bitset(&[0, 2, 3]));
        assert_eq!(live.block_live_outs(Block(2)), &bitset(&[0, 2, 3]));

        assert_eq!(live.block_live_ins(Block(3)), &bitset(&[0, 2, 3]));
        assert_eq!(live.block_live_outs(Block(3)), &bitset(&[0, 3]));

        assert_eq!(live.block_live_ins(Block(4)), &bitset(&[2]));
        assert_eq!(live.block_live_outs(Block(4)), &bitset(&[]));

        assert_eq!(live.block_live_ins(Block(5)), &bitset(&[0, 3]));
        assert_eq!(live.block_live_outs(Block(5)), &bitset(&[0]));

        assert_eq!(live.block_live_ins(Block(6)), &bitset(&[0, 3]));
        assert_eq!(live.block_live_outs(Block(6)), &bitset(&[0]));
    }
}
