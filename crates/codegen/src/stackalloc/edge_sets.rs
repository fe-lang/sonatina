use std::collections::BTreeSet;

use crate::cfg::ControlFlowGraph;
use cranelift_entity::{packed_option::PackedOption, PrimaryMap, SecondaryMap};
use sonatina_ir::Block;

// Vec::drain_filter https://github.com/rust-lang/rust/issues/43244
use drain_filter_polyfill::VecExt;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Copy, Hash)]
pub struct EdgeSet(pub u32);
cranelift_entity::entity_impl!(EdgeSet);

#[derive(Default, Debug)]
pub struct EdgeSets {
    sets: PrimaryMap<EdgeSet, BTreeSet<(Block, Block)>>,
    /// Block => (predecessor_edge_set, succ_edge_set)
    block_sets: SecondaryMap<Block, (PackedOption<EdgeSet>, PackedOption<EdgeSet>)>,
}

impl EdgeSets {
    pub fn compute(&mut self, cfg: &ControlFlowGraph) {
        self.clear();

        // - each edge is in exactly one edge set
        // - if two edges share either a pred or succ block, they are in the same edge set
        // - the x-stack is the same for every edge in an edge set

        let mut edges = cfg.iter_edges().copied().collect::<Vec<_>>();
        let mut heads = BTreeSet::<Block>::new();
        let mut tails = BTreeSet::<Block>::new();

        // We build each edge-set in turn, by collecting the edges that share
        // either a head or tail with an edge already in the set.
        while let Some((a, b)) = edges.pop() {
            let setid = self.sets.next_key();
            let mut set = BTreeSet::new();
            set.insert((a, b));
            heads.insert(a);
            tails.insert(b);

            let mut prev_len = 0;
            while set.len() > prev_len {
                prev_len = set.len();
                set.extend(VecExt::drain_filter(&mut edges, |&mut (x, y)| {
                    if heads.contains(&x) {
                        tails.insert(y);
                        true
                    } else if tails.contains(&y) {
                        heads.insert(x);
                        true
                    } else {
                        false
                    }
                }));
            }
            self.sets.push(set);
            heads
                .iter()
                .for_each(|&b| self.block_sets[b].1 = setid.into());
            tails
                .iter()
                .for_each(|&b| self.block_sets[b].0 = setid.into());
            heads.clear();
            tails.clear();
        }
    }

    pub fn pred_edge_set(&self, block: Block) -> Option<&BTreeSet<(Block, Block)>> {
        let id = self.block_sets[block].0.expand()?;
        Some(&self.sets[id])
    }

    pub fn succ_edge_set(&self, block: Block) -> Option<&BTreeSet<(Block, Block)>> {
        let id = self.block_sets[block].1.expand()?;
        Some(&self.sets[id])
    }

    pub fn len(&self) -> usize {
        self.sets.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = &BTreeSet<(Block, Block)>> {
        self.sets.values()
    }

    pub fn clear(&mut self) {
        self.sets.clear();
        self.block_sets.clear();
    }
}

#[cfg(test)]
mod tests {
    use sonatina_ir::Block;
    use sonatina_parser::parser::Parser;

    use crate::cfg::ControlFlowGraph;

    use super::EdgeSets;

    const SRC: &'static str = r#"
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
    //       <------------
    //      /             \
    // 1 - 2 - 3 - 5 - 7 ->
    //      \   \     /
    //       \   6 -->
    //        4
    //
    // edge sets:
    //  {(1, 2), (7, 2)}
    //  {(2, 3), (2, 4)}
    //  {(3, 5), (3, 6)}
    //  {(5, 7), (6, 7)}

    #[test]
    fn test() {
        let parser = Parser::default();
        let module = parser.parse(SRC).unwrap().module;
        let function = module.funcs.values().next().unwrap();
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(function);

        let mut edgesets = EdgeSets::default();
        edgesets.compute(&cfg);

        assert_eq!(edgesets.len(), 4);
        assert_eq!(
            edgesets.pred_edge_set(Block(2)),
            Some(&[(Block(1), Block(2)), (Block(7), Block(2))].into())
        );
        assert_eq!(
            edgesets.succ_edge_set(Block(2)),
            Some(&[(Block(2), Block(3)), (Block(2), Block(4))].into())
        );
        assert_eq!(
            edgesets.succ_edge_set(Block(3)),
            Some(&[(Block(3), Block(5)), (Block(3), Block(6))].into())
        );
        assert_eq!(
            edgesets.pred_edge_set(Block(7)),
            Some(&[(Block(5), Block(7)), (Block(6), Block(7))].into())
        );
    }
}
