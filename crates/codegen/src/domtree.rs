use cranelift_entity::{packed_option::PackedOption, SecondaryMap};

use super::cfg::ControlFlowGraph;
use super::Block;

#[derive(Default)]
pub struct DomTree {
    doms: SecondaryMap<Block, PackedOption<Block>>,
    rpo: Vec<Block>,
}

impl DomTree {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn idom_of(&self, block: Block) -> Option<Block> {
        self.doms[block].expand()
    }

    pub fn compute(&mut self, cfg: &ControlFlowGraph) {
        self.rpo = cfg.post_order().collect();
        self.rpo.reverse();

        let block_num = self.rpo.len();

        if self.doms.capacity() < block_num {
            self.doms = SecondaryMap::with_capacity(block_num);
        } else {
            self.doms.clear();
        }

        let mut fingers = SecondaryMap::with_capacity(block_num);
        for (i, &block) in self.rpo.iter().enumerate() {
            fingers[block] = (block_num - i) as u32;
        }

        match self.rpo.first() {
            Some(&entry) => self.doms[entry] = entry.into(),
            None => return,
        }

        let mut changed = true;
        while changed {
            changed = false;
            for &block in self.rpo.iter().skip(1) {
                let mut preds = cfg.preds_of(block);

                let mut new_dom = match preds.next() {
                    Some(block) => *block,
                    None => continue,
                };

                for &pred in preds {
                    if self.doms[pred].is_some() {
                        new_dom = self.intersect(new_dom, pred, &fingers);
                    }
                }
                if Some(new_dom) != self.doms[block].expand() {
                    changed = true;
                    self.doms[block] = new_dom.into();
                }
            }
        }
    }

    fn intersect(&self, mut b1: Block, mut b2: Block, fingers: &SecondaryMap<Block, u32>) -> Block {
        while b1 != b2 {
            while fingers[b1] < fingers[b2] {
                b1 = self.doms[b1].unwrap();
            }
            while fingers[b2] < fingers[b1] {
                b2 = self.doms[b2].unwrap();
            }
        }

        b1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::ir::builder::test_util::func_builder;
    use crate::Function;

    fn calc_dom(func: &Function) -> DomTree {
        let mut cfg = ControlFlowGraph::default();
        cfg.compute(func);
        let mut dom_tree = DomTree::default();
        dom_tree.compute(&cfg);
        dom_tree
    }

    #[test]
    fn dom_tree_if_else() {
        let mut builder = func_builder(vec![], vec![]);

        let entry_block = builder.append_block();
        let then_block = builder.append_block();
        let else_block = builder.append_block();
        let merge_block = builder.append_block();

        builder.switch_to_block(entry_block);
        let v0 = builder.imm_u8(1);
        builder.br(v0, else_block, then_block);

        builder.switch_to_block(then_block);
        builder.jump(merge_block);

        builder.switch_to_block(else_block);
        builder.jump(merge_block);

        builder.switch_to_block(merge_block);
        builder.ret(&[]);

        builder.seal_all();

        let dom_tree = calc_dom(&builder.build());
        assert_eq!(dom_tree.idom_of(entry_block), Some(entry_block));
        assert_eq!(dom_tree.idom_of(then_block), Some(entry_block));
        assert_eq!(dom_tree.idom_of(else_block), Some(entry_block));
        assert_eq!(dom_tree.idom_of(merge_block), Some(entry_block));
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn dom_tree_complex() {
        let mut builder = func_builder(vec![], vec![]);

        let a = builder.append_block();
        let b = builder.append_block();
        let c = builder.append_block();
        let d = builder.append_block();
        let e = builder.append_block();
        let f = builder.append_block();
        let g = builder.append_block();
        let h = builder.append_block();
        let i = builder.append_block();
        let j = builder.append_block();
        let k = builder.append_block();
        let l = builder.append_block();
        let m = builder.append_block();

        builder.switch_to_block(a);
        let v0 = builder.imm_u8(1);
        builder.br(v0, c, b);

        builder.switch_to_block(b);
        builder.br(v0, g, d);

        builder.switch_to_block(c);
        builder.br(v0, h, e);

        builder.switch_to_block(d);
        builder.br(v0, g, f);

        builder.switch_to_block(e);
        builder.br(v0, h, c);

        builder.switch_to_block(f);
        builder.br(v0, k, i);

        builder.switch_to_block(g);
        builder.jump(j);

        builder.switch_to_block(h);
        builder.jump(m);

        builder.switch_to_block(i);
        builder.jump(l);

        builder.switch_to_block(j);
        builder.jump(i);

        builder.switch_to_block(k);
        builder.jump(l);

        builder.switch_to_block(l);
        builder.br(v0, m, b);

        builder.switch_to_block(m);
        builder.ret(&[]);

        builder.seal_all();

        let dom_tree = calc_dom(&builder.build());
        assert_eq!(dom_tree.idom_of(a), Some(a));
        assert_eq!(dom_tree.idom_of(b), Some(a));
        assert_eq!(dom_tree.idom_of(c), Some(a));
        assert_eq!(dom_tree.idom_of(d), Some(b));
        assert_eq!(dom_tree.idom_of(e), Some(c));
        assert_eq!(dom_tree.idom_of(f), Some(d));
        assert_eq!(dom_tree.idom_of(g), Some(b));
        assert_eq!(dom_tree.idom_of(h), Some(c));
        assert_eq!(dom_tree.idom_of(i), Some(b));
        assert_eq!(dom_tree.idom_of(j), Some(g));
        assert_eq!(dom_tree.idom_of(k), Some(f));
    }
}
