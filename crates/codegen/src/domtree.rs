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
                let preds = cfg.preds_of(block);
                if preds.is_empty() {
                    continue;
                }

                let mut new_dom = preds[0];
                for &pred in &preds[1..] {
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
