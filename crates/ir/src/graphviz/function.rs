use std::iter;

use dot2::{label::Text, GraphWalk, Id, Labeller, Style};

use crate::{value::DisplayArgValues, Block, ControlFlowGraph, Function, InsnData};

use super::block::BlockNode;

pub(super) const DUMMY_BLOCK: Block = Block(u32::MAX);

pub(super) struct FunctionGraph<'a> {
    func: &'a Function,
    cfg: &'a ControlFlowGraph,
}

impl<'a> FunctionGraph<'a> {
    pub fn new(func: &'a Function, cfg: &'a ControlFlowGraph) -> Self {
        Self { func, cfg }
    }
}

impl<'a> FunctionGraph<'a> {
    pub(super) fn blocks(&self) -> Vec<BlockNode<'a>> {
        let Self { func, cfg } = self;
        // Dummy block is needed to label the graph with the function signature. Returns a vector
        // with the dummy block as a last element.
        cfg.post_order()
            .map(|block| BlockNode::new(func, cfg, block))
            .chain(iter::once(BlockNode::new(func, cfg, DUMMY_BLOCK)))
            .collect()
    }
}

impl<'a> Labeller<'a> for FunctionGraph<'a> {
    type Node = BlockNode<'a>;
    type Edge = BlockEdge<'a>;
    type Subgraph = ();

    fn graph_id(&self) -> dot2::Result<Id<'a>> {
        let func = self.func;
        let sig_name = func.sig.name().to_string();
        Id::new(sig_name)
    }

    fn node_id(&self, n: &Self::Node) -> dot2::Result<Id<'a>> {
        let block = n.block;
        if block == DUMMY_BLOCK {
            return dot2::Id::new("dummy_block");
        }
        dot2::Id::new(format!("{block}"))
    }

    fn node_shape(&self, _n: &Self::Node) -> Option<Text<'a>> {
        Some(Text::LabelStr("none".into()))
    }

    fn edge_style(&'a self, e: &Self::Edge) -> Style {
        if e.from.block == DUMMY_BLOCK {
            Style::Invisible
        } else {
            Style::None
        }
    }

    fn node_label(&'a self, n: &Self::Node) -> dot2::Result<Text<'a>> {
        Ok(n.label())
    }

    fn edge_label(&self, e: &Self::Edge) -> Text<'a> {
        e.label()
    }
}

impl<'a> GraphWalk<'a> for FunctionGraph<'a> {
    type Node = BlockNode<'a>;
    type Edge = BlockEdge<'a>;
    type Subgraph = ();

    fn nodes(&self) -> dot2::Nodes<'a, Self::Node> {
        self.blocks().into()
    }

    fn edges(&'a self) -> dot2::Edges<'a, Self::Edge> {
        let Self { func, cfg } = self;
        let mut blocks = self.blocks();

        let dummy_block = blocks.pop().unwrap();
        let mut edges = vec![BlockEdge {
            from: dummy_block,
            to: BlockNode::new(func, cfg, Block(0u32)),
            func,
        }];
        for block in blocks {
            for succ in block.succs() {
                let edge = BlockEdge {
                    from: block,
                    to: succ,
                    func,
                };
                edges.push(edge);
            }
        }

        edges.into()
    }

    fn source(&self, edge: &Self::Edge) -> Self::Node {
        edge.from
    }

    fn target(&self, edge: &Self::Edge) -> Self::Node {
        edge.to
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) struct BlockEdge<'a> {
    from: BlockNode<'a>,
    to: BlockNode<'a>,
    func: &'a Function,
}

impl<'a> BlockEdge<'a> {
    fn label(self) -> Text<'static> {
        let Self { from, to, func } = self;
        let to = to.block;
        let from = from.block;
        for insn in func.layout.iter_insn(to) {
            if let InsnData::Phi { values, blocks, .. } = func.dfg.insn_data(insn) {
                for (i, block) in blocks.into_iter().enumerate() {
                    if *block == from {
                        let flow_arg = [values[i]];
                        let v = DisplayArgValues::new(&flow_arg, &func.dfg);
                        return Text::LabelStr(format!("{v}").into());
                    }
                }
            }
        }
        Text::LabelStr("".into())
    }
}
