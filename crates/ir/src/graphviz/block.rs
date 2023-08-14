use std::fmt::Write;

use dot2::label;

use crate::{function::DisplaySignature, insn::DisplayInsn, Block, ControlFlowGraph, Function};

#[derive(Debug, Clone, Copy)]
pub(super) struct BlockNode<'a> {
    pub(super) func: &'a Function,
    pub(super) block: Block,
}

impl<'a> BlockNode<'a> {
    pub(super) fn new(func: &'a Function, block: Block) -> Self {
        Self { func, block }
    }

    pub(super) fn succs(self) -> Vec<Self> {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(self.func);
        cfg.succs_of(self.block)
            .map(|block| BlockNode::new(self.func, *block))
            .collect()
    }
}

impl<'a> BlockNode<'a> {
    pub(super) fn label(self) -> label::Text<'static> {
        let Self { block, func } = self;
        let Function {
            sig, dfg, layout, ..
        } = func;
        if block.0 == u32::MAX {
            let sig = DisplaySignature::new(sig, dfg);
            return label::Text::LabelStr(format!("{sig}").into());
        }

        let mut label = r#"<table border="0" cellborder="1" cellspacing="0">"#.to_string();

        // Write block header.
        write!(
            &mut label,
            r#"<tr><td bgcolor="gray" align="center" colspan="1">{}</td></tr>"#,
            block
        )
        .unwrap();

        // Write block body.
        write!(label, r#"<tr><td align="left" balign="left">"#).unwrap();
        for insn in layout.iter_insn(self.block) {
            let display_insn = DisplayInsn::new(insn, dfg);
            let mut insn_string = String::new();
            write!(&mut insn_string, "{}", display_insn).unwrap();

            write!(label, "{}", dot2::escape_html(&insn_string)).unwrap();
            write!(label, "<br/>").unwrap();
        }
        write!(label, r#"</td></tr>"#).unwrap();

        write!(label, "</table>").unwrap();

        label::Text::HtmlStr(label.into())
    }
}
