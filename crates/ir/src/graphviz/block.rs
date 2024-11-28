use std::fmt::Write;

use dot2::label;

use super::function::DUMMY_BLOCK;
use crate::{
    ir_writer::{FuncWriteCtx, IrWrite, ValueWithTy},
    BlockId, ControlFlowGraph, Function,
};

#[derive(Clone, Copy)]
pub(super) struct BlockNode<'a> {
    pub(super) ctx: &'a FuncWriteCtx<'a>,
    pub(super) cfg: &'a ControlFlowGraph,
    pub(super) block: BlockId,
}

impl<'a> BlockNode<'a> {
    pub(super) fn new(ctx: &'a FuncWriteCtx, cfg: &'a ControlFlowGraph, block: BlockId) -> Self {
        Self { ctx, cfg, block }
    }

    pub(super) fn succs(self) -> Vec<Self> {
        self.cfg
            .succs_of(self.block)
            .map(|block| BlockNode::new(self.ctx, self.cfg, *block))
            .collect()
    }
}

impl<'a> BlockNode<'a> {
    pub(super) fn label(self) -> label::Text<'static> {
        let Self { block, ctx, .. } = self;
        let Function { sig, layout, .. } = &ctx.func;
        if block == DUMMY_BLOCK {
            let sig = sig.dump_string(self.ctx);
            return label::Text::LabelStr(sig.into());
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
        for inst in layout.iter_inst(self.block) {
            let mut inst_string = String::new();
            if let Some(result) = self.ctx.func.dfg.inst_result(inst) {
                let result_with_ty = ValueWithTy(result);
                write!(
                    &mut inst_string,
                    "{} = ",
                    result_with_ty.dump_string(self.ctx)
                )
                .unwrap();
            }
            let inst = inst.dump_string(self.ctx);
            write!(&mut inst_string, "{inst};").unwrap();

            write!(label, "{}", dot2::escape_html(&inst_string)).unwrap();
            write!(label, "<br/>").unwrap();
        }
        write!(label, r#"</td></tr>"#).unwrap();

        write!(label, "</table>").unwrap();

        label::Text::HtmlStr(label.into())
    }
}
