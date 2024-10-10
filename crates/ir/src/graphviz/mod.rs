use std::io;

use crate::{ir_writer::FuncWriteCtx, module::FuncRef, ControlFlowGraph, Function};

mod block;
mod function;

use function::FunctionGraph;

pub fn render_to<W: io::Write>(
    func: &Function,
    func_ref: FuncRef,
    output: &mut W,
) -> io::Result<()> {
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(func);
    let ctx = FuncWriteCtx::new(func, func_ref);
    let func_graph = FunctionGraph::new(&ctx, &cfg);
    dot2::render(&func_graph, output).map_err(|err| match err {
        dot2::Error::Io(err) => err,
        _ => panic!("invalid graphviz id"),
    })
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        builder::test_util::test_func_builder,
        inst::{
            arith::Add,
            control_flow::{Br, Jump, Phi, Return},
        },
        isa::Isa,
        Type,
    };

    #[test]
    fn test_dump_ir() {
        let (evm, mut builder) = test_func_builder(&[Type::I64], Type::Void);
        let is = evm.inst_set();

        let entry_block = builder.append_block();
        let then_block = builder.append_block();
        let else_block = builder.append_block();
        let merge_block = builder.append_block();

        let arg0 = builder.args()[0];

        builder.switch_to_block(entry_block);
        let br = Br::new(is, arg0, then_block, else_block);
        builder.insert_inst_no_result(br);

        builder.switch_to_block(then_block);
        let v1 = builder.make_imm_value(1i64);
        let jump = Jump::new(is, merge_block);
        builder.insert_inst_no_result(jump);

        builder.switch_to_block(else_block);
        let v2 = builder.make_imm_value(2i64);
        let jump = Jump::new(is, merge_block);
        builder.insert_inst_no_result(jump);

        builder.switch_to_block(merge_block);
        let phi = Phi::new(is, vec![(v1, then_block), (v2, else_block)], Type::I64);
        let v3 = builder.insert_inst(phi, Type::I64);
        let add = Add::new(is, v3, arg0);
        builder.insert_inst(add, Type::I64);
        let ret = Return::new(is, None);
        builder.insert_inst_no_result(ret);

        builder.seal_all();
        let module = builder.finish().build();
        let func_ref = module.iter_functions().next().unwrap();

        let mut text = vec![];
        render_to(&module.funcs[func_ref], func_ref, &mut text).unwrap();
        let text = String::from_utf8(text).unwrap();
        let expected = "digraph test_func {
    block3[label=<<table border=\"0\" cellborder=\"1\" cellspacing=\"0\"><tr><td bgcolor=\"gray\" align=\"center\" colspan=\"1\">block3</td></tr><tr><td align=\"left\" balign=\"left\">v3.i64 = phi (1.i64 block1) (2.i64 block2);<br/>v4.i64 = add v3 v0;<br/>return;<br/></td></tr></table>>][shape=\"none\"];
    block2[label=<<table border=\"0\" cellborder=\"1\" cellspacing=\"0\"><tr><td bgcolor=\"gray\" align=\"center\" colspan=\"1\">block2</td></tr><tr><td align=\"left\" balign=\"left\">jump block3;<br/></td></tr></table>>][shape=\"none\"];
    block1[label=<<table border=\"0\" cellborder=\"1\" cellspacing=\"0\"><tr><td bgcolor=\"gray\" align=\"center\" colspan=\"1\">block1</td></tr><tr><td align=\"left\" balign=\"left\">jump block3;<br/></td></tr></table>>][shape=\"none\"];
    block0[label=<<table border=\"0\" cellborder=\"1\" cellspacing=\"0\"><tr><td bgcolor=\"gray\" align=\"center\" colspan=\"1\">block0</td></tr><tr><td align=\"left\" balign=\"left\">br v0 block1 block2;<br/></td></tr></table>>][shape=\"none\"];
    dummy_block[label=\"func public %test_func(i64) -> void\"][shape=\"none\"];
    dummy_block -> block0[label=\"\"][style=\"invis\"];
    block2 -> block3[label=\"2.i64\"];
    block1 -> block3[label=\"1.i64\"];
    block0 -> block1[label=\"\"];
    block0 -> block2[label=\"\"];
}
";
        assert_eq!(text, expected);
    }
}
