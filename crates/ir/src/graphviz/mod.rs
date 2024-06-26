use std::io;

use crate::{ControlFlowGraph, Function};

mod block;
mod function;

use function::FunctionGraph;

pub fn render_to<W: io::Write>(func: &Function, output: &mut W) -> io::Result<()> {
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(func);
    let func_graph = FunctionGraph::new(func, &cfg);
    dot2::render(&func_graph, output).map_err(|err| match err {
        dot2::Error::Io(err) => err,
        _ => panic!("invalid graphviz id"),
    })
}

#[cfg(test)]
mod test {
    use crate::{builder::test_util::test_func_builder, Type};

    use super::*;

    #[test]
    fn test_dump_ir() {
        let mut builder = test_func_builder(&[Type::I64], Type::Void);

        let entry_block = builder.append_block();
        let then_block = builder.append_block();
        let else_block = builder.append_block();
        let merge_block = builder.append_block();

        let arg0 = builder.args()[0];

        builder.switch_to_block(entry_block);
        builder.br(arg0, then_block, else_block);

        builder.switch_to_block(then_block);
        let v1 = builder.make_imm_value(1i64);
        builder.jump(merge_block);

        builder.switch_to_block(else_block);
        let v2 = builder.make_imm_value(2i64);
        builder.jump(merge_block);

        builder.switch_to_block(merge_block);
        let v3 = builder.phi(Type::I64, &[(v1, then_block), (v2, else_block)]);
        builder.add(v3, arg0);
        builder.ret(None);

        builder.seal_all();
        let module = builder.finish().build();
        let func_ref = module.iter_functions().next().unwrap();

        let mut text = vec![];
        render_to(&module.funcs[func_ref], &mut text).unwrap();
        let text = String::from_utf8(text).unwrap();

        let expected =             "digraph test_func {
    block3[label=<<table border=\"0\" cellborder=\"1\" cellspacing=\"0\"><tr><td bgcolor=\"gray\" align=\"center\" colspan=\"1\">block3</td></tr><tr><td align=\"left\" balign=\"left\">v3.i64 = phi (1.i64 block1) (2.i64 block2);<br/>v4.i64 = add v3 v0;<br/>ret;<br/></td></tr></table>>][shape=\"none\"];
    block2[label=<<table border=\"0\" cellborder=\"1\" cellspacing=\"0\"><tr><td bgcolor=\"gray\" align=\"center\" colspan=\"1\">block2</td></tr><tr><td align=\"left\" balign=\"left\">jump block3;<br/></td></tr></table>>][shape=\"none\"];
    block1[label=<<table border=\"0\" cellborder=\"1\" cellspacing=\"0\"><tr><td bgcolor=\"gray\" align=\"center\" colspan=\"1\">block1</td></tr><tr><td align=\"left\" balign=\"left\">jump block3;<br/></td></tr></table>>][shape=\"none\"];
    block0[label=<<table border=\"0\" cellborder=\"1\" cellspacing=\"0\"><tr><td bgcolor=\"gray\" align=\"center\" colspan=\"1\">block0</td></tr><tr><td align=\"left\" balign=\"left\">branch v0 block1 block2;<br/></td></tr></table>>][shape=\"none\"];
    dummy_block[label=\"func public %test_func(i64) -> ()\"][shape=\"none\"];
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
