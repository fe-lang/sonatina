use dir_test::{dir_test, Fixture};

use hex::ToHex;
use sonatina_codegen::{
    cfg::ControlFlowGraph,
    critical_edge::CriticalEdgeSplitter,
    domtree::DomTree,
    isa::evm::{opcode::OpCode, EvmBackend},
    liveness::Liveness,
    machinst::{assemble::ObjectLayout, lower::Lower, vcode::VCode},
    stackalloc::SimpleAlloc,
};
use sonatina_ir::{Block, Function};
use sonatina_parser::{
    parser::{ParsedModule, Parser},
    ErrorKind,
};
use std::io::Write;

// XXX copied from fe test-utils
#[macro_export]
macro_rules! snap_test {
    ($value:expr, $fixture_path: expr) => {
        let mut settings = insta::Settings::new();
        let fixture_path = ::std::path::Path::new($fixture_path);
        let fixture_dir = fixture_path.parent().unwrap();
        let fixture_name = fixture_path.file_stem().unwrap().to_str().unwrap();

        settings.set_snapshot_path(fixture_dir);
        settings.set_input_file($fixture_path);
        settings.set_prepend_module_to_snapshot(false);
        settings.bind(|| {
            insta::_macro_support::assert_snapshot(
                insta::_macro_support::AutoName.into(),
                &$value,
                env!("CARGO_MANIFEST_DIR"),
                fixture_name,
                module_path!(),
                file!(),
                line!(),
                stringify!($value),
            )
            .unwrap()
        })
    };
}

fn parse_sona(content: &str) -> Result<ParsedModule, String> {
    let parser = Parser::default();
    match parser.parse(content) {
        Ok(module) => Ok(module),
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

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/evm",
    glob: "*.sntn"
)]
fn test_evm(fixture: Fixture<&str>) {
    let mut module = match parse_sona(fixture.content()) {
        Ok(m) => m,
        Err(err) => panic!("{}", err),
    };

    let backend = EvmBackend::default();

    let mut v = Vec::new();
    let funcs = module
        .module
        .funcs
        .iter_mut()
        .map(|(fref, function)| {
            let (vcode, block_order) = vcode_for_fn(function, &backend);
            vcode.print(&mut v, function).unwrap();
            writeln!(v).unwrap();
            (fref, vcode, block_order)
        })
        .collect();

    write!(&mut v, "\n\n---------------\n\n").unwrap();

    let mut layout = ObjectLayout::new(funcs, 0);
    let mut i = 0;
    while layout.resize(&backend, 0) {
        i += 1;
        println!("resize iteration {i}");
    }
    layout.print(&mut v, &module.module.funcs).unwrap();

    let mut bytecode = Vec::new();
    layout.emit(&backend, &mut bytecode);
    let hex = bytecode.encode_hex::<String>();

    write!(&mut v, "\n\n0x{hex}").unwrap();

    snap_test!(String::from_utf8(v).unwrap(), fixture.path());
}

fn vcode_for_fn(function: &mut Function, backend: &EvmBackend) -> (VCode<OpCode>, Vec<Block>) {
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(function);
    let mut splitter = CriticalEdgeSplitter::new();
    splitter.run(function, &mut cfg);

    let mut liveness = Liveness::new();
    liveness.compute(function, &cfg);
    let mut dom = DomTree::new();
    dom.compute(&cfg);
    let mut alloc = SimpleAlloc::for_function(function, &cfg, &dom, &liveness, 16);
    let lower = Lower::new(function);

    match lower.lower(backend, &mut alloc) {
        Ok(vcode) => (vcode, dom.rpo().to_owned()),
        Err(err) => panic!("{:?}", err),
    }
}
