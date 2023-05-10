use dir_test::{dir_test, Fixture};

use sonatina_codegen::{
    cfg::ControlFlowGraph, isa::evm::EvmBackend, liveness::Liveness, machinst::lower::Lower,
    stackalloc::SimpleAlloc,
};
use sonatina_parser::{
    parser::{ParsedModule, Parser},
    ErrorKind,
};

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
    let module = match parse_sona(fixture.content()) {
        Ok(m) => m,
        Err(err) => panic!("{}", err),
    };

    let function = module.module.funcs.values().next().unwrap();
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(function);
    let mut liveness = Liveness::new();
    liveness.compute(function, &cfg);
    let mut alloc = SimpleAlloc::for_function(function, &cfg, &liveness, 16);
    let lower = Lower::new(function);
    let backend = EvmBackend::default();

    let vcode = match lower.lower(&backend, &mut alloc) {
        Ok(vcode) => vcode,
        Err(err) => panic!("{:?}", err),
    };

    let mut v = Vec::new();
    vcode.print(&mut v, function).unwrap();
    snap_test!(String::from_utf8(v).unwrap(), fixture.path());
}
