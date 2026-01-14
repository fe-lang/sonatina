mod common;

use dir_test::{Fixture, dir_test};
use sonatina_codegen::optim::inliner::{Inliner, InlinerConfig};
use sonatina_ir::ir_writer::FuncWriter;
use sonatina_parser::ParsedModule;

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/inliner/",
    glob: "*.sntn"
    loader: common::parse_module,
)]
fn test(fixture: Fixture<ParsedModule>) {
    let fixture_path = fixture.path();
    let mut parsed = fixture.into_content();
    let module = &mut parsed.module;

    let mut inliner = Inliner::new(InlinerConfig::default());
    inliner.run(module);

    let mut result = String::new();
    for func_ref in module.funcs() {
        module.func_store.view(func_ref, |func| {
            result.push_str(&FuncWriter::new(func_ref, func).dump_string());
        });
        result.push_str("\n\n");
    }

    snap_test!(result, fixture_path);
}

#[test]
fn no_op_rewrite_self_wrapper_is_not_counted_as_rewrite() {
    let source = r#"
target = "evm-ethereum-london"

func private %foo(v0.i32) -> i32 {
    block0:
        v1.i32 = call %foo v0;
        return v1;
}

func public %caller(v0.i32) -> i32 {
    block0:
        v1.i32 = call %foo v0;
        return v1;
}
"#;

    let mut parsed = sonatina_parser::parse_module(source)
        .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"));
    let module = &mut parsed.module;
    let before = dump_module(module);

    let mut inliner = Inliner::new(InlinerConfig::default());
    let stats = inliner.run(module);

    assert_eq!(stats.calls_rewritten, 0);
    assert_eq!(before, dump_module(module));
}

fn dump_module(module: &sonatina_ir::Module) -> String {
    let mut result = String::new();
    for func_ref in module.funcs() {
        module.func_store.view(func_ref, |func| {
            result.push_str(&FuncWriter::new(func_ref, func).dump_string());
        });
        result.push_str("\n\n");
    }
    result
}
