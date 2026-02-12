mod common;

use dir_test::{Fixture, dir_test};
use sonatina_codegen::{
    analysis::func_behavior,
    optim::inliner::{Inliner, InlinerConfig},
};
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

#[test]
fn splice_require_pure_allows_proven_pure_calls() {
    let source = r#"
target = "evm-ethereum-london"

func private %leaf(v0.i32) -> i32 {
    block0:
        v1.i32 = add v0 1.i32;
        return v1;
}

func private %wrapper(v0.i32) -> i32 {
    block0:
        v1.i32 = call %leaf v0;
        v2.i32 = mul v1 2.i32;
        return v2;
}

func public %caller(v0.i32) -> i32 {
    block0:
        v1.i32 = call %wrapper v0;
        return v1;
}
"#;

    let mut parsed = sonatina_parser::parse_module(source)
        .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"));
    let module = &mut parsed.module;
    func_behavior::analyze_module(module);

    let mut cfg = InlinerConfig::default();
    cfg.splice_require_pure = true;
    let mut inliner = Inliner::new(cfg);
    let stats = inliner.run(module);

    let dumped = dump_module(module);
    assert!(
        stats.calls_spliced > 0,
        "pure call body should be spliceable in pure mode:\n{dumped}"
    );
    assert!(
        !dumped.contains("call %wrapper"),
        "wrapper call should be eliminated:\n{dumped}"
    );
}

#[test]
fn splice_require_pure_rejects_mem_read_calls() {
    let source = r#"
target = "evm-ethereum-london"

func private %read_mem(v0.*i32) -> i32 {
    block0:
        v1.i32 = mload v0 i32;
        return v1;
}

func private %wrapper(v0.*i32) -> i32 {
    block0:
        v1.i32 = call %read_mem v0;
        v2.i32 = add v1 1.i32;
        return v2;
}

func public %caller(v0.*i32) -> i32 {
    block0:
        v1.i32 = call %wrapper v0;
        return v1;
}
"#;

    let mut parsed = sonatina_parser::parse_module(source)
        .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"));
    let module = &mut parsed.module;
    func_behavior::analyze_module(module);

    let mut cfg = InlinerConfig::default();
    cfg.splice_require_pure = true;
    let mut inliner = Inliner::new(cfg);
    let stats = inliner.run(module);

    let dumped = dump_module(module);
    assert_eq!(
        stats.calls_spliced, 0,
        "unexpected splice in pure mode:\n{dumped}"
    );
    assert!(
        dumped.contains("call %wrapper"),
        "wrapper call should remain when body contains mem-read call:\n{dumped}"
    );
    assert!(stats.skipped_not_pure > 0);
}

#[test]
fn splice_require_pure_rejects_mem_write_and_noreturn_calls() {
    let source = r#"
target = "evm-ethereum-london"

func private %write_mem(v0.*i32) {
    block0:
        mstore v0 1.i32 i32;
        return;
}

func private %spin() {
    block0:
        jump block0;
}

func private %wrapper_write(v0.*i32) -> i32 {
    block0:
        call %write_mem v0;
        return 7.i32;
}

func private %wrapper_noreturn() {
    block0:
        call %spin;
        unreachable;
}

func public %caller_write(v0.*i32) -> i32 {
    block0:
        v1.i32 = call %wrapper_write v0;
        return v1;
}

func public %caller_noreturn() {
    block0:
        call %wrapper_noreturn;
        return;
}
"#;

    let mut parsed = sonatina_parser::parse_module(source)
        .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"));
    let module = &mut parsed.module;
    func_behavior::analyze_module(module);

    let mut cfg = InlinerConfig::default();
    cfg.splice_require_pure = true;
    let mut inliner = Inliner::new(cfg);
    let stats = inliner.run(module);

    let dumped = dump_module(module);
    assert_eq!(
        stats.calls_spliced, 0,
        "unexpected splice in pure mode:\n{dumped}"
    );
    assert!(
        dumped.contains("call %wrapper_write"),
        "mem-write wrapper call should remain:\n{dumped}"
    );
    assert!(
        dumped.contains("call %wrapper_noreturn"),
        "noreturn wrapper call should remain:\n{dumped}"
    );
    assert!(stats.skipped_not_pure > 0);
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
