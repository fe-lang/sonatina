mod common;

use dir_test::{Fixture, dir_test};
use sonatina_codegen::{
    analysis::func_behavior,
    optim::inliner::{Inliner, InlinerConfig},
};
use sonatina_ir::{ir_writer::FuncWriter, module::FuncAttrs};
use sonatina_parser::ParsedModule;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

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

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/inliner_full/",
    glob: "*.sntn"
    loader: common::parse_module,
)]
fn test_full(fixture: Fixture<ParsedModule>) {
    let fixture_path = fixture.path();
    let mut parsed = fixture.into_content();
    let module = &mut parsed.module;

    let mut inliner = Inliner::new(full_inliner_test_config());
    let stats = inliner.run(module);
    assert!(
        stats.full_calls_inlined > 0,
        "expected at least one full-inline in {}",
        fixture_path
    );
    assert_module_verified(module);

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

    let cfg = InlinerConfig {
        splice_require_pure: true,
        ..Default::default()
    };
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
fn splice_require_pure_allows_mem_read_calls() {
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

    let cfg = InlinerConfig {
        splice_require_pure: true,
        ..Default::default()
    };
    let mut inliner = Inliner::new(cfg);
    let stats = inliner.run(module);

    let dumped = dump_module(module);
    assert!(
        stats.calls_spliced > 0,
        "mem-read call body should be spliceable in pure mode:\n{dumped}"
    );
    assert!(
        !dumped.contains("call %wrapper"),
        "wrapper call should be eliminated when body contains mem-read call:\n{dumped}"
    );
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

    let cfg = InlinerConfig {
        splice_require_pure: true,
        ..Default::default()
    };
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

#[test]
fn single_callsite_splices_large_single_block_even_with_tight_cap() {
    let source = r#"
target = "evm-ethereum-london"

func private %large(v0.i32) -> i32 {
    block0:
        v1.i32 = add v0 1.i32;
        v2.i32 = add v1 2.i32;
        v3.i32 = add v2 3.i32;
        v4.i32 = add v3 4.i32;
        v5.i32 = add v4 5.i32;
        v6.i32 = add v5 6.i32;
        v7.i32 = add v6 7.i32;
        v8.i32 = add v7 8.i32;
        return v8;
}

func public %caller(v0.i32) -> i32 {
    block0:
        v2.i32 = call %large v0;
        return v2;
}
"#;

    let mut parsed = sonatina_parser::parse_module(source)
        .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"));
    let module = &mut parsed.module;

    let cfg = InlinerConfig {
        splice_max_insts: 1,
        ..Default::default()
    };
    let mut inliner = Inliner::new(cfg);
    let stats = inliner.run(module);

    let dumped = dump_module(module);
    assert!(
        stats.calls_spliced >= 1,
        "single callsite should splice even when cap is tight:\n{dumped}"
    );
    assert!(
        !dumped.contains("call %large"),
        "single callsite should inline large callee:\n{dumped}"
    );
}

#[test]
fn multi_callsite_splice_uses_configurable_size_cap() {
    let source = r#"
target = "evm-ethereum-london"

func private %large(v0.i32) -> i32 {
    block0:
        v1.i32 = add v0 1.i32;
        v2.i32 = add v1 2.i32;
        v3.i32 = add v2 3.i32;
        v4.i32 = add v3 4.i32;
        v5.i32 = add v4 5.i32;
        return v5;
}

func public %caller(v0.i32, v1.i32) -> i32 {
    block0:
        v2.i32 = call %large v0;
        v3.i32 = call %large v1;
        v4.i32 = add v2 v3;
        return v4;
}
"#;

    let mut parsed = sonatina_parser::parse_module(source)
        .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"));
    let module = &mut parsed.module;

    let mut inliner = Inliner::new(InlinerConfig {
        splice_max_insts: 2,
        ..Default::default()
    });
    let stats = inliner.run(module);
    let dumped = dump_module(module);

    assert_eq!(
        stats.calls_spliced, 0,
        "large multi-callsite callee should be capped"
    );
    assert!(
        dumped.contains("call %large"),
        "tight multi-callsite cap should keep calls:\n{dumped}"
    );

    let mut parsed = sonatina_parser::parse_module(source)
        .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"));
    let module = &mut parsed.module;

    let mut inliner = Inliner::new(InlinerConfig {
        splice_max_insts: 8,
        ..Default::default()
    });
    let stats = inliner.run(module);
    let dumped = dump_module(module);

    assert!(
        stats.calls_spliced >= 2,
        "looser multi-callsite cap should allow splicing:\n{dumped}"
    );
    assert!(
        !dumped.contains("call %large"),
        "large callee should inline when multi-callsite cap is raised:\n{dumped}"
    );
}

#[test]
fn inliner_splices_multi_result_callees_without_legalizing_them() {
    let source = r#"
target = "evm-ethereum-osaka"

func private %leaf(v0.i256, v1.i256) -> i256 {
    block0:
        (v2.i256, v3.i1) = uaddo v0 v1;
        return v2;
}

func public %caller(v0.i256, v1.i256) -> i256 {
    block0:
        v2.i256 = call %leaf v0 v1;
        return v2;
}
"#;

    let mut parsed = sonatina_parser::parse_module(source)
        .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"));
    let module = &mut parsed.module;

    let mut inliner = Inliner::new(InlinerConfig::default());
    let stats = inliner.run(module);

    let dumped = dump_module(module);
    assert!(
        !dumped.contains("call %leaf"),
        "inliner should splice the callsite:\n{dumped}"
    );
    assert!(
        dumped.contains("uaddo"),
        "inliner should preserve multi-result instructions until lowering:\n{dumped}"
    );
    assert!(
        stats.calls_spliced >= 1,
        "expected the callsite to be spliced:\n{dumped}"
    );
    let report = verify_module(module, &VerifierConfig::for_level(VerificationLevel::Fast));
    assert!(report.is_ok(), "module failed verification: {report:?}");
}

#[test]
fn inliner_splices_multi_return_callees() {
    let source = r#"
target = "evm-ethereum-osaka"

func private %pair_leaf(v0.i256, v1.i256) -> (i256, i1) {
    block0:
        (v2.i256, v3.i1) = uaddo v0 v1;
        return (v2, v3);
}

func public %caller(v0.i256, v1.i256) -> (i256, i1) {
    block0:
        (v2.i256, v3.i1) = call %pair_leaf v0 v1;
        return (v2, v3);
}
"#;

    let mut parsed = sonatina_parser::parse_module(source)
        .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"));
    let module = &mut parsed.module;

    let mut inliner = Inliner::new(InlinerConfig::default());
    let stats = inliner.run(module);

    let dumped = dump_module(module);
    assert!(
        !dumped.contains("call %pair_leaf"),
        "inliner should splice the multi-return callsite:\n{dumped}"
    );
    assert!(
        dumped.contains("uaddo"),
        "spliced body should preserve multi-result instructions:\n{dumped}"
    );
    assert!(stats.calls_spliced >= 1, "expected splice:\n{dumped}");
    let report = verify_module(module, &VerifierConfig::for_level(VerificationLevel::Fast));
    assert!(report.is_ok(), "module failed verification: {report:?}");
}

#[test]
fn inliner_rewrites_multi_return_wrappers() {
    let source = r#"
target = "evm-ethereum-osaka"

func private %leaf(v0.i256, v1.i256) -> (i256, i1) {
    block0:
        (v2.i256, v3.i1) = uaddo v0 v1;
        return (v2, v3);
}

func private %wrapper(v0.i256, v1.i256) -> (i256, i1) {
    block0:
        (v2.i256, v3.i1) = call %leaf v0 v1;
        return (v2, v3);
}

func public %caller(v0.i256, v1.i256) -> (i256, i1) {
    block0:
        (v2.i256, v3.i1) = call %wrapper v0 v1;
        return (v2, v3);
}
"#;

    let mut parsed = sonatina_parser::parse_module(source)
        .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"));
    let module = &mut parsed.module;

    let mut inliner = Inliner::new(InlinerConfig {
        enable_single_block_splice: false,
        ..Default::default()
    });
    let stats = inliner.run(module);

    let dumped = dump_module(module);
    assert!(
        !dumped.contains("call %wrapper"),
        "wrapper call should be rewritten:\n{dumped}"
    );
    assert!(
        dumped.contains("call %leaf"),
        "rewritten call should target leaf directly:\n{dumped}"
    );
    assert!(stats.calls_rewritten >= 1, "expected rewrite:\n{dumped}");
    let report = verify_module(module, &VerifierConfig::for_level(VerificationLevel::Fast));
    assert!(report.is_ok(), "module failed verification: {report:?}");
}

#[test]
fn inliner_rewrites_wrappers_that_reorder_differently_typed_args() {
    let source = r#"
target = "evm-ethereum-osaka"

func private %leaf(v0.*i8, v1.i256) {
    block0:
        mstore v0 v1 i256;
        return;
}

func private %wrapper(v0.i256, v1.*i8) {
    block0:
        call %leaf v1 v0;
        return;
}

func public %caller(v0.i256, v1.*i8) {
    block0:
        call %wrapper v0 v1;
        return;
}
"#;

    let mut parsed = sonatina_parser::parse_module(source)
        .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"));
    let module = &mut parsed.module;

    let mut inliner = Inliner::new(InlinerConfig {
        enable_single_block_splice: false,
        ..Default::default()
    });
    let stats = inliner.run(module);

    let dumped = dump_module(module);
    assert!(
        !dumped.contains("call %wrapper"),
        "wrapper call should be rewritten:\n{dumped}"
    );
    assert!(
        dumped.contains("call %leaf v1 v0"),
        "rewritten call should preserve reordered args:\n{dumped}"
    );
    assert!(stats.calls_rewritten >= 1, "expected rewrite:\n{dumped}");
    let report = verify_module(module, &VerifierConfig::for_level(VerificationLevel::Fast));
    assert!(report.is_ok(), "module failed verification: {report:?}");
}

#[test]
fn inliner_removes_multi_return_return_only_calls() {
    let source = r#"
target = "evm-ethereum-osaka"

func private %forward(v0.i256, v1.i1) -> (i256, i1) {
    block0:
        return (v0, v1);
}

func public %caller(v0.i256, v1.i1) -> (i256, i1) {
    block0:
        (v2.i256, v3.i1) = call %forward v0 v1;
        return (v2, v3);
}
"#;

    let mut parsed = sonatina_parser::parse_module(source)
        .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"));
    let module = &mut parsed.module;

    let mut inliner = Inliner::new(InlinerConfig::default());
    let stats = inliner.run(module);

    let dumped = dump_module(module);
    assert!(
        !dumped.contains("call %forward"),
        "return-only multi-return call should be removed:\n{dumped}"
    );
    assert!(
        dumped.contains("return (v0, v1);"),
        "call results should alias elementwise:\n{dumped}"
    );
    assert!(stats.calls_removed >= 1, "expected removal:\n{dumped}");
    let report = verify_module(module, &VerifierConfig::for_level(VerificationLevel::Fast));
    assert!(report.is_ok(), "module failed verification: {report:?}");
}

#[test]
fn full_inliner_respects_growth_budget() {
    let source = r#"
target = "evm-ethereum-london"

func private %multi(v0.i1) -> i32 {
    block0:
        br v0 block1 block2;

    block1:
        return 1.i32;

    block2:
        return 2.i32;
}

func public %caller(v0.i1) -> i32 {
    block0:
        v1.i32 = call %multi v0;
        return v1;
}
"#;

    let mut parsed = sonatina_parser::parse_module(source)
        .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"));
    let module = &mut parsed.module;

    let cfg = InlinerConfig {
        enable_full_inliner: true,
        max_growth_per_caller: 1,
        max_inlinee_blocks: 64,
        max_inlinee_insts: 256,
        inline_threshold: 1000,
        inline_threshold_cold: 1000,
        ..Default::default()
    };
    let mut inliner = Inliner::new(cfg);
    let stats = inliner.run(module);
    assert_module_verified(module);

    let dumped = dump_module(module);
    assert!(
        dumped.contains("call %multi"),
        "growth budget should keep the call:\n{dumped}"
    );
    assert!(stats.skipped_budget > 0);
}

#[test]
fn full_inliner_skips_recursive_scc_when_disabled() {
    let source = r#"
target = "evm-ethereum-london"

func private %self(v0.i1, v1.i32) -> i32 {
    block0:
        br v0 block1 block2;

    block1:
        return v1;

    block2:
        v2.i32 = call %self v0 v1;
        return v2;
}

func public %caller(v0.i1, v1.i32) -> i32 {
    block0:
        v2.i32 = call %self v0 v1;
        return v2;
}
"#;

    let mut parsed = sonatina_parser::parse_module(source)
        .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"));
    let module = &mut parsed.module;

    let mut inliner = Inliner::new(InlinerConfig {
        enable_full_inliner: true,
        max_inlinee_blocks: 64,
        max_inlinee_insts: 256,
        inline_threshold: 1000,
        inline_threshold_cold: 1000,
        ..Default::default()
    });
    let stats = inliner.run(module);
    assert_module_verified(module);

    assert!(stats.skipped_recursive_scc > 0);
}

#[test]
fn full_inliner_honors_noinline_and_alwaysinline_attrs() {
    let source = r#"
target = "evm-ethereum-london"

func private %forced(v0.i1, v1.i32) -> i32 {
    block0:
        br v0 block1 block2;

    block1:
        return v1;

    block2:
        v2.i32 = add v1 1.i32;
        return v2;
}

func private %blocked(v0.i1, v1.i32) -> i32 {
    block0:
        br v0 block1 block2;

    block1:
        return v1;

    block2:
        v2.i32 = add v1 2.i32;
        return v2;
}

func public %caller(v0.i1, v1.i32) -> i32 {
    block0:
        v2.i32 = call %forced v0 v1;
        v3.i32 = call %blocked v0 v2;
        return v3;
}
"#;

    let mut parsed = sonatina_parser::parse_module(source)
        .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"));
    let module = &mut parsed.module;

    let forced = find_func(module, "forced");
    let blocked = find_func(module, "blocked");
    module.ctx.set_func_attrs(forced, FuncAttrs::ALWAYSINLINE);
    module.ctx.set_func_attrs(blocked, FuncAttrs::NOINLINE);

    let mut inliner = Inliner::new(InlinerConfig {
        enable_full_inliner: true,
        max_inlinee_blocks: 64,
        max_inlinee_insts: 256,
        inline_threshold: -1000,
        inline_threshold_cold: -1000,
        ..Default::default()
    });
    let stats = inliner.run(module);
    assert_module_verified(module);

    let dumped = dump_module(module);
    assert!(
        !dumped.contains("call %forced"),
        "alwaysinline call should be inlined:\n{dumped}"
    );
    assert!(
        dumped.contains("call %blocked"),
        "noinline call should remain:\n{dumped}"
    );
    assert!(stats.full_calls_inlined > 0);
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

fn assert_module_verified(module: &sonatina_ir::Module) {
    let mut cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    cfg.allow_detached_entities = true;
    let report = verify_module(module, &cfg);
    assert!(!report.has_errors(), "{report}");
}

fn full_inliner_test_config() -> InlinerConfig {
    InlinerConfig {
        enable_full_inliner: true,
        max_inlinee_blocks: 64,
        max_inlinee_insts: 1024,
        max_growth_per_caller: 4096,
        max_total_growth: 1 << 20,
        inline_threshold: 1000,
        inline_threshold_cold: 1000,
        ..Default::default()
    }
}

fn find_func(module: &sonatina_ir::Module, name: &str) -> sonatina_ir::module::FuncRef {
    module
        .funcs()
        .into_iter()
        .find(|func_ref| module.ctx.func_sig(*func_ref, |sig| sig.name() == name))
        .unwrap_or_else(|| panic!("function %{name} not found"))
}
