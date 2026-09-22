use sonatina_codegen::{
    analysis::func_behavior,
    optim::{
        dead_func::{DeadFuncElimConfig, collect_object_roots, run_dead_func_elim},
        inliner::{Inliner, InlinerConfig},
    },
};
use sonatina_ir::{Module, ir_writer::ModuleWriter};
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

const SOURCE: &str = r#"
target = "evm-ethereum-london"

func private %helper(v0.i1, v1.i256) -> i256 {
    block0:
        br v0 block1 block2;
    block1:
        return v1;
    block2:
        v2.i256 = add v1 7.i256;
        return v2;
}

func public %caller(v0.i1, v1.i256) -> i256 {
    block0:
        v2.i256 = call %helper v0 v1;
        return v2;
}
"#;

fn config() -> InlinerConfig {
    InlinerConfig {
        enable_noop: false,
        enable_return_alias: false,
        enable_wrapper_rewrite: false,
        enable_single_block_splice: false,
        enable_full_inliner: true,
        max_inlinee_blocks: 1,
        max_inlinee_insts: 1,
        max_growth_per_caller: 1,
        max_total_growth: 1,
        inline_threshold: -1000,
        inline_threshold_cold: -1000,
        ..InlinerConfig::default()
    }
}

fn verify(module: &Module) {
    let report = verify_module(
        module,
        &VerifierConfig {
            level: VerificationLevel::Full,
            ..VerifierConfig::default()
        },
    );
    assert!(!report.has_errors(), "{report:?}");
}

fn instruction_count(module: &Module) -> usize {
    module
        .funcs()
        .into_iter()
        .map(|func_ref| {
            module.func_store.view(func_ref, |func| {
                func.layout
                    .iter_block()
                    .map(|block| func.layout.iter_inst(block).count())
                    .sum::<usize>()
            })
        })
        .sum()
}

#[test]
fn removable_single_use_budgets_net_module_growth() {
    let mut module = sonatina_parser::parse_module(SOURCE).unwrap().module;
    func_behavior::analyze_module(&module);
    let before = instruction_count(&module);
    let stats = Inliner::new(config()).run(&mut module);
    verify(&module);
    assert_eq!(stats.full_calls_inlined, 1);

    let roots = collect_object_roots(&module);
    let eliminated = run_dead_func_elim(&mut module, &roots, DeadFuncElimConfig::default());
    assert_eq!(eliminated.removed_defs, 1);
    // The body replaces its only call; only the result-merge phi adds module size.
    assert_eq!(instruction_count(&module), before + 1);
    verify(&module);
}

#[test]
fn removal_credit_tracks_calls_eliminated_earlier_in_the_iteration() {
    let source = SOURCE.replace(
        "v2.i256 = call %helper v0 v1;",
        "v3.i256 = call %helper v0 v1;\n        v2.i256 = call %helper v0 v3;",
    );
    let mut module = sonatina_parser::parse_module(&source).unwrap().module;
    func_behavior::analyze_module(&module);
    let stats = Inliner::new(InlinerConfig {
        max_inlinee_blocks: 8,
        max_inlinee_insts: 32,
        max_growth_per_caller: 6,
        max_total_growth: 6,
        inline_threshold: 1000,
        inline_threshold_cold: 1000,
        ..config()
    })
    .run(&mut module);
    verify(&module);
    assert_eq!(stats.full_calls_inlined, 2);
    assert!(
        !ModuleWriter::new(&module)
            .dump_string()
            .contains("call %helper")
    );
}

#[test]
fn full_growth_budget_includes_split_jump_and_every_result_phi() {
    for (ret_ty, first, second, call) in [
        ("i256", "v1", "v2", "v2.i256"),
        ("(i256, i256)", "(v1, v1)", "(v2, v1)", "(v2.i256, v3.i256)"),
    ] {
        let source = format!(
            r#"
target = "evm-ethereum-london"
func public %helper(v0.i1, v1.i256) -> {ret_ty} {{
    block0:
        br v0 block1 block2;
    block1:
        return {first};
    block2:
        v2.i256 = add v1 7.i256;
        return {second};
}}
func public %caller(v0.i1, v1.i256) -> i256 {{
    block0:
        {call} = call %helper v0 v1;
        return v2;
}}
"#
        );
        let expected_growth = if ret_ty == "i256" { 5 } else { 6 };
        for budget in [expected_growth - 1, expected_growth] {
            let mut module = sonatina_parser::parse_module(&source).unwrap().module;
            func_behavior::analyze_module(&module);
            let before = instruction_count(&module);
            let stats = Inliner::new(InlinerConfig {
                max_inlinee_blocks: 8,
                max_inlinee_insts: 32,
                max_growth_per_caller: budget,
                max_total_growth: budget,
                inline_threshold: 1000,
                inline_threshold_cold: 1000,
                ..config()
            })
            .run(&mut module);
            verify(&module);
            if budget == expected_growth {
                assert_eq!(stats.full_calls_inlined, 1);
                assert_eq!(instruction_count(&module) - before, expected_growth);
            } else {
                assert_eq!(stats.full_calls_inlined, 0);
                assert_eq!(instruction_count(&module), before);
            }
        }
    }
}

#[test]
fn retained_functions_do_not_receive_removal_credit() {
    let referenced = |inst: &str| {
        SOURCE.replace(
            "v2.i256 = call %helper v0 v1;",
            &format!("{inst}\n        v2.i256 = call %helper v0 v1;"),
        )
    };
    let cases = [
        SOURCE.replacen("func private", "func public", 1),
        format!("{SOURCE}\nobject @O {{ section runtime {{ entry %caller; include %helper; }} }}"),
        format!("{SOURCE}\nobject @O {{ section runtime {{ entry %helper; }} }}"),
        referenced("v3.*(i1, i256) -> i256 = get_function_ptr %helper;"),
        referenced("v3.i256 = sym_addr %helper;"),
        referenced("v3.i256 = sym_size %helper;"),
        SOURCE.replacen("func private", "func inline(never) private", 1),
    ];
    for source in cases {
        let mut module = sonatina_parser::parse_module(&source).unwrap().module;
        verify(&module);
        func_behavior::analyze_module(&module);
        let stats = Inliner::new(config()).run(&mut module);
        verify(&module);
        assert_eq!(stats.full_calls_inlined, 0, "{source}");
    }
}

#[test]
fn removable_single_use_has_a_resulting_caller_size_limit() {
    // The original caller has two instructions; inlining adds five.
    for (limit, expected_inlines) in [(0, 0), (6, 0), (7, 1)] {
        let mut module = sonatina_parser::parse_module(SOURCE).unwrap().module;
        func_behavior::analyze_module(&module);
        let stats = Inliner::new(InlinerConfig {
            max_single_use_caller_insts: limit,
            ..config()
        })
        .run(&mut module);
        verify(&module);
        assert_eq!(stats.full_calls_inlined, expected_inlines, "limit: {limit}");
    }
}

#[test]
fn single_use_preserves_depth_and_recursion_guards() {
    let wrapper = r#"
func private %wrapper(v0.i1, v1.i256) -> i256 {
    block0:
        v2.i256 = call %helper v0 v1;
        jump block1;
    block1:
        return v2;
}
"#;
    let source = SOURCE.replace("call %helper", "call %wrapper") + wrapper;
    let mut module = sonatina_parser::parse_module(&source).unwrap().module;
    func_behavior::analyze_module(&module);
    let stats = Inliner::new(InlinerConfig {
        max_inline_depth: 1,
        ..config()
    })
    .run(&mut module);
    verify(&module);
    assert_eq!(stats.full_calls_inlined, 1);
    assert!(
        ModuleWriter::new(&module)
            .dump_string()
            .contains("call %wrapper")
    );

    let source = SOURCE.replace("v2.i256 = add v1 7.i256;", "v2.i256 = call %helper v0 v1;");
    let mut module = sonatina_parser::parse_module(&source).unwrap().module;
    func_behavior::analyze_module(&module);
    let stats = Inliner::new(config()).run(&mut module);
    verify(&module);
    assert_eq!(stats.full_calls_inlined, 0);
    assert!(stats.skipped_recursive_scc > 0);
}

#[test]
fn removable_single_use_still_budgets_result_merge_phis() {
    let source = SOURCE
        .replacen("-> i256", "-> (i256, i256)", 1)
        .replacen("return v1;", "return (v1, v1);", 1)
        .replacen("return v2;", "return (v2, v1);", 1)
        .replace("v2.i256 = call", "(v2.i256, v3.i256) = call");
    for budget in [1, 2] {
        let mut module = sonatina_parser::parse_module(&source).unwrap().module;
        func_behavior::analyze_module(&module);
        let before = instruction_count(&module);
        let stats = Inliner::new(InlinerConfig {
            max_growth_per_caller: budget,
            max_total_growth: budget,
            ..config()
        })
        .run(&mut module);
        verify(&module);
        assert_eq!(stats.full_calls_inlined, usize::from(budget == 2));
        if budget == 2 {
            run_dead_func_elim(&mut module, &[], DeadFuncElimConfig::default());
            assert_eq!(instruction_count(&module), before + 2);
        }
    }
}

#[test]
fn recursive_snapshot_targets_keep_ordinary_growth_limits() {
    let source = SOURCE.replace(
        "v2.i256 = call %helper v0 v1;\n        return v2;",
        "v2.i256 = call %helper v0 v1;\n        v3.i256 = call %caller v0 v2;\n        return v3;",
    );
    let mut module = sonatina_parser::parse_module(&source).unwrap().module;
    func_behavior::analyze_module(&module);
    let stats = Inliner::new(InlinerConfig {
        allow_inline_recursive: true,
        ..config()
    })
    .run(&mut module);
    verify(&module);
    // Cloning the caller's frozen body can recreate the call to helper, even
    // after its only live reference disappears. Do not credit removing helper.
    assert_eq!(stats.full_calls_inlined, 0);
}
