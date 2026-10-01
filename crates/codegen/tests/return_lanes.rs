use sonatina_codegen::optim::{
    dead_ret::{DeadRetElimConfig, run_dead_ret_elim},
    forwarded_ret::{ForwardedRetElimConfig, run_forwarded_ret_elim},
};
use sonatina_ir::ir_writer::ModuleWriter;
use sonatina_parser::parse_module;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module_or_panic};

#[test]
fn externally_exposed_function_pointer_signatures_keep_return_lanes() {
    let source = r#"
target = "evm-ethereum-osaka"
declare external %consume(*(i256) -> i256);
func private %identity(v0.i256) -> i256 {
block0:
    return v0;
}
func public %entry() {
block0:
    v0.*(i256) -> i256 = get_function_ptr %identity;
    call %consume v0;
    v1.i256 = call %identity 42.i256;
    return;
}
"#;
    let config = VerifierConfig::for_level(VerificationLevel::Full);
    for forwarded in [false, true] {
        let module = parse_module(source).unwrap().module;
        verify_module_or_panic(&module, &config);
        let (removed, blocked) = if forwarded {
            let stats = run_forwarded_ret_elim(&module, &[], ForwardedRetElimConfig::default());
            (stats.removed_rets, stats.blocked_higher_order_funcs)
        } else {
            let stats = run_dead_ret_elim(&module, &[], DeadRetElimConfig::default());
            (stats.removed_rets, stats.blocked_higher_order_funcs)
        };
        assert_eq!((removed, blocked), (0, 1));
        verify_module_or_panic(&module, &config);
        assert!(ModuleWriter::new(&module).dump_string().contains("-> i256"));
    }
}

#[test]
fn exposed_structural_types_keep_return_lanes_without_function_addresses() {
    for exposure in [
        "func public %entry(v0.@callback) {\nblock0:\n    return;\n}",
        "declare external %consume(@callback);",
        "func public %entry() -> @callback {\nblock0:\n    return undef.@callback;\n}",
        "global public @callback $callback = {0};",
    ] {
        let source = format!(
            r#"
target = "evm-ethereum-osaka"
type @callback = {{ *(i256) -> i256 }};
{exposure}
func private %identity(v0.i256) -> i256 {{
block0:
    return v0;
}}
"#
        );
        let config = VerifierConfig::for_level(VerificationLevel::Full);
        for forwarded in [false, true] {
            let module = parse_module(&source).unwrap().module;
            verify_module_or_panic(&module, &config);
            let before = ModuleWriter::new(&module).dump_string();
            let (removed, blocked) = if forwarded {
                let stats = run_forwarded_ret_elim(&module, &[], ForwardedRetElimConfig::default());
                (stats.removed_rets, stats.blocked_higher_order_funcs)
            } else {
                let stats = run_dead_ret_elim(&module, &[], DeadRetElimConfig::default());
                (stats.removed_rets, stats.blocked_higher_order_funcs)
            };
            assert_eq!((removed, blocked), (0, 1), "{exposure}");
            verify_module_or_panic(&module, &config);
            assert_eq!(before, ModuleWriter::new(&module).dump_string());
        }
    }
}

#[test]
fn mixed_return_lanes_keep_values_and_effectful_calls() {
    let source = r#"
target = "evm-ethereum-osaka"
func private %mixed(v0.i256, v1.i256) -> (i256, i256, i256, i256) {
block0:
    evm_sstore 0.i256 v0;
    v2.i256 = xor v0 v1;
    v3.i256 = add v0 v1;
    return (v1, v2, v3, v0);
}
func private %effects_only(v0.i256) -> i256 {
block0:
    evm_sstore 1.i256 v0;
    return v0;
}
func public %entry(v0.i256, v1.i256) -> (i256, i256, i256) {
block0:
    (v2.i256, v3.i256, v4.i256, v5.i256) = call %mixed v0 v1;
    v6.i256 = call %effects_only v0;
    return (v2, v3, v5);
}
"#;
    let module = parse_module(source).unwrap().module;
    let config = VerifierConfig::for_level(VerificationLevel::Full);
    verify_module_or_panic(&module, &config);
    let forwarded = run_forwarded_ret_elim(&module, &[], ForwardedRetElimConfig::default());
    assert_eq!(forwarded.removed_rets, 3);
    verify_module_or_panic(&module, &config);
    let dead = run_dead_ret_elim(&module, &[], DeadRetElimConfig::default());
    assert_eq!(dead.removed_rets, 1);
    verify_module_or_panic(&module, &config);
    let text = ModuleWriter::new(&module).dump_string();
    assert!(text.contains("v3.i256 = call %mixed v0 v1;"), "{text}");
    assert!(text.contains("call %effects_only v0;"), "{text}");
    assert!(text.contains("return (v1, v3, v0);"), "{text}");
}

#[test]
fn higher_order_blocked_stats_count_distinct_functions_across_rounds() {
    let source = r#"
target = "evm-ethereum-osaka"
declare external %consume(*(i256) -> i256);
func private %identity(v0.i256) -> i256 {
block0:
    return v0;
}
func private %rewritable(v0.i256, v1.i256) -> i256 {
block0:
    return v0;
}
"#;
    for forwarded in [false, true] {
        let module = parse_module(source).unwrap().module;
        let (removed, blocked) = if forwarded {
            let stats = run_forwarded_ret_elim(&module, &[], ForwardedRetElimConfig::default());
            (stats.removed_rets, stats.blocked_higher_order_funcs)
        } else {
            let stats = run_dead_ret_elim(&module, &[], DeadRetElimConfig::default());
            (stats.removed_rets, stats.blocked_higher_order_funcs)
        };
        assert_eq!((removed, blocked), (1, 1));
        verify_module_or_panic(&module, &VerifierConfig::for_level(VerificationLevel::Full));
    }
}

#[test]
fn object_directives_preserve_private_root_returns() {
    let source = r#"
target = "evm-ethereum-osaka"
func private %entry(v0.i256) -> i256 {
block0:
    return v0;
}
func private %included(v0.i256) -> i256 {
block0:
    return v0;
}
object @Contract { section runtime { entry %entry; include %included; } }
"#;
    for forwarded in [false, true] {
        let module = parse_module(source).unwrap().module;
        let before = ModuleWriter::new(&module).dump_string();
        let removed = if forwarded {
            run_forwarded_ret_elim(&module, &[], ForwardedRetElimConfig::default()).removed_rets
        } else {
            run_dead_ret_elim(&module, &[], DeadRetElimConfig::default()).removed_rets
        };
        assert_eq!(removed, 0);
        assert_eq!(before, ModuleWriter::new(&module).dump_string());
        verify_module_or_panic(&module, &VerifierConfig::for_level(VerificationLevel::Full));
    }
}
