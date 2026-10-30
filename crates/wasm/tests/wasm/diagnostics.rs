//! Unsupported input is rejected with an error that names it.

use sonatina_codegen::{Backend, BackendOptions};
use sonatina_wasm::{WasmBackend, WasmError};

use crate::harness::{compile_valid, parse, parse_with_target};

fn compile_error(source: &str) -> WasmError {
    let module = parse(source);
    let mut errors = WasmBackend::new()
        .compile_module(&module, &BackendOptions::default())
        .expect_err("the module should be rejected");
    assert_eq!(errors.len(), 1, "{errors:?}");
    errors.remove(0)
}

fn message(source: &str) -> String {
    compile_error(source).to_string()
}

#[test]
fn i256_parameters_results_and_operations_are_named() {
    let parameter = message(
        "func public %f(v0.i256) -> i32 {
    block0:
        return 0.i32;
}",
    );
    assert!(
        parameter.contains("i256") && parameter.contains("parameter 0"),
        "{parameter}"
    );
    assert!(parameter.contains("function `f`"), "{parameter}");

    let result = message(
        "func public %g() -> i256 {
    block0:
        return 1.i256;
}",
    );
    assert!(
        result.contains("i256") && result.contains("result 0"),
        "{result}"
    );

    // The saturating forms are not translated for 256 bits.
    for (op, line) in [
        ("umulsat", "v3.i256 = umulsat v1 v1;"),
        ("saddsat", "v3.i256 = saddsat v1 v1;"),
    ] {
        let message = message(&format!(
            "func public %h(v0.i32) -> i32 {{
    block0:
        v1.i256 = zext v0 i256;
        {line}
        v5.i32 = trunc v3 i32;
        return v5;
}}"
        ));
        assert!(
            message.contains("i256") && message.contains(&format!("`{op}`")),
            "{op}: {message}"
        );
        assert!(message.contains("function `h`"), "{op}: {message}");
    }
}

#[test]
fn i128_is_rejected_like_i256() {
    let message = message(
        "func public %f(v0.i128) -> i128 {
    block0:
        return v0;
}",
    );
    assert!(message.contains("i128"), "{message}");
}

#[test]
fn unsupported_instructions_are_named() {
    let cases = [
        (
            "get_function_ptr",
            "declare external %callee(i32) -> i32;
func public %f() -> i32 {
    block0:
        v0.*(i32) -> i32 = get_function_ptr %callee;
        v1.i32 = ptr_to_int v0 i32;
        return v1;
}",
        ),
        (
            "sym_addr",
            "func public %f() -> i32 {
    block0:
        v0.i256 = sym_addr .;
        v1.i32 = trunc v0 i32;
        return v1;
}",
        ),
    ];
    for (name, source) in cases {
        let error = compile_error(source);
        let WasmError::Unsupported(text) = &error else {
            panic!("{name}: expected an unsupported error, got {error:?}");
        };
        assert!(text.contains(&format!("`{name}`")), "{name}: {text}");
        assert!(text.contains("function `f`"), "{name}: {text}");
    }
}

#[test]
fn global_variables_must_be_private() {
    for (linkage, word) in [("public", "public"), ("external", "external")] {
        let initializer = if linkage == "external" { "" } else { " = 3" };
        let message = message(&format!(
            "global {linkage} i32 $counter{initializer};
func public %f() -> i32 {{
    block0:
        return 0.i32;
}}"
        ));
        assert!(
            message.contains("global variable")
                && message.contains("counter")
                && message.contains(word),
            "{linkage}: {message}"
        );
    }
}

#[test]
fn other_targets_are_rejected() {
    let module = parse_with_target(
        "evm-ethereum-london",
        "func public %f() {
    block0:
        return;
}",
    );
    let errors = WasmBackend::new()
        .compile_module(&module, &BackendOptions::default())
        .expect_err("an EVM module is not a wasm32 module");
    assert!(
        matches!(errors.as_slice(), [WasmError::UnsupportedTarget(text)] if text.contains("evm-ethereum-london"))
    );
}

#[test]
fn malformed_input_is_an_error_not_a_panic() {
    // `call` arity and a phi type mismatch are rejected by the verifier, but
    // the backend does not depend on it having run.
    let arity = message(
        "func private %callee(v0.i32) -> i32 {
    block0:
        return v0;
}
func public %f() -> i32 {
    block0:
        v0.i32 = call %callee;
        return v0;
}",
    );
    assert!(arity.contains("arguments"), "{arity}");

    let operand_types = message(
        "func public %f(v0.i32, v1.i64) -> i32 {
    block0:
        v2.i32 = add v0 v1;
        return v2;
}",
    );
    assert!(operand_types.contains("`add`"), "{operand_types}");
}

#[test]
fn compiling_a_module_twice_gives_identical_bytes() {
    let source = "func private %inc(v0.i64) -> i64 {
    block0:
        v1.i64 = add v0 1.i64;
        return v1;
}
func public %loop_sum(v0.i64) -> i64 {
    block0:
        jump block1;
    block1:
        v1.i64 = phi (0.i64 block0) (v3 block2);
        v2.i64 = phi (0.i64 block0) (v4 block2);
        v5.i1 = lt v1 v0;
        br v5 block2 block3;
    block2:
        v3.i64 = call %inc v1;
        v4.i64 = add v2 v1;
        jump block1;
    block3:
        return v2;
}
func public %pair(v0.i32) -> (i32, i64) {
    block0:
        v1.i64 = zext v0 i64;
        return (v0, v1);
}
";
    // Separate parses of the same text, not two compilations of one module.
    let first = compile_valid(&parse(source));
    let second = compile_valid(&parse(source));
    assert_eq!(first, second);
    assert!(!first.is_empty());
}

#[test]
fn malformed_aggregate_input_is_an_error_not_a_panic() {
    let cases = [
        (
            "a struct field index that is not a constant",
            "type @P = { i32, i32 };
func public %f(v0.i32) -> i32 {
    block0:
        v1.@P = insert_value undef.@P v0 1.i32;
        v2.i32 = extract_value v1 0.i32;
        return v2;
}",
            "constant",
        ),
        (
            "an element that does not exist",
            "type @P = { i32, i32 };
func public %f() -> i32 {
    block0:
        v0.objref<@P> = obj.alloc @P;
        v1.objref<i32> = obj.proj v0 2.i32;
        v2.i32 = obj.load v1;
        return v2;
}",
            "offset",
        ),
        (
            "an element of the wrong type",
            "type @P = { i32, i64 };
func private %take(v0.@P) -> i32 {
    block0:
        v1.i32 = extract_value v0 0.i32;
        return v1;
}
func public %f(v0.i32) -> i32 {
    block0:
        v1.@P = insert_value undef.@P 1.i32 v0;
        v2.i32 = call %take v1;
        return v2;
}",
            "insert_value",
        ),
        (
            "an address of the wrong type",
            "func public %f(v0.i64) -> i32 {
    block0:
        v1.i32 = mload v0 i32;
        return v1;
}",
            "address",
        ),
        (
            "a 128-bit value read from memory",
            "func public %f(v0.*i128) -> i32 {
    block0:
        v1.i128 = mload v0 i128;
        v2.i32 = trunc v1 i32;
        return v2;
}",
            "i128",
        ),
    ];
    for (what, source, needle) in cases {
        let module = parse(source);
        let errors = WasmBackend::new()
            .compile_module(&module, &BackendOptions::default())
            .expect_err(what);
        let text = errors[0].to_string();
        assert!(text.contains(needle), "{what}: {text}");
    }
}
