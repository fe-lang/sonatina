use sonatina_parser::parse_module;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

const DECLS: &str = "target = \"x86_64-unknown-native\"
type @S = { i64, i64 };
declare external %snprintf(*i8, i64, *i8, ...) -> i32;
";

/// The error messages of `source`, after `DECLS`, at every level.
fn errors(source: &str) -> Vec<String> {
    let source = format!("{DECLS}{source}");
    let parsed = parse_module(&source).unwrap();
    let [standard, full] = [VerificationLevel::Standard, VerificationLevel::Full].map(|level| {
        verify_module(&parsed.module, &VerifierConfig::for_level(level))
            .errors()
            .map(|diagnostic| diagnostic.message.to_string())
            .collect::<Vec<_>>()
    });
    assert_eq!(standard, full, "{source}");
    full
}

fn call_with(extras: &str) -> Vec<String> {
    errors(&format!(
        "func private %f(v0.*i8, v1.objref<i64>, v2.*objref<i64>, v3.*@S) -> i32 {{
block0:
    v4.i32 = call %snprintf v0 16.i64 v0{extras};
    return v4;
}}"
    ))
}

#[test]
fn variadic_calls_pass_extra_words_and_pointers() {
    assert_eq!(call_with(""), Vec::<String>::new());
    assert_eq!(
        call_with(" 1.i32 2.i64 v0 v3 3.i32 4.i64"),
        Vec::<String>::new()
    );
}

#[test]
fn variadic_calls_take_at_least_the_fixed_arguments() {
    let errors = errors(
        "func public %f(v0.*i8) -> i32 {
block0:
    v1.i32 = call %snprintf v0 16.i64;
    return v1;
}",
    );
    assert_eq!(
        errors,
        ["call argument count does not match callee signature"]
    );
}

#[test]
fn variadic_extra_arguments_are_words_or_pointers() {
    for (extra, message) in [
        (
            "1.i8",
            "variadic call argument must be i32, i64 or a pointer",
        ),
        (
            "1.i128",
            "variadic call argument must be i32, i64 or a pointer",
        ),
        ("v1", "variadic call argument must be i32, i64 or a pointer"),
        (
            "v2",
            "variadic call argument must not point to object references",
        ),
    ] {
        assert_eq!(call_with(&format!(" {extra}")), [message], "{extra}");
    }
}

#[test]
fn variadic_signatures_are_external_with_word_or_pointer_parameters() {
    for (decl, message) in [
        (
            "declare external %g(i128, ...);",
            "a variadic function's fixed arguments must be i32, i64 or pointers",
        ),
        (
            "declare external %g(i8, ...);",
            "a variadic function's fixed arguments must be i32, i64 or pointers",
        ),
        (
            "declare external %g(@S, ...);",
            "a variadic function's fixed arguments must be i32, i64 or pointers",
        ),
    ] {
        assert_eq!(errors(decl), [message], "{decl}");
    }
    assert_eq!(
        errors("declare external %g(i32, i64, *@S, ...);"),
        Vec::<String>::new()
    );
}

#[test]
fn defined_functions_are_not_variadic() {
    let source = format!(
        "{DECLS}func public %g(v0.i32) -> i32 {{
block0:
    return v0;
}}"
    );
    let parsed = parse_module(&source).unwrap();
    let g = parsed
        .module
        .ctx
        .declared_funcs
        .iter()
        .find_map(|entry| (entry.value().name() == "g").then(|| *entry.key()))
        .unwrap();
    parsed
        .module
        .ctx
        .declared_funcs
        .get_mut(&g)
        .unwrap()
        .set_variadic(true);
    let report = verify_module(
        &parsed.module,
        &VerifierConfig::for_level(VerificationLevel::Full),
    );
    assert!(
        report
            .errors()
            .any(|diagnostic| diagnostic.message == "only an external function can be variadic"),
        "{report}"
    );
}

#[test]
fn variadic_functions_have_no_address() {
    assert_eq!(
        errors(
            "func public %f() {
block0:
    v0.*(*i8, i64, *i8) -> i32 = get_function_ptr %snprintf;
    return;
}"
        ),
        ["get_function_ptr cannot take the address of a variadic function"]
    );
    assert_eq!(
        errors(
            "func public %f() {
block0:
    v0.i64 = sym_addr %snprintf;
    return;
}"
        ),
        ["sym_addr cannot take the address of a variadic function"]
    );
}
