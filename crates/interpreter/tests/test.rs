mod common;

use common::parse_test_cases;
use dir_test::{Fixture, dir_test};
use sonatina_interpreter::Machine;
use sonatina_ir::{Immediate, interpret::EvalValue};
use sonatina_parser::ParsedModule;

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files",
    glob: "*.sntn",
    loader: common::parse_module,
)]
fn test(fixture: Fixture<ParsedModule>) {
    let parsed_module = fixture.into_content();
    let test_cases = match parse_test_cases(&parsed_module) {
        Ok(test_cases) => test_cases,
        Err(e) => panic!("{e}"),
    };

    let mut machine = Machine::new(parsed_module.module);

    let mut errors = Vec::new();
    for case in test_cases {
        if let Err(e) = case.run(&mut machine) {
            errors.push(e);
        }
    }

    if !errors.is_empty() {
        let mut s = String::new();
        let err_num = errors.len();
        for (i, err) in errors.into_iter().enumerate() {
            s.push_str(&err);
            if i != err_num - 1 {
                s.push('\n');
            }
        }
        panic!("{s}");
    }
}

#[test]
fn interpreter_executes_multi_return_calls() {
    let source = r#"
target = "evm-ethereum-london"

func private %pair_add(v0.i8, v1.i8) -> (i8, i1) {
    block0:
        (v2.i8, v3.i1) = uaddo v0 v1;
        return (v2, v3);
}

func public %caller(v0.i8, v1.i8) -> (i8, i1) {
    block0:
        (v2.i8, v3.i1) = call %pair_add v0 v1;
        return (v2, v3);
}
"#;

    let parsed = sonatina_parser::parse_module(source).expect("module should parse");
    let caller = parsed
        .module
        .ctx
        .declared_funcs
        .iter()
        .find_map(|entry| (entry.value().name() == "caller").then(|| *entry.key()))
        .expect("caller should be declared");
    let mut machine = Machine::new(parsed.module);
    let results = machine.run_results(
        caller,
        vec![
            EvalValue::Imm(Immediate::I8(-1)),
            EvalValue::Imm(Immediate::I8(1)),
        ],
    );

    assert_eq!(
        results.as_slice(),
        &[
            EvalValue::Imm(Immediate::I8(0)),
            EvalValue::Imm(Immediate::I1(true))
        ]
    );
}

#[test]
fn interpreter_single_return_calls_continue_execution() {
    let source = r#"
target = "evm-ethereum-london"

func private %add1(v0.i32) -> i32 {
    block0:
        v1.i32 = add v0 1.i32;
        return v1;
}

func public %caller(v0.i32) -> i32 {
    block0:
        v1.i32 = call %add1 v0;
        v2.i32 = mul v1 4.i32;
        return v2;
}
"#;

    let parsed = sonatina_parser::parse_module(source).expect("module should parse");
    let caller = parsed
        .module
        .ctx
        .declared_funcs
        .iter()
        .find_map(|entry| (entry.value().name() == "caller").then(|| *entry.key()))
        .expect("caller should be declared");
    let mut machine = Machine::new(parsed.module);

    assert_eq!(
        machine.run(caller, vec![EvalValue::Imm(Immediate::I32(3))]),
        EvalValue::Imm(Immediate::I32(16))
    );
}

#[test]
#[should_panic(expected = "run called on multi-return function")]
fn interpreter_run_panics_on_multi_return_function() {
    let source = r#"
target = "evm-ethereum-london"

func public %pair() -> (i8, i1) {
    block0:
        return (1.i8, 0.i1);
}
"#;

    let parsed = sonatina_parser::parse_module(source).expect("module should parse");
    let pair = parsed
        .module
        .ctx
        .declared_funcs
        .iter()
        .find_map(|entry| (entry.value().name() == "pair").then(|| *entry.key()))
        .expect("pair should be declared");
    let mut machine = Machine::new(parsed.module);
    let _ = machine.run(pair, vec![]);
}
