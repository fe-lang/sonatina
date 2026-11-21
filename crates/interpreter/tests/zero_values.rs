//! The shared `zero.T` cases, run by the interpreter: the values the backends
//! must compute.
#[path = "../../codegen/tests/zero_values/mod.rs"]
mod zero_values;

use sonatina_interpreter::Machine;
use sonatina_ir::{Immediate, interpret::EvalValue};

#[test]
fn zero_values_interpret() {
    let source = format!(
        "target = \"evm-ethereum-osaka\"\n{}",
        zero_values::ZERO_SOURCE
    );
    let module = sonatina_parser::parse_module(&source).unwrap().module;
    // The interpreter has no enum instructions.
    let funcs: Vec<_> = zero_values::ZERO_CASES
        .iter()
        .filter(|&&(name, _)| !name.starts_with("enum_"))
        .map(|&(name, expected)| {
            let func = module
                .funcs()
                .into_iter()
                .find(|&func| module.ctx.func_sig(func, |sig| sig.name() == name))
                .unwrap();
            (name, func, expected)
        })
        .collect();
    let mut machine = Machine::new(module);
    for (name, func, expected) in funcs {
        assert_eq!(
            machine.run(func, Vec::new()),
            EvalValue::Imm(Immediate::I64(expected)),
            "{name}"
        );
    }
}
