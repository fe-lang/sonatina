use std::io::Write;

use once_cell::sync::Lazy;
use regex::Regex;
use sonatina_interpreter::Machine;
use sonatina_ir::{interpret::EvalValue, module::FuncRef, Immediate};
use sonatina_parser::{
    ast::{Value, ValueKind},
    syntax::{FromSyntax, Node, Parser, Rule},
    ParsedModule, PestParser,
};

pub fn parse_module(file_path: &str) -> ParsedModule {
    let content = std::fs::read_to_string(file_path).unwrap();

    match sonatina_parser::parse_module(&content) {
        Ok(r) => r,
        Err(errs) => {
            let mut v: Vec<u8> = Vec::new();
            for err in errs {
                err.print(&mut v, file_path, &content, false).unwrap();
                writeln!(&mut v).unwrap();
            }
            let err_str = String::from_utf8(v).unwrap();

            panic!("{err_str}");
        }
    }
}

pub fn parse_test_cases(module: &ParsedModule) -> Result<Vec<TestCase>, String> {
    let mut cases = Vec::new();
    for func in module.module.funcs() {
        let func_cases = parse_func_cases(module, func)?;
        cases.extend(func_cases.into_iter());
    }

    Ok(cases)
}

#[derive(Debug)]
pub struct TestCase {
    args: Vec<Immediate>,
    ret: Option<Immediate>,
    text: String,
    func: FuncRef,
}

impl TestCase {
    pub fn run(self, machine: &mut Machine) -> Result<(), String> {
        let evaluated = machine.run(
            self.func,
            self.args.iter().cloned().map(EvalValue::Imm).collect(),
        );
        machine.clear_state();

        let err_pair = match self.ret {
            Some(expected) => {
                if evaluated != EvalValue::Imm(expected) {
                    Some((EvalValue::Imm(expected), evaluated))
                } else {
                    None
                }
            }

            None => {
                if !evaluated.is_undef() {
                    Some((EvalValue::Undef, evaluated))
                } else {
                    None
                }
            }
        };

        if let Some((expected, evaluated)) = err_pair {
            let text = &self.text;
            let func = machine.funcs.get(&self.func).unwrap();
            let func_name = func.sig.name();
            let msg = format!(
                "Error in ModuleLinker:\n\
                Function: {func_name}\n\
                Description: {text}\n\
                Issue: Inconsistent declarations.\n\
                Expected: {expected}\n\
                Evaluated: {evaluated}\n"
            );
            Err(format_error(func_name, &msg))
        } else {
            Ok(())
        }
    }

    fn parse(module: &ParsedModule, func_ref: FuncRef, comment: &str) -> Result<Self, String> {
        let Some(caps) = PATTERN.captures(comment) else {
            return module.module.func_store.view(func_ref, |func| {
                let func_name = func.sig.name();
                Err(format_error(
                    func_name,
                    &format!(
                        "Parsing Error:\n\
                        Function: {func_name}\n\
                        Comment: `{comment}`\n\
                        Expected Format: `#[(args_list) -> ret]`."
                    ),
                ))
            });
        };
        let args = if !caps["args"].is_empty() {
            caps["args"]
                .split(",")
                .map(|arg| {
                    let arg = arg.trim();
                    parse_value(module, func_ref, arg)
                })
                .collect::<Result<_, _>>()?
        } else {
            vec![]
        };

        let ret = caps
            .name("ret")
            .map(|m| {
                let ret_val = m.as_str();
                parse_value(module, func_ref, ret_val)
            })
            .transpose()?;

        Ok(Self {
            args,
            ret,
            text: comment.to_string(),
            func: func_ref,
        })
    }
}

fn parse_func_cases(module: &ParsedModule, func_ref: FuncRef) -> Result<Vec<TestCase>, String> {
    module.debug.func_comments[func_ref]
        .iter()
        .map(|s| TestCase::parse(module, func_ref, s))
        .collect()
}

// TODO: Allow Compound value.
fn parse_value(module: &ParsedModule, func_ref: FuncRef, input: &str) -> Result<Immediate, String> {
    let value = match Parser::parse(Rule::value, input) {
        Ok(mut pairs) => {
            let pair = pairs.next().unwrap();
            debug_assert_eq!(pair.as_rule(), Rule::value);
            let mut node = Node::new(pair);

            Value::from_syntax(&mut node)
        }

        Err(err) => {
            let error_message = err.to_string();
            return module.module.func_store.view(func_ref, |func| {
                let func_name = func.sig.name();
                Err(format_error(func_name, &format!(
                    "Generic Error:\n\
                    Function: {func_name}\n\
                    Message: {error_message}\n\
                    Please check the module for inconsistencies."
                    ),
                ))
            });
        }
    };

    match value.kind {
        ValueKind::Immediate(imm) => Ok(imm),
        _ => Err("{imm}.{int_type} is expected".to_string()),
    }
}

static PATTERN: Lazy<Regex> = Lazy::new(|| {
    // [((args,)*) (-> ret)?]
    Regex::new(
        r"(?x)
        \[
        \((?P<args>[a-zA-Z0-9_.@*-]*(?:,\s*[a-zA-Z0-9_.@*-]+)*,?)\)
        (?:\s*->\s*(?P<ret>[a-zA-Z0-9_.@*-]+))?
        \]
    ",
    )
    .unwrap()
});

fn format_error(func_name: &str, msg: &str) -> String {
    format!("[%{func_name}]: {msg}")
}
