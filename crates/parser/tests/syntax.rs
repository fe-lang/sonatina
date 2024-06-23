use dir_test::{dir_test, Fixture};
use indenter::indented;
use ir::ir_writer::ModuleWriter;
use pest::{iterators::Pairs, Parser as _};
use sonatina_parser::{
    ast, parse_module,
    syntax::{Parser, Rule},
    Error,
};
use std::fmt::{self, Write};
mod common;

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/syntax/stmts",
    glob: "*.sntn"
)]
fn test_stmts(fixture: Fixture<&str>) {
    test_rule(Rule::_stmts, fixture)
}

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/syntax/func",
    glob: "*.sntn"
)]
fn test_func(fixture: Fixture<&str>) {
    test_rule(Rule::_functions, fixture)
}

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/syntax/module",
    glob: "*.sntn"
)]
fn test_module(fixture: Fixture<&str>) {
    test_rule(Rule::module, fixture)
}

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/syntax/module",
    glob: "*.sntn"
)]
fn test_module_ast(fixture: Fixture<&str>) {
    let module = ast::parse(fixture.content()).unwrap();
    snap_test!(format!("{:#?}", module), fixture.path(), Some("ast"));
}

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/syntax/module",
    glob: "*.sntn"
)]
fn test_module_ir(fixture: Fixture<&str>) {
    let module = parse_module(fixture.content()).unwrap();
    let mut w = ModuleWriter::with_debug_provider(&module.module, &module.debug);
    snap_test!(w.dump_string().unwrap(), fixture.path(), Some("ir"));
}

fn test_rule(rule: Rule, fixture: Fixture<&str>) {
    match Parser::parse(rule, fixture.content()) {
        Ok(r) => {
            let s = format!("{:?}", PairsWrapper(r));
            snap_test!(s, fixture.path());
        }
        Err(err) => {
            report_error(err, &fixture);
            panic!();
        }
    }
}

fn report_error(err: pest::error::Error<Rule>, fixture: &Fixture<&str>) {
    let s = Error::SyntaxError(err).print_to_string(fixture.path(), fixture.content(), true);
    eprintln!("{s}");
}

struct PairsWrapper<'i>(Pairs<'i, Rule>);

impl<'i> fmt::Debug for PairsWrapper<'i> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for pair in self.0.clone() {
            let rule = pair.as_rule();
            writeln!(f, "{rule:?} \"{}\"", pair.as_str(),)?;
            let pairs = pair.into_inner();
            if pairs.len() > 0 {
                write!(indented(f).with_str("  "), "{:?}", &PairsWrapper(pairs))?;
            }
        }
        Ok(())
    }
}
