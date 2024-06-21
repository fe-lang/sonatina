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
    let mut w = ModuleWriter::new(&module.module);
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
    let s = Error::SyntaxError(err).print_to_string(fixture.path(), fixture.content());
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

// xxx copied from fe test-utils
#[doc(hidden)]
pub use insta as _insta;
/// A macro to assert that a value matches a snapshot.
/// If the snapshot does not exist, it will be created in the same directory as
/// the test file.
#[macro_export]
macro_rules! snap_test {
    ($value:expr, $fixture_path: expr) => {
        snap_test!($value, $fixture_path, None)
    };

    ($value:expr, $fixture_path: expr, $suffix: expr) => {
        let mut settings = insta::Settings::new();
        let fixture_path = ::std::path::Path::new($fixture_path);
        let fixture_dir = fixture_path.parent().unwrap();
        let fixture_name = fixture_path.file_stem().unwrap().to_str().unwrap();

        settings.set_snapshot_path(fixture_dir);
        settings.set_input_file($fixture_path);
        settings.set_prepend_module_to_snapshot(false);
        let suffix: Option<&str> = $suffix;
        let name = if let Some(suffix) = suffix {
            format!("{fixture_name}.{suffix}")
        } else {
            fixture_name.into()
        };
        settings.bind(|| {
            insta::_macro_support::assert_snapshot(
                name.into(),
                &$value,
                env!("CARGO_MANIFEST_DIR"),
                fixture_name,
                module_path!(),
                file!(),
                line!(),
                stringify!($value),
            )
            .unwrap()
        })
    };
}
