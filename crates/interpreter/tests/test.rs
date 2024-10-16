mod common;

use common::parse_test_cases;
use dir_test::{dir_test, Fixture};
use sonatina_interpreter::Machine;
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
