mod common;

use dir_test::{dir_test, Fixture};
use sonatina_codegen::optim::egraph::func_to_egglog;
use sonatina_parser::ParsedModule;

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/egraph/",
    glob: "*.sntn"
    loader: common::parse_module,
)]
fn test(fixture: Fixture<ParsedModule>) {
    let parsed = fixture.content();
    let module = &parsed.module;

    let mut result = String::new();
    for func_ref in module.funcs() {
        module.func_store.view(func_ref, |func| {
            let egglog = func_to_egglog(func);
            result.push_str(&egglog);
        });
    }

    snap_test!(result, fixture.path());
}