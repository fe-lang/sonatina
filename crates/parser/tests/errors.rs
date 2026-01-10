use std::path::Path;

use dir_test::{Fixture, dir_test};
use sonatina_parser::parse_module;
mod common;

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/errors/",
    glob: "*.sntn"
)]
fn test_errors(fixture: Fixture<&str>) {
    let Err(errs) = parse_module(fixture.content()) else {
        panic!("expected parse_module to fail with errors");
    };
    let path = Path::new(fixture.path())
        .file_name()
        .unwrap()
        .to_string_lossy();

    let mut v = vec![];
    for err in errs {
        err.print(&mut v, &path, fixture.content(), false).unwrap();
    }
    let s = String::from_utf8(v).unwrap();
    snap_test!(s, fixture.path());
}
