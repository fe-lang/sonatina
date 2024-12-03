mod common;
use std::{env, path::Path};

use common::parse_module;
use sonatina_codegen::module_linker::LinkedModule;

macro_rules! test_error {
    ($name:ident) => {
        #[test]
        fn $name() {
            let name = stringify!($name);
            let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
            let manifest_dir = Path::new(&manifest_dir);
            let fixture_dir = manifest_dir.join("tests/linker/fixtures/errors");
            let path_a = fixture_dir.join(format!("{name}_a.sntn"));
            let path_b = fixture_dir.join(format!("{name}_b.sntn"));

            let module_a = parse_module(path_a.to_str().unwrap());
            let module_b = parse_module(path_b.to_str().unwrap());

            let linked = LinkedModule::link(vec![module_a.module, module_b.module]);
            assert!(linked.is_err());
        }
    };
}

test_error!(struct_error);
test_error!(gv_error);
test_error!(func_error);
