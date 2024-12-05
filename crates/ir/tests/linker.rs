mod common;
use std::{
    env,
    path::{Path, PathBuf},
};

use common::parse_module;
use sonatina_ir::{ir_writer::ModuleWriter, module_linker::LinkedModule};

fn fixture_dir() -> PathBuf {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let manifest_dir = Path::new(&manifest_dir);
    manifest_dir.join("tests/linker/fixtures")
}

macro_rules! test_ok {
    ($name:ident) => {
        #[test]
        fn $name() {
            let name = stringify!($name);
            let dir = fixture_dir().join("link_ok");

            let path_a = dir.join(format!("{name}_a.sntn"));
            let path_b = dir.join(format!("{name}_b.sntn"));
            let module_a = parse_module(path_a.to_str().unwrap());
            let module_b = parse_module(path_b.to_str().unwrap());

            let (linked, _) = LinkedModule::link(vec![module_a.module, module_b.module]).unwrap();
            let mut writer = ModuleWriter::new(linked.module());
            let module_text = writer.dump_string();

            let snap_file_path = dir.join(format!("{name}.snap"));
            snap_test!(module_text, snap_file_path.to_str().unwrap());
        }
    };
}

test_ok!(module);

macro_rules! test_error {
    ($name:ident) => {
        #[test]
        fn $name() {
            let name = stringify!($name);
            let dir = fixture_dir().join("link_errors");

            let path_a = dir.join(format!("{name}_a.sntn"));
            let path_b = dir.join(format!("{name}_b.sntn"));
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
test_error!(sig_error);
