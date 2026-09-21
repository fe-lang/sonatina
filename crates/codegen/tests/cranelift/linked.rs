use std::{fs, os::unix::process::ExitStatusExt, path::Path, process::Command};

use sonatina_codegen::{
    Compile,
    backend::{Backend, BackendOptions},
    compile::OptLevel,
    isa::cranelift::CraneliftObjectBackend,
};
use sonatina_ir::isa::Isa;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};
use tempfile::Builder;

use super::{host_architecture, native_isa};

#[test]
fn linked_c_executable_exercises_native_abi_and_shared_globals() {
    let triple = native_isa(host_architecture()).triple();
    let source = include_str!("../../test_files/cranelift/linked_abi.sntn");
    let c_source = Path::new(env!("CARGO_MANIFEST_DIR")).join("test_files/cranelift/linked_abi.c");
    for level in [OptLevel::O0, OptLevel::O2] {
        for optimize_ir in [false, true] {
            let module = sonatina_parser::parse_module(&format!("target = \"{triple}\"\n{source}"))
                .unwrap()
                .module;
            let report =
                verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
            assert!(!report.has_errors(), "{report}");
            // Test both the exact private aggregate ABI and the full pipeline,
            // which may specialize private signatures before native codegen.
            let artifact = if optimize_ir {
                Compile::new(module, CraneliftObjectBackend::new())
                    .with_opt_level(level)
                    .compile()
                    .unwrap()
            } else {
                CraneliftObjectBackend::new()
                    .compile_module(&module, &BackendOptions { opt_level: level })
                    .unwrap()
            };
            let directory = Builder::new()
                .prefix("sonatina-native-link-")
                .tempdir()
                .unwrap();
            let object = directory.path().join("native.o");
            let executable = directory.path().join("native-abi");
            fs::write(&object, artifact.as_bytes()).unwrap();
            let link = Command::new("cc")
                .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"])
                .arg(&c_source)
                .arg(&object)
                .arg("-o")
                .arg(&executable)
                .output()
                .expect("native object tests require a host C compiler (cc)");
            assert!(
                link.status.success(),
                "C link failed at {level:?} (optimize_ir={optimize_ir}):\n{}\n{}",
                String::from_utf8_lossy(&link.stdout),
                String::from_utf8_lossy(&link.stderr)
            );
            let run = Command::new(&executable)
                .output()
                .expect("linked native executable should run");
            assert!(
                run.status.success(),
                "native executable failed at {level:?} (optimize_ir={optimize_ir}): {}\n{}\n{}",
                run.status,
                String::from_utf8_lossy(&run.stdout),
                String::from_utf8_lossy(&run.stderr)
            );
        }
    }
}

#[test]
fn dynamic_allocation_handles_zero_size_and_traps_before_size_truncation() {
    let triple = native_isa(host_architecture()).triple();
    let source = r#"
func public %allocate256(v0.i64) -> *i8 {
block0:
    v1.i256 = zext v0 i256;
    v2.i256 = shl 64.i256 v1;
    v3.*i8 = mem.alloc_dynamic v2;
    return v3;
}
func public %allocate128(v0.i64) -> *i8 {
block0:
    v1.i128 = zext v0 i128;
    v2.i128 = shl 64.i128 v1;
    v3.*i8 = mem.alloc_dynamic v2;
    return v3;
}
"#;
    let c_source = r#"
#include <stdint.h>
#include <stdlib.h>
extern void *allocate256(uint64_t high);
extern void *allocate128(uint64_t high);
int main(int argc, char **argv) {
    if (argc != 2) return 2;
    if (argv[1][0] == '0') {
        void *a = allocate256(0);
        void *b = allocate128(0);
        if (!a || !b || a == b) return 3;
        free(a);
        free(b);
    } else if (argv[1][0] == '1') {
        free(allocate256(1));
    } else {
        free(allocate128(1));
    }
    return 0;
}
"#;
    for level in [OptLevel::O0, OptLevel::O2] {
        let module = sonatina_parser::parse_module(&format!("target = \"{triple}\"\n{source}"))
            .unwrap()
            .module;
        let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(!report.has_errors(), "{report}");
        let artifact = Compile::new(module, CraneliftObjectBackend::new())
            .with_opt_level(level)
            .compile()
            .unwrap();
        let directory = Builder::new()
            .prefix("sonatina-native-allocation-")
            .tempdir()
            .unwrap();
        let object = directory.path().join("allocate.o");
        let harness = directory.path().join("main.c");
        let executable = directory.path().join("allocate");
        fs::write(&object, artifact.as_bytes()).unwrap();
        fs::write(&harness, c_source).unwrap();
        let link = Command::new("cc")
            .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"])
            .arg(&harness)
            .arg(&object)
            .arg("-o")
            .arg(&executable)
            .output()
            .unwrap();
        assert!(
            link.status.success(),
            "{}",
            String::from_utf8_lossy(&link.stderr)
        );
        let zero = Command::new(&executable).arg("0").output().unwrap();
        assert!(zero.status.success(), "{level:?}: {zero:?}");
        for width in ["1", "2"] {
            let overflow = Command::new(&executable).arg(width).output().unwrap();
            assert!(
                overflow.status.signal().is_some(),
                "{level:?} {width}: {overflow:?}"
            );
        }
    }
}
