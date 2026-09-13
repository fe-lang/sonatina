use std::{fs, path::Path, process::Command};

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
