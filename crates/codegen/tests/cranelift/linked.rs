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

#[test]
fn dead_aggregates_share_frame_slots() {
    // Sixteen 4 KiB snapshots, each dead before the next, need one slot.
    // A C probe measures the stack depth below the caller's frame.
    let triple = native_isa(host_architecture()).triple();
    let loads: String = (2..18)
        .map(|value| {
            format!("    v{value}.[i64; 512] = mload v0 [i64; 512];\n    mstore v1 v{value} [i64; 512];\n")
        })
        .collect();
    let source = format!(
        "target = \"{triple}\"\ndeclare external %probe();\nfunc public %copies(v0.*[i64; 512], v1.*[i64; 512]) {{\nblock0:\n{loads}    call %probe;\n    return;\n}}\n"
    );
    let c_source = r#"
#include <stdint.h>
#include <stdio.h>
extern void copies(int64_t *source, int64_t *destination);
static uintptr_t deepest;
void probe(void) {
    volatile char marker = 0;
    deepest = (uintptr_t)&marker;
}
int main(void) {
    static int64_t source[512], destination[512];
    for (int i = 0; i < 512; i++) source[i] = i;
    volatile char marker = 0;
    copies(source, destination);
    for (int i = 0; i < 512; i++) if (destination[i] != i) return 1;
    printf("%lu\n", (unsigned long)((uintptr_t)&marker - deepest));
    return 0;
}
"#;
    for level in [OptLevel::O0, OptLevel::O2] {
        let module = sonatina_parser::parse_module(&source).unwrap().module;
        let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(!report.has_errors(), "{report}");
        let artifact = CraneliftObjectBackend::new()
            .compile_module(&module, &BackendOptions { opt_level: level })
            .unwrap();
        let directory = Builder::new()
            .prefix("sonatina-native-frame-")
            .tempdir()
            .unwrap();
        let object = directory.path().join("copies.o");
        let harness = directory.path().join("main.c");
        let executable = directory.path().join("copies");
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
        let run = Command::new(&executable).output().unwrap();
        assert!(run.status.success(), "{level:?}: {run:?}");
        let depth: u64 = String::from_utf8_lossy(&run.stdout).trim().parse().unwrap();
        assert!(
            (4096..12 * 1024).contains(&depth),
            "{level:?}: copies used {depth} stack bytes"
        );
    }
}

#[test]
fn linked_tail_call_switches_relocate_their_tables() {
    // An interpreter whose dispatch tail-calls through a table of handler
    // addresses, which the linker relocates in an executable.
    let triple = native_isa(host_architecture()).triple();
    let source = r#"
func private %dispatch(v0.*i8, v1.i64, v2.i64) -> i64 {
block0:
    v3.i64 = ptr_to_int v0 i64;
    v4.i64 = add v3 v1;
    v5.*i8 = int_to_ptr v4 *i8;
    v6.i8 = mload v5 i8;
    v7.i32 = zext v6 i32;
    br_table v7 block4 (0.i32 block1) (1.i32 block2) (2.i32 block3);
block1:
    v8.i64 = call %halt v0 v1 v2;
    return v8;
block2:
    v9.i64 = call %inc v0 v1 v2;
    return v9;
block3:
    v10.i64 = call %double v0 v1 v2;
    return v10;
block4:
    v11.i64 = call %invalid v0 v1 v2;
    return v11;
}

func private %halt(v0.*i8, v1.i64, v2.i64) -> i64 {
block0:
    return v2;
}

func private %inc(v0.*i8, v1.i64, v2.i64) -> i64 {
block0:
    v3.i64 = add v1 1.i64;
    v4.i64 = add v2 1.i64;
    v5.i64 = call %dispatch v0 v3 v4;
    return v5;
}

func private %double(v0.*i8, v1.i64, v2.i64) -> i64 {
block0:
    v3.i64 = add v1 1.i64;
    v4.i64 = mul v2 2.i64;
    v5.i64 = call %dispatch v0 v3 v4;
    return v5;
}

func private %invalid(v0.*i8, v1.i64, v2.i64) -> i64 {
block0:
    return -1.i64;
}

func public %run(v0.*i8) -> i64 {
block0:
    v1.i64 = call %dispatch v0 0.i64 0.i64;
    return v1;
}
"#;
    let c_source = r#"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
extern int64_t run(const uint8_t *code);
int main(void) {
    size_t n = 1000000;
    uint8_t *code = malloc(n);
    if (!code) return 2;
    memset(code, 1, n);
    code[n - 2] = 2;
    code[n - 1] = 0;
    if (run(code) != (int64_t)(n - 2) * 2) return 3;
    code[n / 2] = 7;
    if (run(code) != -1) return 4;
    free(code);
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
            .prefix("sonatina-native-tail-switch-")
            .tempdir()
            .unwrap();
        let object = directory.path().join("dispatch.o");
        let harness = directory.path().join("main.c");
        let executable = directory.path().join("dispatch");
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
        let run = Command::new(&executable).output().unwrap();
        assert!(run.status.success(), "{level:?}: {run:?}");
    }
}
