#[cfg(feature = "cranelift-jit")]
use std::{hint::black_box, time::Instant};

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[path = "cranelift/linked.rs"]
mod linked;

use object::{Object, ObjectSection, ObjectSymbol};
#[cfg(feature = "cranelift-jit")]
use sonatina_codegen::isa::cranelift::CraneliftJitBackend;
use sonatina_codegen::{
    Compile,
    backend::{Backend, BackendOptions},
    compile::OptLevel,
    isa::cranelift::{CraneliftError, CraneliftObjectBackend},
};
use sonatina_ir::{
    Linkage, Signature, Type,
    builder::ModuleBuilder,
    func_cursor::InstInserter,
    inst::control_flow,
    isa::{Isa, native::Native},
    module::ModuleCtx,
};
use sonatina_triple::{Architecture, OperatingSystem, TargetTriple, Vendor};
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

fn host_architecture() -> Architecture {
    if cfg!(target_arch = "x86_64") {
        Architecture::X86_64
    } else if cfg!(target_arch = "aarch64") {
        Architecture::Aarch64
    } else {
        panic!("Cranelift tests require an x86_64 or aarch64 host")
    }
}

fn native_isa(architecture: Architecture) -> Native {
    Native::new(TargetTriple::new(
        architecture,
        Vendor::Unknown,
        OperatingSystem::Native,
    ))
}

fn return_constant_module(isa: &Native) -> sonatina_ir::Module {
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(isa));
    let function = builder
        .declare_function(Signature::new_single(
            "main",
            Linkage::Public,
            &[],
            Type::I32,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    function_builder.switch_to_block(entry);
    let value = function_builder.make_imm_value(42i32);
    function_builder.insert_inst_no_result(control_flow::Return::new_single(instructions, value));
    function_builder.seal_all();
    function_builder.finish();
    builder.build()
}

fn wide_division_module(width: usize, op: &str) -> sonatina_ir::Module {
    let triple = native_isa(host_architecture()).triple();
    let source = format!(
        r#"target = "{triple}"
func public %divide(v0.*i{width}, v1.*i{width}, v2.*i{width}) {{
block0:
    v3.i{width} = mload v0 i{width};
    v4.i{width} = mload v1 i{width};
    v5.i{width} = {op} v3 v4;
    mstore v2 v5 i{width};
    return;
}}
"#
    );
    let module = sonatina_parser::parse_module(&source).unwrap().module;
    let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
    assert!(!report.has_errors(), "{report}");
    module
}

#[test]
fn wide_division_stays_within_text_budget() {
    for width in [128, 256] {
        for op in ["udiv", "umod", "sdiv", "smod"] {
            for level in [OptLevel::O0, OptLevel::O2] {
                let artifact = Compile::new(
                    wide_division_module(width, op),
                    CraneliftObjectBackend::new(),
                )
                .with_opt_level(level)
                .compile()
                .unwrap();
                let object = object::File::parse(artifact.as_bytes()).unwrap();
                let text_size: u64 = object
                    .sections()
                    .filter(|section| section.kind() == object::SectionKind::Text)
                    .map(|section| section.size())
                    .sum();
                assert!(
                    text_size > 0 && text_size < 16 * 1024,
                    "i{width} {op} {level:?} emitted {text_size} text bytes"
                );
            }
        }
    }
}

#[cfg(feature = "cranelift-jit")]
#[test]
#[ignore = "manual release-profile compile/runtime measurement; run with --release --ignored --nocapture"]
fn wide_division_release_profile() {
    if cfg!(debug_assertions) {
        panic!("measure a release-built compiler");
    }
    for width in [128, 256] {
        for level in [OptLevel::O0, OptLevel::O2] {
            let module = wide_division_module(width, "udiv");
            let mut compile_times = Vec::new();
            let mut text_size = 0;
            for _ in 0..5 {
                let compiler = Compile::new(
                    module.clone_for_funcs(&module.funcs()),
                    CraneliftObjectBackend::new(),
                )
                .with_opt_level(level);
                let start = Instant::now();
                let artifact = compiler.compile().unwrap();
                compile_times.push(start.elapsed());
                text_size = object::File::parse(artifact.as_bytes())
                    .unwrap()
                    .sections()
                    .filter(|section| section.kind() == object::SectionKind::Text)
                    .map(|section| section.size())
                    .sum::<u64>();
            }
            compile_times.sort_unstable();
            let artifact = Compile::new(module, CraneliftJitBackend::new())
                .with_opt_level(level)
                .compile()
                .unwrap();
            let divide: unsafe extern "C" fn(*const u8, *const u8, *mut u8) =
                unsafe { std::mem::transmute(artifact.function_address("divide").unwrap()) };
            let lhs = [0xfdu8; 32];
            let mut rhs = [0u8; 32];
            rhs[0] = 7;
            let mut output = [0u8; 32];
            // A warmed, fixed-input microbenchmark isolates generated divider
            // throughput. It is not an application-level performance claim.
            unsafe { divide(lhs.as_ptr(), rhs.as_ptr(), output.as_mut_ptr()) };
            let start = Instant::now();
            for _ in 0..10_000 {
                unsafe {
                    divide(
                        black_box(lhs.as_ptr()),
                        black_box(rhs.as_ptr()),
                        output.as_mut_ptr(),
                    )
                };
                black_box(output);
            }
            eprintln!(
                "i{width} {level:?}: text={text_size} bytes, median compile={:?}, 10000 divisions={:?}",
                compile_times[2],
                start.elapsed()
            );
        }
    }
}

#[test]
fn generic_pipeline_emits_a_host_object() {
    let isa = native_isa(host_architecture());
    let artifact = Compile::new(return_constant_module(&isa), CraneliftObjectBackend::new())
        .with_opt_level(OptLevel::O2)
        .compile()
        .expect("host object compilation should succeed");
    let bytes = artifact.as_bytes();

    let object = object::File::parse(bytes).expect("artifact should be a readable object file");
    assert_eq!(
        object.architecture(),
        match host_architecture() {
            Architecture::X86_64 => object::Architecture::X86_64,
            Architecture::Aarch64 => object::Architecture::Aarch64,
            Architecture::Evm => unreachable!(),
        }
    );
    assert!(object.symbols().any(|symbol| {
        symbol
            .name()
            .is_ok_and(|name| name.trim_start_matches('_') == "main")
    }));

    if cfg!(target_os = "macos") {
        assert_eq!(object.format(), object::BinaryFormat::MachO);
        assert_macos_platform_metadata(bytes);
    } else if cfg!(target_os = "linux") {
        assert_eq!(object.format(), object::BinaryFormat::Elf);
    }
}

#[test]
fn object_backend_compiles_direct_i128_signatures_and_calls() {
    let triple = native_isa(host_architecture()).triple();
    let source = include_str!("../test_files/cranelift/i128_abi.sntn");
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
        let object = object::File::parse(artifact.as_bytes()).unwrap();
        for name in ["mix", "forward", "via_pointers"] {
            assert!(
                object.symbols().any(|symbol| !symbol.is_undefined()
                    && symbol
                        .name()
                        .is_ok_and(|s| s.trim_start_matches('_') == name)),
                "missing {name} at {level:?}"
            );
        }
    }
}

#[test]
fn object_globals_preserve_linkage_storage_and_relocations() {
    let triple = native_isa(host_architecture()).triple();
    let source = format!(
        r#"
target = "{triple}"
type @Aligned = {{i8, i128}};
global public const @Aligned $table = {{7, -1}};
global private i64 $counter = 42;
global public i256 $zero;
global external i64 $imported;
func public %read() -> i64 {{
block0:
    v0.i64 = mload $imported i64;
    v1.i64 = mload $counter i64;
    v2.i64 = add v0 v1;
    return v2;
}}
"#
    );
    for level in [OptLevel::O0, OptLevel::O2] {
        let module = sonatina_parser::parse_module(&source).unwrap().module;
        let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(!report.has_errors(), "{report}");
        let artifact = Compile::new(module, CraneliftObjectBackend::new())
            .with_opt_level(level)
            .compile()
            .unwrap();
        let object = object::File::parse(artifact.as_bytes()).unwrap();
        for (name, public, kind, alignment) in [
            ("table", true, object::SectionKind::ReadOnlyData, 16),
            ("counter", false, object::SectionKind::Data, 8),
            ("zero", true, object::SectionKind::UninitializedData, 16),
        ] {
            let symbols: Vec<_> = object
                .symbols()
                .filter(|symbol| {
                    symbol
                        .name()
                        .is_ok_and(|s| s.trim_start_matches('_') == name)
                })
                .collect();
            assert_eq!(symbols.len(), 1, "{name} must have one shared definition");
            let symbol = &symbols[0];
            assert_eq!(symbol.is_global(), public, "{name}");
            assert!(!symbol.is_undefined(), "{name}");
            let section = object
                .section_by_index(symbol.section_index().unwrap())
                .unwrap();
            assert_eq!(section.kind(), kind, "{name}");
            assert!(section.align() >= alignment, "{name}");
            assert_eq!(symbol.address() % alignment, 0, "{name}");
            if name == "table" {
                let bytes = section.data_range(symbol.address(), 32).unwrap().unwrap();
                assert_eq!(bytes[0], 7);
                assert!(bytes[1..16].iter().all(|&byte| byte == 0));
                assert!(bytes[16..32].iter().all(|&byte| byte == 255));
            }
        }
        assert!(object.symbols().any(|symbol| {
            symbol.is_undefined()
                && symbol
                    .name()
                    .is_ok_and(|name| name.trim_start_matches('_') == "imported")
        }));
        assert!(
            object
                .sections()
                .any(|section| section.relocations().next().is_some())
        );
    }
}

#[test]
fn native_backends_reject_public_and_external_object_reference_signatures() {
    let triple = native_isa(host_architecture()).triple();
    let mut sources = vec![
        r#"
func public %escape() -> objref<i64> {
block0:
    v0.objref<i64> = obj.alloc i64;
    obj.store v0 42.i64;
    return v0;
}
"#
        .to_string(),
    ];
    for ty in [
        "objref<i64>",
        "constref<i64>",
        "[objref<i64>; 2]",
        "*objref<i64>",
    ] {
        sources.push(format!("declare external %consume({ty});"));
        sources.push(format!("declare external %produce() -> {ty};"));
        sources.push(format!(
            r#"
func public %identity(v0.{ty}) -> {ty} {{
block0:
    return v0;
}}
"#
        ));
    }
    for source in sources {
        let module = sonatina_parser::parse_module(&format!("target = \"{triple}\"\n{source}"))
            .expect("reference signatures should parse")
            .module;
        let errors = CraneliftObjectBackend::new()
            .compile_module(&module, &BackendOptions::default())
            .expect_err("object backend must reject reference escape");
        assert!(errors.iter().any(|error| matches!(error,
            CraneliftError::Translation(message) if message.contains("signatures must not expose object references")
        )), "{errors:?}");
        #[cfg(feature = "cranelift-jit")]
        {
            let errors = CraneliftJitBackend::new()
                .compile_module(&module, &BackendOptions::default())
                .err()
                .expect("JIT backend must reject reference escape");
            assert!(errors.iter().any(|error| matches!(error,
                CraneliftError::Translation(message) if message.contains("signatures must not expose object references")
            )), "{errors:?}");
        }
    }
}

#[test]
fn object_backend_rejects_a_non_host_native_target() {
    let architecture = match host_architecture() {
        Architecture::X86_64 => Architecture::Aarch64,
        Architecture::Aarch64 => Architecture::X86_64,
        Architecture::Evm => unreachable!(),
    };
    let isa = native_isa(architecture);
    let errors = Compile::new(return_constant_module(&isa), CraneliftObjectBackend::new())
        .compile()
        .expect_err("cross-host native compilation must be rejected");

    assert!(matches!(
        errors.as_slice(),
        [CraneliftError::UnsupportedTarget(message)] if message.contains("does not match")
    ));
}

#[test]
fn object_backend_emits_external_import_relocations() {
    let isa = native_isa(host_architecture());
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let putchar = builder
        .declare_function(Signature::new_single(
            "putchar",
            Linkage::External,
            &[Type::I32],
            Type::I32,
        ))
        .unwrap();
    let main = builder
        .declare_function(Signature::new_single(
            "main",
            Linkage::Public,
            &[],
            Type::I32,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(main);
    let entry = function_builder.append_block();
    function_builder.switch_to_block(entry);
    let character = function_builder.make_imm_value(65i32);
    function_builder.insert_inst(
        control_flow::Call::new(instructions, putchar, smallvec::smallvec![character]),
        Type::I32,
    );
    let status = function_builder.make_imm_value(0i32);
    function_builder.insert_inst_no_result(control_flow::Return::new_single(instructions, status));
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftObjectBackend::new())
        .compile()
        .expect("external import should compile to an object");
    let object = object::File::parse(artifact.as_bytes()).unwrap();
    assert!(object.symbols().any(|symbol| {
        symbol.is_undefined()
            && symbol
                .name()
                .is_ok_and(|name| name.trim_start_matches('_') == "putchar")
    }));
    assert!(
        object
            .sections()
            .any(|section| section.relocations().next().is_some())
    );
}

#[test]
fn parsed_native_ir_compiles_to_an_object() {
    let triple = TargetTriple::new(
        host_architecture(),
        Vendor::Unknown,
        OperatingSystem::Native,
    );
    let source = include_str!("../test_files/cranelift/native_coverage.sntn")
        .replace("$NATIVE_TARGET", &triple.to_string());
    let parsed = sonatina_parser::parse_module(&source)
        .unwrap_or_else(|errors| panic!("native fixture should parse: {errors:?}"));
    let artifact = Compile::new(parsed.module, CraneliftObjectBackend::new())
        .compile()
        .expect("parsed native fixture should compile");
    let object = object::File::parse(artifact.as_bytes()).unwrap();
    assert!(object.symbols().any(|symbol| {
        symbol
            .name()
            .is_ok_and(|name| name.trim_start_matches('_') == "native_fixture")
    }));
}

fn assert_macos_platform_metadata(bytes: &[u8]) {
    let read_u32 = |offset: usize| {
        u32::from_le_bytes(bytes[offset..offset + 4].try_into().expect("u32 bytes"))
    };
    assert!(bytes.len() >= 32, "Mach-O header is truncated");
    assert_eq!(read_u32(0), 0xfeed_facfu32, "expected 64-bit Mach-O");

    let command_count = read_u32(16);
    let mut offset = 32usize;
    for _ in 0..command_count {
        assert!(
            offset + 8 <= bytes.len(),
            "Mach-O load command is truncated"
        );
        let command = read_u32(offset);
        let command_size = read_u32(offset + 4) as usize;
        assert!(command_size >= 8, "invalid Mach-O load command size");
        assert!(
            offset + command_size <= bytes.len(),
            "Mach-O load command exceeds the object"
        );
        if command == 0x32 {
            assert!(offset + 12 <= bytes.len(), "LC_BUILD_VERSION is truncated");
            assert_ne!(read_u32(offset + 8), 0, "Apple platform must be concrete");
            return;
        }
        offset += command_size;
    }
    panic!("Mach-O object is missing LC_BUILD_VERSION");
}
