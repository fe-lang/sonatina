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

#[cfg(not(feature = "sp1"))]
#[test]
fn sp1_requires_its_explicit_feature() {
    let module = return_constant_module(&Native::new(TargetTriple::SP1));
    let errors = CraneliftObjectBackend::new()
        .compile_module(&module, &BackendOptions::default())
        .unwrap_err();
    assert!(matches!(&errors[0], CraneliftError::UnsupportedTarget(_)));
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

#[test]
fn aggregate_construction_has_linear_code_size_and_executes_large_arrays() {
    for length in [64, 4096] {
        let inserts = (0..length)
            .map(|index| {
                let source = if index == 0 {
                    format!("undef.[i8; {length}]")
                } else {
                    format!("v{}", index * 2 + 1)
                };
                format!(
                    "v{}.i8 = add v1 {}.i8;\nv{}.[i8; {length}] = insert_value {source} {index}.i64 v{};\n",
                    index * 2 + 2, index % 251, index * 2 + 3, index * 2 + 2,
                )
            })
            .collect::<String>();
        let triple = native_isa(host_architecture()).triple();
        let last = length * 2 + 1;
        let source = format!(
            "target = \"{triple}\"\nfunc public %construct(v0.*[i8; {length}], v1.i8) {{\nblock0:\n{inserts}mstore v0 v{last} [i8; {length}];\nreturn;\n}}"
        );
        for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2] {
            let module = sonatina_parser::parse_module(&source).unwrap().module;
            let report =
                verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
            assert!(!report.has_errors(), "{report}");
            let artifact = Compile::new(
                module.clone_for_funcs(&module.funcs()),
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
                text_size > 0 && text_size < length * 64 + 4096,
                "{length}-byte construction at {level:?} emitted {text_size} text bytes"
            );
            #[cfg(feature = "cranelift-jit")]
            {
                let artifact = Compile::new(module, CraneliftJitBackend::new())
                    .with_opt_level(level)
                    .compile()
                    .unwrap();
                let construct: unsafe extern "C" fn(*mut u8, u8) =
                    unsafe { std::mem::transmute(artifact.function_address("construct").unwrap()) };
                for seed in [0u8, 1, 127, 255] {
                    let mut output = vec![0xa5; length as usize];
                    unsafe { construct(output.as_mut_ptr(), seed) };
                    for (index, byte) in output.into_iter().enumerate() {
                        assert_eq!(byte, seed.wrapping_add((index % 251) as u8));
                    }
                }
            }
        }
    }
}

fn text_size(bytes: &[u8]) -> u64 {
    object::File::parse(bytes)
        .unwrap()
        .sections()
        .filter(|section| section.kind() == object::SectionKind::Text)
        .map(|section| section.size())
        .sum()
}

fn imports(bytes: &[u8], name: &str) -> bool {
    object::File::parse(bytes).unwrap().symbols().any(|symbol| {
        symbol.is_undefined()
            && symbol
                .name()
                .is_ok_and(|symbol| symbol.trim_start_matches('_') == name)
    })
}

#[test]
fn large_aggregate_copies_have_constant_code_size() {
    // Snapshot loads, chain-head copies, return buffers, stores and undef
    // zero fills of every length share one bounded code size.
    for length in [8, 4096] {
        let triple = native_isa(host_architecture()).triple();
        let source = format!(
            r#"target = "{triple}"
type @Pair = {{[i64; {length}], [i64; {length}]}};
func inline(never) private %update(v0.[i64; {length}], v1.i64) -> [i64; {length}] {{
block0:
    v2.[i64; {length}] = insert_value v0 1.i64 v1;
    return v2;
}}
func public %copy(v0.*[i64; {length}], v1.*[i64; {length}], v2.*@Pair) {{
block0:
    v3.[i64; {length}] = mload v0 [i64; {length}];
    mstore v0 undef.[i64; {length}] [i64; {length}];
    v4.[i64; {length}] = call %update v3 99.i64;
    mstore v1 v4 [i64; {length}];
    v5.@Pair = insert_value undef.@Pair 0.i64 v3;
    mstore v2 v5 @Pair;
    return;
}}
"#
        );
        let module = sonatina_parser::parse_module(&source).unwrap().module;
        let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(!report.has_errors(), "{report}");
        for level in [OptLevel::O0, OptLevel::O2] {
            let artifact = Compile::new(
                module.clone_for_funcs(&module.funcs()),
                CraneliftObjectBackend::new(),
            )
            .with_opt_level(level)
            .compile()
            .unwrap();
            let bytes = artifact.as_bytes();
            let text_size = text_size(bytes);
            assert!(
                text_size > 0 && text_size < 4096,
                "[i64; {length}] copies at {level:?} emitted {text_size} text bytes"
            );
            // 64-byte arrays and 128-byte pairs stay inline; 32 KiB ones call libc.
            assert_eq!(imports(bytes, "memcpy"), length > 16, "{length} {level:?}");
            assert_eq!(imports(bytes, "memset"), length > 16, "{length} {level:?}");
            #[cfg(feature = "cranelift-jit")]
            {
                let artifact = Compile::new(
                    module.clone_for_funcs(&module.funcs()),
                    CraneliftJitBackend::new(),
                )
                .with_opt_level(level)
                .compile()
                .unwrap();
                let copy: unsafe extern "C" fn(*mut i64, *mut i64, *mut i64) =
                    unsafe { std::mem::transmute(artifact.function_address("copy").unwrap()) };
                let length = length as usize;
                let original: Vec<i64> = (0..length as i64).map(|i| i * 3 - 7).collect();
                let mut source = original.clone();
                let mut updated = vec![-1; length];
                let mut pair = vec![-1; length * 2];
                unsafe { copy(source.as_mut_ptr(), updated.as_mut_ptr(), pair.as_mut_ptr()) };
                assert!(source.iter().all(|&word| word == 0), "{level:?}");
                let mut expected = original.clone();
                expected[1] = 99;
                assert_eq!(updated, expected, "{level:?}");
                assert_eq!(pair[..length], original[..], "{level:?}");
                assert!(pair[length..].iter().all(|&word| word == 0), "{level:?}");
            }
        }
    }
}

#[test]
fn undef_insert_chains_zero_only_unwritten_bytes() {
    // A chain that writes both halves needs no zero fill, one that writes a
    // half zeroes the other, and padding is zeroed inline.
    let triple = native_isa(host_architecture()).triple();
    let cases = [
        (
            "v3.@T = insert_value undef.@T 0.i64 v2;\n    v4.@T = insert_value v3 1.i64 v2;",
            false,
        ),
        ("v4.@T = insert_value undef.@T 1.i64 v2;", true),
    ];
    for (inserts, zero_fill) in cases {
        let source = format!(
            r#"target = "{triple}"
type @T = {{[i64; 32], [i64; 32]}};
type @Padded = {{i8, [i64; 32]}};
func public %build(v0.*[i64; 32], v1.*@T) {{
block0:
    v2.[i64; 32] = mload v0 [i64; 32];
    {inserts}
    mstore v1 v4 @T;
    return;
}}
func public %pad(v0.*[i64; 32], v1.i8, v2.*@Padded) {{
block0:
    v3.[i64; 32] = mload v0 [i64; 32];
    v4.@Padded = insert_value undef.@Padded 1.i64 v3;
    v5.@Padded = insert_value v4 0.i64 v1;
    mstore v2 v5 @Padded;
    return;
}}
"#
        );
        let module = sonatina_parser::parse_module(&source).unwrap().module;
        let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(!report.has_errors(), "{report}");
        let artifact = CraneliftObjectBackend::new()
            .compile_module(
                &module,
                &BackendOptions {
                    opt_level: OptLevel::O2,
                },
            )
            .unwrap();
        assert_eq!(
            imports(artifact.as_bytes(), "memset"),
            zero_fill,
            "{inserts}"
        );
        #[cfg(feature = "cranelift-jit")]
        {
            let artifact = CraneliftJitBackend::new()
                .compile_module(
                    &module,
                    &BackendOptions {
                        opt_level: OptLevel::O2,
                    },
                )
                .unwrap();
            let build: unsafe extern "C" fn(*const i64, *mut i64) =
                unsafe { std::mem::transmute(artifact.function_address("build").unwrap()) };
            let pad: unsafe extern "C" fn(*const i64, u8, *mut u8) =
                unsafe { std::mem::transmute(artifact.function_address("pad").unwrap()) };
            let input: Vec<i64> = (1..=32).collect();
            let mut output = vec![-1; 64];
            unsafe { build(input.as_ptr(), output.as_mut_ptr()) };
            let first: &[i64] = if zero_fill { &[0; 32] } else { &input };
            assert_eq!(output[..32], first[..], "{inserts}");
            assert_eq!(output[32..], input[..], "{inserts}");
            let mut padded = vec![0xa5u8; 8 + 256];
            unsafe { pad(input.as_ptr(), 7, padded.as_mut_ptr()) };
            assert_eq!(padded[..8], [7, 0, 0, 0, 0, 0, 0, 0]);
            assert_eq!(padded[8..16], 1i64.to_le_bytes());
        }
    }
}

/// The number of relocations in text sections that refer to symbol `name`.
fn references(bytes: &[u8], name: &str) -> usize {
    let object = object::File::parse(bytes).unwrap();
    object
        .sections()
        .filter(|section| section.kind() == object::SectionKind::Text)
        .flat_map(|section| section.relocations())
        .filter(|(_, relocation)| match relocation.target() {
            object::RelocationTarget::Symbol(index) => object
                .symbol_by_index(index)
                .and_then(|symbol| symbol.name())
                .is_ok_and(|symbol| symbol.trim_start_matches('_') == name),
            _ => false,
        })
        .count()
}

#[test]
fn aggregates_skip_temporary_copies() {
    // Each case's only memcpy calls are the copies its result needs: paths
    // build results in the return buffer, and a single-use load copies
    // straight from memory into its consumer.
    let cases = [
        (
            "func private %pair(v0.i1, v1.[i64; 32], v2.[i64; 32]) -> @Pair {
block0:
    br v0 block1 block2;
block1:
    v3.@Pair = insert_value undef.@Pair 0.i64 v1;
    v4.@Pair = insert_value v3 1.i64 v2;
    return v4;
block2:
    v5.@Pair = insert_value undef.@Pair 0.i64 v2;
    v6.@Pair = insert_value v5 1.i64 v1;
    return v6;
}",
            4,
        ),
        (
            "func private %load(v0.*[i64; 32]) -> [i64; 32] {
block0:
    v1.[i64; 32] = mload v0 [i64; 32];
    return v1;
}",
            1,
        ),
        (
            "func private %wrap(v0.*[i64; 32], v1.*@Pair) {
block0:
    v2.[i64; 32] = mload v0 [i64; 32];
    v3.@Pair = insert_value undef.@Pair 1.i64 v2;
    mstore v1 v3 @Pair;
    return;
}",
            2,
        ),
        (
            "func private %update(v0.*@Pair, v1.[i64; 32]) -> @Pair {
block0:
    v2.@Pair = mload v0 @Pair;
    v3.@Pair = insert_value v2 0.i64 v1;
    return v3;
}",
            2,
        ),
    ];
    let triple = native_isa(host_architecture()).triple();
    for (function, copies) in cases {
        let source =
            format!("target = \"{triple}\"\ntype @Pair = {{[i64; 32], [i64; 32]}};\n{function}\n");
        let module = sonatina_parser::parse_module(&source).unwrap().module;
        let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(!report.has_errors(), "{report}");
        for level in [OptLevel::O0, OptLevel::O2] {
            let artifact = CraneliftObjectBackend::new()
                .compile_module(&module, &BackendOptions { opt_level: level })
                .unwrap();
            assert_eq!(
                references(artifact.as_bytes(), "memcpy"),
                copies,
                "{level:?}\n{function}"
            );
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
            Architecture::Evm | Architecture::Riscv64im => unreachable!(),
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
        Architecture::Evm | Architecture::Riscv64im => unreachable!(),
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

/// A chain of `count` public functions: each runs `ops` dependent i64
/// operations on its argument and returns the next one's result. With
/// enough instructions, Cranelift compiles the functions in parallel.
fn function_chain(count: usize, ops: usize) -> String {
    let triple = TargetTriple::new(
        host_architecture(),
        Vendor::Unknown,
        OperatingSystem::Native,
    );
    let mut source = format!("target = \"{triple}\"\n");
    for i in 0..count {
        source += &format!("func public %f{i}(v0.i64) -> i64 {{\nblock0:\n");
        for k in 0..ops {
            let op = ["add", "xor", "mul"][k % 3];
            source += &format!("    v{}.i64 = {op} v{k} {}.i64;\n", k + 1, 2 * k + 1);
        }
        let result = if i + 1 < count {
            source += &format!("    v{}.i64 = call %f{} v{ops};\n", ops + 1, i + 1);
            ops + 1
        } else {
            ops
        };
        source += &format!("    return v{result};\n}}\n");
    }
    source
}

/// What `%f0` of `function_chain(count, ops)` returns for `input`.
#[cfg(feature = "cranelift-jit")]
fn function_chain_result(count: usize, ops: usize, input: i64) -> i64 {
    (0..count).fold(input, |value, _| {
        (0..ops).fold(value, |value, k| {
            let constant = 2 * k as i64 + 1;
            match k % 3 {
                0 => value.wrapping_add(constant),
                1 => value ^ constant,
                _ => value.wrapping_mul(constant),
            }
        })
    })
}

#[test]
fn functions_compiled_in_parallel_give_deterministic_objects() {
    let source = function_chain(80, 120);
    let compile = || {
        let module = sonatina_parser::parse_module(&source).unwrap().module;
        Compile::new(module, CraneliftObjectBackend::new())
            .compile()
            .unwrap()
            .into_bytes()
    };
    let object = compile();
    assert!(text_size(&object) > 0);
    for _ in 0..3 {
        assert!(
            compile() == object,
            "parallel compilation changed the object"
        );
    }
}

#[cfg(feature = "cranelift-jit")]
#[test]
fn jit_runs_functions_compiled_in_parallel() {
    let module = sonatina_parser::parse_module(&function_chain(80, 120))
        .unwrap()
        .module;
    let artifact = Compile::new(module, CraneliftJitBackend::new())
        .compile()
        .unwrap();
    let f0: unsafe extern "C" fn(i64) -> i64 =
        unsafe { std::mem::transmute(artifact.function_address("f0").unwrap()) };
    for input in [0, 7, -3, i64::MAX] {
        assert_eq!(unsafe { f0(input) }, function_chain_result(80, 120, input));
    }
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
