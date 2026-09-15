use object::{Object, ObjectSection, ObjectSymbol, RelocationFlags, SectionKind};
#[cfg(feature = "cranelift-jit")]
use sonatina_codegen::isa::cranelift::{CraneliftError, CraneliftJitBackend};
use sonatina_codegen::{
    Compile,
    backend::{Backend, BackendOptions},
    compile::OptLevel,
    isa::cranelift::CraneliftObjectBackend,
};
use sonatina_ir::{Module, Type};
use sonatina_triple::TargetTriple;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

fn parse(source: &str) -> Module {
    let source = format!("target = \"{}\"\n{source}", TargetTriple::SP1);
    let module = sonatina_parser::parse_module(&source).unwrap().module;
    let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
    assert!(!report.has_errors(), "{report}");
    module
}

#[test]
fn emits_rv64_soft_float_elf_at_every_optimization_level() {
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::Os] {
        let source = include_str!("../test_files/cranelift/native_coverage.sntn")
            .replace("$NATIVE_TARGET", &TargetTriple::SP1.to_string());
        let module = sonatina_parser::parse_module(&source).unwrap().module;
        let artifact = Compile::new(module, CraneliftObjectBackend::new())
            .with_opt_level(level)
            .compile()
            .unwrap();
        let object = object::File::parse(artifact.as_bytes()).unwrap();
        assert_eq!(object.format(), object::BinaryFormat::Elf);
        assert_eq!(object.architecture(), object::Architecture::Riscv64);
        assert!(object.is_little_endian());
        assert_eq!(
            object.flags(),
            object::FileFlags::Elf {
                os_abi: 0,
                abi_version: 0,
                e_flags: 0
            }
        );
    }
}

#[test]
fn sp1_layout_has_64_bit_pointers_and_16_byte_wide_alignment() {
    let module = parse("func public %main() -> i32 {\nblock0:\n    return 0.i32;\n}");
    assert_eq!(module.ctx.type_layout.pointer_repl(), Type::I64);
    for (ty, size, alignment) in [
        (Type::I32, 4, 4),
        (Type::I64, 8, 8),
        (Type::I128, 16, 16),
        (Type::I256, 32, 16),
    ] {
        assert_eq!(module.ctx.size_of(ty).unwrap(), size);
        assert_eq!(module.ctx.align_of(ty).unwrap(), alignment);
    }
}

#[test]
fn explicit_traps_are_four_byte_ebreaks() {
    let artifact = CraneliftObjectBackend::new()
        .compile_module(
            &parse("func public %fail() {\nblock0:\n    unreachable;\n}"),
            &BackendOptions::default(),
        )
        .unwrap();
    let object = object::File::parse(artifact.as_bytes()).unwrap();
    let text = object
        .sections()
        .find(|section| section.kind() == SectionKind::Text)
        .unwrap();
    assert!(
        text.data()
            .unwrap()
            .as_chunks::<4>()
            .0
            .contains(&[0x73, 0, 0x10, 0])
    );
}

#[test]
fn imports_globals_and_memory_helpers_use_pc_relative_relocations() {
    let source = r#"
global external i64 $imported;
declare external %consume(*i8);
func public %main(v0.*i8, v1.i64) -> i64 {
block0:
    memzero v0 v1;
    call %consume v0;
    v2.i64 = mload $imported i64;
    return v2;
}
"#;
    let artifact = CraneliftObjectBackend::new()
        .compile_module(&parse(source), &BackendOptions::default())
        .unwrap();
    let object = object::File::parse(artifact.as_bytes()).unwrap();
    for name in ["consume", "imported", "memset"] {
        assert!(
            object
                .symbols()
                .any(|symbol| symbol.is_undefined() && symbol.name() == Ok(name)),
            "missing {name}"
        );
    }
    let mut count = 0;
    for section in object
        .sections()
        .filter(|section| section.kind() == SectionKind::Text)
    {
        for (_, relocation) in section.relocations() {
            let RelocationFlags::Elf { r_type } = relocation.flags() else {
                panic!("expected ELF relocation")
            };
            assert!(
                matches!(
                    r_type,
                    object::elf::R_RISCV_CALL_PLT
                        | object::elf::R_RISCV_PCREL_HI20
                        | object::elf::R_RISCV_PCREL_LO12_I
                ),
                "unexpected text relocation {r_type}"
            );
            count += 1;
        }
    }
    assert!(count >= 4);
}

#[cfg(feature = "cranelift-jit")]
#[test]
fn jit_rejects_sp1_without_translating_it() {
    let module = parse("func public %main() -> i32 {\nblock0:\n    return 0.i32;\n}");
    let errors = CraneliftJitBackend::new()
        .compile_module(&module, &BackendOptions::default())
        .err()
        .unwrap();
    assert!(matches!(
        errors.as_slice(),
        [CraneliftError::UnsupportedTarget(_)]
    ));
}
