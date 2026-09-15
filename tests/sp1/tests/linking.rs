use object::{
    Architecture, BinaryFormat, Endianness, SymbolFlags, SymbolKind, SymbolScope,
    write::{Object, Symbol, SymbolSection},
};
use sonatina_codegen::compile::OptLevel;
use sonatina_sp1::Sp1Error;
use sonatina_sp1_integration::{compile, runtime};
use sp1_sdk::{
    Elf,
    blocking::{Prover, ProverClient, SP1Stdin},
};

#[test]
fn separate_objects_share_globals_calls_aggregates_and_references() {
    let client = ProverClient::builder().cpu().build();
    for level in [OptLevel::O0, OptLevel::O2] {
        let library = compile(
            include_str!("../../../crates/codegen/test_files/cranelift/linked_abi.sntn"),
            level,
        );
        let main = compile(include_str!("../fixtures/linked.sntn"), level);
        let elf = Elf::from(runtime().link_objects(&[&main, &library]).unwrap());
        for (branch, answer) in [(0u64, 100u64), (1, 200), (2, 300), (u64::MAX, 300)] {
            let mut stdin = SP1Stdin::new();
            stdin.write_slice(&16u64.to_le_bytes());
            stdin.write_slice(&branch.to_le_bytes());
            let (values, report) = client.execute(elf.clone(), stdin).run().unwrap();
            assert_eq!(report.exit_code, 0);
            let expected: Vec<u8> = [0u64, 17, 51, 42, 17, 0, 23, 42, 77, answer]
                .into_iter()
                .flat_map(u64::to_le_bytes)
                .collect();
            assert_eq!(values.as_slice(), expected, "{level:?}, branch {branch}");
        }
    }
}

#[test]
fn unresolved_import_is_a_link_error() {
    let source = "declare external %missing();\nfunc public %main() -> i32 {\nblock0:\n    call %missing;\n    return 0.i32;\n}";
    let error = runtime()
        .link_objects(&[&compile(source, OptLevel::O0)])
        .unwrap_err();
    assert!(matches!(
        error,
        Sp1Error::Command {
            operation: "ELF link",
            ..
        }
    ));
    assert!(error.to_string().contains("missing"));
}

#[test]
fn out_of_range_call_is_a_link_error() {
    let source = "declare external %far();\nfunc public %main() -> i32 {\nblock0:\n    call %far;\n    return 0.i32;\n}";
    let main = compile(source, OptLevel::O0);
    let mut external = Object::new(BinaryFormat::Elf, Architecture::Riscv64, Endianness::Little);
    external.add_symbol(Symbol {
        name: b"far".to_vec(),
        value: 0x1_7800_0000,
        size: 0,
        kind: SymbolKind::Text,
        scope: SymbolScope::Linkage,
        weak: false,
        section: SymbolSection::Absolute,
        flags: SymbolFlags::None,
    });
    let external = external.write().unwrap();
    let error = runtime().link_objects(&[&main, &external]).unwrap_err();
    assert!(matches!(
        error,
        Sp1Error::Command {
            operation: "ELF link",
            ..
        }
    ));
    assert!(error.to_string().contains("out of range"));
}
