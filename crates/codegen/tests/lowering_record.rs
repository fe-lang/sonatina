//! The lowering record (`EvmCompile::with_lowering_record`): recording it
//! changes no byte, and what it says agrees with the bytes and with itself.

use dir_test::{Fixture, dir_test};
use sonatina_codegen::{
    EvmCompile, OptLevel,
    isa::evm::opcode::OpCode,
    object::{
        ObjectArtifact, encode_gv_initializer_to_bytes,
        lowering::{CodeLabel, SectionLowering, StackSlot},
    },
};
use sonatina_parser::parse_module;
use std::collections::BTreeSet;

fn compile(source: &str, opt: OptLevel, record: bool) -> Vec<ObjectArtifact> {
    EvmCompile::new(parse_module(source).expect("fixture parses").module)
        .with_opt_level(opt)
        .with_lowering_record(record)
        .compile()
        .expect("fixture compiles")
}

/// The offsets at which instructions start, decoding from the start of the
/// section's code.
fn instruction_starts(bytes: &[u8], code_end: usize) -> BTreeSet<u32> {
    let mut starts = BTreeSet::new();
    let mut pc = 0;
    while pc < code_end {
        starts.insert(pc as u32);
        let op = bytes[pc];
        let push = OpCode::PUSH1 as u8..=OpCode::PUSH32 as u8;
        pc += 1 + if push.contains(&op) {
            usize::from(op - OpCode::PUSH1 as u8 + 1)
        } else {
            0
        };
    }
    starts
}

fn check_record(lowering: &SectionLowering, bytes: &[u8]) {
    let source = parse_module(&lowering.source_ir)
        .expect("the source IR parses")
        .module;
    parse_module(&lowering.machine_ir).expect("the machine IR parses");

    let source_funcs: BTreeSet<_> = source
        .funcs()
        .into_iter()
        .map(|func| source.ctx.func_sig(func, |sig| format!("%{}", sig.name())))
        .collect();
    for (symbol, def) in &lowering.symbols {
        let (start, end) = (def.offset as usize, (def.offset + def.size) as usize);
        assert!(end <= bytes.len(), "{symbol} ends past the section");
        if let Some(name) = symbol.strip_prefix('$') {
            let gv = source
                .ctx
                .with_gv_store(|store| store.lookup_gv(name))
                .unwrap_or_else(|| panic!("{symbol} is not a global of the source IR"));
            let data = encode_gv_initializer_to_bytes(&source.ctx, gv).expect("data encodes");
            assert!(
                start >= lowering.code_size as usize,
                "{symbol} is in the code"
            );
            assert_eq!(bytes[start..end], data, "the bytes of {symbol}");
        } else if symbol.starts_with('%') {
            assert!(
                source_funcs.contains(symbol),
                "{symbol} is not a function of the source IR"
            );
            assert!(
                end <= lowering.code_size as usize,
                "{symbol} is past the code"
            );
        } else if symbol == "." {
            assert_eq!((start, end), (0, bytes.len()));
        }
    }

    let starts = instruction_starts(bytes, lowering.code_size as usize);
    for func in &lowering.funcs {
        for block in &func.blocks {
            if let Some(offset) = block.offset {
                assert!(
                    starts.contains(&offset),
                    "{}: block{} starts at {offset}, inside an instruction",
                    func.name,
                    block.block.0
                );
            }
        }
    }

    let blocks: BTreeSet<_> = lowering
        .funcs
        .iter()
        .flat_map(|func| {
            func.blocks
                .iter()
                .map(|block| (func.name.as_str(), block.block))
        })
        .collect();
    let funcs: BTreeSet<_> = lowering
        .funcs
        .iter()
        .map(|func| func.name.as_str())
        .collect();
    let units: BTreeSet<_> = lowering
        .units
        .iter()
        .map(|(name, ..)| name.as_str())
        .collect();
    for (old, new) in &lowering.redirects {
        for label in [old, new] {
            match label {
                CodeLabel::Block { func, block } => assert!(
                    blocks.contains(&(func.as_str(), *block)) || units.contains(func.as_str()),
                    "redirect names unknown block{} of {func}",
                    block.0
                ),
                CodeLabel::Func(func) => assert!(funcs.contains(func.as_str())),
                CodeLabel::Unit(unit) => assert!(units.contains(unit.as_str())),
                CodeLabel::Inst => {}
            }
        }
    }

    for func in &lowering.funcs {
        for (block, _) in &func.frame.call_preserves {
            assert!(
                blocks.contains(&(func.name.as_str(), *block)),
                "{}: a call preserve in unknown block{}",
                func.name,
                block.0
            );
        }
        if func.frame.dyn_sp_init_calls != 0 || func.frame.dyn_sp_entry_init.is_some() {
            assert!(
                lowering.funcs.iter().any(|f| f.frame.lazy_frame),
                "{}: initializes the dynamic stack pointer, but no function has a frame",
                func.name
            );
        }
    }
    for func in &lowering.funcs {
        let Some(entry) = func.blocks.first() else {
            continue;
        };
        let returns = entry.entry_stack.last() == Some(&StackSlot::FuncReturn);
        assert!(
            entry.entry_stack[..entry.entry_stack.len() - usize::from(returns)]
                .iter()
                .all(|slot| matches!(slot, StackSlot::Value(_) | StackSlot::Imm(_))),
            "{}: the entry stack holds only arguments above the return address",
            func.name
        );
    }
}

#[dir_test(dir: "$CARGO_MANIFEST_DIR/tests/fixtures", glob: "*.sntn")]
fn lowering_record_is_metadata_and_agrees_with_bytes(fixture: Fixture<&str>) {
    if !fixture.content().contains("\nobject ") {
        return;
    }
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::Os] {
        let plain = compile(fixture.content(), opt, false);
        let recorded = compile(fixture.content(), opt, true);
        assert_eq!(plain.len(), recorded.len());
        for (plain, recorded) in plain.iter().zip(&recorded) {
            for ((name, plain), (_, recorded)) in plain.sections.iter().zip(&recorded.sections) {
                assert_eq!(plain.bytes, recorded.bytes, "{name:?} at {opt:?}");
                assert!(plain.lowering.is_none());
                let lowering = recorded
                    .lowering
                    .as_ref()
                    .expect("a recorded compile has a lowering record");
                check_record(lowering, &recorded.bytes);
            }
        }
    }
}

/// `%runtime` reads a table at an index from calldata through `%get`. The
/// backend's pipeline specializes `%get` for the table and moves the table to
/// a word blob: a function and a global the compiled module does not have,
/// named in the record as the section's IR names them. The compiled module
/// has no function with the new function's id.
#[test]
fn lowering_record_names_symbols_of_the_section_module() {
    let source = r#"
target = "evm-ethereum-osaka"

global private const [i256; 6] $table = [5, 17, 2, 99, 1234567, 8];

func inline(never) private %get(v0.constref<[i256; 6]>, v1.i256) -> i256 {
    block0:
        v2.constref<i256> = const.index v0 v1;
        v3.i256 = const.load v2;
        return v3;
}

func public %runtime() {
    block0:
        v0.i256 = evm_calldata_load 0.i256;
        v1.constref<[i256; 6]> = const.ref $table;
        v2.i256 = call %get v1 v0;
        mstore 0.i256 v2 i256;
        evm_return 0.i256 32.i256;
}

func public %init() {
    block0:
        v0.i256 = sym_addr &runtime;
        v1.i256 = sym_size &runtime;
        evm_code_copy 0.i256 v0 v1;
        evm_return 0.i256 v1;
}

object @Table {
  section init {
    entry %init;
    embed .runtime as &runtime;
  }
  section runtime {
    entry %runtime;
  }
}
"#;
    let input = parse_module(source).expect("fixture parses").module;
    let input_symbols: BTreeSet<_> = input
        .funcs()
        .into_iter()
        .map(|func| input.ctx.func_sig(func, |sig| format!("%{}", sig.name())))
        .chain(["$table".to_string(), ".".to_string()])
        .collect();
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::Os] {
        let artifacts = compile(source, opt, true);
        for section in artifacts[0].sections.values() {
            check_record(
                section.lowering.as_ref().expect("a lowering record"),
                &section.bytes,
            );
        }
        let (_, runtime) = artifacts[0]
            .sections
            .iter()
            .find(|(name, _)| name.0.as_str() == "runtime")
            .expect("a runtime section");
        let lowering = runtime.lowering.as_ref().expect("a lowering record");
        let new: Vec<_> = lowering
            .symbols
            .iter()
            .map(|(symbol, _)| symbol.as_str())
            .filter(|symbol| !input_symbols.contains(*symbol))
            .collect();
        for prefix in ['%', '$'] {
            assert!(
                new.iter().any(|symbol| symbol.starts_with(prefix)),
                "{opt:?}: no `{prefix}` symbol of the section's own in {new:?}"
            );
        }
    }
}
