//! The lowering record (`EvmCompile::with_lowering_record`): recording it
//! changes no byte, and what it says agrees with the bytes and with itself.

use dir_test::{Fixture, dir_test};
use sonatina_codegen::{
    EvmCompile, OptLevel,
    isa::evm::opcode::OpCode,
    object::{
        ObjectArtifact,
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
    parse_module(&lowering.source_ir).expect("the source IR parses");
    parse_module(&lowering.machine_ir).expect("the machine IR parses");

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
