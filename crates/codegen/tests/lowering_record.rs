//! The lowering record (`EvmCompile::with_lowering_record`): recording it
//! changes no byte, and what it says agrees with the bytes and with itself.

use dir_test::{Fixture, dir_test};
use sonatina_codegen::{
    EvmCompile, OptLevel,
    isa::evm::opcode::OpCode,
    object::{
        ObjectArtifact, encode_gv_initializer_to_bytes,
        lowering::{
            CodeLabel, CodePoint, FuncLowering, SectionLowering, SpillLocation, StableLowering,
            StackSlot,
        },
    },
};
use sonatina_ir::BlockId;
use sonatina_parser::parse_module;
use std::collections::{BTreeMap, BTreeSet};

fn try_compile(source: &str, opt: OptLevel, record: bool) -> Option<Vec<ObjectArtifact>> {
    EvmCompile::new(parse_module(source).expect("fixture parses").module)
        .with_opt_level(opt)
        .with_lowering_record(record)
        .compile()
        .ok()
}

fn compile(source: &str, opt: OptLevel, record: bool) -> Vec<ObjectArtifact> {
    try_compile(source, opt, record).expect("fixture compiles")
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
    check_spill_accesses(lowering, bytes, &starts);
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

/// The block of `func` a point is in.
fn point_block(func: &FuncLowering, point: CodePoint) -> BlockId {
    match point {
        CodePoint::Entry => func.blocks[0].block,
        CodePoint::Before { block, .. }
        | CodePoint::After { block, .. }
        | CodePoint::Case { block, .. } => block,
    }
}

/// The constant addresses each block of each function of the machine IR
/// stores to with `evm_mstore` (`true`) and loads from with `evm_mload`, from
/// its text.
fn machine_ir_accesses(machine_ir: &str) -> BTreeMap<(String, u32, bool), Vec<u32>> {
    let mut accesses: BTreeMap<_, Vec<u32>> = BTreeMap::new();
    let (mut func, mut block) = (String::new(), 0);
    for line in machine_ir.lines().map(str::trim) {
        if let Some(rest) = line.split_once('%') {
            if line.starts_with("func ") {
                func = rest.1.split('(').next().unwrap().to_string();
            }
        } else if let Some(n) = line.strip_prefix("block").and_then(|l| l.strip_suffix(':')) {
            block = n.parse().unwrap();
        } else if let Some((store, operands)) = line
            .strip_prefix("evm_mstore ")
            .map(|operands| (true, operands))
            .or_else(|| {
                line.split_once("= evm_mload ")
                    .map(|(_, operands)| (false, operands))
            })
            && let Some((addr, _)) = operands.split_once(".i256")
            && let Ok(addr) = addr.parse()
        {
            accesses
                .entry((func.clone(), block, store))
                .or_default()
                .push(addr);
        }
    }
    accesses
}

/// The recorded stores and reloads of memory spills are the code's: in each
/// block, every `PUSH w; MSTORE` (`PUSH w; MLOAD`) of a spill word `w` of the
/// function is a store (reload) the record lists there or a store (load) of
/// the machine IR at `w`, and every one listed is in the code. Sections whose
/// code the late merges moved, and functions whose code saves words around
/// calls or addresses a dynamic frame, access spill words in other ways and
/// are left out. Returns the number of stores and reloads checked.
fn check_spill_accesses(lowering: &SectionLowering, bytes: &[u8], starts: &BTreeSet<u32>) -> usize {
    if !lowering.units.is_empty() || !lowering.redirects.is_empty() {
        return 0;
    }
    let mut checked = 0;
    let mut block_starts: BTreeSet<u32> = lowering
        .funcs
        .iter()
        .flat_map(|func| {
            func.offset
                .into_iter()
                .chain(func.blocks.iter().filter_map(|b| b.offset))
        })
        .collect();
    block_starts.insert(lowering.code_size);
    let ir_accesses = machine_ir_accesses(&lowering.machine_ir);
    for func in &lowering.funcs {
        if func.offset.is_none()
            || !func.frame.call_preserves.is_empty()
            || func.frame.lazy_frame
            || func.frame.stable == StableLowering::DynamicFrame
        {
            continue;
        }
        let mut recorded: BTreeMap<(BlockId, u32, bool), usize> = BTreeMap::new();
        let mut words = BTreeSet::new();
        for spill in &func.spills {
            let SpillLocation::Memory(word) = spill.location else {
                continue;
            };
            words.insert(word);
            for (points, store) in [(&spill.stores, true), (&spill.reloads, false)] {
                for &point in points {
                    *recorded
                        .entry((point_block(func, point), word, store))
                        .or_default() += 1;
                }
            }
        }
        for block in &func.blocks {
            let Some(start) = block.offset else {
                assert!(
                    !recorded.keys().any(|(b, ..)| *b == block.block),
                    "{}: block{} has spill stores or reloads but no code",
                    func.name,
                    block.block.0
                );
                continue;
            };
            let end = *block_starts.range(start + 1..).next().unwrap();
            let mut found: BTreeMap<(u32, bool), usize> = BTreeMap::new();
            for pc in starts.range(start..end) {
                let (pc, op) = (*pc as usize, bytes[*pc as usize]);
                let width = match op {
                    op if op == OpCode::PUSH0 as u8 => 0,
                    op if (OpCode::PUSH1 as u8..=OpCode::PUSH4 as u8).contains(&op) => {
                        usize::from(op - OpCode::PUSH1 as u8 + 1)
                    }
                    _ => continue,
                };
                let word = bytes[pc + 1..=pc + width]
                    .iter()
                    .fold(0u32, |word, &byte| word << 8 | u32::from(byte));
                let store = match bytes.get(pc + 1 + width) {
                    Some(&op) if op == OpCode::MSTORE as u8 => true,
                    Some(&op) if op == OpCode::MLOAD as u8 => false,
                    _ => continue,
                };
                if words.contains(&word) {
                    *found.entry((word, store)).or_default() += 1;
                }
            }
            for &word in &words {
                for store in [true, false] {
                    let listed = recorded
                        .get(&(block.block, word, store))
                        .copied()
                        .unwrap_or(0);
                    let code = found.get(&(word, store)).copied().unwrap_or(0);
                    let ir = ir_accesses
                        .get(&(func.name.clone(), block.block.0, store))
                        .map_or(0, |ir| ir.iter().filter(|&&addr| addr == word).count());
                    checked += listed;
                    assert!(
                        listed <= code && code <= listed + ir,
                        "{}: block{} {} word {word} {code} times, with {listed} recorded and \
                         {ir} of the machine IR",
                        func.name,
                        block.block.0,
                        if store { "stores" } else { "loads" }
                    );
                }
            }
        }
    }
    checked
}

/// Compiles `source` at each of `levels` with and without the record: the
/// bytes are the same, and the record agrees with them.
fn check_fixture(source: &str, levels: &[OptLevel]) {
    for &opt in levels {
        let Some(plain) = try_compile(source, opt, false) else {
            assert!(try_compile(source, opt, true).is_none());
            continue;
        };
        let recorded = compile(source, opt, true);
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

#[dir_test(dir: "$CARGO_MANIFEST_DIR/tests/fixtures", glob: "*.sntn")]
fn lowering_record_is_metadata_and_agrees_with_bytes(fixture: Fixture<&str>) {
    if fixture.content().contains("\nobject ") {
        check_fixture(
            fixture.content(),
            &[OptLevel::O0, OptLevel::O1, OptLevel::Os],
        );
    }
}

/// The EVM fixtures, at O0: late merges, which leave spills out of
/// `check_spill_accesses`, are off.
#[dir_test(dir: "$CARGO_MANIFEST_DIR/test_files/evm", glob: "*.sntn")]
fn lowering_record_of_evm_fixtures_agrees_with_bytes(fixture: Fixture<&str>) {
    if fixture.content().contains("\nobject ") {
        check_fixture(fixture.content(), &[OptLevel::O0]);
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

/// The stores and reloads of each spill of the function `name` of the
/// fixture `file` compiled at O0, as `(value, location, stores, reloads)`.
fn spill_points(file: &str, name: &str) -> Vec<String> {
    let path = format!("{}/test_files/evm/{file}", env!("CARGO_MANIFEST_DIR"));
    let source = std::fs::read_to_string(path).expect("fixture reads");
    let artifacts = compile(&source, OptLevel::O0, true);
    let section = artifacts[0].sections.values().next().expect("a section");
    let lowering = section.lowering.as_ref().expect("a lowering record");
    let starts = instruction_starts(&section.bytes, lowering.code_size as usize);
    assert!(
        check_spill_accesses(lowering, &section.bytes, &starts) > 0,
        "the stores and reloads are checked against the bytes"
    );
    let func = lowering
        .funcs
        .iter()
        .find(|func| func.name == name)
        .expect("the function is recorded");
    let point = |point: &CodePoint| match *point {
        CodePoint::Entry => "entry".to_string(),
        CodePoint::Before { block, index } => format!("before block{}:{index}", block.0),
        CodePoint::After { block, index } => format!("after block{}:{index}", block.0),
        CodePoint::Case { block, index, case } => {
            format!("case {case} of block{}:{index}", block.0)
        }
    };
    let points = |points: &[CodePoint]| points.iter().map(point).collect::<Vec<_>>().join(", ");
    func.spills
        .iter()
        .map(|spill| {
            format!(
                "v{} {:?} stores [{}] reloads [{}]",
                spill.value.as_u32(),
                spill.location,
                points(&spill.stores),
                points(&spill.reloads)
            )
        })
        .collect()
}

/// At O0 `%spill` keeps its arguments `v1` to `v7` in memory across the
/// calls of its loop: each is stored at entry and reloaded for the first call
/// (`block2:1`, after the phi), and `v7` again for the `add` at `block2:4`.
#[test]
fn lowering_record_lists_argument_stores_and_reloads() {
    let word = |value: u32| {
        let reloads = if value == 7 {
            "before block2:1, before block2:4"
        } else {
            "before block2:1"
        };
        format!(
            "v{value} Memory({}) stores [entry] reloads [{reloads}]",
            32 * (value - 1)
        )
    };
    assert_eq!(
        spill_points("spill.sntn", "spill"),
        (1..=7).map(word).collect::<Vec<_>>()
    );
}

/// At O0 `%rotate`'s twenty rotating phis are stored on the edge from
/// `block0` and on the backedge from `block2`, before each block's `jump`,
/// and reloaded on the backedge for the rotation. The counter's increment
/// `v24` is not spilled: the backedge takes it from the stack, and only
/// reloaded values are stored.
#[test]
fn lowering_record_lists_phi_edge_stores_and_reloads() {
    let spills = spill_points("spilled_phi_edge_rotation.sntn", "rotate");
    for expected in [
        "v0 Memory(0) stores [entry] reloads [before block1:21]",
        "v1 Memory(32) stores [before block0:0, before block2:1] reloads [before block2:1]",
        "v20 Memory(640) stores [before block0:0, before block2:1] \
         reloads [before block2:1, before block3:0]",
        "v21 Memory(672) stores [before block0:0, before block2:1] \
         reloads [before block1:21, before block2:0]",
    ] {
        assert!(
            spills.iter().any(|spill| spill == expected),
            "{expected} in {spills:#?}"
        );
    }
    assert_eq!(spills.len(), 22, "{spills:#?}");
}
