//! Public-door attribution coverage for mandatory EVM preparation.
//!
//! This is intentionally a narrow regression fixture. It checks that a
//! dynamic `const.load` survives mandatory preparation with its exact stamp,
//! while other lowering output remains honestly unmapped. The marker add gives
//! the test a content-derived PC oracle instead of trusting IDs.

use sonatina_codegen::{
    EvmCompile, OptInstId, OptLevel,
    object::{PcAttribution, UnmappedReason},
};
use sonatina_ir::{
    I256, Immediate, Type,
    inst::{arith::Add, data::ConstLoad, downcast},
};
use sonatina_parser::parse_module;

const MARKER: u32 = 10_597_059;

const FIXTURE: &str = r#"
target = "evm-ethereum-osaka"

global private const [i256; 2] $values = [11, 22];

func public %runtime(v0.i256) -> i256 {
    block0:
        v1.constref<[i256; 2]> = const.ref $values;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
        v4.i256 = add v3 10597059.i256;
        mstore 0.i256 v4 i256;
        return v4;
}

object @Contract {
  section runtime {
    entry %runtime;
  }
}
"#;

fn entry_covering(
    observability: &sonatina_codegen::object::SectionObservability,
    pc: u32,
) -> &sonatina_codegen::object::PcMapEntry {
    observability
        .pc_map
        .iter()
        .find(|entry| entry.pc_start <= pc && pc < entry.pc_end)
        .expect("marker PC must be covered by the pc map")
}

fn marker_push3_positions(code: &[u8], marker: u32) -> Vec<usize> {
    let bytes = marker.to_be_bytes();
    let mut positions = Vec::new();
    let mut pc = 0;
    while pc < code.len() {
        let opcode = code[pc];
        let push_len = opcode.checked_sub(0x5f).filter(|&len| len <= 32);
        if opcode == 0x62 && code.get(pc + 1..pc + 4) == Some(&bytes[1..]) {
            positions.push(pc);
        }
        pc += 1 + push_len.unwrap_or(0) as usize;
    }
    positions
}

#[test]
fn mandatory_preparation_keeps_exact_stamps_and_marks_unstamped_output_unmapped() {
    for opt in [OptLevel::O0, OptLevel::O2, OptLevel::Os] {
        let parsed = parse_module(FIXTURE).expect("fixture parses");
        let mut compile = EvmCompile::new(parsed.module)
            .with_opt_level(opt)
            .with_observability(true);

        let func = compile.optimize().funcs()[0];
        let (const_load, marker_add) = compile.optimize().func_store.view(func, |function| {
            let mut const_load = None;
            let mut marker_add = None;
            for inst in function.dfg.inst_ids() {
                let is = function.inst_set();
                if downcast::<&ConstLoad>(is, function.dfg.inst(inst)).is_some() {
                    const_load = Some(inst);
                } else if let Some(add) = downcast::<&Add>(is, function.dfg.inst(inst)) {
                    let marker = Immediate::from_i256(I256::from(MARKER as i64), Type::I256);
                    if function.dfg.value_imm(*add.lhs()) == Some(marker)
                        || function.dfg.value_imm(*add.rhs()) == Some(marker)
                    {
                        marker_add = Some(inst);
                    }
                }
            }
            (
                const_load.expect("dynamic const.load must survive optimization"),
                marker_add.expect("marker add must survive optimization"),
            )
        });

        compile
            .stamp_post_opt_provenance(func, OptInstId(const_load), "prep:const-load")
            .unwrap_or_else(|error| panic!("opt={opt:?}: const.load stamp rejected: {error}"));
        compile
            .stamp_post_opt_provenance(func, OptInstId(marker_add), "prep:marker-add")
            .unwrap_or_else(|error| panic!("opt={opt:?}: marker add stamp rejected: {error}"));

        let artifacts = compile
            .compile()
            .unwrap_or_else(|errors| panic!("opt={opt:?}: fixture failed: {errors:?}"));
        let runtime = artifacts[0]
            .sections
            .iter()
            .find(|(name, _)| name.0.as_str() == "runtime")
            .map(|(_, section)| section)
            .expect("runtime section exists");
        let observability = runtime
            .observability
            .as_ref()
            .expect("observability enabled");

        assert_eq!(
            observability.mapped_code_bytes + observability.unmapped_code_bytes,
            observability.code_bytes,
            "opt={opt:?}: preparation must conserve emitted code bytes"
        );
        assert!(
            observability.mapped_code_bytes > 0,
            "opt={opt:?}: at least one exact stamped operation must map"
        );

        let code_bytes = observability.code_bytes as usize;
        let marker_hits = marker_push3_positions(
            runtime
                .bytes
                .get(..code_bytes)
                .expect("code bytes must be within section bytes"),
            MARKER,
        );
        assert_eq!(
            marker_hits.len(),
            1,
            "opt={opt:?}: marker PUSH3 must be unique at an instruction boundary"
        );
        let marker_entry = entry_covering(observability, marker_hits[0] as u32);
        assert!(matches!(
            &marker_entry.attribution,
            PcAttribution::Mapped { post_opt_provenance, .. }
                if post_opt_provenance == "prep:marker-add"
        ));

        assert!(observability.pc_map.iter().any(|entry| matches!(
            &entry.attribution,
            PcAttribution::Mapped { post_opt_provenance, .. }
                if post_opt_provenance == "prep:const-load"
        )));
        assert!(observability.pc_map.iter().any(|entry| matches!(
            &entry.attribution,
            PcAttribution::Unmapped {
                reason: UnmappedReason::MissingProvenance,
                ..
            }
        )));
    }
}
