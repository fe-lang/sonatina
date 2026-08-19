//! Attribution conformance: drives sonatina-codegen exactly as an external
//! frontend does (the `EvmCompile` public door only) and checks properties,
//! not anecdotes: byte conservation, no-wrong-mapping (a content oracle that
//! does not trust ids), and honest loss.
//!
//! The content oracle is the point. Both the machine-IR and optimized-IR inst
//! arenas are dense from zero, so their numeric ids collide by construction.
//! A pc range is attributed correctly only if the provenance string stamped on
//! it decodes to the optimized instruction that actually owns that range,
//! independent of any positional/id join. The three shipped "post-hoc
//! provenance" rounds all did a positional join and would fail the hard arm
//! below; so would any future reintroduction in the linker or elsewhere.

use sonatina_codegen::{
    EvmCompile, OptInstId, OptLevel,
    object::{
        ObjectArtifact, PcAttribution, PcMapEntry, PcMapUnit, SectionArtifact,
        SectionObservability, UnmappedReason,
    },
};
use sonatina_ir::{
    I256, Immediate, Type,
    inst::{arith::Add, downcast},
    module::FuncRef,
};
use sonatina_parser::parse_module;
use std::collections::{BTreeMap, HashMap, HashSet};

// 0xA1B2C3, 0xA1B2C4, 0xA1B2C5: each a genuine 3-byte constant (PUSH3), each
// used exactly once so it cannot be folded, hoisted, or deduplicated.
const MARKERS: [u32; 3] = [10_597_059, 10_597_060, 10_597_061];

// A one-to-many glue op (`le` + `zext`) precedes the marked adds. Its lowering
// carries no provenance (one-to-many glue is unmapped by design), yet the glue
// range still records the machine inst id of `le`/`zext`, whose optimized ids
// are also stamped. That is the cross-arena collision the removed post-hoc join
// mis-resolved: it keyed the optimized provenance map by that machine id and so
// would stamp the glue range with `le`/`zext`'s source. The correct pipeline
// leaves it unmapped; `exact_mapping_...` replays the join and requires the two
// to disagree. v3 is dynamic and each constant is used once, so no pass folds
// the marked adds.
const FIXTURE: &str = r#"
target = "evm-ethereum-osaka"

func public %runtime(v0.i256, v1.i256) {
    block0:
        v2.i1 = le v0 v1;
        v3.i256 = zext v2 i256;
        v4.i256 = add v3 10597059.i256;
        mstore 0.i256 v4 i256;
        v5.i256 = add v3 10597060.i256;
        mstore 32.i256 v5 i256;
        v6.i256 = add v3 10597061.i256;
        mstore 64.i256 v6 i256;
        evm_return 0.i256 96.i256;
}

object @Contract {
  section runtime {
    entry %runtime;
  }
}
"#;

// Two sections, each with two private helpers that end in byte-identical
// terminal blocks (current-section sym_addr/sym_size + mstore + evm_return).
// Under any non-Off late-cleanup profile the duplicate terminal is outlined
// into one shared section unit, minted as `PcMapUnit::Synthetic`. Distinct
// section names keep the two synthetic identities apart. Shape lifted from the
// in-crate outline test `link_section_resolves_sym_fixups_in_late_outlined_helper`
// (isa/evm/tests.rs).
const FIXTURE_B: &str = r#"
target = "evm-ethereum-osaka"

func inline(never) private %a1(v0.i1) {
block0:
    br v0 block1 block2;
block1:
    jump block3;
block2:
    evm_invalid;
block3:
    v1.i256 = sym_addr .;
    v2.i256 = sym_size .;
    mstore 0.i256 v1 i256;
    mstore 32.i256 v2 i256;
    evm_return 0.i256 64.i256;
}

func inline(never) private %b1(v0.i1) {
block0:
    br v0 block1 block2;
block1:
    jump block3;
block2:
    evm_invalid;
block3:
    v3.i256 = sym_addr .;
    v4.i256 = sym_size .;
    mstore 0.i256 v3 i256;
    mstore 32.i256 v4 i256;
    evm_return 0.i256 64.i256;
}

func public %main1(v0.i1) {
block0:
    br v0 block1 block2;
block1:
    call %a1 1.i1;
    return;
block2:
    call %b1 1.i1;
    return;
}

func inline(never) private %a2(v0.i1) {
block0:
    br v0 block1 block2;
block1:
    jump block3;
block2:
    evm_invalid;
block3:
    v1.i256 = sym_addr .;
    v2.i256 = sym_size .;
    mstore 0.i256 v1 i256;
    mstore 32.i256 v2 i256;
    evm_return 0.i256 64.i256;
}

func inline(never) private %b2(v0.i1) {
block0:
    br v0 block1 block2;
block1:
    jump block3;
block2:
    evm_invalid;
block3:
    v3.i256 = sym_addr .;
    v4.i256 = sym_size .;
    mstore 0.i256 v3 i256;
    mstore 32.i256 v4 i256;
    evm_return 0.i256 64.i256;
}

func public %main2(v0.i1) {
block0:
    br v0 block1 block2;
block1:
    call %a2 1.i1;
    return;
block2:
    call %b2 1.i1;
    return;
}

object @Contract {
  section init {
    entry %main1;
  }
  section runtime {
    entry %main2;
  }
}
"#;

// ---- helpers -------------------------------------------------------------

// A stamp encodes its own (func, optimized-inst) identity, so decoding it later
// recovers which optimized instruction a range claims to come from.
fn stamp_string(func: FuncRef, inst: OptInstId) -> String {
    format!("conformance:{}:{}", func.as_u32(), inst.raw().as_u32())
}

fn section<'a>(artifact: &'a ObjectArtifact, name: &str) -> &'a SectionArtifact {
    artifact
        .sections
        .iter()
        .find(|(n, _)| n.0.as_str() == name)
        .map(|(_, s)| s)
        .expect("section missing")
}

fn push3_needle(marker: u32) -> [u8; 4] {
    let b = marker.to_be_bytes();
    [0x62, b[1], b[2], b[3]]
}

/// Exactly one occurrence, or the fixture is invalid for the oracle.
fn unique_needle_pc(bytes: &[u8], needle: &[u8]) -> u32 {
    let hits: Vec<usize> = bytes
        .windows(needle.len())
        .enumerate()
        .filter(|(_, w)| *w == needle)
        .map(|(i, _)| i)
        .collect();
    assert_eq!(
        hits.len(),
        1,
        "marker byte pattern must be unique: {hits:?}"
    );
    hits[0] as u32
}

fn entry_covering(obs: &SectionObservability, pc: u32) -> &PcMapEntry {
    obs.pc_map
        .iter()
        .find(|e| e.pc_start <= pc && pc < e.pc_end)
        .expect("pc not covered by any pc-map entry")
}

/// The link-path byte equation (object/link.rs), observed as an outcome of the
/// public pipeline: re-derive totals from the entries, count inter-entry and
/// trailing gaps as unmapped (as the backend does), and require balance.
fn assert_conserved(obs: &SectionObservability) {
    let mut entries: Vec<&PcMapEntry> = obs.pc_map.iter().collect();
    entries.sort_by_key(|e| (e.pc_start, e.pc_end));
    let (mut mapped, mut unmapped, mut cursor) = (0u32, 0u32, 0u32);
    for e in entries {
        assert!(
            e.pc_start >= cursor,
            "overlapping pc-map entries at {}",
            e.pc_start
        );
        unmapped += e.pc_start - cursor; // inter-entry gap
        let span = e.pc_end - e.pc_start;
        match &e.attribution {
            PcAttribution::Mapped { .. } => mapped += span,
            PcAttribution::Unmapped { .. } => unmapped += span,
        }
        cursor = e.pc_end;
    }
    unmapped += obs.code_bytes.saturating_sub(cursor); // trailing gap
    assert_eq!(mapped, obs.mapped_code_bytes, "mapped byte total");
    assert_eq!(unmapped, obs.unmapped_code_bytes, "unmapped byte total");
    assert_eq!(
        mapped + unmapped,
        obs.code_bytes,
        "mapped + unmapped must equal code_bytes"
    );
}

/// The full set of optimized instructions the frontend stamps, keyed by
/// (func-as-u32, inst-as-u32). This is exactly the domain the removed post-hoc
/// join looked instructions up in, so it is what we replay the join against.
type StampedSet = HashSet<(u32, u32)>;

/// Full frontend pattern through the public door. Returns the artifacts, the
/// expected marker->stamp map (built by reading the *optimized* module: which
/// optimized add owns which marker constant, never from position), and the set
/// of every stamped optimized inst id.
fn compile_fully_stamped(
    source: &str,
    opt: OptLevel,
) -> (Vec<ObjectArtifact>, BTreeMap<u32, String>, StampedSet) {
    let parsed = parse_module(source).expect("fixture parses");
    let mut compile = EvmCompile::new(parsed.module)
        .with_opt_level(opt)
        .with_observability(true);

    // Content-derived expectations plus the full stamped-id domain.
    let mut expected: BTreeMap<u32, String> = BTreeMap::new();
    let mut stamped: StampedSet = HashSet::new();
    {
        let module = compile.optimize();
        for func in module.funcs() {
            module.func_store.view(func, |function| {
                let is = function.inst_set();
                let insts: Vec<_> = function.dfg.inst_ids().collect();
                for inst in insts {
                    stamped.insert((func.as_u32(), inst.as_u32()));
                    if let Some(add) = downcast::<&Add>(is, function.dfg.inst(inst)) {
                        for &marker in &MARKERS {
                            let imm = Immediate::from_i256(I256::from(marker as i64), Type::I256);
                            if function.dfg.value_imm(*add.rhs()) == Some(imm)
                                || function.dfg.value_imm(*add.lhs()) == Some(imm)
                            {
                                let prior =
                                    expected.insert(marker, stamp_string(func, OptInstId(inst)));
                                assert!(prior.is_none(), "marker {marker} matched twice");
                            }
                        }
                    }
                }
            });
        }
    }
    assert_eq!(
        expected.len(),
        MARKERS.len(),
        "optimizer must not destroy the marker adds"
    );

    // Full stamping through the bulk door: every live optimized inst gets a
    // stamp encoding its own id.
    compile.stamp_all_post_opt_provenance(|func, inst| Some(stamp_string(func, inst)));

    (
        compile.compile().expect("compile succeeds"),
        expected,
        stamped,
    )
}

/// Stamp every optimized inst and compile, no marker expectation (for fixtures
/// that carry no marker adds).
fn stamp_all_and_compile(source: &str, opt: OptLevel) -> Vec<ObjectArtifact> {
    let parsed = parse_module(source).expect("fixture parses");
    let mut compile = EvmCompile::new(parsed.module)
        .with_opt_level(opt)
        .with_observability(true);
    compile.stamp_all_post_opt_provenance(|func, inst| Some(stamp_string(func, inst)));
    compile.compile().expect("compile succeeds")
}

// ---- the suite -----------------------------------------------------------

/// Markers expected to lose their stamp at a given opt level, by mandatory-prep
/// pass (R1#1). Empty at this commit: every marker maps at every level. When a
/// prep change legitimately drops one, register it here with the cause, which
/// keeps the loss a reviewed diff instead of sanctioned silence.
fn expected_marker_losses(_opt: OptLevel) -> Vec<u32> {
    Vec::new()
}

#[test]
fn exact_mapping_is_content_correct_and_conserved_at_all_opt_levels() {
    for opt in [OptLevel::O0, OptLevel::O2, OptLevel::Os] {
        let (artifacts, expected, stamped) = compile_fully_stamped(FIXTURE, opt);
        let runtime = section(&artifacts[0], "runtime");
        let obs = runtime.observability.as_ref().expect("observability on");

        // Conservation (HARD): every code byte is accounted for, as a pipeline
        // outcome, with inter-entry and trailing gaps counted unmapped.
        assert_conserved(obs);

        let mut lost_markers: Vec<u32> = Vec::new();
        for &marker in &MARKERS {
            let pc = unique_needle_pc(&runtime.bytes, &push3_needle(marker));
            let entry = entry_covering(obs, pc);

            match &entry.attribution {
                // HARD arm (no-wrong-mapping content oracle): if this range is
                // mapped at all, its string must decode to the add that owns this
                // marker. This is the assertion the three shipped id-pun rounds
                // would fail, and that any reintroduced positional/id join fails.
                PcAttribution::Mapped {
                    post_opt_provenance,
                    ..
                } => {
                    assert_eq!(
                        post_opt_provenance, &expected[&marker],
                        "opt={opt:?} marker {marker:#x}: range attributed to the wrong source"
                    );
                }
                // KNOWN-LOSS arm (R1#1): mandatory prep in lowering may replace a
                // stamped add with an unstamped clone, dropping provenance. This
                // is a completeness loss only; it does NOT weaken the mapped arm.
                PcAttribution::Unmapped { reason, .. } => {
                    assert_eq!(
                        *reason,
                        UnmappedReason::MissingProvenance,
                        "marker lost with an unexpected reason"
                    );
                    lost_markers.push(marker);
                }
            }
        }

        // Completeness floor (HARD): the expected-loss register is empty, so at
        // this commit every marker maps at every opt level. A marker landing in
        // the KNOWN-LOSS arm above is a provenance-carry regression until it is
        // registered in expected_marker_losses together with the mandatory-prep
        // pass that legitimately causes it (R1#1). This turns the suite into the
        // measured R1#1 sensor rather than a sanctioned silence.
        assert_eq!(
            lost_markers,
            expected_marker_losses(opt),
            "opt={opt:?}: markers lost their stamps; if a mandatory-prep change \
             caused this legitimately, register the loss with a reason instead \
             of weakening this assert"
        );

        // Fixture validity (HARD): replay the exact join the removed
        // post-hoc-provenance code did. It keyed the optimized provenance map by
        // the machine-namespace inst id carried on each PC range (both arenas
        // count from zero, so the ids collide silently). We reconstruct that
        // lookup and require it to produce a DIFFERENT attribution than the
        // pipeline's actual result on at least one range. That divergence proves
        // the fixture exercises a real cross-arena id collision, so the content
        // oracle above is not passing vacuously; the pipeline's actual answer
        // (never the pun's) is the property under test. (Concretely: the `le`
        // glue range carries the machine id of `le`, whose optimized id is also
        // stamped, so the join would wrongly map a range the pipeline correctly
        // leaves unmapped.)
        let mut pun_would_diverge = false;
        for e in &obs.pc_map {
            let Some(func) = e.unit.function() else {
                continue;
            };
            let Some(m) = e.attribution.machine_inst() else {
                continue;
            };
            let pun_answer: Option<String> = if stamped.contains(&(func.as_u32(), m.raw().as_u32()))
            {
                Some(stamp_string(func, OptInstId(m.raw())))
            } else {
                None
            };
            let actual_answer: Option<String> =
                e.attribution.post_opt_provenance().map(str::to_string);
            if pun_answer != actual_answer {
                pun_would_diverge = true;
            }
        }
        assert!(
            pun_would_diverge,
            "opt={opt:?}: fixture does not exercise a machine/optimized id collision; \
             the removed post-hoc join would have produced the same answer, so this \
             fixture cannot distinguish the correct path from the pun"
        );

        // Honest-loss floor: even with every optimized inst stamped, unmapped
        // bytes still exist (glue lowering carries no provenance by design).
        assert!(
            obs.unmapped_code_bytes > 0,
            "opt={opt:?}: expected some unmapped glue bytes"
        );
    }
}

#[test]
fn synthetic_units_are_unique_across_sections() {
    // Late section-terminal outlining runs only under a non-Off cleanup profile.
    // Os selects Size, which outlines the byte-identical terminal blocks of the
    // inline(never) helpers in FIXTURE_B into a shared section unit per section,
    // minted as `PcMapUnit::Synthetic`. A synthetic unit spans many PC ranges
    // (one per machine insn), so identities repeat across a unit's own entries;
    // the property under test is cross-section, not per-entry.
    let artifacts = stamp_all_and_compile(FIXTURE_B, OptLevel::Os);

    // Distinct synthetic identities (deduped across a unit's own entries), and,
    // per raw section-unit number, the set of sections that minted it.
    let mut identities: HashSet<(String, String, u32)> = HashSet::new();
    let mut sections_by_raw_unit: HashMap<u32, HashSet<String>> = HashMap::new();
    let mut synthetic_seen = false;

    for artifact in &artifacts {
        for (_, sec) in artifact.sections.iter() {
            let Some(obs) = sec.observability.as_ref() else {
                continue;
            };
            assert_conserved(obs);
            for e in &obs.pc_map {
                if let PcMapUnit::Synthetic {
                    object,
                    section,
                    unit,
                } = &e.unit
                {
                    synthetic_seen = true;
                    let obj = object.0.as_str().to_string();
                    let sect = section.0.as_str().to_string();
                    identities.insert((obj, sect.clone(), unit.0));
                    sections_by_raw_unit.entry(unit.0).or_default().insert(sect);
                    // A synthetic range is compiler-synthesized, so it is always
                    // unmapped with the Synthetic reason, never mapped to source.
                    assert!(matches!(
                        &e.attribution,
                        PcAttribution::Unmapped {
                            reason: UnmappedReason::Synthetic,
                            ..
                        }
                    ));
                }
            }
        }
    }

    // Non-vacuous: fail loudly if the fixture minted nothing to test.
    assert!(
        synthetic_seen,
        "fixture minted no synthetic units; iterate FIXTURE_B"
    );

    // The hazard is real: each section numbers its outlined units from zero, so
    // the same raw unit id appears in more than one section. If the identity were
    // just that raw number (as a bare arena id would be), the two would pun.
    let raw_collision = sections_by_raw_unit
        .values()
        .any(|sections| sections.len() >= 2);
    assert!(
        raw_collision,
        "expected the same raw section-unit id in more than one section; \
         FIXTURE_B did not exercise a cross-section unit-id collision"
    );

    // The property: object+section fully disambiguates those colliding ids, so
    // every (section, raw-unit) pair maps to its own distinct identity and no
    // identity is shared across sections.
    let distinct_section_unit_pairs: usize = sections_by_raw_unit.values().map(|s| s.len()).sum();
    assert_eq!(
        identities.len(),
        distinct_section_unit_pairs,
        "object+section must keep colliding synthetic unit ids apart"
    );
}
