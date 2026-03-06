//! Stack allocation via deterministic block-entry templates and edge fixups.
//!
//! - Each block `B` has a unique entry template `StackIn(B) = P(B) ++ T(B)`.
//!   - `P(B)` is a stack-resident parameter prefix:
//!     - function args for the entry block
//!     - non-spilled phi results for other blocks
//!   - `T(B)` is a transfer region: live-in, non-phi values in a chosen order.
//!     - `T(B)` is derived from simulated predecessor stacks (`cand(pred→B)`), not heuristics.
//!     - Layouts are solved in reachable-CFG SCC topo order; cyclic SCCs use a fixed point.
//! - For merge blocks, all incoming edges are normalized to the same `StackIn(B)` (often a no-op);
//!   spilled phi results are stored directly on the incoming edge instead of being carried in
//!   `P(B)`.
//! - When a value cannot be duplicated from within `DUP16` reach, it is added to `spill_set`,
//!   assigned a stack object, and reloaded from memory; `spill_set` is discovered via a
//!   monotone fixed point.
//!
//! Notes specific to this codebase:
//! - Critical edges must be split before running this allocator.
//! - Internal calls rely on an implicit return address value on the EVM stack.
//!   The allocator models this as a special stack item barrier to avoid popping
//!   into the caller's preserved stack segment.

mod alloc;
mod builder;
mod flow_templates;
mod iteration;
mod planner;
mod slots;
mod spill;
mod sym_stack;
mod templates;
mod trace;

pub use alloc::StackifyAlloc;
pub use builder::StackifyBuilder;

use builder::StackifyContext;

const DUP_MAX: usize = 16; // DUP16 duplicates stack[15]
const SWAP_DEPTH_MAX: usize = 16; // SWAP16 swaps stack[0] and stack[16]
const SWAP_WINDOW_MAX: usize = SWAP_DEPTH_MAX + 1; // reachable items (incl. top)
/// Maximum `SWAP*` chain length used to consume a last-use operand directly from the stack.
///
/// This is a purely local heuristic: we rotate a last-use value up (preserving the current
/// operand prefix order) so the instruction consumes it, avoiding a `DUP*` + later cleanup.
const CONSUME_LAST_USE_MAX_SWAPS: usize = 4;

#[cfg(test)]
mod tests {
    use super::StackifyBuilder;
    use crate::{
        critical_edge::CriticalEdgeSplitter,
        domtree::DomTree,
        isa::evm::{EvmBackend, canonicalize_alias_value},
        liveness::{InstLiveness, Liveness},
        stackalloc::Action,
    };
    use cranelift_entity::SecondaryMap;
    use sonatina_ir::{
        ValueId, cfg::ControlFlowGraph, inst::control_flow::BranchKind, isa::evm::Evm,
    };
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};
    use std::fmt::Write;

    #[test]
    fn scratch_spills_respect_scratch_live_values() {
        const SRC: &str = include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/test_files/evm/spill.sntn"
        ));

        let parsed = parse_module(SRC).unwrap();
        let spill_func = parsed
            .debug
            .func_order
            .iter()
            .copied()
            .find(|&f| parsed.module.ctx.func_sig(f, |sig| sig.name() == "spill"))
            .expect("missing spill func");

        parsed.module.func_store.modify(spill_func, |function| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);

            let mut splitter = CriticalEdgeSplitter::new();
            splitter.run(function, &mut cfg);

            let mut liveness = Liveness::new();
            liveness.compute(function, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut inst_live = InstLiveness::new();
            inst_live.compute(function, &cfg, &liveness);
            let scratch_live_values = inst_live.call_live_values(function);
            assert!(
                !scratch_live_values.is_empty(),
                "expected some scratch-live values"
            );

            let alloc = StackifyBuilder::new(function, &cfg, &dom, &liveness, 16)
                .with_scratch_live_values(scratch_live_values.clone())
                .with_scratch_spills(2)
                .compute();

            for (v, slot) in alloc.scratch_slot_of_value.iter() {
                if slot.is_some() {
                    assert!(
                        !scratch_live_values.contains(v),
                        "scratch spill used for a scratch-live value"
                    );
                }
            }

            assert!(
                scratch_live_values
                    .iter()
                    .any(|v| alloc.spill_obj[v].is_some()),
                "expected at least one scratch-live value to spill to a stack object"
            );
        });
    }

    #[test]
    fn alias_aware_trace_keeps_noop_casts_action_free() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256, v1.i256) {
block0:
    v2.*i8 = int_to_ptr v0 *i8;
    v3.*i32 = bitcast v2 *i32;
    v4.*i256 = bitcast v3 *i256;
    mstore v4 v1 i256;
    return;
}
"#;

        let parsed = parse_module(SRC).unwrap();
        let fref = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&f| parsed.module.ctx.func_sig(f, |sig| sig.name() == "f"))
            .expect("missing f");
        let backend = EvmBackend::new(Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        }));

        parsed.module.func_store.view(fref, |function| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let value_aliases =
                backend.compute_stackify_value_aliases(function, &parsed.module.ctx);

            let mut liveness = Liveness::new();
            liveness.compute_with_value_normalizer(function, &cfg, |v| {
                canonicalize_alias_value(&value_aliases, v)
            });

            let (_, trace) = StackifyBuilder::new(function, &cfg, &dom, &liveness, 16)
                .with_value_aliases(&value_aliases)
                .compute_with_trace();

            let lines: Vec<_> = trace.lines().collect();
            for (i, line) in lines.iter().enumerate() {
                if line.trim_start().starts_with("bitcast [") {
                    let prev_is_pre = i > 0 && lines[i - 1].trim_start().starts_with("pre:");
                    assert!(
                        !prev_is_pre,
                        "alias-only cast should not have stack prep actions:\n{trace}"
                    );
                }
            }
        });
    }

    #[test]
    fn alias_aware_trace_keeps_multihop_noop_casts_action_free() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256, v1.i256) {
block0:
    v2.*i8 = int_to_ptr v0 *i8;
    v3.*i32 = bitcast v2 *i32;
    v4.*i256 = bitcast v3 *i256;
    mstore v4 v1 i256;
    return;
}
"#;

        let parsed = parse_module(SRC).unwrap();
        let fref = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&f| parsed.module.ctx.func_sig(f, |sig| sig.name() == "f"))
            .expect("missing f");

        parsed.module.func_store.view(fref, |function| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let v0 = parsed.debug.value(fref, "v0").expect("v0");
            let v2 = parsed.debug.value(fref, "v2").expect("v2");
            let v3 = parsed.debug.value(fref, "v3").expect("v3");
            let v4 = parsed.debug.value(fref, "v4").expect("v4");

            let mut value_aliases: SecondaryMap<ValueId, Option<ValueId>> = SecondaryMap::new();
            for v in function.dfg.values.keys() {
                value_aliases[v] = Some(v);
            }
            value_aliases[v2] = Some(v0);
            value_aliases[v3] = Some(v2);
            value_aliases[v4] = Some(v3);

            let mut liveness = Liveness::new();
            liveness.compute_with_value_normalizer(function, &cfg, |v| {
                canonicalize_alias_value(&value_aliases, v)
            });

            let (_, trace) = StackifyBuilder::new(function, &cfg, &dom, &liveness, 16)
                .with_value_aliases(&value_aliases)
                .compute_with_trace();

            let lines: Vec<_> = trace.lines().collect();
            for (i, line) in lines.iter().enumerate() {
                let op = line.trim_start();
                if op.starts_with("bitcast [") || op.starts_with("int_to_ptr [") {
                    let prev_is_pre = i > 0 && lines[i - 1].trim_start().starts_with("pre:");
                    assert!(
                        !prev_is_pre,
                        "multi-hop alias no-op cast should not have stack prep actions:\n{trace}"
                    );
                }
            }
        });
    }

    #[test]
    fn entry_backedge_jump_emits_fixup_at_terminator() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %loop(v0.i256, v1.i256) -> i256 {
block0:
    v2.i1 = eq v0 0.i256;
    br v2 block2 block1;

block1:
    v3.i256 = add v0 1.i256;
    jump block0;

block2:
    return v0;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let fref = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&f| parsed.module.ctx.func_sig(f, |sig| sig.name() == "loop"))
            .expect("missing loop");

        parsed.module.func_store.view(fref, |function| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);

            let mut liveness = Liveness::new();
            liveness.compute(function, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let v1 = parsed.debug.value(fref, "v1").expect("v1 exists");
            let entry = cfg.entry().expect("entry block exists");
            let backedge_block = function
                .layout
                .iter_block()
                .find(|&block| block != entry)
                .expect("backedge block exists");
            let jump_inst = function
                .layout
                .last_inst_of(backedge_block)
                .expect("backedge terminator exists");

            let branch = function
                .dfg
                .branch_info(jump_inst)
                .expect("terminator is control flow");
            assert!(
                matches!(branch.branch_kind(), BranchKind::Jump(_)),
                "expected unconditional backedge"
            );

            let alloc = StackifyBuilder::new(function, &cfg, &dom, &liveness, 16).compute();

            assert!(
                alloc.pre_actions[jump_inst]
                    .iter()
                    .any(|action| matches!(action, Action::MemLoadObj(_) | Action::MemLoadAbs(_))),
                "expected backedge to entry to reload the dropped entry arg:\npre_actions={:?}",
                alloc.pre_actions[jump_inst]
            );
            assert!(
                alloc.spill_obj[v1].is_some(),
                "expected dropped entry arg to become spill-reloadable on the backedge"
            );
        });
    }

    #[test]
    fn spilled_merge_phi_store_avoids_out_of_range_dup() {
        let mut src = String::from(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i1) -> i32 {
block0:
    br v0 block1 block2;

block1:
"#,
        );
        for i in 0..18 {
            let _ = writeln!(&mut src, "    v{}.i32 = add {i}.i32 1.i32;", i + 1);
        }
        src.push_str(
            r#"
    jump block3;

block2:
"#,
        );
        for i in 0..18 {
            let _ = writeln!(&mut src, "    v{}.i32 = add {}.i32 1.i32;", i + 19, 100 + i);
        }
        src.push_str(
            r#"
    jump block3;

block3:
"#,
        );
        for i in 0..18 {
            let _ = writeln!(
                &mut src,
                "    v{}.i32 = phi (v{} block1) (v{} block2);",
                i + 37,
                i + 1,
                i + 19
            );
        }
        src.push_str(
            r#"
    v55.i32 = add v54 1.i32;
"#,
        );
        for (idx, phi) in (37..54).enumerate() {
            let acc = 55 + idx;
            let next = acc + 1;
            let _ = writeln!(&mut src, "    v{next}.i32 = add v{acc} v{phi};");
        }
        src.push_str(
            r#"
    return v72;
}
"#,
        );

        let parsed = parse_module(&src).expect("module parses");
        let fref = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&f| parsed.module.ctx.func_sig(f, |sig| sig.name() == "f"))
            .expect("missing f");

        parsed.module.func_store.modify(fref, |function| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);

            let mut splitter = CriticalEdgeSplitter::new();
            splitter.run(function, &mut cfg);

            let mut liveness = Liveness::new();
            liveness.compute(function, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let deep_phi = parsed.debug.value(fref, "v54").expect("v54 exists");
            let alloc = StackifyBuilder::new(function, &cfg, &dom, &liveness, 16).compute();

            assert!(
                alloc.spill_obj[deep_phi].is_some(),
                "expected deepest phi to spill so merge repair must store it"
            );
            assert!(
                alloc.pre_actions.values().any(|actions| {
                    actions
                        .iter()
                        .any(|action| matches!(action, Action::MemStoreObj(_) | Action::MemStoreAbs(_)))
                }),
                "expected merge repair to emit at least one spill store"
            );
            assert!(
                alloc.pre_actions.values().all(|actions| {
                    actions
                        .iter()
                        .all(|action| !matches!(action, Action::StackDup(slot) if *slot >= super::DUP_MAX as u8))
                }),
                "unexpected out-of-range DUP in merge repair: {:?}",
                alloc.pre_actions
            );
        });
    }
}
