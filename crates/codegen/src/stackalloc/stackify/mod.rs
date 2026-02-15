//! Stack allocation via deterministic block-entry templates and edge fixups.
//!
//! - Each block `B` has a unique entry template `StackIn(B) = P(B) ++ T(B)`.
//!   - `P(B)` is a parameter prefix (phi results; plus function args for the entry block).
//!   - `T(B)` is a transfer region: live-in, non-phi values in a chosen order.
//!     - `T(B)` is derived from simulated predecessor stacks (`cand(pred→B)`), not heuristics.
//!     - Layouts are solved in reachable-CFG SCC topo order; cyclic SCCs use a fixed point.
//! - For merge blocks, all incoming edges are normalized to the same `StackIn(B)` (often a no-op).
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

pub use alloc::{StackifyAlloc, StackifyLiveValues};

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
    use super::{StackifyAlloc, StackifyLiveValues};
    use crate::{
        critical_edge::CriticalEdgeSplitter,
        domtree::DomTree,
        liveness::{InstLiveness, Liveness},
    };
    use sonatina_ir::cfg::ControlFlowGraph;
    use sonatina_parser::parse_module;

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

            let alloc = StackifyAlloc::for_function_with_call_live_values_and_scratch_spills(
                function,
                &cfg,
                &dom,
                &liveness,
                16,
                StackifyLiveValues {
                    scratch_live_values: scratch_live_values.clone(),
                },
                2,
            );

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
}
