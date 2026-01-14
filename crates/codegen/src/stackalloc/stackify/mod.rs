//! Stack allocation via deterministic block-entry templates and edge fixups.
//!
//! - Each block `B` has a unique entry template `StackIn(B) = P(B) ++ T(B)`.
//!   - `P(B)` is a parameter prefix (phi results; plus function args for the entry block).
//!   - `T(B)` is a transfer region: live-in, non-phi values in a chosen order.
//!     - `T(B)` is derived from simulated predecessor stacks (`cand(pred→B)`), not heuristics.
//!     - Layouts are solved in reachable-CFG SCC topo order; cyclic SCCs use a fixed point.
//! - For merge blocks, all incoming edges are normalized to the same `StackIn(B)` (often a no-op).
//! - When a value cannot be duplicated from within `DUP16` reach, it is added to `spill_set`,
//!   assigned a frame slot, and reloaded from memory; `spill_set` is discovered via a
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

use builder::StackifyContext;

const DUP_MAX: usize = 16; // DUP16 duplicates stack[15]
const SWAP_MAX: usize = 17; // SWAP16 swaps stack[0] and stack[16]
/// Maximum `SWAP*` chain length used to consume a last-use operand directly from the stack.
///
/// This is a purely local heuristic: we rotate a last-use value up (preserving the current
/// operand prefix order) so the instruction consumes it, avoiding a `DUP*` + later cleanup.
const CONSUME_LAST_USE_MAX_SWAPS: usize = 3;
