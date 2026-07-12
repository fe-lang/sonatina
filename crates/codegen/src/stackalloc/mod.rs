use crate::bitset::BitSet;
use cranelift_entity::SecondaryMap;
use smallvec::SmallVec;
use sonatina_ir::{Function, Immediate, InstId, ValueId};

use crate::isa::evm::static_arena_alloc::StackObjId;

mod edge_split;
mod stackify;
pub use edge_split::StackifyEdgeSplitter;
pub(crate) use stackify::{
    HOT_IMMEDIATE_SIZE_MIN_BLOCK_USES, HOT_IMMEDIATE_SIZE_MIN_MATERIALIZATION_BYTES, StackifyTrace,
};
pub use stackify::{StackifyAlloc, StackifyBuilder, StackifySearchProfile};

pub type Actions = SmallVec<[Action; 2]>;

pub trait Allocator {
    /// Actions to run at function entry (function-argument spill stores).
    fn enter_function(&self, function: &Function) -> Actions;

    /// Actions to run immediately before `inst`'s opcode(s).
    fn pre_inst(&self, inst: InstId) -> &Actions;
    /// Actions to run immediately after `inst`'s opcode(s).
    fn post_inst(&self, inst: InstId) -> &Actions;
    /// Actions preparing the `case_index`th `br_table` compare, in IR case order.
    fn br_table_case(&self, inst: InstId, case_index: usize) -> &Actions;
}

pub(crate) fn canonicalize_value_alias(
    value_aliases: &SecondaryMap<ValueId, Option<ValueId>>,
    value: ValueId,
) -> ValueId {
    let mut current = value;
    loop {
        let next = value_aliases[current].unwrap_or(current);
        if next == current {
            return current;
        }
        current = next;
    }
}

pub(crate) fn normalize_value_alias_map(
    function: &Function,
    value_aliases: &mut SecondaryMap<ValueId, Option<ValueId>>,
) {
    for value in function.dfg.value_ids() {
        let mut seen: BitSet<ValueId> = BitSet::default();
        let mut path = SmallVec::<[ValueId; 8]>::new();
        let mut current = value;
        let mut rep = None;
        loop {
            if !seen.insert(current) {
                // Invalid alias cycles should not be canonicalized to an arbitrary value from
                // outside the cycle. Keep all traversed values self-canonical.
                for v in path.iter().copied() {
                    value_aliases[v] = Some(v);
                }
                break;
            }
            path.push(current);
            let next = value_aliases[current].unwrap_or(current);
            if next == current {
                rep = Some(current);
                break;
            }
            current = next;
        }
        if let Some(rep) = rep {
            for v in path {
                value_aliases[v] = Some(rep);
            }
        }
    }

    #[cfg(debug_assertions)]
    for value in function.dfg.value_ids() {
        let rep = value_aliases[value].unwrap_or(value);
        debug_assert_eq!(
            value_aliases[rep].unwrap_or(rep),
            rep,
            "value alias map is not one-hop canonical for v{}",
            value.as_u32()
        );
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Action {
    StackDup(u8),
    StackSwap(u8),
    Push(Immediate),
    /// For CALL: Push code offset that callee should jump to upon return
    PushContinuationOffset,
    Pop,
    MemLoadAbs(u32),
    /// Local dynamic-frame word offset, excluding backend metadata such as the
    /// hidden caller-SP link slot.
    MemLoadFrameSlot(u32),
    MemStoreAbs(u32),
    /// Local dynamic-frame word offset, excluding backend metadata such as the
    /// hidden caller-SP link slot.
    MemStoreFrameSlot(u32),
    MaterializeLocalAddr {
        alloca: InstId,
        offset_bytes: i64,
    },
    /// Local dynamic-frame word offset, excluding backend metadata such as the
    /// hidden caller-SP link slot.
    PushFrameAddr {
        offset_words: u32,
        extra_bytes: i64,
    },

    /// Virtual stack-object memory operation, rewritten during lowering.
    MemLoadObj(StackObjId),
    MemStoreObj(StackObjId),
}
