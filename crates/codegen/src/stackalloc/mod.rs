use smallvec::SmallVec;
use sonatina_ir::{BlockId, Function, Immediate, InstId, ValueId};

use crate::isa::evm::static_arena_alloc::StackObjId;

mod stackify;
pub use stackify::{StackifyAlloc, StackifyBuilder, StackifySearchProfile};

pub type Actions = SmallVec<[Action; 2]>;

pub trait Allocator {
    fn enter_function(&self, function: &Function) -> Actions;

    // xxx rename these to make it clear that these are pre- and post-insn operations
    /// Return the actions required to place `vals` on the stack,
    /// in the specified order. I.e. the first `Value` in `vals`
    /// will be on the top of the stack.
    fn read(&self, inst: InstId, vals: &[ValueId]) -> Actions;
    /// Return the actions required for the `case_index`th `br_table` compare in IR order.
    fn read_br_table_case(&self, inst: InstId, case_index: usize) -> Actions;
    fn write(&self, inst: InstId, vals: &[ValueId]) -> Actions;

    fn traverse_edge(&self, from: BlockId, to: BlockId) -> Actions;
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
