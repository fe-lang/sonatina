use smallvec::SmallVec;
use sonatina_ir::{BlockId, Function, Immediate, InstId, ValueId};

mod stackify;
pub use stackify::StackifyAlloc;

pub type Actions = SmallVec<[Action; 2]>;

pub trait Allocator {
    fn enter_function(&self, function: &Function) -> Actions;

    /// Returns the number of 32-byte frame slots used by this function for
    /// spilling/reloading values.
    fn frame_size_slots(&self) -> u32 {
        0
    }

    // xxx rename these to make it clear that these are pre- and post-insn operations
    /// Return the actions required to place `vals` on the stack,
    /// in the specified order. I.e. the first `Value` in `vals`
    /// will be on the top of the stack.
    fn read(&self, inst: InstId, vals: &[ValueId]) -> Actions;
    fn write(&self, inst: InstId, val: Option<ValueId>) -> Actions;

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
    /// Relative to `LowerBackend`-defined frame pointer
    MemLoadFrameSlot(u32),
    MemStoreAbs(u32),
    MemStoreFrameSlot(u32),
}
