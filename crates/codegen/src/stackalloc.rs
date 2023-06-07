use smallvec::SmallVec;
use sonatina_ir::{Block, Function, Immediate, Insn, Value};

mod edge_sets;
mod local_stack;
mod simple;
pub use simple::SimpleAlloc;

pub type Actions = SmallVec<[Action; 2]>;

pub trait Allocator {
    fn enter_function(&self, function: &Function) -> Actions;

    /// Return the actions required to place `vals` on the stack,
    /// in the specified order. I.e. the first `Value` in `vals`
    /// will be on the top of the stack.
    fn read(&self, insn: Insn, vals: &[Value]) -> Actions;
    fn write(&self, insn: Insn, val: Value) -> Actions;

    fn brtable_case(&self, insn: Insn, val: Option<Value>, block: Block) -> (Actions, Actions);
    fn traverse_edge(&self, from: Block, to: Block) -> Actions;
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
