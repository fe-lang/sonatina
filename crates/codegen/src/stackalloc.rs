use smallvec::SmallVec;
use sonatina_ir::{Block, Immediate, Insn, Value};

mod edge_sets;
mod local_stack;
mod simple;
pub use simple::SimpleAlloc;

pub type Actions = SmallVec<[Action; 2]>;

pub trait Allocator {
    /// Return the actions required to place `vals` on the stack,
    /// in the specified order. I.e. the first `Value` in `vals`
    /// will be on the top of the stack.
    fn read(&mut self, insn: Insn, vals: &[Value]) -> Actions;
    fn write(&mut self, insn: Insn, val: Value) -> Actions;

    fn traverse_edge(&mut self, from: Block, to: Block) -> Actions;
}

#[derive(Copy, Clone, Debug)]
pub enum Action {
    StackDup(u8),
    StackSwap(u8),
    Push(Immediate),
    Pop,
    MemLoadAbs(u32),
    /// Relative to `LowerBackend`-defined frame pointer
    MemLoadFrameSlot(u32),
    MemStoreAbs(u32),
    MemStoreFrameSlot(u32),
}
