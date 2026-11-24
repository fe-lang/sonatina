//! The operand stack that the stack allocator planned for each machine instruction.
//!
//! A front end that wants to show where a source value lives while the program runs needs two
//! facts: which machine value holds it, and where that value sits on the EVM operand stack at a
//! given opcode. [`StackPlan`] is the second fact, stored structurally. The first is carried by
//! [`ValueLabel`]s, which a front end attaches to IR values and which each [`StackValue`] repeats.
//!
//! A plan is only produced when stack plan capture is requested, with
//! [`EvmBackend::with_stackify_trace_capture`](super::EvmBackend::with_stackify_trace_capture).
//! Capturing it observes the allocation and never changes it.
//!
//! # Scope
//!
//! The plans are meant for code compiled at optimization level 0, which is the level at which the
//! tests check them against executed code. Above level 0 the plans still describe the machine
//! functions as they were planned, but two later steps change which code runs:
//!
//! - Code that is outlined into a shared unit belongs to no function. Such a unit has no plan,
//!   so [`SectionObservability::stack_before`](crate::object::SectionObservability::stack_before)
//!   returns `None` for it.
//! - Identical private functions are merged after planning. Executing the removed function runs
//!   the surviving function's code, so a consumer sees the plan and the labels of the survivor.
//!
//! Passes that clone code give the clones values without labels, and a value without a label
//! has no location.
//!
//! # What a stack word is
//!
//! A word on the stack is the machine representation of the value, as the EVM holds it. For a
//! narrow integer or an aggregate that representation can differ from the source value: an
//! aggregate that is passed by reference holds an address. A consumer decodes a word by the
//! source type of the value. The plan does not say whether the upper bits of a word that holds a
//! narrow integer are canonical.
//!
//! A value that the allocator keeps in memory is described by a plan only while a copy of it is
//! on the stack. A value that was spilled has no position at the points where it is not on the
//! stack, and memory places are not exported.

use sonatina_ir::{ValueId, ValueLabel};

use crate::object::MachineInstId;

/// What the stack allocator planned for one machine function.
///
/// The plan belongs to a function unit of the machine IR: the value and instruction ids in it are
/// local to that function's machine IR, the same namespace as [`MachineInstId`] in a
/// [`PcMapEntry`](crate::object::PcMapEntry) whose unit is that function.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct StackPlan {
    /// One record per machine instruction that has an operand stack plan, in ascending
    /// instruction id order. An instruction that emits no opcode, such as a phi, may be absent.
    pub insts: Vec<InstStack>,
}

impl StackPlan {
    /// The planned stack of `inst`, or `None` when the plan has no record for it.
    pub fn stack_before(&self, inst: MachineInstId) -> Option<&InstStack> {
        let key = inst.raw().as_u32();
        self.insts
            .binary_search_by_key(&key, |record| record.inst.raw().as_u32())
            .ok()
            .map(|idx| &self.insts[idx])
    }
}

/// The operand stack planned for one machine instruction.
///
/// `stack` is the state of the EVM operand stack before the first opcode that the instruction
/// emits, top of the stack first. That is the first opcode of the instruction's own group of
/// opcodes: any block-entry shuffle that the allocator planned for the instruction is part of
/// the group, and `stack` is the state before it.
///
/// The list holds the words that the allocator planned with: the function's values and, in a
/// function that returns to a caller, the return address ([`StackEntry::ReturnAddress`]), which
/// is the last entry. The words that the caller left below the return address are not listed.
/// Counted from the top, entry `i` is the word `i` places below the top of the real stack, with
/// one exception.
///
/// In a block that ends the transaction without returning (every path from it ends in `REVERT`,
/// `RETURN`, `STOP`, `INVALID` or `SELFDESTRUCT`), the allocator starts from a stack that lists
/// only the words the block pushes itself and the return address. Words that the function left
/// on the stack before it entered the block lie between the two and are not listed. In such a
/// block the entries above the return address are at their listed places; the return address
/// entry, and so any number of caller words derived from the length of the list, is not. A
/// consumer must therefore not derive a frame base from `stack.len()` in such a block.
///
/// The stack is the state before the first opcode only. The instruction emits further opcodes
/// that change the stack before its own operation runs, and the operation changes it again. A
/// consumer that needs the stack at a later opcode of the same instruction applies the opcodes
/// that were actually emitted, which the PC map of the section lists, to this stack:
///
/// - `PUSH`, `DUP`, `SWAP` and `POP` change the stack as the EVM defines.
/// - Any other opcode in the group ends what this record describes. Such opcodes are the
///   operation itself, a memory load or store of a spilled value, a calldata load that rebuilds a
///   value, the frame setup and teardown of a function, and the arithmetic that builds a
///   constant from several words (a `PUSH` followed by `SIGNEXTEND`, `NOT`, `SHL` or `SHR`). A
///   consumer stops there and takes the stack from the record of the next instruction.
///
/// The emitted opcodes are authoritative within the group: the emitter simplifies some shuffles
/// that the allocator planned, so the allocator's own action list is not a substitute.
///
/// Some opcodes belong to no machine instruction and have no record: the `JUMPDEST` that begins a
/// block, the entry sequence of a function and the frame setup at the start of a block. Only for
/// the block-head `JUMPDEST` is anything stated: it leaves the stack unchanged, so the record of
/// the next instruction describes the stack at it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstStack {
    /// The machine instruction.
    pub inst: MachineInstId,
    /// The planned stack, top first. See the type documentation.
    pub stack: Vec<StackEntry>,
}

/// One word of a planned stack.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StackEntry {
    /// A machine value.
    Value(StackValue),
    /// The address that the function returns to, pushed by its caller. See [`InstStack`] for the
    /// blocks in which its place is not the listed one.
    ReturnAddress,
    /// The address at which the function resumes after an internal call that is being set up.
    /// The allocator pushes it while it plans the call, after the point at which a record is
    /// taken, so a record that was taken at the start of an instruction does not list it. The
    /// variant exists because the allocator's own stack item has it.
    CallContinuation,
}

/// A machine value on the stack, with the facts the allocator had about it.
///
/// A value that carries no label is not known to correspond to anything in the source program. A
/// consumer must treat it as "no location known" for every label, never as a location of its own.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackValue {
    /// The machine value, local to the function's machine IR.
    pub value: ValueId,
    /// No instruction from this one on, in this block or after it, reads the value. The word is
    /// still on the stack and still holds the value. A dead value stays on the stack until the
    /// allocator pops it, which may be after this instruction. Never set for a constant.
    pub dead: bool,
    /// The value is an immediate. The word on the stack is a copy of the constant, which the
    /// allocator may keep for later uses.
    pub constant: bool,
    /// The labels of the IR values that this machine value stands for, in ascending order. They
    /// are exactly the labels that a front end attached, plus the labels merged onto the value
    /// when a pass replaced an IR value by another one. A value with no labels is not known to
    /// correspond to any source value.
    pub labels: Vec<ValueLabel>,
}
