//! A record of how the EVM backend lowered a section: the IR machine lowering
//! read, the machine IR the section's code is emitted from, each step of the
//! machine stage between the machine IR lowering built and that one
//! (`SectionLowering::machine_steps`), and what connects the machine IR to
//! the bytes. It is meant for an external checker that validates each
//! compilation's bytes against its IR.
//!
//! The record is an in-memory API with no version and no stability promise.
//! Sonatina does not serialize it; its consumer does. Turn it on with
//! `EvmCompile::with_lowering_record`, which puts it in
//! `SectionArtifact::lowering`. Calling `compile_all_objects` directly, it
//! takes both `EvmBackend::with_lowering_record`, which keeps what the record
//! is built from, and `CompileOptions::emit_lowering`, which builds it.
//! Recording does not change the generated code: the tests compile each
//! fixture with and without it and compare the bytes.
//!
//! Functions and symbols are named as the IR text of the section's module
//! names them, values and blocks by their ids in the text of their module
//! (`v12`, `block3`).

use sonatina_ir::{BlockId, Immediate, InstId, ValueId, module::FuncRef};

use super::SymbolDef;
use crate::isa::evm::LateCleanupProfile;

#[derive(Debug, Clone)]
pub struct SectionLowering {
    /// The section's module after the backend's IR pipeline: what machine
    /// lowering reads.
    pub source_ir: String,
    /// The machine module the section's code is emitted from.
    pub machine_ir: String,
    /// The bytes the code takes; data and embeds follow it.
    pub code_size: u32,
    pub arena_base: u32,
    pub dyn_base: u32,
    /// The free pointer the section entry stores at `0x40` before anything
    /// else, if it stores one.
    pub entry_free_ptr: Option<u32>,
    pub funcs: Vec<FuncLowering>,
    /// The offset and size of each code unit the late merges outlined.
    pub units: Vec<(String, u32, u32)>,
    /// Each label the late merges redirected, as `(old, new)`: code that
    /// jumped or called to `old` now goes to `new`.
    pub redirects: Vec<(CodeLabel, CodeLabel)>,
    /// The section's symbol table, by offset, each symbol as the IR text
    /// writes it (`%func`, `$global`, `&embed`, `.` for the section). The
    /// pipeline adds functions and globals to the section's module, which the
    /// compiled module does not name.
    pub symbols: Vec<(String, SymbolDef)>,
    /// How the machine stage turned the lowered machine IR into `machine_ir`.
    pub machine_steps: MachineSteps,
}

/// Each transformation of the machine stage, from the machine IR that
/// lowering built to `SectionLowering::machine_ir`, with the facts each step
/// relied on. Of the placement iterations of a section, only the one whose
/// code is emitted is recorded.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MachineSteps {
    /// The profile the passes ran under, which decides which of them run.
    pub profile: LateCleanupProfile,
    /// Every function of the section as lowering built it.
    pub lowered: Vec<FuncSnap>,
    /// The passes in the order they ran. Every function finishes a pass
    /// before any starts the next.
    pub passes: Vec<MachinePass>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MachinePass {
    pub kind: MachinePassKind,
    /// What the pass read of the behavior of each function of the module,
    /// as analyzed of the module before it, or before an earlier pass whose
    /// changes did not lead the round to analyze it again. `None` for a pass
    /// that reads none.
    pub func_behavior: Option<Vec<FuncSummary>>,
    /// The steps of the pass in order. A function a step did not change is
    /// not in it, and a step that changed no function is left out.
    pub steps: Vec<MachineStep>,
}

/// What machine passes read of a function's effect summary. A function not
/// listed may do anything.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncSummary {
    pub func: String,
    /// Never returns to its caller.
    pub noreturn: bool,
    /// Always returns to its caller.
    pub will_return: bool,
    /// May read memory or observe other state.
    pub reads: bool,
    /// May write memory.
    pub writes: bool,
    /// May change other state, or allocate.
    pub mutates: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MachinePassKind {
    CfgCleanup,
    BranchCanonicalize,
    ScalarCanonicalize,
    KnownBitsSimplify,
    Sccp,
    Gvn,
    Adce,
    LowerSwitches,
    BranchConditions,
    CoalesceCopies,
    EdgeSplit,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MachineStep {
    pub kind: StepKind,
    /// The functions the step changed, in the section's function order.
    pub funcs: Vec<FuncStep>,
}

/// A step of a machine pass. A pass of one step has a step of its own kind;
/// `Sccp` runs `CfgCleanup`, `SccpPrune`, `SccpFold`, `CfgCleanup`, `Adce`
/// rounds, `CfgCleanup` and `CfgCleanup`, `Gvn` runs `GvnPrune` and
/// `GvnRewrite`, and `Adce` runs `Adce` rounds and `CfgCleanup`. A pass of
/// `ScalarCanonicalize` or `KnownBitsSimplify` runs rounds of its step: a
/// step of a kind that repeats is one round, the same round of each function
/// it lists.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StepKind {
    CfgCleanup,
    BranchCanonicalize,
    ScalarCanonicalize,
    KnownBitsSimplify,
    SccpPrune,
    SccpFold,
    Adce,
    GvnPrune,
    GvnRewrite,
    LowerSwitches,
    BranchConditions,
    CoalesceCopies,
    EdgeSplit,
}

impl StepKind {
    /// Whether a pass runs steps of this kind in rounds.
    pub fn repeats(self) -> bool {
        matches!(
            self,
            Self::ScalarCanonicalize | Self::KnownBitsSimplify | Self::Adce
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncStep {
    /// The whole function after the step.
    pub out: FuncSnap,
    /// What the step relied on, true of the function before the step.
    pub facts: StepFacts,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StepFacts {}

/// A function of the machine module at one point of the machine stage.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncSnap {
    pub func: String,
    pub func_ref: FuncRef,
    /// The function's IR text, values and blocks named by their ids.
    pub text: String,
    /// The instruction of each line of `text`, by block in the order the
    /// text lists them, phis and terminators included.
    pub insts: Vec<Vec<InstId>>,
}

#[derive(Debug, Clone)]
pub struct FuncLowering {
    pub name: String,
    /// Where the function's code starts; `None` if its code is another's.
    pub offset: Option<u32>,
    pub blocks: Vec<BlockLowering>,
    /// Where each value the stack does not hold everywhere is kept, and where
    /// the function's code stores and reloads it.
    pub spills: Vec<SpillLowering>,
    pub frame: FrameLowering,
    /// The placement of each `evm_malloc` of the source IR, by its result.
    pub mallocs: Vec<(ValueId, MallocLowering)>,
}

#[derive(Debug, Clone)]
pub struct BlockLowering {
    /// The block of the machine IR.
    pub block: BlockId,
    /// The blocks of the source IR it comes from.
    pub sources: Vec<BlockId>,
    /// Where its code starts, if it is laid out.
    pub offset: Option<u32>,
    /// The block whose code it is emitted as: a jump-only block is.
    pub alias: Option<BlockId>,
    /// The stack the block starts with, top first. Below it the stack is
    /// the caller's or unused. Empty unless the block is planned.
    pub entry_stack: Vec<StackSlot>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StackSlot {
    Value(ValueId),
    Imm(Immediate),
    /// The address the function returns to.
    FuncReturn,
    /// The address an internal call returns to, pushed for the call.
    CallReturn,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpillLowering {
    pub value: ValueId,
    pub location: SpillLocation,
    /// The points at which the code stores the value into its location, in
    /// emission order: after its definition, at entry for an argument, and
    /// for a phi before the terminator of each predecessor (an edge block,
    /// for a critical edge) that gives it an operand other than itself,
    /// except where the edge would reload that operand from the phi's own
    /// location. The stack top holds the value stored, a phi's operand on its
    /// edge, and the store may take it off the stack.
    pub stores: Vec<CodePoint>,
    /// The points at which the code reloads the value from its location onto
    /// the stack, in emission order.
    pub reloads: Vec<CodePoint>,
}

/// A point of a function's machine IR at which its code runs the stack
/// allocator's moves. `index` is the position of an instruction in its block,
/// phis included. A function without code of its own
/// (`FuncLowering::offset` is `None`) has no points.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CodePoint {
    /// Function entry, before the entry block's first instruction.
    Entry,
    /// Before the instruction's opcodes: where its operands are prepared, and
    /// for a terminator, the moves into its successors.
    Before { block: BlockId, index: u32 },
    /// After the instruction's opcodes, where its results are stored.
    After { block: BlockId, index: u32 },
    /// Before the comparison of case `case` of the `br_table` instruction.
    Case {
        block: BlockId,
        index: u32,
        case: u32,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpillLocation {
    /// The word at this memory address.
    Memory(u32),
    /// This word slot of the function's dynamic frame.
    Frame(u32),
    /// Recomputed, not stored.
    Rematerialized,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrameLowering {
    /// No stable objects, objects at `base_word`, or a dynamic frame.
    pub stable: StableLowering,
    pub scratch_words: u32,
    pub stable_words: u32,
    /// The function's code enters and leaves a dynamic frame.
    pub lazy_frame: bool,
    /// The function's entry initializes the dynamic stack pointer at `0x80`:
    /// always, or only when it is unset (`checked`).
    pub dyn_sp_entry_init: Option<DynSpInitLowering>,
    /// The calls before which the code initializes the dynamic stack pointer.
    pub dyn_sp_init_calls: u32,
    /// Each call around which the code saves and restores the caller's
    /// scratch objects, as its block and its position in the block. What is
    /// saved where is not recorded.
    pub call_preserves: Vec<(BlockId, u32)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DynSpInitLowering {
    Always,
    Checked,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StableLowering {
    None,
    Abs { base_word: u32 },
    DynamicFrame,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MallocLowering {
    /// At this constant address.
    Fixed { base: u32 },
    /// At the free pointer, raised to `min_base`, or at `exact_base` when
    /// the free pointer is known; `update_free_ptr` if it moves the pointer.
    Heap {
        min_base: u32,
        exact_base: Option<u32>,
        update_free_ptr: bool,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CodeLabel {
    Block {
        func: String,
        block: BlockId,
    },
    Func(String),
    Unit(String),
    /// An instruction of the emitted code, which no IR names.
    Inst,
}
