use cranelift_entity::packed_option::ReservedValue;
use sonatina_ir::{module::FuncRef, BlockId, Insn, Layout};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProgramCounter {
    pub func_ref: FuncRef,
    pub insn: Insn,
}

impl ReservedValue for ProgramCounter {
    fn reserved_value() -> Self {
        let func_ref = FuncRef::reserved_value();
        let insn = Insn::reserved_value();
        ProgramCounter { func_ref, insn }
    }

    fn is_reserved_value(&self) -> bool {
        self.func_ref == FuncRef::reserved_value() && self.insn == Insn::reserved_value()
    }
}

impl ProgramCounter {
    pub fn new(entry_func: FuncRef, layout: &Layout) -> Self {
        let entry = layout.entry_block().unwrap();
        let insn = layout.first_inst_of(entry).unwrap();

        Self {
            func_ref: entry_func,
            insn,
        }
    }

    pub fn call(&mut self, callee_ref: FuncRef, callee_layout: &Layout) {
        *self = ProgramCounter::new(callee_ref, callee_layout)
    }

    pub fn next_insn(&mut self, layout: &Layout) {
        self.insn = layout.next_inst_of(self.insn).unwrap();
    }

    pub fn branch_to(&mut self, block: BlockId, layout: &Layout) {
        self.insn = layout.first_inst_of(block).unwrap();
    }

    pub fn resume_frame_at(&mut self, ret_addr: Self) {
        let ProgramCounter { func_ref, insn } = ret_addr;
        self.func_ref = func_ref;
        self.insn = insn;
    }
}
