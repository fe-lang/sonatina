use super::vcode::{Label, VCode, VCodeInst};
use crate::stackalloc::Allocator;
use ir::Immediate;
use sonatina_ir as ir;

pub trait LowerBackend {
    type MInst;

    fn lower(&self, ctx: &mut Lower<Self::MInst>, alloc: &mut dyn Allocator, inst: ir::Insn);
    // -> Option<InstOutput> == SmallVec<[ValueRegs<Reg>; 2]>
}

#[derive(Debug)]
pub struct CodegenError {}
pub type CodegenResult<T> = Result<T, CodegenError>;

pub struct Lower<'a, Op> {
    function: &'a ir::Function,
    vcode: VCode<Op>,

    cur_insn: Option<ir::Insn>,
    cur_block: Option<ir::Block>,
}

impl<'a, Op: Default> Lower<'a, Op> {
    pub fn new(function: &'a ir::Function) -> Self {
        Lower {
            function,
            vcode: VCode::default(),
            cur_insn: None,
            cur_block: None,
        }
    }

    pub fn lower<B: LowerBackend<MInst = Op>>(
        mut self,
        backend: &B,
        alloc: &mut dyn Allocator,
    ) -> CodegenResult<VCode<Op>> {
        for block in self.function.layout.iter_block() {
            // XXX insert JUMPDEST op if block has preds
            self.cur_block = Some(block);

            for insn in self.function.layout.iter_insn(block) {
                self.cur_insn = Some(insn);
                // TODO: skip if insn isn't used and doesn't have side-effects

                backend.lower(&mut self, alloc, insn);
            }
        }

        Ok(self.vcode)
    }

    pub fn push(&mut self, op: Op) -> VCodeInst {
        self.vcode
            .add_inst_to_block(op, self.cur_insn, self.cur_block.unwrap())
    }

    pub fn push_with_imm(&mut self, op: Op, bytes: &[u8]) {
        let i = self.push(op);
        self.add_immediate(i, bytes);
    }

    pub fn next_insn(&self) -> VCodeInst {
        self.vcode.insts.next_key()
    }

    pub fn add_immediate(&mut self, inst: VCodeInst, bytes: &[u8]) {
        self.vcode.inst_imm_bytes.insert(inst, bytes.into());
    }

    pub fn add_jump_fixup_inst(&mut self, inst: VCodeInst, dest: Label) {
        self.vcode.jump_fixups.insert(inst, dest);
    }

    pub fn insn_data(&self, insn: ir::Insn) -> &ir::InsnData {
        self.function.dfg.insn_data(insn)
    }

    pub fn value_imm(&self, value: ir::Value) -> Option<Immediate> {
        self.function.dfg.value_imm(value)
    }

    pub fn insn_result(&self, insn: ir::Insn) -> Option<ir::Value> {
        self.function.dfg.insn_result(insn)
    }

    pub fn insn_block(&self, insn: ir::Insn) -> ir::Block {
        self.function.layout.insn_block(insn)
    }
}
