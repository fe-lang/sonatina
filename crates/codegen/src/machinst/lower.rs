use ir::Immediate;
use sonatina_ir as ir;

use super::vcode::{VCode, VCodeInst, VReg, VRegKind};

pub trait LowerBackend {
    type MInst;

    fn lower(&self, ctx: &mut Lower<Self::MInst>, inst: ir::Insn);
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
        let mut vcode = VCode::default();

        // Add vregs for all `Value`s
        for val in function.dfg.values.keys() {
            let reg = vcode.vregs.push(VRegKind::Value(val));
            vcode.value_regs[val] = reg;
        }

        Lower {
            function,
            vcode,
            cur_insn: None,
            cur_block: None,
        }
    }

    pub fn lower<B: LowerBackend<MInst = Op>>(mut self, backend: &B) -> CodegenResult<VCode<Op>> {
        for block in self.function.layout.iter_block() {
            // XXX insert JUMPDEST op if block has preds
            self.cur_block = Some(block);

            for insn in self.function.layout.iter_insn(block) {
                self.cur_insn = Some(insn);
                // TODO: skip if insn isn't used and doesn't have side-effects

                backend.lower(&mut self, insn);
            }
        }

        Ok(self.vcode)
    }

    pub fn push(&mut self, op: Op, inputs: &[VReg], outputs: &[VReg]) -> VCodeInst {
        self.vcode
            .add_inst_to_block(op, inputs, outputs, self.cur_insn, self.cur_block.unwrap())
    }

    pub fn add_jump_fixup_inst(&mut self, inst: VCodeInst, dest: ir::Block) {
        self.vcode.jump_fixups.push((inst, dest));
    }

    // XXX remove?
    pub fn temp_reg(&mut self, ty: ir::Type) -> VReg {
        self.vcode.vregs.push(VRegKind::Temp(ty))
    }

    pub fn value_reg(&self, val: ir::Value) -> VReg {
        self.vcode.value_regs[val]
    }

    // XXX remove?
    pub fn jumpdest_reg(&mut self, block: ir::Block) -> VReg {
        self.vcode.vregs.push(VRegKind::JumpDest(block))
    }

    pub fn insn_result_reg(&self, insn: ir::Insn) -> Option<VReg> {
        let val = self.function.dfg.insn_result(insn)?;
        Some(self.value_reg(val))
    }

    pub fn insn_data(&self, insn: ir::Insn) -> &ir::InsnData {
        self.function.dfg.insn_data(insn)
    }

    pub fn value_imm(&self, value: ir::Value) -> Option<Immediate> {
        self.function.dfg.value_imm(value)
    }
}
