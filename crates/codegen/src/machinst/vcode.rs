use cranelift_entity::{entity_impl, EntityList, ListPool, PrimaryMap, SecondaryMap};
use sonatina_ir as ir;

// TODO: move to reg/stackalloc crate?
#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct VReg(pub u32);
cranelift_entity::entity_impl!(VReg);

impl VReg {
    pub fn is_invalid(&self) -> bool {
        *self == VReg::default()
    }
}

impl Default for VReg {
    fn default() -> Self {
        VReg(u32::MAX)
    }
}

pub enum VRegKind {
    Value(ir::Value),
    Temp(ir::Type),
    JumpDest(ir::Block),
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct VCodeInst(pub u32);
entity_impl!(VCodeInst);

#[derive(Default)]
pub struct VCode<Op> {
    pub insts: PrimaryMap<VCodeInst, Op>,
    pub inst_inputs: SecondaryMap<VCodeInst, EntityList<VReg>>,
    pub inst_outputs: SecondaryMap<VCodeInst, EntityList<VReg>>,
    pub inst_ir: SecondaryMap<VCodeInst, Option<ir::Insn>>,

    pub jump_fixups: Vec<(VCodeInst, ir::Block)>,

    // Or PrimaryMap<VCodeBlock, ..>?
    blocks: SecondaryMap<ir::Block, EntityList<VCodeInst>>,

    /// Virtual registers
    pub vregs: PrimaryMap<VReg, VRegKind>,
    /// Reverse map to lookup register for a value
    pub value_regs: SecondaryMap<ir::Value, VReg>,

    insts_pool: ListPool<VCodeInst>,
    vregs_pool: ListPool<VReg>,
}

impl<Op> VCode<Op> {
    pub fn add_inst_to_block(
        &mut self,
        op: Op,
        inputs: &[VReg],
        outputs: &[VReg],
        source_insn: Option<ir::Insn>,
        block: ir::Block,
    ) -> VCodeInst {
        let inst = self.insts.push(op);
        self.inst_inputs[inst] = EntityList::from_slice(inputs, &mut self.vregs_pool);
        self.inst_outputs[inst] = EntityList::from_slice(outputs, &mut self.vregs_pool);
        self.inst_ir[inst] = source_insn;
        self.blocks[block].push(inst, &mut self.insts_pool);
        inst
    }

    // pub fn emit(self, alloc: &sonatina_stackalloc::Output)
}
