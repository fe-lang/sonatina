use cranelift_entity::{
    entity_impl, packed_option::ReservedValue, EntityList, EntityRef, ListPool, PrimaryMap,
    SecondaryMap,
};
use indexmap::IndexMap;
use ir::module::FuncRef;
use ir::Block;
use smallvec::SmallVec;
use sonatina_ir as ir;
use std::collections::BTreeMap;
use std::fmt;

#[derive(Debug, Copy, Clone)]
pub enum Label {
    Insn(VCodeInst),
    Block(ir::Block),
    Function(FuncRef),
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct VCodeInst(pub u32);
entity_impl!(VCodeInst);

#[derive(Default)]
pub struct VCode<Op> {
    pub insts: PrimaryMap<VCodeInst, Op>,
    pub inst_ir: SecondaryMap<VCodeInst, Option<ir::Insn>>,

    /// Immediate bytes for PUSH* ops
    pub inst_imm_bytes: BTreeMap<VCodeInst, SmallVec<[u8; 8]>>,

    /// Instructions that contain label offsets that will need to updated
    /// when the bytecode is emitted
    pub jump_fixups: IndexMap<VCodeInst, Label>,

    // Or PrimaryMap<VCodeBlock, ..>?
    blocks: SecondaryMap<ir::Block, EntityList<VCodeInst>>,

    insts_pool: ListPool<VCodeInst>,
}

impl<Op> VCode<Op> {
    pub fn add_inst_to_block(
        &mut self,
        op: Op,
        source_insn: Option<ir::Insn>,
        block: ir::Block,
    ) -> VCodeInst {
        let inst = self.insts.push(op);
        self.inst_ir[inst] = source_insn;
        self.blocks[block].push(inst, &mut self.insts_pool);
        inst
    }

    pub fn block_insns(&self, block: ir::Block) -> impl Iterator<Item = VCodeInst> + '_ {
        EntityIter {
            list: &self.blocks[block],
            pool: &self.insts_pool,
            next: 0,
        }
    }

    // pub fn emit(self, alloc: &sonatina_stackalloc::Output)
}

impl<Op> fmt::Display for VCode<Op>
where
    Op: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for block in self.blocks.keys() {
            if self.block_insns(block).count() > 0 {
                writeln!(f, "block{}:", block.0)?;
            }
            for (idx, insn) in self.block_insns(block).enumerate() {
                write!(f, "    {:?}", self.insts[insn])?;
                if let Some(bytes) = self.inst_imm_bytes.get(&insn) {
                    write!(f, "  {bytes:?}")?;
                } else if let Some(label) = self.jump_fixups.get(&insn) {
                    match label {
                        Label::Block(Block(n)) => write!(f, "  `block{n}`"),
                        Label::Insn(insn) => {
                            let pos = self
                                .block_insns(block)
                                .position(|i| i == *insn)
                                .expect("Label::Insn must be in same block");
                            let offset: i32 = pos as i32 - idx as i32;
                            write!(f, "  `pc + ({offset})`")
                        }
                        Label::Function(func) => write!(f, "  {func:?}"),
                    }?;
                }
                writeln!(f)?;
            }
        }
        Ok(())
    }
}

struct EntityIter<'a, T>
where
    T: EntityRef + ReservedValue,
{
    list: &'a EntityList<T>,
    pool: &'a ListPool<T>,
    next: usize,
}

impl<'a, T> Iterator for EntityIter<'a, T>
where
    T: EntityRef + ReservedValue,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        let next = self.list.get(self.next, self.pool)?;
        self.next += 1;
        Some(next)
    }
}
