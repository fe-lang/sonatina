use cranelift_entity::{
    EntityList, EntityRef, ListPool, PrimaryMap, SecondaryMap, SparseMap, SparseMapValue,
    entity_impl,
    packed_option::{PackedOption, ReservedValue},
};
use smallvec::SmallVec;
use sonatina_ir::{
    BlockId, InstId, U256,
    inst::data::SymbolRef,
    ir_writer::{FuncWriteCtx, FunctionSignature, InstStatement, IrWrite},
    module::FuncRef,
};
use std::{collections::HashSet, fmt, io};

// xxx offset reference graph?
//  fn call graph

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct LabelId(pub u32);
entity_impl!(LabelId);

#[derive(Debug, Copy, Clone)]
pub enum Label {
    Insn(VCodeInst),
    Block(BlockId),
    Function(FuncRef),
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct VCodeInst(pub u32);
entity_impl!(VCodeInst);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SymFixupKind {
    Addr,
    Size,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymFixup {
    pub kind: SymFixupKind,
    pub sym: SymbolRef,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VCodeFixup {
    Label(LabelId),
    Sym(SymFixup),
}

pub struct VCode<Op> {
    pub insts: PrimaryMap<VCodeInst, Op>,
    pub inst_ir: SecondaryMap<VCodeInst, PackedOption<InstId>>,

    /// Immediate bytes for PUSH* ops
    pub inst_imm_bytes: SparseMap<VCodeInst, (VCodeInst, SmallVec<[u8; 8]>)>,

    pub fixups: SparseMap<VCodeInst, (VCodeInst, VCodeFixup)>,

    pub labels: PrimaryMap<LabelId, Label>,

    pub blocks: SecondaryMap<BlockId, EntityList<VCodeInst>>,

    pub insts_pool: ListPool<VCodeInst>,
}

impl<Op> VCode<Op> {
    pub fn add_inst_to_block(
        &mut self,
        op: Op,
        source_insn: Option<InstId>,
        block: BlockId,
    ) -> VCodeInst {
        let inst = self.insts.push(op);
        self.inst_ir[inst] = source_insn.into();
        self.blocks[block].push(inst, &mut self.insts_pool);
        inst
    }

    pub fn block_insns(&self, block: BlockId) -> impl Iterator<Item = VCodeInst> + '_ {
        EntityIter {
            list: &self.blocks[block],
            pool: &self.insts_pool,
            next: 0,
        }
    }

    // pub fn emit(self, alloc: &sonatina_stackalloc::Output)
}

impl<Op> VCode<Op>
where
    Op: fmt::Debug,
{
    pub fn write_with_block_order<W>(
        &self,
        w: &mut W,
        ctx: &FuncWriteCtx,
        block_order: &[BlockId],
    ) -> io::Result<()>
    where
        W: io::Write,
    {
        write!(w, "// ")?;
        FunctionSignature.write(w, ctx)?;
        writeln!(w)?;
        ctx.module_ctx()
            .func_sig(ctx.func_ref, |sig| writeln!(w, "{}:", sig.name()))?;

        let mut cur_ir = None;
        let mut emitted_blocks = HashSet::new();

        let mut write_block = |block: BlockId, cur_ir: &mut Option<InstId>| -> io::Result<()> {
            let block_insts: Vec<_> = self.block_insns(block).collect();
            if block_insts.is_empty() {
                return Ok(());
            }

            writeln!(w, "  block{}:", block.0)?;
            for (idx, insn) in block_insts.iter().copied().enumerate() {
                write!(w, "    {:?}", self.insts[insn])?;
                if let Some((_, bytes)) = self.inst_imm_bytes.get(insn) {
                    let mut be = [0; 32];
                    be[32 - bytes.len()..].copy_from_slice(bytes);
                    let imm = U256::from_big_endian(&be);
                    write!(w, " 0x{imm:x} ({imm})")?;
                } else if let Some((_, fixup)) = self.fixups.get(insn)
                    && let VCodeFixup::Label(label) = fixup
                {
                    match self.labels[*label] {
                        Label::Block(BlockId(n)) => write!(w, " block{n}"),
                        Label::Insn(target_insn) => {
                            let pos = block_insts
                                .iter()
                                .position(|i| *i == target_insn)
                                .expect("Label::Insn must be in same block");
                            let offset: i32 = pos as i32 - idx as i32;
                            write!(w, " `pc + ({offset})`")
                        }
                        Label::Function(func) => write!(w, " {func:?}"),
                    }?;
                }

                if let Some(ir) = self.inst_ir[insn].expand()
                    && *cur_ir != Some(ir)
                {
                    *cur_ir = Some(ir);
                    write!(w, "  // ")?;
                    InstStatement(ir).write(w, ctx)?;
                }
                writeln!(w)?;
            }
            Ok(())
        };

        for &block in block_order {
            if self.blocks.get(block).is_none() || !emitted_blocks.insert(block) {
                continue;
            }
            write_block(block, &mut cur_ir)?;
        }

        Ok(())
    }
}

impl<Op> IrWrite<FuncWriteCtx<'_>> for VCode<Op>
where
    Op: fmt::Debug,
{
    fn write<W>(&self, w: &mut W, ctx: &FuncWriteCtx) -> std::io::Result<()>
    where
        W: io::Write,
    {
        let block_order: Vec<_> = self.blocks.keys().collect();
        self.write_with_block_order(w, ctx, &block_order)
    }
}

impl<Op> Default for VCode<Op> {
    fn default() -> Self {
        Self {
            insts: Default::default(),
            inst_ir: Default::default(),
            inst_imm_bytes: SparseMap::new(), // no `Default` impl
            fixups: SparseMap::new(),
            labels: PrimaryMap::default(),
            blocks: Default::default(),
            insts_pool: Default::default(),
        }
    }
}

impl<T> SparseMapValue<VCodeInst> for (VCodeInst, T) {
    fn key(&self) -> VCodeInst {
        self.0
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

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::{
        Linkage, Signature,
        builder::test_util::test_module_builder,
        ir_writer::{FuncWriteCtx, IrWrite},
    };

    fn write_with_ctx(
        vcode: &VCode<&'static str>,
        f: impl FnOnce(&VCode<&'static str>, &mut Vec<u8>, &FuncWriteCtx<'_>) -> io::Result<()>,
    ) -> String {
        let mb = test_module_builder();
        let func_ref = mb
            .declare_function(Signature::new_unit("test_func", Linkage::Public, &[]))
            .unwrap();
        let module = mb.build();

        module.func_store.view(func_ref, |func| {
            let ctx = FuncWriteCtx::new(func, func_ref);
            let mut out = Vec::new();
            f(vcode, &mut out, &ctx).unwrap();
            String::from_utf8(out).unwrap()
        })
    }

    #[test]
    fn write_with_block_order_only_prints_requested_blocks() {
        let mut vcode = VCode::default();
        vcode.add_inst_to_block("keep", None, BlockId(0));
        vcode.add_inst_to_block("drop", None, BlockId(1));

        let out = write_with_ctx(&vcode, |vcode, out, ctx| {
            vcode.write_with_block_order(out, ctx, &[BlockId(0)])
        });

        assert!(out.contains("  block0:\n"));
        assert!(!out.contains("  block1:\n"));
    }

    #[test]
    fn ir_write_still_prints_all_blocks() {
        let mut vcode = VCode::default();
        vcode.add_inst_to_block("keep", None, BlockId(0));
        vcode.add_inst_to_block("also_keep", None, BlockId(1));

        let out = write_with_ctx(&vcode, |vcode, out, ctx| vcode.write(out, ctx));

        assert!(out.contains("  block0:\n"));
        assert!(out.contains("  block1:\n"));
    }
}
