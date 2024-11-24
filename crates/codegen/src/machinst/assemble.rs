use std::{io, ops::IndexMut};

use cranelift_entity::SecondaryMap;
use indexmap::IndexMap;
use sonatina_ir::{
    ir_writer::{DebugProvider, FuncWriteCtx, FunctionSignature, InstStatement, IrWrite},
    module::FuncRef,
    BlockId, Module, U256,
};

use super::{
    lower::LowerBackend,
    vcode::{Label, LabelId, VCode, VCodeInst},
};

pub struct ObjectLayout<Op> {
    // TODO: data, suffix (solc metadata)
    _offset: u32,
    _size: u32,
    functions: IndexMap<FuncRef, FuncLayout<Op>>,
    func_offsets: SecondaryMap<FuncRef, u32>,
}

impl<Op> ObjectLayout<Op> {
    pub fn new(funcs: Vec<(FuncRef, VCode<Op>, Vec<BlockId>)>, mut offset: u32) -> Self {
        let start = offset;

        let mut func_offsets = SecondaryMap::with_capacity(funcs.len());
        let functions = funcs
            .into_iter()
            .map(|(f, vcode, block_order)| {
                func_offsets[f] = offset;
                let layout = FuncLayout::new(vcode, block_order, offset);
                offset += layout.size;
                (f, layout)
            })
            .collect();

        Self {
            _offset: start,
            _size: offset - start,
            functions,
            func_offsets,
        }
    }

    pub fn resize(&mut self, backend: &impl LowerBackend<MInst = Op>, mut offset: u32) -> bool {
        let mut did_change = false;
        for (funcref, layout) in self.functions.iter_mut() {
            did_change |= layout.resize(backend, offset, &self.func_offsets);
            self.func_offsets[*funcref] = offset;
            offset += layout.size;
        }
        did_change
    }

    pub fn emit(&self, backend: &impl LowerBackend<MInst = Op>, buf: &mut Vec<u8>) {
        for layout in self.functions.values() {
            layout.emit(backend, buf);
        }
    }
}

pub struct FuncLayout<Op> {
    offset: u32,
    size: u32,
    vcode: VCode<Op>,
    block_order: Vec<BlockId>,
    block_offsets: SecondaryMap<BlockId, u32>,
    insn_offsets: SecondaryMap<VCodeInst, u32>,
    label_targets: SecondaryMap<LabelId, u32>,
}

impl<Op> FuncLayout<Op> {
    fn new(vcode: VCode<Op>, block_order: Vec<BlockId>, mut offset: u32) -> Self {
        let start = offset;

        // Rough block offsets, ignoring immediates and labels
        let mut block_offsets = SecondaryMap::default();
        for b in &block_order {
            block_offsets[*b] = offset;
            let block_size = vcode.blocks.get(*b).unwrap().len(&vcode.insts_pool) as u32;
            offset += block_size;
        }

        let imm_bytes: u32 = vcode
            .inst_imm_bytes
            .values()
            .map(|(_, bytes)| bytes.len() as u32)
            .sum();

        // Guess that each label is 2 bytes
        let label_bytes = 2 * vcode.labels.len() as u32;

        let size = offset - start + imm_bytes + label_bytes;

        Self {
            offset,
            size,
            vcode,
            block_order,
            block_offsets,
            insn_offsets: SecondaryMap::default(),
            label_targets: SecondaryMap::default(),
        }
    }

    fn resize(
        &mut self,
        backend: &impl LowerBackend<MInst = Op>,
        mut offset: u32,
        fn_offsets: &SecondaryMap<FuncRef, u32>,
    ) -> bool {
        let mut did_change = update(&mut self.offset, offset);

        for block in self.block_order.iter().copied() {
            did_change |= update(self.block_offsets.index_mut(block), offset);

            let block_insts = self.vcode.blocks[block].as_slice(&self.vcode.insts_pool);
            for insn in block_insts {
                did_change |= update(self.insn_offsets.index_mut(*insn), offset);
                offset += std::mem::size_of::<Op>() as u32;

                if let Some((_, label)) = self.vcode.label_uses.get(*insn) {
                    let address = match self.vcode.labels[*label] {
                        Label::Block(b) => self.block_offsets[b],
                        Label::Function(f) => fn_offsets[f],
                        Label::Insn(i) => self.insn_offsets[i],
                    };
                    did_change |= update(self.label_targets.index_mut(*label), address);

                    let label_bytes =
                        backend.update_opcode_with_label(&mut self.vcode.insts[*insn], address);
                    offset += label_bytes.len() as u32;
                }

                if let Some((_, bytes)) = self.vcode.inst_imm_bytes.get_mut(*insn) {
                    backend.update_opcode_with_immediate_bytes(&mut self.vcode.insts[*insn], bytes);
                    offset += bytes.len() as u32;
                }
            }
        }
        did_change |= update(&mut self.size, offset - self.offset);
        did_change
    }

    fn emit(&self, backend: &impl LowerBackend<MInst = Op>, buf: &mut Vec<u8>) {
        for block in self.block_order.iter().copied() {
            for insn in self.vcode.block_insns(block) {
                backend.emit_opcode(&self.vcode.insts[insn], buf);
                if let Some((_, label)) = self.vcode.label_uses.get(insn) {
                    let address = self.label_targets[*label];
                    backend.emit_label(address, buf); // xxx emit_address_bytes
                }

                if let Some((_, bytes)) = self.vcode.inst_imm_bytes.get(insn) {
                    backend.emit_immediate_bytes(bytes, buf);
                }
            }
        }
    }
}

impl<Op> ObjectLayout<Op>
where
    Op: std::fmt::Debug,
{
    pub fn print(
        &self,
        w: &mut impl std::io::Write,
        module: &Module,
        dbg: &dyn DebugProvider,
    ) -> std::io::Result<()> {
        for (funcref, layout) in self.functions.iter() {
            module.func_store.view(*funcref, |function| {
                let ctx = FuncWriteCtx::with_debug_provider(function, *funcref, dbg);
                layout.write(w, &ctx)
            })?;
        }
        Ok(())
    }
}

impl<Op> IrWrite<FuncWriteCtx<'_>> for FuncLayout<Op>
where
    Op: std::fmt::Debug,
{
    fn write<W>(&self, w: &mut W, ctx: &FuncWriteCtx) -> io::Result<()>
    where
        W: io::Write,
    {
        // Mostly copied from VCode::print

        write!(w, "// ")?;
        FunctionSignature.write(w, ctx)?;
        writeln!(w)?;
        ctx.module_ctx()
            .func_sig(ctx.func_ref, |sig| writeln!(w, "{}:", sig.name()))?;

        let mut cur_ir = None;
        for block in self.block_order.iter().copied() {
            writeln!(w, "  block{}:", block.0)?;
            for insn in self.vcode.block_insns(block) {
                write!(
                    w,
                    "{: >5}    {:?}",
                    self.insn_offsets[insn], self.vcode.insts[insn],
                )?;
                if let Some((_, bytes)) = self.vcode.inst_imm_bytes.get(insn) {
                    let mut be = [0; 32];
                    be[32 - bytes.len()..].copy_from_slice(bytes);
                    let imm = U256::from_big_endian(&be);
                    write!(w, " 0x{imm:x} ({imm})")?;
                } else if let Some((_, label)) = self.vcode.label_uses.get(insn) {
                    write!(w, " {}", self.label_targets[*label])?;
                    match self.vcode.labels[*label] {
                        Label::Block(BlockId(n)) => write!(w, " (block{n})")?,
                        Label::Insn(_) => {}
                        Label::Function(func) => write!(w, " ({func:?})")?,
                    };
                }

                if let Some(ir) = self.vcode.inst_ir[insn].expand() {
                    if cur_ir != Some(ir) {
                        cur_ir = Some(ir);
                        write!(w, "  // ")?;
                        InstStatement(ir).write(w, ctx)?;
                    }
                }
                writeln!(w)?;
            }
        }
        Ok(())
    }
}

fn update(val: &mut u32, to: u32) -> bool {
    let did_change = *val != to;
    *val = to;
    did_change
}
