use std::{fmt, io, ops::IndexMut};

use cranelift_entity::SecondaryMap;
use indexmap::IndexMap;
use smallvec::SmallVec;
use sonatina_ir::{
    BlockId, Module, U256,
    ir_writer::{DebugProvider, FuncWriteCtx, FunctionSignature, InstStatement, IrWrite},
    module::FuncRef,
};

use super::{
    lower::{FixupUpdate, SectionCodeUnit},
    vcode::{Label, LabelId, SectionCodeUnitId, SymFixup, VCode, VCodeFixup, VCodeInst},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LayoutError {
    MissingFunctionOffset(FuncRef),
    MissingSectionUnitOffset(SectionCodeUnitId),
}

impl std::fmt::Display for LayoutError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingFunctionOffset(func) => {
                write!(
                    f,
                    "missing layout offset for function label target {func:?}"
                )
            }
            Self::MissingSectionUnitOffset(unit) => {
                write!(
                    f,
                    "missing layout offset for section helper label target {unit:?}"
                )
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CodeUnitOwner {
    Function(FuncRef),
    SectionUnit(SectionCodeUnitId),
}

impl fmt::Display for CodeUnitOwner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Function(func) => write!(f, "function {func:?}"),
            Self::SectionUnit(unit) => write!(f, "section helper {}", unit.0),
        }
    }
}

pub struct ObjectLayout<Op> {
    // TODO: data, suffix (solc metadata)
    _offset: u32,
    _size: u32,
    functions: IndexMap<FuncRef, FuncLayout<Op>>,
    section_units: IndexMap<SectionCodeUnitId, SectionUnitLayout<Op>>,
    func_offsets: SecondaryMap<FuncRef, u32>,
    section_unit_offsets: SecondaryMap<SectionCodeUnitId, u32>,
}

impl<Op> ObjectLayout<Op> {
    pub fn new(
        funcs: Vec<(FuncRef, VCode<Op>, Vec<BlockId>)>,
        section_units: Vec<SectionCodeUnit<Op>>,
        mut offset: u32,
    ) -> Self {
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
        let mut section_unit_offsets = SecondaryMap::default();
        let section_units = section_units
            .into_iter()
            .map(|unit| {
                section_unit_offsets[unit.id] = offset;
                let layout = FuncLayout::new(unit.vcode, unit.block_order, offset);
                offset += layout.size;
                (
                    unit.id,
                    SectionUnitLayout {
                        name: unit.name,
                        layout,
                    },
                )
            })
            .collect();

        Self {
            _offset: start,
            _size: offset - start,
            functions,
            section_units,
            func_offsets,
            section_unit_offsets,
        }
    }

    pub fn resize(
        &mut self,
        update_opcode_with_label: &mut impl FnMut(&mut Op, u32) -> SmallVec<[u8; 4]>,
        update_opcode_with_immediate_bytes: &mut impl FnMut(&mut Op, &mut SmallVec<[u8; 8]>),
        mut offset: u32,
    ) -> Result<bool, LayoutError> {
        let mut did_change = false;
        for (funcref, layout) in self.functions.iter_mut() {
            did_change |= layout.resize(
                update_opcode_with_label,
                update_opcode_with_immediate_bytes,
                offset,
                &self.func_offsets,
                &self.section_unit_offsets,
            )?;
            self.func_offsets[*funcref] = offset;
            offset += layout.size;
        }
        for (unit_id, unit) in self.section_units.iter_mut() {
            did_change |= unit.layout.resize(
                update_opcode_with_label,
                update_opcode_with_immediate_bytes,
                offset,
                &self.func_offsets,
                &self.section_unit_offsets,
            )?;
            self.section_unit_offsets[*unit_id] = offset;
            offset += unit.layout.size;
        }
        did_change |= update(&mut self._size, offset - self._offset);
        Ok(did_change)
    }

    pub fn emit(
        &self,
        emit_opcode: &mut impl FnMut(&Op, &mut Vec<u8>),
        emit_immediate_bytes: &mut impl FnMut(&[u8], &mut Vec<u8>),
        emit_label: &mut impl FnMut(u32, &mut Vec<u8>),
        buf: &mut Vec<u8>,
    ) {
        for layout in self.functions.values() {
            layout.emit(emit_opcode, emit_immediate_bytes, emit_label, buf);
        }
        for unit in self.section_units.values() {
            unit.layout
                .emit(emit_opcode, emit_immediate_bytes, emit_label, buf);
        }
    }

    pub(crate) fn func_offset(&self, func: FuncRef) -> u32 {
        self.func_offsets[func]
    }

    pub(crate) fn func_size(&self, func: FuncRef) -> Option<u32> {
        self.functions.get(&func).map(|layout| layout.size)
    }

    pub(crate) fn func_layout(&self, func: FuncRef) -> Option<&FuncLayout<Op>> {
        self.functions.get(&func)
    }

    pub(crate) fn code_end(&self) -> u32 {
        self._offset + self._size
    }

    pub(crate) fn section_units(&self) -> &IndexMap<SectionCodeUnitId, SectionUnitLayout<Op>> {
        &self.section_units
    }

    pub(crate) fn apply_sym_fixups<E>(
        &mut self,
        mut apply: impl FnMut(
            CodeUnitOwner,
            &mut VCode<Op>,
            VCodeInst,
            &SymFixup,
        ) -> Result<FixupUpdate, E>,
    ) -> Result<bool, E> {
        let mut layout_changed = false;
        for (func, layout) in self.functions.iter_mut() {
            layout_changed |= apply_sym_fixups_in_vcode(
                CodeUnitOwner::Function(*func),
                &mut layout.vcode,
                &mut apply,
            )?;
        }
        for (unit_id, unit) in self.section_units.iter_mut() {
            layout_changed |= apply_sym_fixups_in_vcode(
                CodeUnitOwner::SectionUnit(*unit_id),
                &mut unit.layout.vcode,
                &mut apply,
            )?;
        }
        Ok(layout_changed)
    }
}

pub struct SectionUnitLayout<Op> {
    name: String,
    layout: FuncLayout<Op>,
}

impl<Op> SectionUnitLayout<Op> {
    pub(crate) fn name(&self) -> &str {
        &self.name
    }

    pub(crate) fn layout(&self) -> &FuncLayout<Op> {
        &self.layout
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
            let block_size = vcode
                .blocks
                .get(*b)
                .map(|block| block.len(&vcode.insts_pool) as u32)
                .unwrap_or(0);
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
        update_opcode_with_label: &mut impl FnMut(&mut Op, u32) -> SmallVec<[u8; 4]>,
        update_opcode_with_immediate_bytes: &mut impl FnMut(&mut Op, &mut SmallVec<[u8; 8]>),
        mut offset: u32,
        fn_offsets: &SecondaryMap<FuncRef, u32>,
        section_unit_offsets: &SecondaryMap<SectionCodeUnitId, u32>,
    ) -> Result<bool, LayoutError> {
        let mut did_change = update(&mut self.offset, offset);

        for block in self.block_order.iter().copied() {
            did_change |= update(self.block_offsets.index_mut(block), offset);

            let block_insts = self.vcode.blocks[block].as_slice(&self.vcode.insts_pool);
            for insn in block_insts {
                did_change |= update(self.insn_offsets.index_mut(*insn), offset);
                offset += std::mem::size_of::<Op>() as u32;

                if let Some((_, fixup)) = self.vcode.fixups.get(*insn)
                    && let VCodeFixup::Label(label) = fixup
                {
                    let address = match self.vcode.labels[*label] {
                        Label::Block(b) => self.block_offsets[b],
                        Label::Function(f) => fn_offsets
                            .get(f)
                            .copied()
                            .ok_or(LayoutError::MissingFunctionOffset(f))?,
                        Label::SectionCodeUnit(unit) => section_unit_offsets
                            .get(unit)
                            .copied()
                            .ok_or(LayoutError::MissingSectionUnitOffset(unit))?,
                        Label::Insn(i) => self.insn_offsets[i],
                    };
                    did_change |= update(self.label_targets.index_mut(*label), address);

                    let label_bytes =
                        update_opcode_with_label(&mut self.vcode.insts[*insn], address);
                    offset += label_bytes.len() as u32;
                }

                if let Some((_, bytes)) = self.vcode.inst_imm_bytes.get_mut(*insn) {
                    update_opcode_with_immediate_bytes(&mut self.vcode.insts[*insn], bytes);
                    offset += bytes.len() as u32;
                }
            }
        }
        did_change |= update(&mut self.size, offset - self.offset);
        Ok(did_change)
    }

    fn emit(
        &self,
        emit_opcode: &mut impl FnMut(&Op, &mut Vec<u8>),
        emit_immediate_bytes: &mut impl FnMut(&[u8], &mut Vec<u8>),
        emit_label: &mut impl FnMut(u32, &mut Vec<u8>),
        buf: &mut Vec<u8>,
    ) {
        for block in self.block_order.iter().copied() {
            for insn in self.vcode.block_insns(block) {
                emit_opcode(&self.vcode.insts[insn], buf);
                if let Some((_, fixup)) = self.vcode.fixups.get(insn)
                    && let VCodeFixup::Label(label) = fixup
                {
                    let address = self.label_targets[*label];
                    emit_label(address, buf); // xxx emit_address_bytes
                }

                if let Some((_, bytes)) = self.vcode.inst_imm_bytes.get(insn) {
                    emit_immediate_bytes(bytes, buf);
                }
            }
        }
    }

    pub(crate) fn block_order(&self) -> &[BlockId] {
        &self.block_order
    }

    pub(crate) fn block_insns(&self, block: BlockId) -> impl Iterator<Item = VCodeInst> + '_ {
        self.vcode.block_insns(block)
    }

    pub(crate) fn insn_offset(&self, insn: VCodeInst) -> u32 {
        self.insn_offsets[insn]
    }

    pub(crate) fn vcode(&self) -> &VCode<Op> {
        &self.vcode
    }

    pub(crate) fn end(&self) -> u32 {
        self.offset + self.size
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
        for unit in self.section_units.values() {
            unit.layout.write_synthetic(w, &unit.name)?;
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
                } else if let Some((_, fixup)) = self.vcode.fixups.get(insn)
                    && let VCodeFixup::Label(label) = fixup
                {
                    write!(w, " {}", self.label_targets[*label])?;
                    match self.vcode.labels[*label] {
                        Label::Block(BlockId(n)) => write!(w, " (block{n})")?,
                        Label::Insn(_) => {}
                        Label::Function(func) => write!(w, " ({func:?})")?,
                        Label::SectionCodeUnit(unit) => write!(w, " (section_unit{})", unit.0)?,
                    };
                }

                if let Some(ir) = self.vcode.inst_ir[insn].expand()
                    && cur_ir != Some(ir)
                {
                    cur_ir = Some(ir);
                    write!(w, "  // ")?;
                    InstStatement(ir).write(w, ctx)?;
                }
                writeln!(w)?;
            }
        }
        Ok(())
    }
}

impl<Op> FuncLayout<Op>
where
    Op: std::fmt::Debug,
{
    pub(crate) fn write_synthetic<W>(&self, w: &mut W, name: &str) -> io::Result<()>
    where
        W: io::Write,
    {
        writeln!(w, "// synthetic section unit")?;
        writeln!(w, "{name}:")?;

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
                } else if let Some((_, fixup)) = self.vcode.fixups.get(insn)
                    && let VCodeFixup::Label(label) = fixup
                {
                    write!(w, " {}", self.label_targets[*label])?;
                    match self.vcode.labels[*label] {
                        Label::Block(BlockId(n)) => write!(w, " (block{n})")?,
                        Label::Insn(_) => {}
                        Label::Function(func) => write!(w, " ({func:?})")?,
                        Label::SectionCodeUnit(unit) => write!(w, " (section_unit{})", unit.0)?,
                    };
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

fn apply_sym_fixups_in_vcode<Op, E>(
    owner: CodeUnitOwner,
    vcode: &mut VCode<Op>,
    apply: &mut impl FnMut(
        CodeUnitOwner,
        &mut VCode<Op>,
        VCodeInst,
        &SymFixup,
    ) -> Result<FixupUpdate, E>,
) -> Result<bool, E> {
    let fixups = collect_sym_fixups(vcode);
    let mut layout_changed = false;
    for (inst, fixup) in fixups {
        layout_changed |= apply(owner, vcode, inst, &fixup)? == FixupUpdate::LayoutChanged;
    }
    Ok(layout_changed)
}

fn collect_sym_fixups<Op>(vcode: &VCode<Op>) -> Vec<(VCodeInst, SymFixup)> {
    let mut out = Vec::new();
    for (insn, fixup) in vcode.fixups.values() {
        let VCodeFixup::Sym(fixup) = fixup else {
            continue;
        };
        out.push((*insn, fixup.clone()));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        isa::evm::opcode::OpCode,
        machinst::vcode::{SymFixup, SymFixupKind},
    };
    use smallvec::smallvec;
    use sonatina_ir::inst::data::SymbolRef;

    #[test]
    fn resize_rejects_missing_function_label_target() {
        let block = BlockId(0);
        let mut vcode = VCode::<OpCode>::default();
        let push = vcode.add_inst_to_block(OpCode::PUSH1, None, block);
        let label = vcode.labels.push(Label::Function(FuncRef::from_u32(1)));
        vcode.fixups.insert((push, VCodeFixup::Label(label)));
        vcode.add_inst_to_block(OpCode::JUMP, None, block);

        let mut layout =
            ObjectLayout::new(vec![(FuncRef::from_u32(0), vcode, vec![block])], vec![], 0);
        let err = layout
            .resize(&mut |_, _| SmallVec::new(), &mut |_, _| {}, 0)
            .expect_err("missing function label target must fail cleanly");
        assert_eq!(
            err,
            LayoutError::MissingFunctionOffset(FuncRef::from_u32(1))
        );
    }

    #[test]
    fn apply_sym_fixups_visits_function_and_section_unit_fixups() {
        let block = BlockId(0);
        let func = FuncRef::from_u32(0);
        let unit = SectionCodeUnitId(0);
        let gv = sonatina_ir::GlobalVariableRef::from_u32(0);

        let mut func_vcode = VCode::<OpCode>::default();
        let func_fixup = func_vcode.add_inst_to_block(OpCode::PUSH0, None, block);
        func_vcode.inst_imm_bytes.insert((func_fixup, smallvec![]));
        func_vcode.fixups.insert((
            func_fixup,
            VCodeFixup::Sym(SymFixup {
                kind: SymFixupKind::Addr,
                sym: SymbolRef::Global(gv),
            }),
        ));

        let mut unit_vcode = VCode::<OpCode>::default();
        let unit_fixup = unit_vcode.add_inst_to_block(OpCode::PUSH0, None, block);
        unit_vcode.inst_imm_bytes.insert((unit_fixup, smallvec![]));
        unit_vcode.fixups.insert((
            unit_fixup,
            VCodeFixup::Sym(SymFixup {
                kind: SymFixupKind::Size,
                sym: SymbolRef::Global(gv),
            }),
        ));

        let mut layout = ObjectLayout::new(
            vec![(func, func_vcode, vec![block])],
            vec![SectionCodeUnit {
                id: unit,
                name: "__helper".to_string(),
                vcode: unit_vcode,
                block_order: vec![block],
            }],
            0,
        );

        let mut visited = Vec::new();
        let layout_changed = layout
            .apply_sym_fixups(|owner, _, inst, fixup| {
                visited.push((owner, inst, fixup.kind.clone()));
                Ok::<_, ()>(FixupUpdate::Unchanged)
            })
            .expect("traversal should not fail");

        assert!(!layout_changed);
        assert_eq!(
            visited,
            vec![
                (
                    CodeUnitOwner::Function(func),
                    func_fixup,
                    SymFixupKind::Addr
                ),
                (
                    CodeUnitOwner::SectionUnit(unit),
                    unit_fixup,
                    SymFixupKind::Size,
                ),
            ]
        );
    }
}
