//! Aggregates, objects, constants, frames and the heap.
//!
//! The semantics follow the host-native backend. A struct or array value is the
//! address of an immutable snapshot in memory. `insert_value` and `obj.load`
//! make a new snapshot, `extract_value` of an aggregate is a view into its
//! source, and a function passes aggregates by address and returns one through
//! a buffer that its caller provides. `obj.alloc` is a slot of the frame:
//! the front end promises that no reference to it is used after the function
//! returns. The heap serves `mem.alloc.dynamic` and the external `malloc` and `free`.
//!
//! Frame slots are static: an instruction in a loop uses the same slot on every
//! iteration, as `alloca` does on the native target.

use sonatina_codegen::OptLevel;
use waffle::{Operator, Type as WType};

use sonatina_ir::{
    GlobalVariableRef, Immediate, InstId, InstSetExt, Type, U256, Value, ValueId,
    types::{CompoundType, EnumVariantRef},
};

use super::{
    Access, FunctionTranslator, Repr, V, align_up, emit_call, invalid, repr, type_name, unsupported,
};
use crate::{
    WasmError,
    arith::Int,
    memory::ALIGN,
    wide::{Limbs, Wide},
};

/// The size of the largest aggregate copied with loads and stores, which
/// are faster than `memory.copy` for small sizes. At `Os` every copy is a
/// `memory.copy`: it takes 10 bytes, and one load and store through a local
/// takes 14.
pub(super) fn inline_copy_bytes(opt_level: OptLevel) -> u32 {
    if opt_level == OptLevel::Os { 0 } else { 64 }
}

/// A value read from memory.
enum Loaded {
    One(V),
    Wide(Wide, Limbs),
}

impl FunctionTranslator<'_> {
    pub(super) fn layout_of(&self, ty: Type) -> Result<(u32, u32), WasmError> {
        let layout = |what: &str, result: Result<usize, _>| {
            let value = result.map_err(|error| {
                unsupported(format!(
                    "function `{}`: cannot lay out {} for its {what}: {error:?}",
                    self.name,
                    type_name(&self.module.ctx, ty)
                ))
            })?;
            u32::try_from(value).map_err(|_| {
                unsupported(format!(
                    "function `{}`: {} is too large for a 32-bit address space",
                    self.name,
                    type_name(&self.module.ctx, ty)
                ))
            })
        };
        Ok((
            layout("size", self.module.ctx.size_of(ty))?,
            layout("alignment", self.module.ctx.align_of(ty))?,
        ))
    }

    /// Reserve `size` bytes of the frame and return their offset from its base.
    pub(super) fn slot(&mut self, size: u32, align: u32) -> Result<u32, WasmError> {
        if self.sp.is_none() {
            return Err(invalid(format!(
                "function `{}` needs a frame but the module has no stack",
                self.name
            )));
        }
        if align > ALIGN {
            return Err(unsupported(format!(
                "function `{}`: storage aligned to {align} bytes; frames are aligned to {ALIGN}",
                self.name
            )));
        }
        let too_large = || {
            unsupported(format!(
                "function `{}`: the frame is too large for a 32-bit address space",
                self.name
            ))
        };
        let offset = align_up(self.frame, align.max(1)).ok_or_else(too_large)?;
        self.frame = offset.checked_add(size.max(1)).ok_or_else(too_large)?;
        Ok(offset)
    }

    /// The address of frame offset `offset`.
    pub(super) fn slot_address(&mut self, wb: waffle::Block, offset: u32) -> Result<V, WasmError> {
        let sp = self.sp.ok_or_else(|| {
            invalid(format!(
                "function `{}` needs a frame but the module has no stack",
                self.name
            ))
        })?;
        if offset == 0 {
            return Ok(sp);
        }
        let offset = self.emit(wb).c32(offset);
        Ok(self
            .emit(wb)
            .op(Operator::I32Add, &[sp, offset], WType::I32))
    }

    /// The end of the frame, which callees receive as their stack top.
    pub(super) fn frame_top(&self) -> Result<V, WasmError> {
        self.top.ok_or_else(|| {
            invalid(format!(
                "function `{}` calls a function that needs a stack but has none",
                self.name
            ))
        })
    }

    /// `address + offset`, in the wrapping arithmetic of 32-bit addresses.
    fn offset_address(&mut self, wb: waffle::Block, base: V, offset: u32) -> V {
        if offset == 0 {
            return base;
        }
        let offset = self.emit(wb).c32(offset);
        self.emit(wb)
            .op(Operator::I32Add, &[base, offset], WType::I32)
    }

    fn chunks(size: u32) -> impl Iterator<Item = (u32, Access)> {
        let mut offset = 0;
        std::iter::from_fn(move || {
            let access = match size - offset {
                0 => return None,
                1 => Access::Byte,
                2..=3 => Access::Half,
                4..=7 => Access::Word,
                _ => Access::Double,
            };
            let chunk = (offset, access);
            offset += access.bytes();
            Some(chunk)
        })
    }

    /// Copy `size` bytes. The ranges may overlap.
    pub(super) fn copy_bytes(&mut self, wb: waffle::Block, dst: V, src: V, size: u32) {
        if size == 0 {
            return;
        }
        if size <= self.inline_copy_bytes {
            // Read everything before writing anything.
            let mut loaded = Vec::new();
            for (offset, access) in Self::chunks(size) {
                let (op, ty) = access.load_u(self.memarg(access, offset));
                let value = self.body.add_op(wb, op, &[src], &[ty]);
                loaded.push((offset, access, value));
            }
            for (offset, access, value) in loaded {
                let op = access.store(self.memarg(access, offset));
                self.body.add_op(wb, op, &[dst, value], &[]);
            }
            return;
        }
        let length = self.emit(wb).c32(size);
        self.body.add_op(
            wb,
            Operator::MemoryCopy {
                dst_mem: self.memory,
                src_mem: self.memory,
            },
            &[dst, src, length],
            &[],
        );
    }

    fn fill_zero(&mut self, wb: waffle::Block, dst: V, size: u32) {
        if size == 0 {
            return;
        }
        let zero = self.emit(wb).c32(0);
        let length = self.emit(wb).c32(size);
        self.body.add_op(
            wb,
            Operator::MemoryFill { mem: self.memory },
            &[dst, zero, length],
            &[],
        );
    }

    /// An aggregate `undef` operand is storage filled with zero.
    pub(super) fn undef_aggregate(
        &mut self,
        wb: waffle::Block,
        id: ValueId,
        ty: Type,
    ) -> Result<V, WasmError> {
        let (size, align) = self.layout_of(ty)?;
        let slot = match self.undef_slots.get(&id) {
            Some(&slot) => slot,
            None => {
                let slot = self.slot(size, align)?;
                self.undef_slots.insert(id, slot);
                slot
            }
        };
        let address = self.slot_address(wb, slot)?;
        self.fill_zero(wb, address, size);
        Ok(address)
    }

    /// The access that moves a scalar or pointer type through memory.
    fn scalar_access(&self, op: &str, ty: Type) -> Result<Access, WasmError> {
        match repr(&self.module.ctx, ty) {
            Some(Repr::Int(Int::I1 | Int::I8)) => Ok(Access::Byte),
            Some(Repr::Int(Int::I16)) => Ok(Access::Half),
            Some(Repr::Int(Int::I32) | Repr::Pointer) => Ok(Access::Word),
            Some(Repr::Int(Int::I64)) => Ok(Access::Double),
            _ => Err(unsupported(format!(
                "function `{}`: `{op}` of {}; only integers, pointers and aggregates are \
                 stored in memory",
                self.name,
                type_name(&self.module.ctx, ty)
            ))),
        }
    }

    /// Read a scalar, a pointer or a 128- or 256-bit integer at `addr + offset`.
    fn load_value(
        &mut self,
        wb: waffle::Block,
        op: &str,
        ty: Type,
        addr: V,
        offset: u32,
    ) -> Result<Loaded, WasmError> {
        if let Some(wide) = Wide::from_type(ty) {
            let carried: Vec<V> = (0..wide.limbs())
                .map(|index| {
                    let memarg = self.memarg(Access::Double, offset + 8 * index as u32);
                    self.body.add_op(
                        wb,
                        Operator::I64Load { memory: memarg },
                        &[addr],
                        &[WType::I64],
                    )
                })
                .collect();
            let limbs = self.emit(wb).wide_from_carried(wide, &carried);
            return Ok(Loaded::Wide(wide, limbs));
        }
        let access = self.scalar_access(op, ty)?;
        let (load, carrier) = access.load_u(self.memarg(access, offset));
        let mut value = self.body.add_op(wb, load, &[addr], &[carrier]);
        if ty == Type::I1 {
            // Only the low bit of a stored byte is the value.
            value = self.emit(wb).canonicalize(Int::I1, value);
        }
        Ok(Loaded::One(value))
    }

    /// Write the value `id` of type `ty` at `addr + offset`.
    fn store_value(
        &mut self,
        wb: waffle::Block,
        op: &str,
        ty: Type,
        addr: V,
        offset: u32,
        id: ValueId,
    ) -> Result<(), WasmError> {
        if self.function.dfg.value_ty(id) != ty {
            return Err(invalid(format!(
                "function `{}`: `{op}` value does not have the stored type",
                self.name
            )));
        }
        match repr(&self.module.ctx, ty) {
            Some(Repr::Aggregate) => {
                let source = self.operand(wb, id)?;
                let (size, _) = self.layout_of(ty)?;
                let dest = self.offset_address(wb, addr, offset);
                self.copy_bytes(wb, dest, source, size);
            }
            Some(Repr::Wide(wide)) => {
                let limbs = self.wide_operand(wb, id)?;
                for (index, &limb) in limbs[..wide.limbs()].iter().enumerate() {
                    let memarg = self.memarg(Access::Double, offset + 8 * index as u32);
                    self.body.add_op(
                        wb,
                        Operator::I64Store { memory: memarg },
                        &[addr, limb],
                        &[],
                    );
                }
            }
            _ => {
                let access = self.scalar_access(op, ty)?;
                let value = self.operand(wb, id)?;
                let store = access.store(self.memarg(access, offset));
                self.body.add_op(wb, store, &[addr, value], &[]);
            }
        }
        Ok(())
    }

    /// Define the result of `inst_id` from a value read from memory.
    fn define_loaded(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        index: usize,
        ty: Type,
        loaded: Loaded,
    ) -> Result<(), WasmError> {
        match loaded {
            Loaded::One(value) => self.define(inst_id, index, value, ty),
            Loaded::Wide(wide, limbs) => self.define_wide(wb, inst_id, index, wide, limbs),
        }
    }

    /// A pointer-like operand: an address. An integer of any width is one too
    /// (Fe holds a raw pointer in a 256-bit integer); an integer address that
    /// does not fit in 32 bits traps.
    fn address_operand(
        &mut self,
        wb: &mut waffle::Block,
        op: &str,
        id: ValueId,
    ) -> Result<V, WasmError> {
        let ty = self.function.dfg.value_ty(id);
        if repr(&self.module.ctx, ty) == Some(Repr::Pointer) {
            return self.operand(*wb, id);
        }
        self.index32(wb, op, id, false)
    }

    /// An index, length or size operand as an `i32`, trapping if the value does
    /// not fit in 32 bits (in the signed range when `signed`).
    pub(super) fn index32(
        &mut self,
        wb: &mut waffle::Block,
        op: &str,
        id: ValueId,
        signed: bool,
    ) -> Result<V, WasmError> {
        let ty = self.function.dfg.value_ty(id);
        if let Some(wide) = Wide::from_type(ty) {
            let limbs = self.wide_operand(*wb, id)?;
            let exceeds = if signed {
                let limbs = self.emit(*wb).wide_sign_extend(wide, limbs);
                self.emit(*wb).wide_exceeds_i32(limbs)
            } else {
                self.emit(*wb).wide_exceeds_u32(limbs)
            };
            self.trap_if(wb, exceeds);
            return Ok(self
                .emit(*wb)
                .op(Operator::I32WrapI64, &[limbs[0]], WType::I32));
        }
        let int = self.int_ty(op, ty)?;
        let value = self.operand(*wb, id)?;
        if int.is_wide() {
            let exceeds = if signed {
                let narrow = self
                    .emit(*wb)
                    .op(Operator::I32WrapI64, &[value], WType::I32);
                let back = self
                    .emit(*wb)
                    .op(Operator::I64ExtendI32S, &[narrow], WType::I64);
                self.emit(*wb)
                    .op(Operator::I64Ne, &[back, value], WType::I32)
            } else {
                let shift = self.emit(*wb).c64(32);
                let high = self
                    .emit(*wb)
                    .op(Operator::I64ShrU, &[value, shift], WType::I64);
                let zero = self.emit(*wb).c64(0);
                self.emit(*wb)
                    .op(Operator::I64Ne, &[high, zero], WType::I32)
            };
            self.trap_if(wb, exceeds);
            return Ok(self
                .emit(*wb)
                .op(Operator::I32WrapI64, &[value], WType::I32));
        }
        Ok(self.emit(*wb).resize(int, Int::I32, signed, value))
    }

    /// `index * scale` as an offset: a constant if the index is one that
    /// `index32` accepts. Any other constant goes through `index32` too, so it
    /// traps when it is executed, as the same index computed at run time does.
    fn scaled_index(
        &mut self,
        wb: &mut waffle::Block,
        op: &str,
        id: ValueId,
        signed: bool,
        scale: u32,
    ) -> Result<Offset, WasmError> {
        let range = if signed {
            i128::from(i32::MIN)..=i128::from(i32::MAX)
        } else {
            0..=i128::from(u32::MAX)
        };
        if let Some(value) = self
            .function
            .dfg
            .value_imm(id)
            .and_then(|imm| immediate_value(imm, signed))
            .filter(|value| range.contains(value))
        {
            // The product wraps like the `i32.mul` of a run-time index.
            return Ok(Offset::Const((value * i128::from(scale)) as u32));
        }
        let index = self.index32(wb, op, id, signed)?;
        if scale == 1 {
            return Ok(Offset::Dynamic(index));
        }
        let scale = self.emit(*wb).c32(scale);
        Ok(Offset::Dynamic(self.emit(*wb).op(
            Operator::I32Mul,
            &[index, scale],
            WType::I32,
        )))
    }

    fn offset_overflow(&self, op: &str) -> WasmError {
        unsupported(format!(
            "function `{}`: `{op}` has an index outside the 32-bit address space",
            self.name
        ))
    }

    fn add_offset(&mut self, wb: waffle::Block, base: V, offset: Offset) -> V {
        match offset {
            Offset::Const(offset) => self.offset_address(wb, base, offset),
            Offset::Dynamic(offset) => {
                self.emit(wb)
                    .op(Operator::I32Add, &[base, offset], WType::I32)
            }
        }
    }

    fn constant_index(&self, op: &str, id: ValueId) -> Result<usize, WasmError> {
        self.function
            .dfg
            .value_imm(id)
            .and_then(|imm| imm.to_nonnegative_usize())
            .ok_or_else(|| {
                invalid(format!(
                    "function `{}`: `{op}` index must be a nonnegative constant",
                    self.name
                ))
            })
    }

    /// The offset and type of element `idx` of an aggregate, looking through
    /// object and constant references.
    fn element_offset(&self, aggregate: Type, idx: usize) -> Result<(u32, Type), WasmError> {
        let ctx = &self.module.ctx;
        if let Some((offset, ty)) = ctx.aggregate_elem_offset(aggregate, idx) {
            let offset = u32::try_from(offset).map_err(|_| {
                unsupported(format!(
                    "function `{}`: an aggregate offset is too large for a 32-bit address space",
                    self.name
                ))
            })?;
            return Ok((offset, ty));
        }
        if let Some(CompoundType::ObjRef(inner) | CompoundType::ConstRef(inner)) =
            aggregate.resolve_compound(ctx)
        {
            return self.element_offset(inner, idx);
        }
        Err(invalid(format!(
            "function `{}`: cannot compute the offset of element {idx} of {}",
            self.name,
            type_name(ctx, aggregate)
        )))
    }

    pub(super) fn mload(
        &mut self,
        wb: &mut waffle::Block,
        inst_id: InstId,
        op: &str,
        addr: ValueId,
        ty: Type,
    ) -> Result<(), WasmError> {
        let addr = self.address_operand(wb, op, addr)?;
        if repr(&self.module.ctx, ty) == Some(Repr::Aggregate) {
            return self.snapshot(*wb, inst_id, ty, addr, 0);
        }
        let loaded = self.load_value(*wb, op, ty, addr, 0)?;
        self.define_loaded(*wb, inst_id, 0, ty, loaded)
    }

    pub(super) fn mstore(
        &mut self,
        wb: &mut waffle::Block,
        op: &str,
        addr: ValueId,
        value: ValueId,
        ty: Type,
    ) -> Result<(), WasmError> {
        let addr = self.address_operand(wb, op, addr)?;
        self.store_value(*wb, op, ty, addr, 0, value)
    }

    /// Define the result of `inst_id` as a new copy of the aggregate at
    /// `source + offset`.
    fn snapshot(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        ty: Type,
        source: V,
        offset: u32,
    ) -> Result<(), WasmError> {
        let (size, align) = self.layout_of(ty)?;
        let slot = self.slot(size, align)?;
        let dest = self.slot_address(wb, slot)?;
        let source = self.offset_address(wb, source, offset);
        self.copy_bytes(wb, dest, source, size);
        self.define(inst_id, 0, dest, ty)
    }

    pub(super) fn memzero(
        &mut self,
        wb: &mut waffle::Block,
        op: &str,
        dest: ValueId,
        len: ValueId,
    ) -> Result<(), WasmError> {
        let dest = self.address_operand(wb, op, dest)?;
        let len = self.index32(wb, op, len, false)?;
        let zero = self.emit(*wb).c32(0);
        self.body.add_op(
            *wb,
            Operator::MemoryFill { mem: self.memory },
            &[dest, zero, len],
            &[],
        );
        Ok(())
    }

    /// `memcopy`: the ranges may overlap, as `memory.copy`'s may.
    pub(super) fn memcopy(
        &mut self,
        wb: &mut waffle::Block,
        op: &str,
        dest: ValueId,
        src: ValueId,
        len: ValueId,
    ) -> Result<(), WasmError> {
        let dest = self.address_operand(wb, op, dest)?;
        let src = self.address_operand(wb, op, src)?;
        let len = self.index32(wb, op, len, false)?;
        self.body.add_op(
            *wb,
            Operator::MemoryCopy {
                dst_mem: self.memory,
                src_mem: self.memory,
            },
            &[dest, src, len],
            &[],
        );
        Ok(())
    }

    pub(super) fn gep(
        &mut self,
        wb: &mut waffle::Block,
        inst_id: InstId,
        op: &str,
        values: &[ValueId],
    ) -> Result<(), WasmError> {
        let Some((&base_value, indices)) = values.split_first() else {
            return Err(invalid(format!(
                "function `{}`: `gep` needs a base pointer",
                self.name
            )));
        };
        let mut address = self.address_operand(wb, op, base_value)?;
        let mut current = self.function.dfg.value_ty(base_value);
        let mut constant = 0u32;
        for &index in indices {
            let Some(compound) = current.resolve_compound(&self.module.ctx) else {
                return Err(invalid(format!(
                    "function `{}`: `gep` indexes through {}",
                    self.name,
                    type_name(&self.module.ctx, current)
                )));
            };
            match compound {
                CompoundType::Ptr(elem) | CompoundType::Array { elem, .. } => {
                    let (size, _) = self.layout_of(elem)?;
                    match self.scaled_index(wb, op, index, true, size)? {
                        Offset::Const(offset) => constant = constant.wrapping_add(offset),
                        offset @ Offset::Dynamic(_) => {
                            address = self.add_offset(*wb, address, offset)
                        }
                    }
                    current = elem;
                }
                CompoundType::Struct(_) => {
                    let field = self.constant_index(op, index)?;
                    let (offset, field_ty) = self.element_offset(current, field)?;
                    constant = constant.wrapping_add(offset);
                    current = field_ty;
                }
                CompoundType::Func { .. }
                | CompoundType::Enum(_)
                | CompoundType::ObjRef(_)
                | CompoundType::ConstRef(_) => {
                    return Err(invalid(format!(
                        "function `{}`: `gep` indexes through {}",
                        self.name,
                        type_name(&self.module.ctx, current)
                    )));
                }
            }
        }
        let address = self.offset_address(*wb, address, constant);
        let ty = self.result_ty(inst_id)?;
        self.define(inst_id, 0, address, ty)
    }

    pub(super) fn alloca(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        ty: Type,
    ) -> Result<(), WasmError> {
        let (size, align) = self.layout_of(ty)?;
        let slot = self.slot(size, align)?;
        let address = self.slot_address(wb, slot)?;
        let result_ty = self.result_ty(inst_id)?;
        self.define(inst_id, 0, address, result_ty)
    }

    fn arena_alloc(&mut self, wb: waffle::Block, size: V) -> Result<V, WasmError> {
        let arena = self.arena.ok_or_else(|| {
            invalid(format!(
                "function `{}` allocates but the module has no arena",
                self.name
            ))
        })?;
        Ok(emit_call(&mut self.body, wb, arena, &[size], &[WType::I32])[0])
    }

    pub(super) fn mem_alloc_dynamic(
        &mut self,
        wb: &mut waffle::Block,
        inst_id: InstId,
        op: &str,
        size: ValueId,
    ) -> Result<(), WasmError> {
        let size = self.index32(wb, op, size, false)?;
        let address = self.arena_alloc(*wb, size)?;
        // The allocator returns null when it cannot meet the request, and the
        // instruction traps then.
        let failed = self.emit(*wb).op(Operator::I32Eqz, &[address], WType::I32);
        self.trap_if(wb, failed);
        let ty = self.result_ty(inst_id)?;
        self.define(inst_id, 0, address, ty)
    }

    pub(super) fn obj_alloc(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        ty: Type,
    ) -> Result<(), WasmError> {
        let (size, align) = self.layout_of(ty)?;
        let slot = self.slot(size, align)?;
        let address = self.slot_address(wb, slot)?;
        let result_ty = self.result_ty(inst_id)?;
        self.define(inst_id, 0, address, result_ty)
    }

    /// `obj.proj` and `const.proj`: the address of a field, by constant indices.
    pub(super) fn projection(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        op: &str,
        values: &[ValueId],
    ) -> Result<(), WasmError> {
        let Some((&base_value, indices)) = values.split_first() else {
            return Err(invalid(format!(
                "function `{}`: `{op}` needs a base value",
                self.name
            )));
        };
        let base = self.operand(wb, base_value)?;
        let mut current = self.function.dfg.value_ty(base_value);
        let mut offset = 0u32;
        for &index in indices {
            let index = self.constant_index(op, index)?;
            let (field_offset, ty) = self.element_offset(current, index)?;
            offset = offset.wrapping_add(field_offset);
            current = ty;
        }
        let address = self.offset_address(wb, base, offset);
        let ty = self.result_ty(inst_id)?;
        self.define(inst_id, 0, address, ty)
    }

    /// `obj.index` and `const.index`: the address of an array element. The
    /// index is not checked against the length; a program that needs the check
    /// compares first, as Fe does.
    pub(super) fn element_address(
        &mut self,
        wb: &mut waffle::Block,
        inst_id: InstId,
        op: &str,
        object: ValueId,
        index: ValueId,
    ) -> Result<(), WasmError> {
        let base = self.operand(*wb, object)?;
        let object_ty = self.function.dfg.value_ty(object);
        let elem = self.array_element(object_ty).ok_or_else(|| {
            invalid(format!(
                "function `{}`: `{op}` indexes {}, which is not an array",
                self.name,
                type_name(&self.module.ctx, object_ty)
            ))
        })?;
        let (size, _) = self.layout_of(elem)?;
        let offset = self.scaled_index(wb, op, index, false, size)?;
        let address = self.add_offset(*wb, base, offset);
        let ty = self.result_ty(inst_id)?;
        self.define(inst_id, 0, address, ty)
    }

    fn array_element(&self, ty: Type) -> Option<Type> {
        match ty.resolve_compound(&self.module.ctx)? {
            CompoundType::Array { elem, .. } => Some(elem),
            CompoundType::ObjRef(inner) | CompoundType::ConstRef(inner) => {
                self.array_element(inner)
            }
            _ => None,
        }
    }

    /// `obj.load`, which makes a copy of an aggregate, and `const.load`, which
    /// views the constant in place.
    pub(super) fn obj_load(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        object: ValueId,
        copy: bool,
    ) -> Result<(), WasmError> {
        let address = self.operand(wb, object)?;
        let ty = self.result_ty(inst_id)?;
        if repr(&self.module.ctx, ty) == Some(Repr::Aggregate) {
            if copy {
                return self.snapshot(wb, inst_id, ty, address, 0);
            }
            return self.define(inst_id, 0, address, ty);
        }
        let loaded = self.load_value(wb, "obj.load", ty, address, 0)?;
        self.define_loaded(wb, inst_id, 0, ty, loaded)
    }

    pub(super) fn obj_store(
        &mut self,
        wb: waffle::Block,
        object: ValueId,
        value: ValueId,
    ) -> Result<(), WasmError> {
        let address = self.operand(wb, object)?;
        let ty = self.function.dfg.value_ty(value);
        self.store_value(wb, "obj.store", ty, address, 0, value)
    }

    /// `obj.materialize.stack` and `.heap`: the object itself. Where it lives
    /// was decided at its allocation.
    pub(super) fn alias(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        object: ValueId,
    ) -> Result<(), WasmError> {
        let address = self.operand(wb, object)?;
        let ty = self.result_ty(inst_id)?;
        self.define(inst_id, 0, address, ty)
    }

    pub(super) fn const_ref(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        gv: GlobalVariableRef,
    ) -> Result<(), WasmError> {
        let address = *self.plan.globals.get(&gv).ok_or_else(|| {
            invalid(format!(
                "function `{}`: `const.ref` of a global variable that has no storage",
                self.name
            ))
        })?;
        let address = self.emit(wb).c32(address);
        let ty = self.result_ty(inst_id)?;
        self.define(inst_id, 0, address, ty)
    }

    pub(super) fn insert_value(
        &mut self,
        block: sonatina_ir::BlockId,
        wb: waffle::Block,
        inst_id: InstId,
        dest: ValueId,
        index: ValueId,
        value: ValueId,
    ) -> Result<(), WasmError> {
        let function = self.function;
        let result_ty = self.result_ty(inst_id)?;
        let (size, align) = self.layout_of(result_ty)?;
        // An insert result owns its storage. Its sole consumer can continue
        // construction in that storage without changing an observable SSA
        // snapshot. Stay in the same block: a use in a nested loop can execute
        // repeatedly for one definition. Other sources do not carry this
        // ownership guarantee.
        let reuse = function.dfg.value_inst(dest).is_some_and(|source_inst| {
            function.layout.inst_block(source_inst) == block
                && function.dfg.users(dest).copied().eq([inst_id])
                && matches!(
                    sonatina_ir::isa::native::inst_set()
                        .resolve_inst(function.dfg.inst(source_inst)),
                    sonatina_ir::inst::native::inst_set::NativeInstKind::InsertValue(_)
                )
        });
        let address = if reuse {
            self.operand(wb, dest)?
        } else {
            let slot = self.slot(size, align)?;
            let address = self.slot_address(wb, slot)?;
            if matches!(function.dfg.value(dest), Value::Undef { .. }) {
                self.fill_zero(wb, address, size);
            } else {
                let source = self.operand(wb, dest)?;
                self.copy_bytes(wb, address, source, size);
            }
            address
        };
        let idx = self.constant_index("insert_value", index)?;
        let (offset, elem_ty) = self.element_offset(result_ty, idx)?;
        if function.dfg.value_ty(value) != elem_ty {
            return Err(invalid(format!(
                "function `{}`: `insert_value` element type mismatch",
                self.name
            )));
        }
        self.store_value(wb, "insert_value", elem_ty, address, offset, value)?;
        self.define(inst_id, 0, address, result_ty)
    }

    pub(super) fn extract_value(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        dest: ValueId,
        index: ValueId,
    ) -> Result<(), WasmError> {
        let base = self.operand(wb, dest)?;
        let idx = self.constant_index("extract_value", index)?;
        let dest_ty = self.function.dfg.value_ty(dest);
        let (offset, elem_ty) = self.element_offset(dest_ty, idx)?;
        let result_ty = self.result_ty(inst_id)?;
        if result_ty != elem_ty {
            return Err(invalid(format!(
                "function `{}`: `extract_value` element type mismatch",
                self.name
            )));
        }
        if repr(&self.module.ctx, result_ty) == Some(Repr::Aggregate) {
            let view = self.offset_address(wb, base, offset);
            return self.define(inst_id, 0, view, result_ty);
        }
        let loaded = self.load_value(wb, "extract_value", result_ty, base, offset)?;
        self.define_loaded(wb, inst_id, 0, result_ty, loaded)
    }

    /// The offset and type of field `field` of `variant`.
    fn variant_field(
        &self,
        op: &str,
        variant: EnumVariantRef,
        field: usize,
    ) -> Result<(u32, Type), WasmError> {
        let enum_ty = Type::Compound(variant.enum_ty());
        let (offset, ty) = self
            .module
            .ctx
            .enum_variant_field_offset(enum_ty, variant.index() as usize, field)
            .ok_or_else(|| {
                invalid(format!(
                    "function `{}`: `{op}` names field {field} of {variant:?}, which it does not have",
                    self.name
                ))
            })?;
        let offset = u32::try_from(offset).map_err(|_| self.offset_overflow(op))?;
        Ok((offset, ty))
    }

    /// The integer type of the tag of `variant`'s enum.
    fn tag_ty(&self, op: &str, variant: EnumVariantRef) -> Result<Type, WasmError> {
        self.module
            .ctx
            .with_ty_store(|store| store.enum_data(variant.enum_ty()).map(|data| data.tag_ty()))
            .ok_or_else(|| invalid(format!("function `{}`: `{op}` of a non-enum", self.name)))
    }

    /// Write `variant`'s tag to the enum at `addr`.
    fn store_tag(
        &mut self,
        wb: waffle::Block,
        op: &str,
        addr: V,
        variant: EnumVariantRef,
    ) -> Result<(), WasmError> {
        let tag_ty = self.tag_ty(op, variant)?;
        let access = self.scalar_access(op, tag_ty)?;
        let tag = match access {
            Access::Double => self.emit(wb).c64(u64::from(variant.index())),
            _ => self.emit(wb).c32(variant.index()),
        };
        let store = access.store(self.memarg(access, 0));
        self.body.add_op(wb, store, &[addr, tag], &[]);
        Ok(())
    }

    /// Write `variant`'s fields `values` and then its tag to the enum at `addr`.
    fn store_variant(
        &mut self,
        wb: waffle::Block,
        op: &str,
        addr: V,
        variant: EnumVariantRef,
        values: &[ValueId],
    ) -> Result<(), WasmError> {
        for (field, &value) in values.iter().enumerate() {
            let (offset, ty) = self.variant_field(op, variant, field)?;
            self.store_value(wb, op, ty, addr, offset, value)?;
        }
        self.store_tag(wb, op, addr, variant)
    }

    /// `enum.make`: a new enum value in a slot of the frame. As on the native
    /// target, the bytes outside the variant are zero, not what an earlier
    /// frame left in the slot.
    pub(super) fn enum_make(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        variant: EnumVariantRef,
        values: &[ValueId],
    ) -> Result<(), WasmError> {
        let ty = self.result_ty(inst_id)?;
        let (size, align) = self.layout_of(ty)?;
        let slot = self.slot(size, align)?;
        let address = self.slot_address(wb, slot)?;
        self.fill_zero(wb, address, size);
        self.store_variant(wb, "enum.make", address, variant, values)?;
        self.define(inst_id, 0, address, ty)
    }

    pub(super) fn enum_write_variant(
        &mut self,
        wb: waffle::Block,
        object: ValueId,
        variant: EnumVariantRef,
        values: &[ValueId],
    ) -> Result<(), WasmError> {
        let address = self.operand(wb, object)?;
        self.store_variant(wb, "enum.write_variant", address, variant, values)
    }

    pub(super) fn enum_set_tag(
        &mut self,
        wb: waffle::Block,
        object: ValueId,
        variant: EnumVariantRef,
    ) -> Result<(), WasmError> {
        let address = self.operand(wb, object)?;
        self.store_tag(wb, "enum.set_tag", address, variant)
    }

    /// `enum.tag` of a value and `enum.get_tag` of an object: the tag at
    /// offset zero.
    pub(super) fn enum_tag(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        op: &str,
        source: ValueId,
    ) -> Result<(), WasmError> {
        let address = self.operand(wb, source)?;
        let ty = self.result_ty(inst_id)?;
        let loaded = self.load_value(wb, op, ty, address, 0)?;
        self.define_loaded(wb, inst_id, 0, ty, loaded)
    }

    pub(super) fn enum_is_variant(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        value: ValueId,
        variant: EnumVariantRef,
    ) -> Result<(), WasmError> {
        let op = "enum.is_variant";
        let address = self.operand(wb, value)?;
        let tag_ty = self.tag_ty(op, variant)?;
        let access = self.scalar_access(op, tag_ty)?;
        let Loaded::One(tag) = self.load_value(wb, op, tag_ty, address, 0)? else {
            unreachable!("a tag is a scalar")
        };
        let mut emit = self.emit(wb);
        let is_variant = match access {
            Access::Double => {
                let index = emit.c64(u64::from(variant.index()));
                emit.op(Operator::I64Eq, &[tag, index], WType::I32)
            }
            _ => {
                let index = emit.c32(variant.index());
                emit.op(Operator::I32Eq, &[tag, index], WType::I32)
            }
        };
        self.define(inst_id, 0, is_variant, Type::I1)
    }

    /// `enum.extract`: a field of a variant of an enum value. An aggregate field
    /// is a view into the enum, as `extract_value` gives.
    pub(super) fn enum_extract(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        value: ValueId,
        variant: EnumVariantRef,
        field: ValueId,
    ) -> Result<(), WasmError> {
        let op = "enum.extract";
        let base = self.operand(wb, value)?;
        let field = self.constant_index(op, field)?;
        let (offset, ty) = self.variant_field(op, variant, field)?;
        if self.result_ty(inst_id)? != ty {
            return Err(invalid(format!(
                "function `{}`: `{op}` field type mismatch",
                self.name
            )));
        }
        if repr(&self.module.ctx, ty) == Some(Repr::Aggregate) {
            let view = self.offset_address(wb, base, offset);
            return self.define(inst_id, 0, view, ty);
        }
        let loaded = self.load_value(wb, op, ty, base, offset)?;
        self.define_loaded(wb, inst_id, 0, ty, loaded)
    }

    /// `enum.proj`: the address of a field of a variant of an enum object.
    pub(super) fn enum_proj(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        object: ValueId,
        variant: EnumVariantRef,
        field: ValueId,
    ) -> Result<(), WasmError> {
        let op = "enum.proj";
        let base = self.operand(wb, object)?;
        let field = self.constant_index(op, field)?;
        let (offset, _) = self.variant_field(op, variant, field)?;
        let address = self.offset_address(wb, base, offset);
        let ty = self.result_ty(inst_id)?;
        self.define(inst_id, 0, address, ty)
    }

    /// `bitcast` between types of the same size. Scalars, pointers and
    /// references of the same size share one representation. Anything else
    /// goes through memory, as on the native target.
    pub(super) fn bitcast(
        &mut self,
        wb: &mut waffle::Block,
        inst_id: InstId,
        op: &str,
        from: ValueId,
        to_ty: Type,
    ) -> Result<(), WasmError> {
        let from_ty = self.function.dfg.value_ty(from);
        if let Some(wide) = Wide::from_type(from_ty)
            && from_ty == to_ty
        {
            let limbs = self.wide_operand(*wb, from)?;
            return self.define_wide(*wb, inst_id, 0, wide, limbs);
        }
        let ctx = &self.module.ctx;
        let from_repr = repr(ctx, from_ty);
        let to_repr = repr(ctx, to_ty);
        let (Some(from_repr), Some(to_repr)) = (from_repr, to_repr) else {
            let bad = if from_repr.is_none() { from_ty } else { to_ty };
            return Err(self.unsupported_type("`bitcast`", bad));
        };
        let (from_size, _) = self.layout_of(from_ty)?;
        let (to_size, to_align) = self.layout_of(to_ty)?;
        if from_size != to_size {
            return Err(invalid(format!(
                "function `{}`: `bitcast` between types of different sizes",
                self.name
            )));
        }
        let scalar = |representation| matches!(representation, Repr::Int(_) | Repr::Pointer);
        if scalar(from_repr) && scalar(to_repr) {
            // Scalars and pointers of the same size share one carrier. An `i1`
            // keeps only the low bit of an `i8`.
            let mut value = self.operand(*wb, from)?;
            if to_ty == Type::I1 && from_ty != Type::I1 {
                value = self.emit(*wb).canonicalize(Int::I1, value);
            }
            return self.define(inst_id, 0, value, to_ty);
        }
        // Make the source addressable, then read it back as the new type.
        let source = match from_repr {
            Repr::Aggregate => self.operand(*wb, from)?,
            _ => {
                let slot = self.slot(from_size, to_align.max(8))?;
                let address = self.slot_address(*wb, slot)?;
                self.store_value(*wb, op, from_ty, address, 0, from)?;
                address
            }
        };
        if to_repr == Repr::Aggregate {
            return self.snapshot(*wb, inst_id, to_ty, source, 0);
        }
        let loaded = self.load_value(*wb, op, to_ty, source, 0)?;
        self.define_loaded(*wb, inst_id, 0, to_ty, loaded)
    }
}

/// The offset of an address from its base: known, or computed at run time.
#[derive(Clone, Copy)]
enum Offset {
    Const(u32),
    Dynamic(V),
}

impl Access {
    fn bytes(self) -> u32 {
        1 << self.align()
    }

    /// The unsigned load of this width and the type of its result.
    fn load_u(self, memory: waffle::MemoryArg) -> (Operator, WType) {
        match self {
            Self::Byte => (Operator::I32Load8U { memory }, WType::I32),
            Self::Half => (Operator::I32Load16U { memory }, WType::I32),
            Self::Word => (Operator::I32Load { memory }, WType::I32),
            Self::Double => (Operator::I64Load { memory }, WType::I64),
        }
    }

    fn store(self, memory: waffle::MemoryArg) -> Operator {
        match self {
            Self::Byte => Operator::I32Store8 { memory },
            Self::Half => Operator::I32Store16 { memory },
            Self::Word => Operator::I32Store { memory },
            Self::Double => Operator::I64Store { memory },
        }
    }
}

/// The value of a small immediate, read as signed or unsigned.
fn immediate_value(imm: Immediate, signed: bool) -> Option<i128> {
    Some(match (imm, signed) {
        (Immediate::I1(value), true) => -i128::from(value),
        (Immediate::I1(value), false) => i128::from(value),
        (Immediate::I8(value), true) => i128::from(value),
        (Immediate::I8(value), false) => i128::from(value as u8),
        (Immediate::I16(value), true) => i128::from(value),
        (Immediate::I16(value), false) => i128::from(value as u16),
        (Immediate::I32(value), true) => i128::from(value),
        (Immediate::I32(value), false) => i128::from(value as u32),
        (Immediate::I64(value), true) => i128::from(value),
        (Immediate::I64(value), false) => i128::from(value as u64),
        (Immediate::I128(value), true) => value,
        // A value above `i128::MAX` is not small.
        (Immediate::I128(value), false) => i128::try_from(value as u128).ok()?,
        (Immediate::I256(value), _) => {
            let bits = value.to_u256();
            let small =
                |bits: U256| (bits <= U256::from(u64::MAX)).then(|| i128::from(bits.low_u64()));
            if !signed || bits <= U256::from(i64::MAX as u64) {
                small(bits)?
            } else {
                // A negative value is small if its magnitude is.
                -small((!bits).overflowing_add(U256::one()).0)?
            }
        }
        _ => return None,
    })
}
