//! Values held in parts: a struct, array or enum of at most
//! [`MAX_PARTS`](sonatina_codegen::isa::native::MAX_PARTS) integer and pointer
//! fields ([`register_parts`]) is one WebAssembly value for each part, as
//! native code holds it in registers. An enum's tag is its first part.
//! Functions pass and return such a value as its parts, a phi carries them as
//! block parameters, and memory sees them only when the value is stored or
//! loaded. Padding is not part of the value, so a store leaves it as it was.

use std::ops::Range;

use sonatina_codegen::isa::native::{Parts, register_parts};
use sonatina_ir::{InstId, Type, Value, ValueId};

use super::{FunctionTranslator, Repr, V, invalid, repr};
use crate::{WasmError, arith::Int};

impl FunctionTranslator<'_> {
    /// The parts of `ty`, which is held in parts.
    pub(super) fn parts_of(&self, ty: Type) -> Parts {
        register_parts(&self.module.ctx, ty).expect("a value held in parts has parts")
    }

    /// The values of the parts of `id`, a value held in parts. A `zero` is
    /// zero in every part.
    pub(super) fn parts_operand(
        &mut self,
        wb: waffle::Block,
        id: ValueId,
    ) -> Result<Vec<V>, WasmError> {
        if let Some(values) = self.parts.get(&id) {
            return Ok(values.clone());
        }
        match self.function.dfg.value(id) {
            Value::Zero { ty } => Ok(self.zero_parts(wb, &self.parts_of(*ty))),
            _ => Err(invalid(format!(
                "function `{}`: value v{} is used before it is defined",
                self.name, id.0
            ))),
        }
    }

    /// Zero in each of `parts`.
    pub(super) fn zero_parts(&mut self, wb: waffle::Block, parts: &Parts) -> Vec<V> {
        parts
            .iter()
            .map(|part| match Int::from_type(part.ty) {
                Some(int) => self.emit(wb).zero(int),
                None => self.emit(wb).c32(0),
            })
            .collect()
    }

    /// Record result `index` of an instruction, of type `expected`, as the
    /// values of its parts.
    pub(super) fn define_parts(
        &mut self,
        inst_id: InstId,
        index: usize,
        values: Vec<V>,
        expected: Type,
    ) -> Result<(), WasmError> {
        let result = self.result_of(inst_id, index, expected)?;
        self.parts.insert(result, values);
        Ok(())
    }

    /// The parts of `parts` within the `size` bytes at `offset` of the value:
    /// a field's, or an enum variant field's.
    pub(super) fn parts_within(parts: &Parts, offset: u32, size: u32) -> Range<usize> {
        let from = |bound: u32| {
            parts
                .iter()
                .position(|part| part.offset >= bound)
                .unwrap_or(parts.len())
        };
        from(offset)..from(offset + size)
    }

    /// Overwrite the values of `parts` within the `ty` field at `offset`
    /// with those of `value`, which `op` writes there: a scalar's one value,
    /// the parts of a value held in parts, and none for an aggregate without
    /// parts, which holds no bytes.
    pub(super) fn insert_field(
        &mut self,
        wb: waffle::Block,
        op: &str,
        (parts, values): (&Parts, &mut [V]),
        (offset, ty): (u32, Type),
        value: ValueId,
    ) -> Result<(), WasmError> {
        if self.function.dfg.value_ty(value) != ty {
            return Err(invalid(format!(
                "function `{}`: `{op}` value does not have the type of its field",
                self.name
            )));
        }
        let field = match repr(&self.module.ctx, ty) {
            Some(Repr::Parts) => self.parts_operand(wb, value)?,
            Some(Repr::Aggregate) => Vec::new(),
            _ => vec![self.operand(wb, value)?],
        };
        let (size, _) = self.layout_of(ty)?;
        let range = Self::parts_within(parts, offset, size);
        if range.len() != field.len() {
            return Err(invalid(format!(
                "function `{}`: `{op}` writes a field at offset {offset} of {} parts, not {}",
                self.name,
                range.len(),
                field.len()
            )));
        }
        values[range].copy_from_slice(&field);
        Ok(())
    }

    /// Record result 0 of `inst_id`, the `ty` field at `offset` of a value
    /// held in parts whose part values are `values`: the field's own parts,
    /// its one value, or for an aggregate without parts storage of its own,
    /// which holds no bytes.
    pub(super) fn define_field(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        (parts, values): (&Parts, &[V]),
        (offset, ty): (u32, Type),
    ) -> Result<(), WasmError> {
        let (size, align) = self.layout_of(ty)?;
        let field = values[Self::parts_within(parts, offset, size)].to_vec();
        match repr(&self.module.ctx, ty) {
            Some(Repr::Parts) => self.define_parts(inst_id, 0, field, ty),
            Some(Repr::Aggregate) => {
                let slot = self.slot(size, align)?;
                let address = self.slot_address(wb, slot)?;
                self.define(inst_id, 0, address, ty)
            }
            _ => {
                let [value] = field[..] else {
                    return Err(invalid(format!(
                        "function `{}`: a scalar field at offset {offset} spans {} parts",
                        self.name,
                        field.len()
                    )));
                };
                self.define(inst_id, 0, value, ty)
            }
        }
    }

    /// The address of `id`, an aggregate: its storage, or for a value held
    /// in parts a new slot of the frame that they are stored to.
    pub(super) fn aggregate_address(
        &mut self,
        wb: waffle::Block,
        op: &str,
        id: ValueId,
    ) -> Result<V, WasmError> {
        let ty = self.function.dfg.value_ty(id);
        if repr(&self.module.ctx, ty) != Some(Repr::Parts) {
            return self.operand(wb, id);
        }
        let (size, align) = self.layout_of(ty)?;
        let slot = self.slot(size, align)?;
        let address = self.slot_address(wb, slot)?;
        self.store_value(wb, op, ty, address, 0, id)?;
        Ok(address)
    }
}
