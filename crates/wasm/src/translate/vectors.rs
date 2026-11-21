//! Byte swaps of 128- and 256-bit integers with `v128` values. A swap
//! reverses the bytes of each 16-byte half with one `i8x16.shuffle` and
//! exchanges the halves. A value loaded from memory only to be swapped is
//! loaded as `v128` halves, and a swapped value is stored as its halves, so
//! that a big-endian word moves between memory and limbs, as EVM code reads
//! and writes them, without its limbs passing through `i64` values.

use sonatina_ir::{
    InstId, InstSetExt, ValueId, inst::native::inst_set::NativeInstKind, isa::native,
};
use waffle::{Operator, Type as WType};

use super::{Access, FunctionTranslator, V};
use crate::{
    WasmError,
    wide::{LIMBS, Limbs, Wide},
};

/// The lanes of an `i8x16.shuffle` that reverse the bytes of a `v128`.
const REVERSED: [u8; 16] = [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0];

impl FunctionTranslator<'_> {
    /// Whether the result of `inst_id` is swapped by a `bswap`.
    pub(super) fn feeds_bswap(&self, inst_id: InstId) -> bool {
        let dfg = &self.function.dfg;
        dfg.inst_result(inst_id).is_some_and(|result| {
            dfg.users(result).any(|&user| {
                matches!(
                    native::inst_set().resolve_inst(dfg.inst(user)),
                    NativeInstKind::Bswap(_)
                )
            })
        })
    }

    /// Define result 0 of `inst_id`, a value of `wide`, by loading its
    /// halves from `addr + offset`, and keep them for its swap.
    pub(super) fn load_halves(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        wide: Wide,
        (addr, offset): (V, u32),
    ) -> Result<(), WasmError> {
        let halves: Vec<V> = (0..wide.limbs() / 2)
            .map(|half| {
                let (memarg, addr) = self.memarg(Access::Double, addr, offset + 16 * half as u32);
                self.body.add_op(
                    wb,
                    Operator::V128Load { memory: memarg },
                    &[addr],
                    &[WType::V128],
                )
            })
            .collect();
        self.define_halves(wb, inst_id, wide, halves)
    }

    /// Define result 0 of `inst_id`, a value of `wide`, from its halves,
    /// which are kept for a store or a swap.
    fn define_halves(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        wide: Wide,
        halves: Vec<V>,
    ) -> Result<(), WasmError> {
        let mut limbs: Limbs = [self.emit(wb).c64(0); LIMBS];
        for (index, limb) in limbs.iter_mut().enumerate().take(wide.limbs()) {
            *limb = self.emit(wb).op(
                Operator::I64x2ExtractLane {
                    lane: (index % 2) as u8,
                },
                &[halves[index / 2]],
                WType::I64,
            );
        }
        self.define_wide(wb, inst_id, 0, wide, limbs)?;
        let result = self.result_of(inst_id, 0, wide.ty())?;
        self.vectors.insert(result, halves);
        Ok(())
    }

    /// `bswap` of a 128- or 256-bit value: its halves, in reverse order,
    /// each with its bytes reversed.
    pub(super) fn wide_bswap(
        &mut self,
        wb: waffle::Block,
        inst_id: InstId,
        arg: ValueId,
        wide: Wide,
    ) -> Result<(), WasmError> {
        let halves = match self.vectors.get(&arg) {
            Some(halves) => halves.clone(),
            None => {
                let limbs = self.wide_operand(wb, arg)?;
                (0..wide.limbs() / 2)
                    .map(|half| {
                        let mut emit = self.emit(wb);
                        let low = emit.op(Operator::I64x2Splat, &[limbs[2 * half]], WType::V128);
                        emit.op(
                            Operator::I64x2ReplaceLane { lane: 1 },
                            &[low, limbs[2 * half + 1]],
                            WType::V128,
                        )
                    })
                    .collect()
            }
        };
        let swapped = halves
            .iter()
            .rev()
            .map(|&half| {
                self.emit(wb).op(
                    Operator::I8x16Shuffle { lanes: REVERSED },
                    &[half, half],
                    WType::V128,
                )
            })
            .collect();
        self.define_halves(wb, inst_id, wide, swapped)
    }

    /// Store the halves of `id`, a 128- or 256-bit value, at `addr + offset`,
    /// if they are at hand.
    pub(super) fn store_halves(
        &mut self,
        wb: waffle::Block,
        id: ValueId,
        (addr, offset): (V, u32),
    ) -> bool {
        let Some(halves) = self.vectors.get(&id).cloned() else {
            return false;
        };
        for (half, value) in halves.into_iter().enumerate() {
            let (memarg, addr) = self.memarg(Access::Double, addr, offset + 16 * half as u32);
            self.body.add_op(
                wb,
                Operator::V128Store { memory: memarg },
                &[addr, value],
                &[],
            );
        }
        true
    }
}
