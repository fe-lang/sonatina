use std::collections::HashMap;

use cranelift_codegen::{
    ir::{self as clif, InstBuilder, instructions::BlockArg},
    isa::TargetFrontendConfig,
};
use cranelift_frontend::FunctionBuilder;
use sonatina_ir::{
    BlockId, Function, Type, ValueId,
    inst::{inst_set::InstSetExt, native::inst_set::NativeInstKind},
    isa::native::inst_set as native_inst_set,
};

use super::{
    ValueMap, aggregate_elem_offset, constant_value_index, copy_bytes, frame::FrameSlots,
    resolve_i256, resolve_value, stack_slot_data, store_indirect,
    uses_indirect_value_representation, value_storage_size,
};

/// Lowers CFG edges. Scalar phis receive Cranelift block arguments, and an
/// i256 phi four, one per limb. Each aggregate phi owns a slot that its
/// incoming edges copy into, so a phi costs one copy per edge rather than
/// one block parameter per word.
pub(super) struct Edges<'a> {
    pub function: &'a Function,
    pub block_map: &'a HashMap<BlockId, clif::Block>,
    pub frame: &'a FrameSlots,
    pub config: TargetFrontendConfig,
}

/// Where a branch to `succ` goes. An edge with aggregate phi copies runs
/// them in a block of its own, which `Edges::fill` completes after the branch.
pub(super) struct EdgeTarget {
    pub block: clif::Block,
    pub args: Vec<BlockArg>,
    copies: bool,
}

impl Edges<'_> {
    /// Copies aggregate phi inputs and jumps from the current block to `succ`.
    pub fn jump(
        &self,
        pred: BlockId,
        succ: BlockId,
        value_map: &ValueMap,
        builder: &mut FunctionBuilder,
    ) -> Result<(), String> {
        self.copy_aggregate_inputs(pred, succ, value_map, builder)?;
        let args = self.scalar_args(pred, succ, value_map, builder)?;
        builder.ins().jump(self.block_map[&succ], &args);
        Ok(())
    }

    pub fn target(
        &self,
        pred: BlockId,
        succ: BlockId,
        value_map: &ValueMap,
        builder: &mut FunctionBuilder,
    ) -> Result<EdgeTarget, String> {
        if self.aggregate_phis(pred, succ).next().is_some() {
            return Ok(EdgeTarget {
                block: builder.create_block(),
                args: Vec::new(),
                copies: true,
            });
        }
        Ok(EdgeTarget {
            block: self.block_map[&succ],
            args: self.scalar_args(pred, succ, value_map, builder)?,
            copies: false,
        })
    }

    /// Whether the edge from `pred` to `succ` passes phi inputs.
    pub fn has_inputs(&self, pred: BlockId, succ: BlockId) -> bool {
        self.phi_inputs(pred, succ).next().is_some()
    }

    pub fn fill(
        &self,
        target: EdgeTarget,
        pred: BlockId,
        succ: BlockId,
        value_map: &ValueMap,
        builder: &mut FunctionBuilder,
    ) -> Result<(), String> {
        if target.copies {
            builder.switch_to_block(target.block);
            self.jump(pred, succ, value_map, builder)?;
        }
        Ok(())
    }

    /// Each phi of `succ` with its input from `pred`.
    fn phi_inputs(
        &self,
        pred: BlockId,
        succ: BlockId,
    ) -> impl Iterator<Item = (ValueId, ValueId)> + '_ {
        let dfg = &self.function.dfg;
        self.function
            .layout
            .iter_inst(succ)
            .map_while(|inst| {
                let phi = dfg.cast_phi(inst)?;
                Some((dfg.inst_result(inst)?, phi))
            })
            .filter_map(move |(phi, inst)| {
                let (input, _) = inst.args().iter().find(|(_, block)| *block == pred)?;
                Some((phi, *input))
            })
    }

    fn aggregate_phis(
        &self,
        pred: BlockId,
        succ: BlockId,
    ) -> impl Iterator<Item = (ValueId, ValueId)> + '_ {
        self.phi_inputs(pred, succ)
            .filter(|&(phi, _)| self.is_aggregate(phi))
    }

    fn is_aggregate(&self, value: ValueId) -> bool {
        uses_indirect_value_representation(self.function.ctx(), self.function.dfg.value_ty(value))
    }

    /// The block arguments of the edge's non-aggregate phis: four limbs
    /// for an i256 phi, otherwise one value.
    fn scalar_args(
        &self,
        pred: BlockId,
        succ: BlockId,
        value_map: &ValueMap,
        builder: &mut FunctionBuilder,
    ) -> Result<Vec<BlockArg>, String> {
        let mut args = Vec::new();
        for (phi, input) in self.phi_inputs(pred, succ) {
            if self.function.dfg.value_ty(phi) == Type::I256 {
                let limbs = resolve_i256(self.function, input, value_map, builder)?;
                args.extend(limbs.map(BlockArg::Value));
            } else if !self.is_aggregate(phi) {
                let value = resolve_value(self.function, input, value_map, builder)?;
                args.push(BlockArg::Value(value));
            }
        }
        Ok(args)
    }

    /// Runs the edge's aggregate phi copies as one parallel copy. An input
    /// can be another phi of `succ`, or a view into one, so a destination is
    /// written only once no pending copy reads it. When every pending
    /// destination is still read (a swap cycle), one is first saved in a
    /// temporary that its readers then copy from.
    fn copy_aggregate_inputs(
        &self,
        pred: BlockId,
        succ: BlockId,
        value_map: &ValueMap,
        builder: &mut FunctionBuilder,
    ) -> Result<(), String> {
        struct Copy {
            phi: ValueId,
            input: ValueId,
            /// The copy's position of the phi whose old contents it reads,
            /// and the offset of the input within them.
            reads: Option<(usize, i32)>,
            saved: Option<(clif::StackSlot, i32)>,
        }
        let phis: Vec<_> = self.aggregate_phis(pred, succ).collect();
        let mut copies = Vec::with_capacity(phis.len());
        for &(phi, input) in &phis {
            let (base, offset) = self.storage_base(input)?;
            copies.push(Copy {
                phi,
                input,
                reads: phis
                    .iter()
                    .position(|&(phi, _)| phi == base)
                    .map(|index| (index, offset)),
                saved: None,
            });
        }

        let mut pending: Vec<usize> = (0..copies.len())
            .filter(|&index| copies[index].input != copies[index].phi)
            .collect();
        while !pending.is_empty() {
            let unread = |index: usize| {
                !pending
                    .iter()
                    .any(|&reader| matches!(copies[reader].reads, Some((read, _)) if read == index))
            };
            let position = pending.iter().position(|&index| unread(index));
            let index = match position {
                Some(position) => pending.remove(position),
                None => {
                    let index = pending[0];
                    let phi = copies[index].phi;
                    let slot = builder.create_sized_stack_slot(stack_slot_data(
                        self.function.dfg.value_ty(phi),
                        self.function.ctx(),
                    )?);
                    let src = self.frame.address(phi, builder)?;
                    let dst = builder
                        .ins()
                        .stack_addr(self.config.pointer_type(), slot, 0);
                    copy_bytes(src, dst, self.size(phi)?, self.config, builder);
                    for &reader in &pending {
                        if let Some((read, offset)) = copies[reader].reads
                            && read == index
                        {
                            copies[reader].reads = None;
                            copies[reader].saved = Some((slot, offset));
                        }
                    }
                    continue;
                }
            };
            let copy = &copies[index];
            let dst = self.frame.address(copy.phi, builder)?;
            let size = self.size(copy.phi)?;
            match copy.saved {
                Some((slot, offset)) => {
                    let src = builder
                        .ins()
                        .stack_addr(self.config.pointer_type(), slot, offset);
                    copy_bytes(src, dst, size, self.config, builder);
                }
                None => store_indirect(
                    self.function,
                    copy.input,
                    dst,
                    size,
                    value_map,
                    self.config,
                    builder,
                )?,
            }
        }
        Ok(())
    }

    /// The value whose storage holds `value`, and the offset of `value`
    /// there: an extracted aggregate is a view into its base.
    fn storage_base(&self, mut value: ValueId) -> Result<(ValueId, i32), String> {
        let function = self.function;
        let mut offset = 0;
        while let Some(inst) = function.dfg.value_inst(value)
            && let NativeInstKind::ExtractValue(extract) =
                native_inst_set().resolve_inst(function.dfg.inst(inst))
            && uses_indirect_value_representation(function.ctx(), function.dfg.value_ty(value))
        {
            let base = *extract.dest();
            let index = constant_value_index(function, *extract.idx(), "extract_value")?;
            offset += aggregate_elem_offset(function.ctx(), function.dfg.value_ty(base), index)?.0;
            value = base;
        }
        Ok((value, offset))
    }

    fn size(&self, phi: ValueId) -> Result<u32, String> {
        value_storage_size(self.function.dfg.value_ty(phi), self.function.ctx())
    }
}
