//! `black_box`. Cranelift folds through any copy of a value, so the value goes
//! through memory that a call could change: a no-op local to the object, which
//! Cranelift does not inline, receives the address of the value's stack slot.

use cranelift_codegen::{
    Context,
    ir::{self as clif, AbiParam, InstBuilder, MemFlagsData, StackSlotData, StackSlotKind},
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{FuncId, Module as ClifModule};

/// The module's out-of-line no-op, declared on first use and defined after
/// the functions that call it, with the current function's reference to it.
#[derive(Default)]
pub(super) struct BlackBoxBarrier {
    id: Option<FuncId>,
    func: Option<clif::FuncRef>,
}

impl BlackBoxBarrier {
    /// Forgets the previous function's reference to the no-op.
    pub fn start_function(&mut self) {
        self.func = None;
    }

    /// Stores `values` in a new stack slot, hides the slot from the optimizer
    /// and returns the values loaded back.
    pub fn hide<const N: usize>(
        &mut self,
        values: [clif::Value; N],
        clif_module: &mut impl ClifModule,
        builder: &mut FunctionBuilder,
    ) -> Result<[clif::Value; N], String> {
        let func = self.func(clif_module, builder)?;
        let ty = builder.func.dfg.value_type(values[0]);
        let slot = builder.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            ty.bytes() * N as u32,
            ty.bytes().trailing_zeros() as u8,
        ));
        let pointer_type = clif_module.target_config().pointer_type();
        let address = builder.ins().stack_addr(pointer_type, slot, 0);
        let flags = MemFlagsData::trusted();
        let offset = |index: usize| (ty.bytes() as usize * index) as i32;
        for (index, value) in values.into_iter().enumerate() {
            builder.ins().store(flags, value, address, offset(index));
        }
        builder.ins().call(func, &[address]);
        Ok(std::array::from_fn(|index| {
            builder.ins().load(ty, flags, address, offset(index))
        }))
    }

    fn func(
        &mut self,
        clif_module: &mut impl ClifModule,
        builder: &mut FunctionBuilder,
    ) -> Result<clif::FuncRef, String> {
        if let Some(func) = self.func {
            return Ok(func);
        }
        let id = match self.id {
            Some(id) => id,
            None => {
                let id = clif_module
                    .declare_anonymous_function(&signature(clif_module))
                    .map_err(|error| format!("failed to declare the black box: {error}"))?;
                *self.id.insert(id)
            }
        };
        let func = clif_module.declare_func_in_func(id, builder.func);
        self.func = Some(func);
        Ok(func)
    }

    /// The no-op's id and CLIF, if any function calls it.
    pub fn finish(self, clif_module: &impl ClifModule) -> Option<(FuncId, Context)> {
        let id = self.id?;
        let mut ctx = clif_module.make_context();
        ctx.func.signature = signature(clif_module);
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.ins().return_(&[]);
        builder.seal_all_blocks();
        builder.finalize(clif_module.target_config());
        Some((id, ctx))
    }
}

fn signature(clif_module: &impl ClifModule) -> clif::Signature {
    let mut signature = clif_module.make_signature();
    signature
        .params
        .push(AbiParam::new(clif_module.target_config().pointer_type()));
    signature
}
