use cranelift_entity::SecondaryMap;
use smallvec::SmallVec;
use sonatina_ir::{
    BlockId, Function, I256, Immediate, Inst, InstSetExt, Signature, Type, U256, Value, ValueId,
    cfg::ControlFlowGraph,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{
        arith, cmp, control_flow, data,
        evm::{
            self,
            inst_set::{EvmInstKind, EvmInstSet},
            machine_inst_set::EvmMachineInstSet,
        },
        logic,
    },
    isa::{Isa, evm::EvmMachine},
    module::{FuncRef, ModuleCtx},
    types::CompoundType,
};

use crate::{domtree::DomTree, machinst::lower::SectionWorkModule};

use super::{
    super::{
        DYN_SP_SLOT, DynamicFrameLayout, EvmBackend, FREE_PTR_SLOT, ObjLoc, WORD_BYTES,
        immediate_u32, memory_plan::StableMode,
    },
    module::{FuncMachineMap, MachineSectionModule, SourceMachineMap},
    placement::{EvmFuncPlacementPlan, EvmMemoryPlacementPlan, MallocPlacement},
    verify::verify_machine_module,
};

pub(crate) fn lower_section_to_machine(
    source_work: &SectionWorkModule,
    funcs: &[FuncRef],
    placement: &EvmMemoryPlacementPlan,
    backend: &EvmBackend,
) -> Result<MachineSectionModule, String> {
    let source = source_work.module();
    let machine_isa = EvmMachine::new(source.ctx.triple);
    let mut machine_module = source.clone_for_funcs(&[]);
    machine_module.ctx.inst_set = machine_isa.inst_set();
    machine_module.ctx.type_layout = machine_isa.type_layout();

    for &func_ref in funcs {
        let source_sig = source.ctx.func_sig(func_ref, Clone::clone);
        let machine_sig = lower_signature(&source.ctx, &source_sig)?;
        machine_module
            .ctx
            .declared_funcs
            .insert(func_ref, machine_sig);
    }

    let mut source_to_machine = SourceMachineMap::default();
    for &func_ref in funcs {
        let func_placement = placement
            .funcs
            .get(&func_ref)
            .ok_or_else(|| format!("missing placement for func {}", func_ref.as_u32()))?;
        let (machine_func, func_map) = source.func_store.view(func_ref, |source_func| {
            lower_function(
                func_ref,
                source_func,
                &source.ctx,
                &machine_module.ctx,
                func_placement,
                backend.isa.inst_set(),
                machine_isa.inst_set(),
            )
        })?;
        machine_module.func_store.restore(func_ref, machine_func);
        source_to_machine.funcs.insert(func_ref, func_map);
    }

    verify_machine_module(&machine_module, funcs)?;

    let work = SectionWorkModule::from_module_subset(
        &machine_module,
        funcs,
        source_work.entry(),
        source_work.includes(),
        source_work.data(),
    );
    Ok(MachineSectionModule {
        work,
        source_to_machine,
    })
}

fn lower_signature(module: &ModuleCtx, sig: &Signature) -> Result<Signature, String> {
    let args = sig
        .args()
        .iter()
        .copied()
        .map(|ty| machine_type(module, ty))
        .collect::<Result<Vec<_>, _>>()?;
    let ret_tys = sig
        .ret_tys()
        .iter()
        .copied()
        .map(|ty| machine_type(module, ty))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Signature::new(sig.name(), sig.linkage(), &args, &ret_tys))
}

fn machine_type(module: &ModuleCtx, ty: Type) -> Result<Type, String> {
    if ty.is_pointer(module) {
        return Ok(Type::I256);
    }
    match ty {
        Type::Unit => Ok(Type::Unit),
        Type::I1 | Type::I256 => Ok(Type::I256),
        Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 | Type::EnumTag(_) => {
            Ok(Type::I256)
        }
        Type::Compound(_) => Err(format!("unsupported machine type {ty:?}")),
    }
}

struct FuncLowerCtx<'a> {
    func_ref: FuncRef,
    source: &'a Function,
    source_module: &'a ModuleCtx,
    placement: &'a EvmFuncPlacementPlan,
    source_is: &'static EvmInstSet,
    is: &'static EvmMachineInstSet,
    machine: Function,
    map: FuncMachineMap,
    source_block_order: Vec<BlockId>,
    block_terminal_map: SecondaryMap<BlockId, Option<BlockId>>,
    current_block: Option<BlockId>,
    active_source_inst: Option<sonatina_ir::InstId>,
    pending_phis: Vec<(sonatina_ir::InstId, sonatina_ir::InstId)>,
}

fn lower_function(
    func_ref: FuncRef,
    source: &Function,
    source_module: &ModuleCtx,
    machine_module: &ModuleCtx,
    placement: &EvmFuncPlacementPlan,
    source_is: &'static EvmInstSet,
    is: &'static EvmMachineInstSet,
) -> Result<(Function, FuncMachineMap), String> {
    let sig = machine_module.func_sig(func_ref, Clone::clone);
    let machine = Function::new(machine_module, &sig);
    let source_block_order = source_lowering_order(source);
    let mut ctx = FuncLowerCtx {
        func_ref,
        source,
        source_module,
        placement,
        source_is,
        is,
        machine,
        map: FuncMachineMap::new(),
        source_block_order,
        block_terminal_map: SecondaryMap::new(),
        current_block: None,
        active_source_inst: None,
        pending_phis: Vec::new(),
    };

    ctx.initialize_map_slots();
    ctx.map_args()?;
    ctx.create_source_blocks();
    ctx.create_phi_stubs()?;
    ctx.lower_non_phi_insts()?;
    ctx.patch_phi_args()?;
    ctx.machine.rebuild_users();

    Ok((ctx.machine, ctx.map))
}

impl FuncLowerCtx<'_> {
    fn initialize_map_slots(&mut self) {
        for block in self.source.dfg.block_ids() {
            let _ = &mut self.map.blocks[block];
            let _ = &mut self.block_terminal_map[block];
        }
        for value in self.source.dfg.value_ids() {
            let _ = &mut self.map.values[value];
        }
        for inst in self.source.dfg.inst_ids() {
            let _ = &mut self.map.insts[inst];
        }
    }

    fn map_args(&mut self) -> Result<(), String> {
        for (idx, &source_arg) in self.source.arg_values.iter().enumerate() {
            let Some(&machine_arg) = self.machine.arg_values.get(idx) else {
                return Err(format!(
                    "missing machine argument {idx} in func {}",
                    self.func_ref.as_u32()
                ));
            };
            self.map.values[source_arg] = Some(machine_arg);
        }
        Ok(())
    }

    fn create_source_blocks(&mut self) {
        for source_block in self.source.layout.iter_block() {
            let machine_block = self.machine.dfg.make_block();
            self.machine.layout.append_block(machine_block);
            self.map.blocks[source_block] = Some(machine_block);
        }
    }

    fn create_phi_stubs(&mut self) -> Result<(), String> {
        for source_block in self.source.layout.iter_block() {
            let machine_block = self.machine_block(source_block)?;
            let mut cursor = InstInserter::at_location(CursorLocation::BlockBottom(machine_block));
            for source_inst in self.source.layout.iter_inst(source_block) {
                if !self.source.dfg.is_phi(source_inst) {
                    continue;
                }
                let machine_inst = cursor.insert_inst_data(
                    &mut self.machine,
                    control_flow::Phi::new_unchecked(self.is, Vec::new()),
                );
                self.copy_debug_context_to_machine(source_inst, machine_inst);
                let result_tys = self.machine_result_tys(source_inst)?;
                let results = cursor.make_results(&mut self.machine, machine_inst, &result_tys);
                cursor.attach_results(&mut self.machine, machine_inst, &results);
                self.map_inst_results(source_inst, machine_inst, &results);
                self.pending_phis.push((source_inst, machine_inst));
            }
        }
        Ok(())
    }

    fn lower_non_phi_insts(&mut self) -> Result<(), String> {
        for source_block in self.source_block_order.clone() {
            let start_block = self.machine_block(source_block)?;
            self.current_block = Some(start_block);
            for source_inst in self.source.layout.iter_inst(source_block) {
                if self.source.dfg.is_phi(source_inst) {
                    continue;
                }
                self.lower_inst(source_inst)?;
            }
            self.block_terminal_map[source_block] = self.current_block;
        }
        Ok(())
    }

    fn patch_phi_args(&mut self) -> Result<(), String> {
        for (source_inst, machine_inst) in self.pending_phis.clone() {
            let EvmInstKind::Phi(phi) = self
                .source_is
                .resolve_inst(self.source.dfg.inst(source_inst))
            else {
                return Err("pending phi was not a source phi".to_string());
            };
            let mut args = Vec::with_capacity(phi.args().len());
            for &(value, pred) in phi.args() {
                let value = self.lower_value(value)?;
                let pred = self.machine_pred_block(pred)?;
                args.push((value, pred));
            }
            let machine_phi =
                <&mut control_flow::Phi as sonatina_ir::InstDowncastMut>::downcast_mut(
                    self.machine.inst_set(),
                    self.machine.dfg.inst_mut(machine_inst),
                )
                .expect("machine phi downcast failed");
            for (value, pred) in args {
                machine_phi.append_phi_arg(value, pred);
            }
        }
        Ok(())
    }

    fn lower_inst(&mut self, source_inst: sonatina_ir::InstId) -> Result<(), String> {
        if self.source_inst_results_already_mapped(source_inst) {
            return Ok(());
        }

        let previous = self.active_source_inst.replace(source_inst);
        let result = self.lower_inst_active(source_inst);
        self.active_source_inst = previous;
        result
    }

    fn lower_inst_active(&mut self, source_inst: sonatina_ir::InstId) -> Result<(), String> {
        let data = self
            .source_is
            .resolve_inst(self.source.dfg.inst(source_inst));
        match data {
            EvmInstKind::Jump(jump) => self.insert_no_result(
                source_inst,
                control_flow::Jump::new(self.is, self.machine_block(*jump.dest())?),
            ),
            EvmInstKind::Br(br) => {
                let cond = self.lower_value(*br.cond())?;
                let nz_dest = self.machine_block(*br.nz_dest())?;
                let z_dest = self.machine_block(*br.z_dest())?;
                self.insert_no_result(
                    source_inst,
                    control_flow::Br::new(self.is, cond, nz_dest, z_dest),
                )
            }
            EvmInstKind::BrTable(table) => {
                let scrutinee = self.lower_value(*table.scrutinee())?;
                let default = table
                    .default()
                    .map(|block| self.machine_block(block))
                    .transpose()?;
                let mut cases = Vec::with_capacity(table.table().len());
                for &(value, block) in table.table() {
                    cases.push((self.lower_value(value)?, self.machine_block(block)?));
                }
                self.insert_no_result(
                    source_inst,
                    control_flow::BrTable::new(self.is, scrutinee, default, cases),
                )
            }
            EvmInstKind::Call(call) => {
                let args = call
                    .args()
                    .iter()
                    .copied()
                    .map(|value| self.lower_value(value))
                    .collect::<Result<SmallVec<[_; 8]>, _>>()?;
                self.insert_with_results(
                    source_inst,
                    control_flow::Call::new(self.is, *call.callee(), args),
                )
            }
            EvmInstKind::Return(ret) => {
                let args = ret
                    .args()
                    .iter()
                    .copied()
                    .map(|value| self.lower_value(value))
                    .collect::<Result<SmallVec<[_; 2]>, _>>()?;
                self.insert_no_result(
                    source_inst,
                    control_flow::Return::new(self.is, control_flow::ReturnArgs::from(args)),
                )
            }
            EvmInstKind::Mload(mload) => self.lower_mload(source_inst, mload),
            EvmInstKind::Mstore(mstore) => self.lower_mstore(source_inst, mstore),
            EvmInstKind::Alloca(_) => self.lower_alloca(source_inst),
            EvmInstKind::Gep(gep) => self.lower_gep(source_inst, gep.values()),
            EvmInstKind::EvmMalloc(_) => self.lower_malloc(source_inst),
            EvmInstKind::Memzero(memzero) => self.lower_memzero(source_inst, memzero),
            EvmInstKind::Le(_) => {
                let (lhs, rhs) = self.lower_binary_values(source_inst)?;
                self.lower_inverted_cmp(source_inst, cmp::Gt::new(self.is, lhs, rhs))
            }
            EvmInstKind::Ge(_) => {
                let (lhs, rhs) = self.lower_binary_values(source_inst)?;
                self.lower_inverted_cmp(source_inst, cmp::Lt::new(self.is, lhs, rhs))
            }
            EvmInstKind::Sle(_) => {
                let (lhs, rhs) = self.lower_binary_values(source_inst)?;
                self.lower_inverted_cmp(source_inst, cmp::Sgt::new(self.is, lhs, rhs))
            }
            EvmInstKind::Sge(_) => {
                let (lhs, rhs) = self.lower_binary_values(source_inst)?;
                self.lower_inverted_cmp(source_inst, cmp::Slt::new(self.is, lhs, rhs))
            }
            EvmInstKind::Ne(_) => {
                let (lhs, rhs) = self.lower_binary_values(source_inst)?;
                self.lower_inverted_cmp(source_inst, cmp::Eq::new(self.is, lhs, rhs))
            }
            EvmInstKind::Bitcast(bitcast) => {
                self.lower_bitcast(source_inst, *bitcast.from(), *bitcast.ty())
            }
            EvmInstKind::IntToPtr(cast) => self.lower_int_to_ptr(source_inst, *cast.from()),
            EvmInstKind::PtrToInt(cast) => {
                self.lower_ptr_to_int(source_inst, *cast.from(), *cast.ty())
            }
            EvmInstKind::Zext(cast) => {
                self.lower_zext_or_trunc(source_inst, *cast.from(), *cast.ty())
            }
            EvmInstKind::Trunc(cast) => {
                self.lower_zext_or_trunc(source_inst, *cast.from(), *cast.ty())
            }
            EvmInstKind::Sext(cast) => self.lower_sext(source_inst, *cast.from()),
            _ => self.lower_structural(source_inst),
        }
    }

    fn lower_mload(
        &mut self,
        source_inst: sonatina_ir::InstId,
        mload: &data::Mload,
    ) -> Result<(), String> {
        let size = self
            .source_module
            .size_of(*mload.ty())
            .map_err(|err| format!("invalid mload type in machine lowering: {err:?}"))?;
        if size != WORD_BYTES as usize {
            return Err(format!(
                "machine lowering expected 32-byte mload, got {size}"
            ));
        }
        let addr = self.lower_value(*mload.addr())?;
        self.insert_with_results(source_inst, evm::EvmMload::new(self.is, addr))
    }

    fn lower_mstore(
        &mut self,
        source_inst: sonatina_ir::InstId,
        mstore: &data::Mstore,
    ) -> Result<(), String> {
        let size = self
            .source_module
            .size_of(*mstore.ty())
            .map_err(|err| format!("invalid mstore type in machine lowering: {err:?}"))?;
        if size == 0 {
            self.map.insts[source_inst] = None;
            return Ok(());
        }
        if size != WORD_BYTES as usize {
            return Err(format!(
                "machine lowering expected 32-byte mstore, got {size}"
            ));
        }
        let addr = self.lower_value(*mstore.addr())?;
        let value = self.lower_value(*mstore.value())?;
        self.insert_no_result(source_inst, evm::EvmMstore::new(self.is, addr, value))
    }

    fn lower_binary_values(
        &mut self,
        source_inst: sonatina_ir::InstId,
    ) -> Result<(ValueId, ValueId), String> {
        let args = self.source.dfg.inst(source_inst).collect_values();
        let [lhs, rhs] = args.as_slice() else {
            return Err(format!(
                "expected binary instruction at inst{} in func {}",
                source_inst.as_u32(),
                self.func_ref.as_u32()
            ));
        };
        Ok((self.lower_value(*lhs)?, self.lower_value(*rhs)?))
    }

    fn lower_inverted_cmp<I: Inst>(
        &mut self,
        source_inst: sonatina_ir::InstId,
        cmp_inst: I,
    ) -> Result<(), String> {
        let cmp = self.emit_binary(cmp_inst, Type::I256);
        let inverted = self.emit_unary(cmp::IsZero::new(self.is, cmp), Type::I256);
        self.alias_inst_single_result(source_inst, inverted)
    }

    fn lower_alloca(&mut self, source_inst: sonatina_ir::InstId) -> Result<(), String> {
        let loc = self
            .placement
            .alloca_loc
            .get(&source_inst)
            .copied()
            .ok_or_else(|| format!("missing alloca placement for inst {}", source_inst.as_u32()))?;
        let value = match loc {
            ObjLoc::ScratchAbs(_) | ObjLoc::StableAbs(_) => {
                let base = self.alloca_abs_addr(loc)?;
                self.i256_imm(base)
            }
            ObjLoc::StableFrame(offset_words) => {
                let layout =
                    DynamicFrameLayout::new(self.placement.stable_words).ok_or_else(|| {
                        "dynamic frame alloca missing stable frame layout".to_string()
                    })?;
                let local_word = layout
                    .local_word(offset_words)
                    .ok_or_else(|| "dynamic frame alloca offset out of range".to_string())?;
                let dyn_sp = self.emit_mload_abs(DYN_SP_SLOT as u32);
                let offset = layout.sp_relative_bytes(local_word);
                if offset == 0 {
                    dyn_sp
                } else {
                    let offset = self.i256_imm(offset);
                    self.emit_binary(arith::Sub::new(self.is, dyn_sp, offset), Type::I256)
                }
            }
            ObjLoc::StackPinned(depth) => {
                return Err(format!(
                    "stack-pinned alloca is not supported (depth={depth})"
                ));
            }
        };
        self.alias_inst_single_result(source_inst, value)
    }

    fn lower_gep(
        &mut self,
        source_inst: sonatina_ir::InstId,
        values: &[ValueId],
    ) -> Result<(), String> {
        let Some((&base, indices)) = values.split_first() else {
            return Err("gep without operands".to_string());
        };
        let mut current_ty = self.source.dfg.value_ty(base);
        if !current_ty.is_pointer(self.source_module) {
            return Err(format!("gep base is not a pointer: {current_ty:?}"));
        }

        let mut addr = self.lower_value(base)?;
        let mut const_offset = 0u32;
        for &idx_value in indices {
            let Some(compound) = current_ty.resolve_compound(self.source_module) else {
                return Err(format!("invalid gep through scalar type {current_ty:?}"));
            };
            match compound {
                CompoundType::Ptr(elem) | CompoundType::Array { elem, .. } => {
                    let elem_size = u32::try_from(self.source_module.size_of_unchecked(elem))
                        .map_err(|_| "gep element size overflow".to_string())?;
                    if let Some(idx) = self.source_value_imm_u32(idx_value) {
                        const_offset = const_offset
                            .checked_add(
                                elem_size
                                    .checked_mul(idx)
                                    .ok_or_else(|| "gep const offset overflow".to_string())?,
                            )
                            .ok_or_else(|| "gep const offset overflow".to_string())?;
                    } else if elem_size != 0 {
                        if const_offset != 0 {
                            addr = self.add_const(addr, const_offset);
                            const_offset = 0;
                        }
                        let idx = self.lower_value(idx_value)?;
                        let scale = self.i256_imm(elem_size);
                        let scaled =
                            self.emit_binary(arith::Mul::new(self.is, idx, scale), Type::I256);
                        addr = self.emit_binary(arith::Add::new(self.is, addr, scaled), Type::I256);
                    }
                    current_ty = elem;
                }
                CompoundType::Struct(_) => {
                    let idx = self.source_value_imm_u32(idx_value).ok_or_else(|| {
                        "struct gep indices must be immediate constants".to_string()
                    })? as usize;
                    let (offset, field_ty) = self
                        .source_module
                        .aggregate_elem_offset(current_ty, idx)
                        .ok_or_else(|| "invalid struct gep field index".to_string())?;
                    const_offset = const_offset
                        .checked_add(
                            u32::try_from(offset)
                                .map_err(|_| "struct gep field offset overflow".to_string())?,
                        )
                        .ok_or_else(|| "gep const offset overflow".to_string())?;
                    current_ty = field_ty;
                }
                CompoundType::Func { .. }
                | CompoundType::Enum(_)
                | CompoundType::ObjRef(_)
                | CompoundType::ConstRef(_) => {
                    return Err(format!("unsupported gep through {compound:?}"));
                }
            }
        }

        if const_offset != 0 {
            addr = self.add_const(addr, const_offset);
        }
        self.alias_inst_single_result(source_inst, addr)
    }

    fn lower_malloc(&mut self, source_inst: sonatina_ir::InstId) -> Result<(), String> {
        let placement = self
            .placement
            .malloc_placements
            .get(&source_inst)
            .copied()
            .ok_or_else(|| format!("missing malloc placement for inst {}", source_inst.as_u32()))?;
        match placement {
            MallocPlacement::Fixed { base } => {
                let value = self.i256_imm(base);
                self.alias_inst_single_result(source_inst, value)
            }
            MallocPlacement::Heap {
                min_base,
                needs_dyn_sp_clamp,
                update_free_ptr,
            } => {
                let known_free_ptr_floor = self
                    .placement
                    .free_ptr_floor_before_malloc
                    .get(&source_inst)
                    .copied()
                    .flatten();
                let base = self.emit_heap_base(min_base, needs_dyn_sp_clamp, known_free_ptr_floor);
                if update_free_ptr {
                    let size = self.lower_malloc_aligned_size(source_inst)?;
                    let new_free =
                        self.emit_binary(arith::Add::new(self.is, base, size), Type::I256);
                    let slot = self.i256_imm(FREE_PTR_SLOT as u32);
                    self.insert_no_result(
                        source_inst,
                        evm::EvmMstore::new(self.is, slot, new_free),
                    )?;
                } else {
                    self.map.insts[source_inst] = None;
                }
                self.alias_inst_single_result(source_inst, base)
            }
        }
    }

    fn lower_int_to_ptr(
        &mut self,
        source_inst: sonatina_ir::InstId,
        from: ValueId,
    ) -> Result<(), String> {
        let source_ty = self.source.dfg.value_ty(from);
        let value = self.lower_value(from)?;
        let value = if matches!(
            source_ty,
            Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128
        ) {
            self.mask_value(value, source_ty)?
        } else {
            value
        };
        self.alias_inst_single_result(source_inst, value)
    }

    fn lower_ptr_to_int(
        &mut self,
        source_inst: sonatina_ir::InstId,
        from: ValueId,
        to: Type,
    ) -> Result<(), String> {
        let value = self.lower_value(from)?;
        let value = if matches!(
            to,
            Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 | Type::I1
        ) {
            self.mask_value(value, to)?
        } else {
            value
        };
        self.alias_inst_single_result(source_inst, value)
    }

    fn lower_zext_or_trunc(
        &mut self,
        source_inst: sonatina_ir::InstId,
        from: ValueId,
        to: Type,
    ) -> Result<(), String> {
        let source_ty = self.source.dfg.value_ty(from);
        if source_ty == Type::I1 && scalar_bits(to).is_some() {
            let value = self.lower_value(from)?;
            return self.alias_inst_single_result(source_inst, value);
        }
        let value = self.lower_value(from)?;
        let source_bits = word_bits(source_ty, self.source_module)
            .ok_or_else(|| format!("cannot zero-extend or truncate non-word type {source_ty:?}"))?;
        let target_bits = word_bits(to, self.source_module)
            .ok_or_else(|| format!("cannot zero-extend or truncate to non-word type {to:?}"))?;
        let bits = source_bits.min(target_bits);
        let value = if bits < 256 {
            self.mask_value_to_bits(value, bits)?
        } else {
            value
        };
        self.alias_inst_single_result(source_inst, value)
    }

    fn lower_sext(
        &mut self,
        source_inst: sonatina_ir::InstId,
        from: ValueId,
    ) -> Result<(), String> {
        let source_ty = self.source.dfg.value_ty(from);
        let bits = scalar_bits(source_ty)
            .ok_or_else(|| format!("cannot sign-extend non-scalar type {source_ty:?}"))?;
        let value = self.lower_value(from)?;
        if bits == 256 {
            return self.alias_inst_single_result(source_inst, value);
        }
        if bits == 1 {
            let zero = self.i256_imm(0);
            let extended = self.emit_binary(arith::Sub::new(self.is, zero, value), Type::I256);
            return self.alias_inst_single_result(source_inst, extended);
        }
        let byte = self.i256_imm(u32::from(bits / 8 - 1));
        let extended = self.emit_binary(evm::EvmSignExtend::new(self.is, byte, value), Type::I256);
        self.alias_inst_single_result(source_inst, extended)
    }

    fn lower_memzero(
        &mut self,
        source_inst: sonatina_ir::InstId,
        memzero: &data::Memzero,
    ) -> Result<(), String> {
        let dest = self.lower_value(*memzero.dest())?;
        let len = self.lower_value(*memzero.len())?;
        let calldata_size = self.emit_unary(evm::EvmCalldataSize::new(self.is), Type::I256);
        self.insert_no_result(
            source_inst,
            evm::EvmCalldataCopy::new(self.is, dest, calldata_size, len),
        )
    }

    fn lower_bitcast(
        &mut self,
        source_inst: sonatina_ir::InstId,
        from: ValueId,
        to: Type,
    ) -> Result<(), String> {
        if self.source.dfg.value_ty(from) == Type::I1 && scalar_bits(to).is_some() {
            let value = self.lower_value(from)?;
            return self.alias_inst_single_result(source_inst, value);
        }
        let value = self.lower_value(from)?;
        let from_bits = word_bits(self.source.dfg.value_ty(from), self.source_module)
            .ok_or_else(|| "cannot bitcast from non-word type".to_string())?;
        let to_bits = word_bits(to, self.source_module)
            .ok_or_else(|| "cannot bitcast to non-word type".to_string())?;
        let bits = from_bits.min(to_bits);
        let value = if bits < 256 {
            self.mask_value_to_bits(value, bits)?
        } else {
            value
        };
        self.alias_inst_single_result(source_inst, value)
    }

    fn lower_structural(&mut self, source_inst: sonatina_ir::InstId) -> Result<(), String> {
        let mut cloned = self.source.dfg.clone_inst(source_inst);
        let mut err = None;
        cloned.for_each_value_mut(&mut |value| match self.lower_value(*value) {
            Ok(lowered) => *value = lowered,
            Err(e) => err = Some(e),
        });
        if let Some(err) = err {
            return Err(err);
        }
        self.insert_dyn_with_results(source_inst, cloned)
    }

    fn lower_malloc_aligned_size(
        &mut self,
        source_inst: sonatina_ir::InstId,
    ) -> Result<ValueId, String> {
        let args = self.source.dfg.inst(source_inst).collect_values();
        let size = *args
            .first()
            .ok_or_else(|| "evm_malloc missing size operand".to_string())?;
        if let Some(size) = self.source_value_imm_u32(size) {
            return Ok(self.i256_imm(align_malloc_size(size)?));
        }

        let size = self.lower_value(size)?;
        let plus = self.i256_imm(31);
        let size = self.emit_binary(arith::Add::new(self.is, size, plus), Type::I256);
        let mask = self
            .machine
            .dfg
            .make_imm_value(Immediate::from_i256(!I256::from(31u8), Type::I256));
        Ok(self.emit_binary(logic::And::new(self.is, size, mask), Type::I256))
    }

    fn emit_heap_base(
        &mut self,
        min_base: u32,
        needs_dyn_sp_clamp: bool,
        known_free_ptr_floor: Option<u32>,
    ) -> ValueId {
        let mut base = self.emit_mload_abs(FREE_PTR_SLOT as u32);
        if needs_dyn_sp_clamp {
            let dyn_sp = self.emit_mload_abs(DYN_SP_SLOT as u32);
            base = self.emit_word_max(base, dyn_sp);
        }
        if known_free_ptr_floor.is_some_and(|floor| floor >= min_base) {
            return base;
        }
        self.emit_word_max_const_u32(base, min_base)
    }

    fn emit_word_max(&mut self, lhs: ValueId, rhs: ValueId) -> ValueId {
        let delta = self.emit_binary(arith::Sub::new(self.is, rhs, lhs), Type::I256);
        let cond = self.emit_binary(cmp::Lt::new(self.is, lhs, rhs), Type::I256);
        let selected_delta = self.emit_binary(arith::Mul::new(self.is, delta, cond), Type::I256);
        self.emit_binary(arith::Add::new(self.is, lhs, selected_delta), Type::I256)
    }

    fn emit_word_max_const_u32(&mut self, lhs: ValueId, rhs: u32) -> ValueId {
        if rhs == 0 {
            return lhs;
        }
        let value = self.i256_imm(rhs);
        let compare = self.i256_imm(rhs - 1);
        self.emit_word_max_with_compare(lhs, value, compare)
    }

    fn emit_word_max_with_compare(
        &mut self,
        lhs: ValueId,
        rhs: ValueId,
        compare_rhs: ValueId,
    ) -> ValueId {
        let cond = self.emit_binary(cmp::Gt::new(self.is, lhs, compare_rhs), Type::I256);
        let from_block = self.current_block.expect("word max needs current block");
        let lhs_block = self.append_machine_block();
        let rhs_block = self.append_machine_block();
        let join_block = self.append_machine_block();
        self.append_inst_no_result_to(
            from_block,
            control_flow::Br::new(self.is, cond, lhs_block, rhs_block),
        );
        self.append_inst_no_result_to(lhs_block, control_flow::Jump::new(self.is, join_block));
        self.append_inst_no_result_to(rhs_block, control_flow::Jump::new(self.is, join_block));

        let phi = self.append_inst_with_results_to(
            join_block,
            control_flow::Phi::new(self.is, vec![(lhs, lhs_block), (rhs, rhs_block)]),
            &[Type::I256],
        );
        self.current_block = Some(join_block);
        self.machine.dfg.inst_results(phi)[0]
    }

    fn emit_mload_abs(&mut self, addr: u32) -> ValueId {
        let addr = self.i256_imm(addr);
        self.emit_unary(evm::EvmMload::new(self.is, addr), Type::I256)
    }

    fn emit_unary<I: Inst>(&mut self, inst: I, ty: Type) -> ValueId {
        let block = self
            .current_block
            .expect("helper instruction needs current block");
        let inst = self.append_inst_with_results_to(block, inst, &[ty]);
        self.machine.dfg.inst_results(inst)[0]
    }

    fn emit_binary<I: Inst>(&mut self, inst: I, ty: Type) -> ValueId {
        self.emit_unary(inst, ty)
    }

    fn mask_value(&mut self, value: ValueId, ty: Type) -> Result<ValueId, String> {
        if ty == Type::I256 {
            return Ok(value);
        }
        let Some(bits) = scalar_bits(ty) else {
            return Err(format!("cannot mask non-scalar type {ty:?}"));
        };
        self.mask_value_to_bits(value, bits)
    }

    fn mask_value_to_bits(&mut self, value: ValueId, bits: u16) -> Result<ValueId, String> {
        let mask = if bits == 256 {
            I256::all_one()
        } else {
            I256::from((U256::one() << bits) - U256::one())
        };
        let mask = self
            .machine
            .dfg
            .make_imm_value(Immediate::from_i256(mask, Type::I256));
        Ok(self.emit_binary(logic::And::new(self.is, value, mask), Type::I256))
    }

    fn add_const(&mut self, value: ValueId, offset: u32) -> ValueId {
        let offset = self.i256_imm(offset);
        self.emit_binary(arith::Add::new(self.is, value, offset), Type::I256)
    }

    fn lower_value(&mut self, value: ValueId) -> Result<ValueId, String> {
        if let Some(mapped) = self.map.values[value] {
            return Ok(mapped);
        }
        match self.source.dfg.value(value) {
            Value::Immediate { imm, ty } => {
                let imm = lower_immediate(*imm, *ty, self.source_module)?;
                let lowered = self.machine.dfg.make_imm_value(imm);
                self.map.values[value] = Some(lowered);
                Ok(lowered)
            }
            Value::Undef { ty } => {
                let ty = machine_type(self.source_module, *ty)?;
                let lowered = self.machine.dfg.make_undef_value(ty);
                self.map.values[value] = Some(lowered);
                Ok(lowered)
            }
            Value::Global { gv, .. } => {
                let lowered = self.machine.dfg.make_global_value(*gv);
                self.map.values[value] = Some(lowered);
                Ok(lowered)
            }
            Value::Inst { inst, .. } if self.source_inst_is_rematerializable(*inst) => {
                self.lower_inst(*inst)?;
                self.map.values[value].ok_or_else(|| {
                    format!(
                        "rematerializable value v{} in func {} did not produce a machine value",
                        value.as_u32(),
                        self.func_ref.as_u32()
                    )
                })
            }
            Value::Inst { inst, .. } => Err(format!(
                "value v{} from inst{} ({}) in func {} was used before machine lowering mapped it",
                value.as_u32(),
                inst.as_u32(),
                self.source.dfg.inst(*inst).as_text(),
                self.func_ref.as_u32()
            )),
            Value::Arg { .. } => Err(format!(
                "value v{} in func {} was used before machine lowering mapped it",
                value.as_u32(),
                self.func_ref.as_u32()
            )),
        }
    }

    fn source_inst_results_already_mapped(&self, source_inst: sonatina_ir::InstId) -> bool {
        let results = self.source.dfg.inst_results(source_inst);
        !results.is_empty()
            && results
                .iter()
                .all(|&value| self.map.values[value].is_some())
    }

    fn source_inst_is_rematerializable(&self, source_inst: sonatina_ir::InstId) -> bool {
        matches!(
            self.source_is
                .resolve_inst(self.source.dfg.inst(source_inst)),
            EvmInstKind::GetFunctionPtr(_) | EvmInstKind::SymAddr(_) | EvmInstKind::SymSize(_)
        )
    }

    fn machine_result_tys(
        &self,
        source_inst: sonatina_ir::InstId,
    ) -> Result<SmallVec<[Type; 2]>, String> {
        self.source
            .dfg
            .inst_results(source_inst)
            .iter()
            .map(|&value| machine_type(self.source_module, self.source.dfg.value_ty(value)))
            .collect()
    }

    fn insert_with_results<I: Inst>(
        &mut self,
        source_inst: sonatina_ir::InstId,
        inst: I,
    ) -> Result<(), String> {
        let result_tys = self.machine_result_tys(source_inst)?;
        let machine_inst = self.append_inst_with_results_to(
            self.current_block.expect("insert needs current block"),
            inst,
            &result_tys,
        );
        self.set_exact_lowering_provenance(source_inst, machine_inst);
        let results = self.machine.dfg.inst_results(machine_inst).to_vec();
        self.map_inst_results(source_inst, machine_inst, &results);
        Ok(())
    }

    fn insert_dyn_with_results(
        &mut self,
        source_inst: sonatina_ir::InstId,
        inst: Box<dyn Inst>,
    ) -> Result<(), String> {
        let result_tys = self.machine_result_tys(source_inst)?;
        let block = self.current_block.expect("insert needs current block");
        let mut cursor = InstInserter::at_location(CursorLocation::BlockBottom(block));
        let machine_inst = cursor.insert_inst_data_dyn(&mut self.machine, inst);
        self.set_exact_lowering_provenance(source_inst, machine_inst);
        let results = cursor.make_results(&mut self.machine, machine_inst, &result_tys);
        cursor.attach_results(&mut self.machine, machine_inst, &results);
        self.map_inst_results(source_inst, machine_inst, &results);
        Ok(())
    }

    fn insert_no_result<I: Inst>(
        &mut self,
        source_inst: sonatina_ir::InstId,
        inst: I,
    ) -> Result<(), String> {
        let block = self.current_block.expect("insert needs current block");
        let machine_inst = self.append_inst_no_result_to(block, inst);
        self.set_exact_lowering_provenance(source_inst, machine_inst);
        self.map.insts[source_inst] = Some(machine_inst);
        Ok(())
    }

    fn append_inst_with_results_to<I: Inst>(
        &mut self,
        block: BlockId,
        inst: I,
        tys: &[Type],
    ) -> sonatina_ir::InstId {
        let mut cursor = InstInserter::at_location(CursorLocation::BlockBottom(block));
        let inst = cursor.insert_inst_data(&mut self.machine, inst);
        if let Some(source_inst) = self.active_source_inst {
            self.copy_debug_context_to_machine(source_inst, inst);
        }
        let results = cursor.make_results(&mut self.machine, inst, tys);
        cursor.attach_results(&mut self.machine, inst, &results);
        inst
    }

    fn append_inst_no_result_to<I: Inst>(
        &mut self,
        block: BlockId,
        inst: I,
    ) -> sonatina_ir::InstId {
        let mut cursor = InstInserter::at_location(CursorLocation::BlockBottom(block));
        let inst = cursor.insert_inst_data(&mut self.machine, inst);
        if let Some(source_inst) = self.active_source_inst {
            self.copy_debug_context_to_machine(source_inst, inst);
        }
        inst
    }

    fn copy_debug_context_to_machine(
        &mut self,
        source_inst: sonatina_ir::InstId,
        machine_inst: sonatina_ir::InstId,
    ) {
        self.machine
            .import_inst_debug_from(self.source, source_inst, machine_inst, None);
    }

    fn set_exact_lowering_provenance(
        &mut self,
        source_inst: sonatina_ir::InstId,
        machine_inst: sonatina_ir::InstId,
    ) {
        self.copy_debug_context_to_machine(source_inst, machine_inst);
        if let Some(provenance) = self.source.inst_provenance(source_inst) {
            self.machine
                .set_inst_provenance(machine_inst, provenance.to_string());
        }
    }

    fn map_inst_results(
        &mut self,
        source_inst: sonatina_ir::InstId,
        machine_inst: sonatina_ir::InstId,
        results: &[ValueId],
    ) {
        self.map.insts[source_inst] = Some(machine_inst);
        for (&source_value, &machine_value) in self
            .source
            .dfg
            .inst_results(source_inst)
            .iter()
            .zip(results)
        {
            self.map.values[source_value] = Some(machine_value);
        }
    }

    fn alias_inst_single_result(
        &mut self,
        source_inst: sonatina_ir::InstId,
        value: ValueId,
    ) -> Result<(), String> {
        let results = self.source.dfg.inst_results(source_inst);
        if results.len() != 1 {
            return Err(format!(
                "expected single result for inst {} in func {}",
                source_inst.as_u32(),
                self.func_ref.as_u32()
            ));
        }
        self.map.insts[source_inst] = None;
        self.map.values[results[0]] = Some(value);
        Ok(())
    }

    fn machine_block(&self, source_block: BlockId) -> Result<BlockId, String> {
        self.map.blocks[source_block].ok_or_else(|| {
            format!(
                "missing machine block for b{} in func {}",
                source_block.as_u32(),
                self.func_ref.as_u32()
            )
        })
    }

    fn machine_pred_block(&self, source_block: BlockId) -> Result<BlockId, String> {
        self.block_terminal_map[source_block]
            .or(self.map.blocks[source_block])
            .ok_or_else(|| {
                format!(
                    "missing machine predecessor block for b{} in func {}",
                    source_block.as_u32(),
                    self.func_ref.as_u32()
                )
            })
    }

    fn append_machine_block(&mut self) -> BlockId {
        let block = self.machine.dfg.make_block();
        self.machine.layout.append_block(block);
        block
    }

    fn i256_imm(&mut self, value: u32) -> ValueId {
        self.machine
            .dfg
            .make_imm_value(Immediate::from_i256(I256::from(value), Type::I256))
    }

    fn source_value_imm_u32(&self, value: ValueId) -> Option<u32> {
        self.source.dfg.value_imm(value).and_then(immediate_u32)
    }

    fn alloca_abs_addr(&self, loc: ObjLoc) -> Result<u32, String> {
        self.placement_abs_addr_for_loc(loc)
            .ok_or_else(|| "alloca does not have an absolute placement".to_string())
    }

    fn placement_abs_addr_for_loc(&self, loc: ObjLoc) -> Option<u32> {
        match loc {
            ObjLoc::ScratchAbs(word) => self.word_addr(word),
            ObjLoc::StableAbs(word) => {
                let base = match self.placement.stable_mode {
                    StableMode::StaticAbs { base_word } => base_word,
                    StableMode::None | StableMode::DynamicFrame => {
                        return None;
                    }
                };
                self.word_addr(base.checked_add(word)?)
            }
            ObjLoc::StableFrame(_) | ObjLoc::StackPinned(_) => None,
        }
    }

    fn word_addr(&self, word: u32) -> Option<u32> {
        self.placement
            .arena_base
            .checked_add(word.checked_mul(WORD_BYTES)?)
    }
}

fn source_lowering_order(source: &Function) -> Vec<BlockId> {
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(source);
    let mut dom = DomTree::new();
    dom.compute(&cfg);

    let mut order = dom.rpo().to_owned();
    for block in source.layout.iter_block() {
        if !order.contains(&block) {
            order.push(block);
        }
    }
    order
}

fn lower_immediate(imm: Immediate, ty: Type, module: &ModuleCtx) -> Result<Immediate, String> {
    let ty = machine_type(module, ty)?;
    Ok(match ty {
        Type::I256 => {
            let bits = scalar_bits(imm.ty()).unwrap_or(256);
            let imm = if bits < 256 {
                I256::from(imm.as_i256().to_u256() & ((U256::one() << bits) - U256::one()))
            } else {
                imm.as_i256()
            };
            Immediate::from_i256(imm, Type::I256)
        }
        Type::Unit => return Err("unit immediate cannot be lowered".to_string()),
        _ => unreachable!("machine_type only returns unit/i256"),
    })
}

fn word_bits(ty: Type, module: &ModuleCtx) -> Option<u16> {
    if ty.is_pointer(module) {
        Some(256)
    } else {
        scalar_bits(ty)
    }
}

fn scalar_bits(ty: Type) -> Option<u16> {
    match ty {
        Type::I1 => Some(1),
        Type::I8 => Some(8),
        Type::I16 => Some(16),
        Type::I32 => Some(32),
        Type::I64 => Some(64),
        Type::I128 => Some(128),
        Type::I256 | Type::EnumTag(_) => Some(256),
        Type::Unit | Type::Compound(_) => None,
    }
}

fn align_malloc_size(size: u32) -> Result<u32, String> {
    size.checked_add(31)
        .map(|size| size & !31)
        .ok_or_else(|| "malloc size alignment overflow".to_string())
}
