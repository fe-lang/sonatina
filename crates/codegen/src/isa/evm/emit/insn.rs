use rustc_hash::FxHashSet;
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    Immediate, InstId, InstSetExt, U256, ValueId, inst::evm::inst_set::EvmInstKind, isa::Isa,
    types::CompoundType,
};

use crate::{
    machinst::{
        lower::Lower,
        vcode::{Label, SymFixup, SymFixupKind},
    },
    stackalloc::{Action, Allocator},
    transform::aggregate::shape,
};

use super::{
    super::{DynSpInitKind, FREE_PTR_SLOT, FrameSite, ObjLoc, WORD_BYTES, opcode::OpCode},
    EvmFunctionLowering,
    stack::{
        emit_dyn_frame_addr, emit_malloc_base, emit_narrow_signed_saturating_binary,
        emit_narrow_unsigned_saturating_binary, ensure_dyn_sp_init, fold_stack_actions,
        init_dyn_sp, low_bits_mask, push_bytes, scalar_bit_width, swap_op, u32_to_be, u256_to_be,
    },
};

impl EvmFunctionLowering<'_> {
    pub(crate) fn lower_insn(
        &self,
        ctx: &mut Lower<OpCode>,
        alloc: &mut dyn Allocator,
        insn: InstId,
    ) {
        if self.is_elided_block(ctx.insn_block(insn)) {
            return;
        }

        let frame_layout = self.frame_layout();
        let emit_pre_actions = |ctx: &mut Lower<OpCode>, actions: &[Action]| {
            self.emit_actions_for_site(ctx, actions, frame_layout, FrameSite::PreInst(insn))
        };
        let emit_post_actions = |ctx: &mut Lower<OpCode>, actions: &[Action]| {
            self.emit_actions_for_site(ctx, actions, frame_layout, FrameSite::PostInst(insn))
        };
        let results: SmallVec<[ValueId; 4]> = ctx.insn_results(insn).iter().copied().collect();
        let args = ctx.insn_data(insn).collect_values();
        let data = self
            .backend
            .isa
            .inst_set()
            .resolve_inst(ctx.insn_data(insn));

        let basic_op = |ctx: &mut Lower<OpCode>, ops: &[OpCode]| {
            emit_pre_actions(ctx, &alloc.read(insn, &args));
            for op in ops {
                ctx.push(*op);
            }
            emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
        };

        match &data {
            EvmInstKind::Neg(_) => basic_op(ctx, &[OpCode::PUSH0, OpCode::SUB]),
            EvmInstKind::Add(_) => basic_op(ctx, &[OpCode::ADD]),
            EvmInstKind::Uaddo(_)
            | EvmInstKind::Uaddsat(_)
            | EvmInstKind::Saddo(_)
            | EvmInstKind::Saddsat(_)
            | EvmInstKind::Usubo(_)
            | EvmInstKind::Usubsat(_)
            | EvmInstKind::Ssubo(_)
            | EvmInstKind::Ssubsat(_)
            | EvmInstKind::Umulo(_)
            | EvmInstKind::Umulsat(_)
            | EvmInstKind::Smulo(_)
            | EvmInstKind::Smulsat(_)
            | EvmInstKind::Snego(_) => {
                panic!("overflow instructions must be legalized before EVM lowering")
            }
            EvmInstKind::Mul(_) => basic_op(ctx, &[OpCode::MUL]),
            EvmInstKind::Sub(_) => basic_op(ctx, &[OpCode::SUB]),
            EvmInstKind::Sdiv(_)
            | EvmInstKind::Udiv(_)
            | EvmInstKind::Umod(_)
            | EvmInstKind::Smod(_) => {
                panic!("generic integer div/mod must be legalized before EVM lowering")
            }
            EvmInstKind::Shl(_) => basic_op(ctx, &[OpCode::SHL]),
            EvmInstKind::Shr(_) => basic_op(ctx, &[OpCode::SHR]),
            EvmInstKind::Sar(_) => basic_op(ctx, &[OpCode::SAR]),
            EvmInstKind::Sext(_) => {
                let from = args[0];
                let src_ty = ctx.value_ty(from);
                let src_bits = scalar_bit_width(src_ty, ctx.module).unwrap_or(256);

                emit_pre_actions(ctx, &alloc.read(insn, &args));

                if src_bits == 1 {
                    if let Some(mask) = low_bits_mask(src_bits) {
                        push_bytes(ctx, &u256_to_be(&mask));
                        ctx.push(OpCode::AND);
                    }
                    ctx.push(OpCode::PUSH0);
                    ctx.push(OpCode::SUB);
                } else if (8..256).contains(&src_bits) {
                    let src_bytes = (src_bits / 8) as u8;
                    debug_assert!(src_bytes > 0 && src_bytes <= 32);
                    push_bytes(ctx, &[src_bytes - 1]);
                    ctx.push(OpCode::SIGNEXTEND);
                }

                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::Zext(_) => {
                let from = args[0];
                let src_ty = ctx.value_ty(from);
                let src_bits = scalar_bit_width(src_ty, ctx.module).unwrap_or(256);

                emit_pre_actions(ctx, &alloc.read(insn, &args));
                if let Some(mask) = low_bits_mask(src_bits) {
                    push_bytes(ctx, &u256_to_be(&mask));
                    ctx.push(OpCode::AND);
                }
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::Trunc(trunc) => {
                let dst_ty = *trunc.ty();
                let dst_bits = scalar_bit_width(dst_ty, ctx.module).unwrap_or(256);

                emit_pre_actions(ctx, &alloc.read(insn, &args));
                if let Some(mask) = low_bits_mask(dst_bits) {
                    push_bytes(ctx, &u256_to_be(&mask));
                    ctx.push(OpCode::AND);
                }
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::Bitcast(_) => {
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::IntToPtr(_) => {
                let from = args[0];
                let src_ty = ctx.value_ty(from);
                let src_bits = scalar_bit_width(src_ty, ctx.module).unwrap_or(256);

                emit_pre_actions(ctx, &alloc.read(insn, &args));
                if let Some(mask) = low_bits_mask(src_bits) {
                    push_bytes(ctx, &u256_to_be(&mask));
                    ctx.push(OpCode::AND);
                }
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::PtrToInt(ptr_to_int) => {
                let dst_ty = *ptr_to_int.ty();
                let dst_bits = scalar_bit_width(dst_ty, ctx.module).unwrap_or(256);

                emit_pre_actions(ctx, &alloc.read(insn, &args));
                if let Some(mask) = low_bits_mask(dst_bits) {
                    push_bytes(ctx, &u256_to_be(&mask));
                    ctx.push(OpCode::AND);
                }
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::Lt(_) => basic_op(ctx, &[OpCode::LT]),
            EvmInstKind::Gt(_) => basic_op(ctx, &[OpCode::GT]),
            EvmInstKind::Slt(_) => basic_op(ctx, &[OpCode::SLT]),
            EvmInstKind::Sgt(_) => basic_op(ctx, &[OpCode::SGT]),
            EvmInstKind::Le(_) => basic_op(ctx, &[OpCode::GT, OpCode::ISZERO]),
            EvmInstKind::Ge(_) => basic_op(ctx, &[OpCode::LT, OpCode::ISZERO]),
            EvmInstKind::Sle(_) => basic_op(ctx, &[OpCode::SGT, OpCode::ISZERO]),
            EvmInstKind::Sge(_) => basic_op(ctx, &[OpCode::SLT, OpCode::ISZERO]),
            EvmInstKind::Eq(_) => basic_op(ctx, &[OpCode::EQ]),
            EvmInstKind::Ne(_) => basic_op(ctx, &[OpCode::EQ, OpCode::ISZERO]),
            EvmInstKind::IsZero(_) => basic_op(ctx, &[OpCode::ISZERO]),
            EvmInstKind::Not(_) => basic_op(ctx, &[OpCode::NOT]),
            EvmInstKind::And(_) => basic_op(ctx, &[OpCode::AND]),
            EvmInstKind::Or(_) => basic_op(ctx, &[OpCode::OR]),
            EvmInstKind::Xor(_) => basic_op(ctx, &[OpCode::XOR]),
            EvmInstKind::Jump(jump) => {
                let dest = self.canonical_block_target(*jump.dest());
                emit_pre_actions(ctx, &alloc.read(insn, &[]));

                if !ctx.is_next_block(dest) {
                    let push_op = ctx.push(OpCode::PUSH1);
                    ctx.add_label_reference(push_op, Label::Block(dest));
                    ctx.push(OpCode::JUMP);
                }
            }
            EvmInstKind::Br(br) => {
                let nz_dest = self.canonical_block_target(*br.nz_dest());
                let z_dest = self.canonical_block_target(*br.z_dest());

                emit_pre_actions(ctx, &alloc.read(insn, &args));
                if nz_dest == z_dest {
                    ctx.push(OpCode::POP);
                    if !ctx.is_next_block(nz_dest) {
                        ctx.push_jump_target(OpCode::PUSH1, Label::Block(nz_dest));
                        ctx.push(OpCode::JUMP);
                    }
                } else if ctx.is_next_block(nz_dest) {
                    ctx.push(OpCode::ISZERO);
                    ctx.push_jump_target(OpCode::PUSH1, Label::Block(z_dest));
                    ctx.push(OpCode::JUMPI);
                } else {
                    ctx.push_jump_target(OpCode::PUSH1, Label::Block(nz_dest));
                    ctx.push(OpCode::JUMPI);

                    if !ctx.is_next_block(z_dest) {
                        ctx.push_jump_target(OpCode::PUSH1, Label::Block(z_dest));
                        ctx.push(OpCode::JUMP);
                    }
                }
            }
            EvmInstKind::Phi(_) => {}
            EvmInstKind::Unreachable(_) => {
                emit_pre_actions(ctx, &alloc.read(insn, &[]));
                ctx.push(OpCode::INVALID);
            }
            EvmInstKind::BrTable(br) => {
                let table = br.table().clone();
                let default = (*br.default()).map(|dest| self.canonical_block_target(dest));

                assert!(!table.is_empty(), "empty br_table");
                assert_eq!(
                    table.len(),
                    table
                        .iter()
                        .map(|(value, _)| value)
                        .collect::<FxHashSet<_>>()
                        .len(),
                    "br_table has duplicate scrutinee values"
                );

                for (case_idx, (_, dest)) in table.iter().enumerate() {
                    let dest = self.canonical_block_target(*dest);
                    self.emit_actions_for_site(
                        ctx,
                        &alloc.read_br_table_case(insn, case_idx),
                        frame_layout,
                        FrameSite::PreInst(insn),
                    );
                    ctx.push(OpCode::EQ);
                    ctx.push_jump_target(OpCode::PUSH1, Label::Block(dest));
                    ctx.push(OpCode::JUMPI);
                }

                if let Some(dest) = default
                    && !ctx.is_next_block(dest)
                {
                    ctx.push_jump_target(OpCode::PUSH1, Label::Block(dest));
                    ctx.push(OpCode::JUMP);
                }
            }
            EvmInstKind::Call(call) => {
                let callee = *call.callee();
                let mut actions = alloc.read(insn, &args);

                let cont_pos = actions
                    .iter()
                    .position(|action| matches!(action, Action::PushContinuationOffset));
                if let Some(cont_pos) = cont_pos {
                    let suffix: SmallVec<[Action; 2]> = actions.drain(cont_pos + 1..).collect();
                    let marker = actions.remove(cont_pos);
                    debug_assert_eq!(
                        marker,
                        Action::PushContinuationOffset,
                        "expected continuation marker at split point"
                    );

                    let prefix_folded_len = fold_stack_actions(&actions).len();
                    self.emit_actions_for_site_from_offset(
                        ctx,
                        &actions,
                        frame_layout,
                        FrameSite::PreInst(insn),
                        0,
                    );

                    let push_callback = ctx.push(OpCode::PUSH1);

                    self.emit_actions_for_site_from_offset(
                        ctx,
                        &suffix,
                        frame_layout,
                        FrameSite::PreInst(insn),
                        prefix_folded_len,
                    );

                    match self.frontier_init_kind(insn) {
                        Some(DynSpInitKind::Always) => init_dyn_sp(ctx, self.dyn_base()),
                        Some(DynSpInitKind::Checked) => ensure_dyn_sp_init(ctx, self.dyn_base()),
                        None => {}
                    }

                    let p = ctx.push(OpCode::PUSH1);
                    ctx.add_label_reference(p, Label::Function(callee));
                    ctx.push(OpCode::JUMP);

                    let jumpdest_op = ctx.push(OpCode::JUMPDEST);
                    ctx.add_label_reference(push_callback, Label::Insn(jumpdest_op));

                    emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
                } else {
                    self.emit_actions_for_site(
                        ctx,
                        &actions,
                        frame_layout,
                        FrameSite::PreInst(insn),
                    );

                    match self.frontier_init_kind(insn) {
                        Some(DynSpInitKind::Always) => init_dyn_sp(ctx, self.dyn_base()),
                        Some(DynSpInitKind::Checked) => ensure_dyn_sp_init(ctx, self.dyn_base()),
                        None => {}
                    }

                    let p = ctx.push(OpCode::PUSH1);
                    ctx.add_label_reference(p, Label::Function(callee));
                    ctx.push(OpCode::JUMP);
                }
            }
            EvmInstKind::Return(_) => {
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                if !self.has_lazy_frame_lowering()
                    && let Some(frame_layout) = frame_layout
                {
                    super::stack::leave_frame(ctx, frame_layout);
                }

                for depth in 1..=args.len() {
                    ctx.push(swap_op(depth as u8));
                }
                ctx.push(OpCode::JUMP);
            }
            EvmInstKind::Mload(_) => basic_op(ctx, &[OpCode::MLOAD]),
            EvmInstKind::Mstore(mstore) => {
                let ty_size = self
                    .backend
                    .isa
                    .type_layout()
                    .size_of(*mstore.ty(), ctx.module)
                    .unwrap();

                emit_pre_actions(ctx, &alloc.read(insn, &args));
                if ty_size == 0 {
                    ctx.push(OpCode::POP);
                    ctx.push(OpCode::POP);
                } else {
                    assert!(
                        ty_size == 32,
                        "word-slot model: expected 32-byte store (got {ty_size})"
                    );
                    ctx.push(OpCode::MSTORE);
                }
            }
            EvmInstKind::EvmMcopy(_) => basic_op(ctx, &[OpCode::MCOPY]),
            EvmInstKind::Gep(_) => {
                if args.is_empty() {
                    panic!("gep without operands");
                }

                let gep_plan = build_gep_lower_plan(ctx, &args);
                debug_assert_eq!(
                    gep_plan.runtime_args.len(),
                    1 + gep_plan.runtime_index_count(),
                    "GEP runtime args/step consumption mismatch",
                );

                if let Some(addr_bytes) =
                    self.try_fold_gep_static_arena_addr(ctx, &args, &gep_plan.steps)
                {
                    self.emit_actions_for_site(
                        ctx,
                        &alloc.read(insn, gep_plan.runtime_args.as_slice()),
                        frame_layout,
                        FrameSite::PreInst(insn),
                    );
                    for _ in 0..gep_plan.runtime_args.len() {
                        ctx.push(OpCode::POP);
                    }
                    push_bytes(ctx, &u32_to_be(addr_bytes));
                    emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
                    return;
                }

                self.emit_actions_for_site(
                    ctx,
                    &alloc.read(insn, gep_plan.runtime_args.as_slice()),
                    frame_layout,
                    FrameSite::PreInst(insn),
                );
                for step in gep_plan.steps {
                    match step {
                        GepStep::AddConst {
                            offset_bytes,
                            consume_index,
                        } => {
                            if consume_index {
                                ctx.push(OpCode::SWAP1);
                                ctx.push(OpCode::POP);
                            }
                            if offset_bytes != 0 {
                                push_bytes(ctx, &u32_to_be(offset_bytes));
                                ctx.push(OpCode::ADD);
                            }
                        }
                        GepStep::AddScaled(scale_bytes) => {
                            ctx.push(OpCode::SWAP1);
                            push_bytes(ctx, &u32_to_be(scale_bytes));
                            ctx.push(OpCode::MUL);
                            ctx.push(OpCode::ADD);
                        }
                    }
                }

                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::Alloca(_) => {
                let mem_plan = &self.function_plan.mem_plan;
                let loc = *mem_plan.alloca_loc.get(&insn).expect("missing alloca plan");

                emit_pre_actions(ctx, &alloc.read(insn, &args));

                match loc {
                    ObjLoc::ScratchAbs(_) | ObjLoc::StableAbs(_) => {
                        let addr_bytes =
                            obj_loc_abs_addr_bytes(mem_plan, loc).expect("alloca abs addr missing");
                        push_bytes(ctx, &u32_to_be(addr_bytes));
                    }
                    ObjLoc::StableFrame(offset_words) => {
                        let frame_layout = frame_layout
                            .expect("stable frame alloca requires an addressable dynamic frame");
                        self.emit_lazy_frame_enter_if_site_matches(
                            ctx,
                            Some(frame_layout),
                            FrameSite::Inst(insn),
                        );
                        emit_dyn_frame_addr(
                            ctx,
                            frame_layout,
                            frame_layout.expect_local_word(offset_words, "alloca"),
                        );
                        if self.lazy_frame_plan_matches(|plan| {
                            plan.exit_after_site(FrameSite::Inst(insn))
                        }) {
                            super::stack::leave_frame(ctx, frame_layout);
                        }
                    }
                    ObjLoc::StackPinned(_) => panic!("stack-pinned allocas are not implemented"),
                }

                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::ConstRef(_)
            | EvmInstKind::ConstProj(_)
            | EvmInstKind::ConstIndex(_)
            | EvmInstKind::ConstLoad(_)
            | EvmInstKind::ObjAlloc(_)
            | EvmInstKind::ObjProj(_)
            | EvmInstKind::ObjIndex(_)
            | EvmInstKind::ObjLoad(_)
            | EvmInstKind::ObjStore(_)
            | EvmInstKind::ObjInitConst(_)
            | EvmInstKind::EnumMake(_)
            | EvmInstKind::EnumTag(_)
            | EvmInstKind::EnumIsVariant(_)
            | EvmInstKind::EnumAssertVariant(_)
            | EvmInstKind::EnumAssertVariantRef(_)
            | EvmInstKind::EnumExtract(_)
            | EvmInstKind::EnumSetTag(_)
            | EvmInstKind::EnumWriteVariant(_)
            | EvmInstKind::EnumGetTag(_)
            | EvmInstKind::EnumProj(_)
            | EvmInstKind::ObjMaterializeStack(_)
            | EvmInstKind::ObjMaterializeHeap(_)
            | EvmInstKind::MemAllocDynamic(_) => {
                panic!(
                    "enum/object lowering invariant violated: high-level enum/object instruction reached EVM lowering"
                )
            }
            EvmInstKind::EvmStop(_) => basic_op(ctx, &[OpCode::STOP]),
            EvmInstKind::EvmSdiv(_) => basic_op(ctx, &[OpCode::SDIV]),
            EvmInstKind::EvmUdiv(_) => basic_op(ctx, &[OpCode::DIV]),
            EvmInstKind::EvmSdivo(_)
            | EvmInstKind::EvmUdivo(_)
            | EvmInstKind::EvmUmodo(_)
            | EvmInstKind::EvmSmodo(_) => {
                panic!("checked EVM div/mod instructions must be legalized before EVM lowering")
            }
            EvmInstKind::EvmUaddsat(sat) => {
                let bits = scalar_bit_width(*sat.ty(), ctx.module)
                    .expect("evm_uaddsat requires scalar type");
                assert!(
                    bits < 256,
                    "full-width saturating add must be legalized earlier"
                );
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                emit_narrow_unsigned_saturating_binary(
                    ctx,
                    OpCode::ADD,
                    bits,
                    low_bits_mask(bits).unwrap(),
                );
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::EvmSaddsat(sat) => {
                let bits = scalar_bit_width(*sat.ty(), ctx.module)
                    .expect("evm_saddsat requires scalar type");
                assert!(
                    bits < 256,
                    "full-width saturating add must be legalized earlier"
                );
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                emit_narrow_signed_saturating_binary(ctx, OpCode::ADD, bits);
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::EvmUsubsat(sat) => {
                let bits = scalar_bit_width(*sat.ty(), ctx.module)
                    .expect("evm_usubsat requires scalar type");
                assert!(
                    bits < 256,
                    "full-width saturating sub must be legalized earlier"
                );
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                emit_narrow_unsigned_saturating_binary(ctx, OpCode::SUB, bits, U256::zero());
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::EvmSsubsat(sat) => {
                let bits = scalar_bit_width(*sat.ty(), ctx.module)
                    .expect("evm_ssubsat requires scalar type");
                assert!(
                    bits < 256,
                    "full-width saturating sub must be legalized earlier"
                );
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                emit_narrow_signed_saturating_binary(ctx, OpCode::SUB, bits);
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::EvmUmulsat(sat) => {
                let bits = scalar_bit_width(*sat.ty(), ctx.module)
                    .expect("evm_umulsat requires scalar type");
                assert!(
                    bits < 256,
                    "full-width saturating mul must be legalized earlier"
                );
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                emit_narrow_unsigned_saturating_binary(
                    ctx,
                    OpCode::MUL,
                    bits,
                    low_bits_mask(bits).unwrap(),
                );
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::EvmSmulsat(sat) => {
                let bits = scalar_bit_width(*sat.ty(), ctx.module)
                    .expect("evm_smulsat requires scalar type");
                assert!(
                    bits < 256,
                    "full-width saturating mul must be legalized earlier"
                );
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                emit_narrow_signed_saturating_binary(ctx, OpCode::MUL, bits);
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::EvmUmod(_) => basic_op(ctx, &[OpCode::MOD]),
            EvmInstKind::EvmSmod(_) => basic_op(ctx, &[OpCode::SMOD]),
            EvmInstKind::EvmAddMod(_) => basic_op(ctx, &[OpCode::ADDMOD]),
            EvmInstKind::EvmMulMod(_) => basic_op(ctx, &[OpCode::MULMOD]),
            EvmInstKind::EvmExp(_) => basic_op(ctx, &[OpCode::EXP]),
            EvmInstKind::EvmSignExtend(_) => basic_op(ctx, &[OpCode::SIGNEXTEND]),
            EvmInstKind::EvmByte(_) => basic_op(ctx, &[OpCode::BYTE]),
            EvmInstKind::EvmClz(_) => basic_op(ctx, &[OpCode::CLZ]),
            EvmInstKind::EvmKeccak256(_) => basic_op(ctx, &[OpCode::KECCAK256]),
            EvmInstKind::EvmAddress(_) => basic_op(ctx, &[OpCode::ADDRESS]),
            EvmInstKind::EvmBalance(_) => basic_op(ctx, &[OpCode::BALANCE]),
            EvmInstKind::EvmOrigin(_) => basic_op(ctx, &[OpCode::ORIGIN]),
            EvmInstKind::EvmCaller(_) => basic_op(ctx, &[OpCode::CALLER]),
            EvmInstKind::EvmCallValue(_) => basic_op(ctx, &[OpCode::CALLVALUE]),
            EvmInstKind::EvmCalldataLoad(_) => basic_op(ctx, &[OpCode::CALLDATALOAD]),
            EvmInstKind::EvmCalldataCopy(_) => basic_op(ctx, &[OpCode::CALLDATACOPY]),
            EvmInstKind::EvmCalldataSize(_) => basic_op(ctx, &[OpCode::CALLDATASIZE]),
            EvmInstKind::EvmCodeSize(_) => basic_op(ctx, &[OpCode::CODESIZE]),
            EvmInstKind::EvmCodeCopy(_) => basic_op(ctx, &[OpCode::CODECOPY]),
            EvmInstKind::EvmGasPrice(_) => basic_op(ctx, &[OpCode::GASPRICE]),
            EvmInstKind::EvmExtCodeSize(_) => basic_op(ctx, &[OpCode::EXTCODESIZE]),
            EvmInstKind::EvmExtCodeCopy(_) => basic_op(ctx, &[OpCode::EXTCODECOPY]),
            EvmInstKind::EvmReturnDataSize(_) => basic_op(ctx, &[OpCode::RETURNDATASIZE]),
            EvmInstKind::EvmReturnDataCopy(_) => basic_op(ctx, &[OpCode::RETURNDATACOPY]),
            EvmInstKind::EvmExtCodeHash(_) => basic_op(ctx, &[OpCode::EXTCODEHASH]),
            EvmInstKind::EvmBlockHash(_) => basic_op(ctx, &[OpCode::BLOCKHASH]),
            EvmInstKind::EvmCoinBase(_) => basic_op(ctx, &[OpCode::COINBASE]),
            EvmInstKind::EvmTimestamp(_) => basic_op(ctx, &[OpCode::TIMESTAMP]),
            EvmInstKind::EvmNumber(_) => basic_op(ctx, &[OpCode::NUMBER]),
            EvmInstKind::EvmPrevRandao(_) => basic_op(ctx, &[OpCode::PREVRANDAO]),
            EvmInstKind::EvmGasLimit(_) => basic_op(ctx, &[OpCode::GASLIMIT]),
            EvmInstKind::EvmChainId(_) => basic_op(ctx, &[OpCode::CHAINID]),
            EvmInstKind::EvmSelfBalance(_) => basic_op(ctx, &[OpCode::SELFBALANCE]),
            EvmInstKind::EvmBaseFee(_) => basic_op(ctx, &[OpCode::BASEFEE]),
            EvmInstKind::EvmBlobHash(_) => basic_op(ctx, &[OpCode::BLOBHASH]),
            EvmInstKind::EvmBlobBaseFee(_) => basic_op(ctx, &[OpCode::BLOBBASEFEE]),
            EvmInstKind::EvmMstore8(_) => basic_op(ctx, &[OpCode::MSTORE8]),
            EvmInstKind::EvmSload(_) => basic_op(ctx, &[OpCode::SLOAD]),
            EvmInstKind::EvmSstore(_) => basic_op(ctx, &[OpCode::SSTORE]),
            EvmInstKind::EvmMsize(_) => basic_op(ctx, &[OpCode::MSIZE]),
            EvmInstKind::EvmGas(_) => basic_op(ctx, &[OpCode::GAS]),
            EvmInstKind::EvmTload(_) => basic_op(ctx, &[OpCode::TLOAD]),
            EvmInstKind::EvmTstore(_) => basic_op(ctx, &[OpCode::TSTORE]),
            EvmInstKind::EvmLog0(_) => basic_op(ctx, &[OpCode::LOG0]),
            EvmInstKind::EvmLog1(_) => basic_op(ctx, &[OpCode::LOG1]),
            EvmInstKind::EvmLog2(_) => basic_op(ctx, &[OpCode::LOG2]),
            EvmInstKind::EvmLog3(_) => basic_op(ctx, &[OpCode::LOG3]),
            EvmInstKind::EvmLog4(_) => basic_op(ctx, &[OpCode::LOG4]),
            EvmInstKind::EvmCreate(_) => basic_op(ctx, &[OpCode::CREATE]),
            EvmInstKind::EvmCall(_) => basic_op(ctx, &[OpCode::CALL]),
            EvmInstKind::EvmCallCode(_) => basic_op(ctx, &[OpCode::CALLCODE]),
            EvmInstKind::EvmReturn(_) => basic_op(ctx, &[OpCode::RETURN]),
            EvmInstKind::EvmDelegateCall(_) => basic_op(ctx, &[OpCode::DELEGATECALL]),
            EvmInstKind::EvmCreate2(_) => basic_op(ctx, &[OpCode::CREATE2]),
            EvmInstKind::EvmStaticCall(_) => basic_op(ctx, &[OpCode::STATICCALL]),
            EvmInstKind::EvmRevert(_) => basic_op(ctx, &[OpCode::REVERT]),
            EvmInstKind::EvmSelfDestruct(_) => basic_op(ctx, &[OpCode::SELFDESTRUCT]),
            EvmInstKind::EvmMalloc(_) => {
                let needs_dyn_sp_clamp = self.malloc_needs_dyn_sp_clamp(insn);
                let has_persistent_mallocs = self.section_plan.has_persistent_mallocs;
                let free_ptr_slot_may_be_written = self.section_plan.free_ptr_slot_may_be_written;
                let mem_plan = &self.function_plan.mem_plan;
                let is_transient = mem_plan.transient_mallocs.contains(&insn);

                let dyn_base_words = self
                    .dyn_base()
                    .checked_sub(self.section_plan.arena_base)
                    .expect("dyn base below arena base")
                    / WORD_BYTES;
                let mut future_words = mem_plan
                    .malloc_future_abs_words
                    .get(&insn)
                    .copied()
                    .unwrap_or(dyn_base_words);
                let escape_kinds = mem_plan
                    .malloc_escape_kinds
                    .get(&insn)
                    .copied()
                    .unwrap_or_default();
                if escape_kinds.has_global_or_unknown() {
                    future_words = future_words.max(dyn_base_words);
                } else if escape_kinds.is_return_only() {
                    future_words = future_words.max(mem_plan.return_escape_caller_abs_words);
                }

                let min_base_bytes = self
                    .section_plan
                    .arena_base
                    .checked_add(
                        WORD_BYTES
                            .checked_mul(future_words)
                            .expect("malloc static bound bytes overflow"),
                    )
                    .expect("malloc static bound bytes overflow");

                let size = *args.first().expect("evm_malloc missing size");
                let aligned_size_imm = ctx.value_imm(size).map(aligned_malloc_size_imm);
                let runtime_args: SmallVec<[ValueId; 1]> = if aligned_size_imm.is_some() {
                    smallvec![]
                } else {
                    smallvec![size]
                };
                self.emit_actions_for_site(
                    ctx,
                    &alloc.read(insn, runtime_args.as_slice()),
                    frame_layout,
                    FrameSite::PreInst(insn),
                );

                if is_transient {
                    if aligned_size_imm.is_none() {
                        ctx.push(OpCode::POP);
                    }

                    let can_use_fixed_transient_base = !needs_dyn_sp_clamp
                        && !has_persistent_mallocs
                        && !free_ptr_slot_may_be_written;
                    if can_use_fixed_transient_base {
                        push_bytes(ctx, &u32_to_be(min_base_bytes));
                    } else {
                        emit_malloc_base(ctx, min_base_bytes, needs_dyn_sp_clamp);
                    }

                    emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
                    return;
                }

                if aligned_size_imm.is_none() {
                    push_bytes(ctx, &[0x1f]);
                    ctx.push(OpCode::ADD);
                    push_bytes(ctx, &[0x1f]);
                    ctx.push(OpCode::NOT);
                    ctx.push(OpCode::AND);
                }

                emit_malloc_base(ctx, min_base_bytes, needs_dyn_sp_clamp);

                if let Some(aligned) = aligned_size_imm {
                    ctx.push(OpCode::DUP1);
                    if !aligned.is_zero() {
                        push_bytes(ctx, &u256_to_be(&aligned));
                        ctx.push(OpCode::ADD);
                    }
                } else {
                    ctx.push(OpCode::DUP1);
                    ctx.push(OpCode::SWAP2);
                    ctx.push(OpCode::ADD);
                }
                push_bytes(ctx, &[FREE_PTR_SLOT]);
                ctx.push(OpCode::MSTORE);

                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::InsertValue(_) => {
                panic!(
                    "aggregate legalization invariant violated: insert_value reached EVM lowering"
                )
            }
            EvmInstKind::ExtractValue(_) => {
                panic!(
                    "aggregate legalization invariant violated: extract_value reached EVM lowering"
                )
            }
            EvmInstKind::GetFunctionPtr(get_fn) => {
                let func = *get_fn.func();
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                ctx.push_jump_target(OpCode::PUSH1, Label::Function(func));
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::EvmInvalid(_) => basic_op(ctx, &[OpCode::INVALID]),
            EvmInstKind::SymAddr(sym_addr) => {
                let sym = sym_addr.sym().clone();
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                ctx.push_sym_fixup(
                    OpCode::PUSH0,
                    SymFixup {
                        kind: SymFixupKind::Addr,
                        sym,
                    },
                );
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::SymSize(sym_size) => {
                let sym = sym_size.sym().clone();
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                ctx.push_sym_fixup(
                    OpCode::PUSH0,
                    SymFixup {
                        kind: SymFixupKind::Size,
                        sym,
                    },
                );
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
        }
    }

    fn try_fold_gep_static_arena_addr(
        &self,
        ctx: &Lower<OpCode>,
        args: &[ValueId],
        steps: &[GepStep],
    ) -> Option<u32> {
        let &base = args.first()?;
        let base_addr = self.try_fold_static_arena_addr_value(ctx, base)?;
        let offset = gep_const_offset_bytes(steps)?;
        base_addr.checked_add(offset)
    }

    fn try_fold_static_arena_addr_value(&self, ctx: &Lower<OpCode>, value: ValueId) -> Option<u32> {
        let inst = ctx.value_def_inst(value)?;
        let data = self
            .backend
            .isa
            .inst_set()
            .resolve_inst(ctx.insn_data(inst));
        match data {
            EvmInstKind::Alloca(_) => {
                let loc = self.function_plan.mem_plan.alloca_loc.get(&inst).copied()?;
                obj_loc_abs_addr_bytes(&self.function_plan.mem_plan, loc)
            }
            EvmInstKind::Bitcast(bitcast) => {
                self.try_fold_static_arena_addr_value(ctx, *bitcast.from())
            }
            EvmInstKind::Gep(gep) => {
                let values = gep.values();
                let &base = values.first()?;
                let base_addr = self.try_fold_static_arena_addr_value(ctx, base)?;
                let steps = build_gep_lower_plan(ctx, values.as_slice()).steps;
                let offset = gep_const_offset_bytes(&steps)?;
                base_addr.checked_add(offset)
            }
            _ => None,
        }
    }
}

#[derive(Clone, Copy)]
enum GepStep {
    AddConst {
        offset_bytes: u32,
        consume_index: bool,
    },
    AddScaled(u32),
}

struct GepLowerPlan {
    runtime_args: SmallVec<[ValueId; 8]>,
    steps: Vec<GepStep>,
}

impl GepLowerPlan {
    fn runtime_index_count(&self) -> usize {
        self.steps
            .iter()
            .filter(|step| match step {
                GepStep::AddConst { consume_index, .. } => *consume_index,
                GepStep::AddScaled(_) => true,
            })
            .count()
    }
}

fn build_gep_lower_plan(ctx: &Lower<OpCode>, args: &[ValueId]) -> GepLowerPlan {
    let Some((&base, _indices)) = args.split_first() else {
        panic!("gep without operands");
    };

    let mut current_ty = ctx.value_ty(args[0]);
    if !current_ty.is_pointer(ctx.module) {
        panic!("gep base must be a pointer (got {current_ty:?})");
    }

    let mut runtime_args = SmallVec::<[ValueId; 8]>::new();
    runtime_args.push(base);
    let mut steps = Vec::new();
    for &idx_val in args.iter().skip(1) {
        let Some(cmpd) = current_ty.resolve_compound(ctx.module) else {
            panic!("invalid gep: indexing into scalar {current_ty:?}");
        };

        let idx_imm_u32 = ctx.value_imm(idx_val).and_then(super::stack::immediate_u32);

        match cmpd {
            CompoundType::Ptr(elem_ty) => {
                let elem_size = u32::try_from(ctx.module.size_of_unchecked(elem_ty))
                    .expect("gep element too large");
                steps.push(gep_step(elem_size, idx_imm_u32));
                if idx_imm_u32.is_none() {
                    runtime_args.push(idx_val);
                }
                current_ty = elem_ty;
            }
            CompoundType::Array { elem, .. } => {
                let elem_size = u32::try_from(ctx.module.size_of_unchecked(elem))
                    .expect("gep element too large");
                steps.push(gep_step(elem_size, idx_imm_u32));
                if idx_imm_u32.is_none() {
                    runtime_args.push(idx_val);
                }
                current_ty = elem;
            }
            CompoundType::Struct(s) => {
                let Some(idx) = idx_imm_u32.map(|idx| idx as usize) else {
                    panic!("struct gep indices must be immediate constants");
                };
                let (field_offset, field_ty) =
                    shape::struct_field_offset_bytes(&s.fields, s.packed, idx, ctx.module)
                        .unwrap_or_else(|| {
                            panic!("invalid struct gep: packed/unsupported field projection")
                        });
                steps.push(GepStep::AddConst {
                    offset_bytes: field_offset,
                    consume_index: false,
                });
                current_ty = field_ty;
            }
            CompoundType::Func { .. } => panic!("invalid gep: indexing into function type"),
            CompoundType::Enum(_) => panic!("invalid gep: indexing into enum type"),
            CompoundType::ObjRef(_) => panic!("invalid gep: indexing into object-reference type"),
            CompoundType::ConstRef(_) => panic!("invalid gep: indexing into const-reference type"),
        }
    }

    GepLowerPlan {
        runtime_args,
        steps,
    }
}

fn gep_const_offset_bytes(steps: &[GepStep]) -> Option<u32> {
    let mut total: u32 = 0;
    for &step in steps {
        let GepStep::AddConst { offset_bytes, .. } = step else {
            return None;
        };
        total = total.checked_add(offset_bytes)?;
    }
    Some(total)
}

fn gep_step(elem_size_bytes: u32, idx: Option<u32>) -> GepStep {
    let Some(idx) = idx else {
        return if elem_size_bytes == 0 {
            GepStep::AddConst {
                offset_bytes: 0,
                consume_index: true,
            }
        } else {
            GepStep::AddScaled(elem_size_bytes)
        };
    };

    GepStep::AddConst {
        offset_bytes: elem_size_bytes
            .checked_mul(idx)
            .expect("gep offset overflow"),
        consume_index: false,
    }
}

fn obj_loc_abs_addr_bytes(mem_plan: &super::super::FuncMemPlan, loc: ObjLoc) -> Option<u32> {
    mem_plan.abs_addr_for_loc(loc)
}

fn aligned_malloc_size_imm(imm: Immediate) -> U256 {
    let size = imm.as_i256().to_u256();
    let (size_padded, _) = size.overflowing_add(U256::from(0x1f_u8));
    size_padded & !U256::from(0x1f_u8)
}
