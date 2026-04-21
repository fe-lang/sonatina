use rustc_hash::FxHashSet;
use smallvec::SmallVec;
use sonatina_ir::{InstId, InstSetExt, U256, ValueId, inst::evm::inst_set::EvmInstKind, isa::Isa};

use crate::{
    machinst::{
        lower::Lower,
        vcode::{Label, SymFixup, SymFixupKind},
    },
    stackalloc::{Action, Allocator},
};

use super::{
    super::opcode::OpCode,
    EvmFunctionLowering,
    stack::{
        emit_narrow_signed_saturating_binary, emit_narrow_unsigned_saturating_binary,
        low_bits_mask, scalar_bit_width, swap_op,
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
            self.emit_actions(ctx, actions, frame_layout)
        };
        let emit_post_actions = |ctx: &mut Lower<OpCode>, actions: &[Action]| {
            self.emit_actions(ctx, actions, frame_layout)
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
            EvmInstKind::Sext(_)
            | EvmInstKind::Zext(_)
            | EvmInstKind::Trunc(_)
            | EvmInstKind::Bitcast(_)
            | EvmInstKind::IntToPtr(_)
            | EvmInstKind::PtrToInt(_) => {
                panic!("casts must be lowered before EVM machine final lowering")
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
                    self.emit_actions(ctx, &alloc.read_br_table_case(insn, case_idx), frame_layout);
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

                    self.emit_actions(ctx, &actions, frame_layout);

                    let push_callback = ctx.push(OpCode::PUSH1);

                    self.emit_actions(ctx, &suffix, frame_layout);

                    let p = ctx.push(OpCode::PUSH1);
                    ctx.add_label_reference(p, Label::Function(callee));
                    ctx.push(OpCode::JUMP);

                    let jumpdest_op = ctx.push(OpCode::JUMPDEST);
                    ctx.add_label_reference(push_callback, Label::Insn(jumpdest_op));

                    emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
                } else {
                    self.emit_actions(ctx, &actions, frame_layout);

                    let p = ctx.push(OpCode::PUSH1);
                    ctx.add_label_reference(p, Label::Function(callee));
                    ctx.push(OpCode::JUMP);
                }
            }
            EvmInstKind::Return(_) => {
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                if let Some(frame_layout) = frame_layout {
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
                panic!("gep must be lowered before EVM machine final lowering")
            }
            EvmInstKind::Alloca(_) => {
                panic!("alloca must be lowered before EVM machine final lowering")
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
            EvmInstKind::EvmMload(_) => basic_op(ctx, &[OpCode::MLOAD]),
            EvmInstKind::EvmMstore(_) => basic_op(ctx, &[OpCode::MSTORE]),
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
                panic!("evm_malloc must be lowered before EVM machine final lowering")
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
}
