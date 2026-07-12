use rustc_hash::FxHashSet;
use smallvec::SmallVec;
use sonatina_ir::{
    InstId, InstSetExt, U256,
    inst::evm::machine_inst_set::EvmMachineInstKind,
    isa::{Isa, evm::EvmMachine},
};

use crate::{
    machinst::{
        lower::Lower,
        vcode::{Label, SymFixup, SymFixupKind},
    },
    stackalloc::{Action, Allocator},
};

use super::{
    super::{DynSpInitKind, machine::lazy_frame::FrameSite, opcode::OpCode},
    EvmMachineFunctionLowering,
    stack::{
        emit_narrow_signed_saturating_binary, emit_narrow_unsigned_saturating_binary,
        ensure_dyn_sp_init, fold_stack_actions, init_dyn_sp, low_bits_mask, scalar_bit_width,
        swap_op,
    },
};

impl EvmMachineFunctionLowering<'_> {
    pub(crate) fn lower_insn(&self, ctx: &mut Lower<OpCode>, alloc: &dyn Allocator, insn: InstId) {
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
        let args = ctx.insn_data(insn).collect_values();
        let machine = EvmMachine::new(ctx.module.triple);
        let data = machine.inst_set().resolve_inst(ctx.insn_data(insn));

        let basic_op = |ctx: &mut Lower<OpCode>, ops: &[OpCode]| {
            emit_pre_actions(ctx, alloc.pre_inst(insn));
            for op in ops {
                ctx.push(*op);
            }
            emit_post_actions(ctx, alloc.post_inst(insn));
        };

        match &data {
            EvmMachineInstKind::Add(_) => basic_op(ctx, &[OpCode::ADD]),
            EvmMachineInstKind::Mul(_) => basic_op(ctx, &[OpCode::MUL]),
            EvmMachineInstKind::Sub(_) => basic_op(ctx, &[OpCode::SUB]),
            EvmMachineInstKind::Shl(_) => basic_op(ctx, &[OpCode::SHL]),
            EvmMachineInstKind::Shr(_) => basic_op(ctx, &[OpCode::SHR]),
            EvmMachineInstKind::Sar(_) => basic_op(ctx, &[OpCode::SAR]),
            EvmMachineInstKind::Lt(_) => basic_op(ctx, &[OpCode::LT]),
            EvmMachineInstKind::Gt(_) => basic_op(ctx, &[OpCode::GT]),
            EvmMachineInstKind::Slt(_) => basic_op(ctx, &[OpCode::SLT]),
            EvmMachineInstKind::Sgt(_) => basic_op(ctx, &[OpCode::SGT]),
            EvmMachineInstKind::Eq(_) => basic_op(ctx, &[OpCode::EQ]),
            EvmMachineInstKind::IsZero(_) => basic_op(ctx, &[OpCode::ISZERO]),
            EvmMachineInstKind::Not(_) => basic_op(ctx, &[OpCode::NOT]),
            EvmMachineInstKind::And(_) => basic_op(ctx, &[OpCode::AND]),
            EvmMachineInstKind::Or(_) => basic_op(ctx, &[OpCode::OR]),
            EvmMachineInstKind::Xor(_) => basic_op(ctx, &[OpCode::XOR]),
            EvmMachineInstKind::Jump(jump) => {
                let dest = self.canonical_block_target(*jump.dest());
                emit_pre_actions(ctx, alloc.pre_inst(insn));

                if !ctx.is_next_block(dest) {
                    let push_op = ctx.push(OpCode::PUSH1);
                    ctx.add_label_reference(push_op, Label::Block(dest));
                    ctx.push(OpCode::JUMP);
                }
            }
            EvmMachineInstKind::Br(br) => {
                let nz_dest = self.canonical_block_target(*br.nz_dest());
                let z_dest = self.canonical_block_target(*br.z_dest());

                emit_pre_actions(ctx, alloc.pre_inst(insn));
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
            EvmMachineInstKind::Phi(_) => {}
            EvmMachineInstKind::Unreachable(_) => {
                emit_pre_actions(ctx, alloc.pre_inst(insn));
                ctx.push(OpCode::INVALID);
            }
            EvmMachineInstKind::BrTable(br) => {
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

                emit_pre_actions(ctx, alloc.pre_inst(insn));

                for (case_idx, (_, dest)) in table.iter().enumerate() {
                    let dest = self.canonical_block_target(*dest);
                    self.emit_actions_for_site(
                        ctx,
                        alloc.br_table_case(insn, case_idx),
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
            EvmMachineInstKind::Call(call) => {
                let callee = *call.callee();
                let mut actions = alloc.pre_inst(insn).clone();

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
                        Some(DynSpInitKind::Checked) => {
                            ensure_dyn_sp_init(ctx, self.dyn_base());
                        }
                        None => {}
                    }

                    let p = ctx.push(OpCode::PUSH1);
                    ctx.add_label_reference(p, Label::Function(callee));
                    ctx.push(OpCode::JUMP);

                    let jumpdest_op = ctx.push(OpCode::JUMPDEST);
                    ctx.add_label_reference(push_callback, Label::Insn(jumpdest_op));

                    emit_post_actions(ctx, alloc.post_inst(insn));
                } else {
                    self.emit_actions_for_site(
                        ctx,
                        &actions,
                        frame_layout,
                        FrameSite::PreInst(insn),
                    );

                    match self.frontier_init_kind(insn) {
                        Some(DynSpInitKind::Always) => init_dyn_sp(ctx, self.dyn_base()),
                        Some(DynSpInitKind::Checked) => {
                            ensure_dyn_sp_init(ctx, self.dyn_base());
                        }
                        None => {}
                    }

                    let p = ctx.push(OpCode::PUSH1);
                    ctx.add_label_reference(p, Label::Function(callee));
                    ctx.push(OpCode::JUMP);
                }
            }
            EvmMachineInstKind::Return(_) => {
                emit_pre_actions(ctx, alloc.pre_inst(insn));
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
            EvmMachineInstKind::EvmMcopy(_) => basic_op(ctx, &[OpCode::MCOPY]),
            EvmMachineInstKind::EvmStop(_) => basic_op(ctx, &[OpCode::STOP]),
            EvmMachineInstKind::EvmSdiv(_) => basic_op(ctx, &[OpCode::SDIV]),
            EvmMachineInstKind::EvmUdiv(_) => basic_op(ctx, &[OpCode::DIV]),
            EvmMachineInstKind::EvmUaddsat(sat) => {
                let bits = scalar_bit_width(*sat.ty(), ctx.module)
                    .expect("evm_uaddsat requires scalar type");
                assert!(
                    bits < 256,
                    "full-width saturating add must be legalized earlier"
                );
                emit_pre_actions(ctx, alloc.pre_inst(insn));
                emit_narrow_unsigned_saturating_binary(
                    ctx,
                    OpCode::ADD,
                    bits,
                    low_bits_mask(bits).unwrap(),
                );
                emit_post_actions(ctx, alloc.post_inst(insn));
            }
            EvmMachineInstKind::EvmSaddsat(sat) => {
                let bits = scalar_bit_width(*sat.ty(), ctx.module)
                    .expect("evm_saddsat requires scalar type");
                assert!(
                    bits < 256,
                    "full-width saturating add must be legalized earlier"
                );
                emit_pre_actions(ctx, alloc.pre_inst(insn));
                emit_narrow_signed_saturating_binary(ctx, OpCode::ADD, bits);
                emit_post_actions(ctx, alloc.post_inst(insn));
            }
            EvmMachineInstKind::EvmUsubsat(sat) => {
                let bits = scalar_bit_width(*sat.ty(), ctx.module)
                    .expect("evm_usubsat requires scalar type");
                assert!(
                    bits < 256,
                    "full-width saturating sub must be legalized earlier"
                );
                emit_pre_actions(ctx, alloc.pre_inst(insn));
                emit_narrow_unsigned_saturating_binary(ctx, OpCode::SUB, bits, U256::zero());
                emit_post_actions(ctx, alloc.post_inst(insn));
            }
            EvmMachineInstKind::EvmSsubsat(sat) => {
                let bits = scalar_bit_width(*sat.ty(), ctx.module)
                    .expect("evm_ssubsat requires scalar type");
                assert!(
                    bits < 256,
                    "full-width saturating sub must be legalized earlier"
                );
                emit_pre_actions(ctx, alloc.pre_inst(insn));
                emit_narrow_signed_saturating_binary(ctx, OpCode::SUB, bits);
                emit_post_actions(ctx, alloc.post_inst(insn));
            }
            EvmMachineInstKind::EvmUmulsat(sat) => {
                let bits = scalar_bit_width(*sat.ty(), ctx.module)
                    .expect("evm_umulsat requires scalar type");
                assert!(
                    bits < 256,
                    "full-width saturating mul must be legalized earlier"
                );
                emit_pre_actions(ctx, alloc.pre_inst(insn));
                emit_narrow_unsigned_saturating_binary(
                    ctx,
                    OpCode::MUL,
                    bits,
                    low_bits_mask(bits).unwrap(),
                );
                emit_post_actions(ctx, alloc.post_inst(insn));
            }
            EvmMachineInstKind::EvmSmulsat(sat) => {
                let bits = scalar_bit_width(*sat.ty(), ctx.module)
                    .expect("evm_smulsat requires scalar type");
                assert!(
                    bits < 256,
                    "full-width saturating mul must be legalized earlier"
                );
                emit_pre_actions(ctx, alloc.pre_inst(insn));
                emit_narrow_signed_saturating_binary(ctx, OpCode::MUL, bits);
                emit_post_actions(ctx, alloc.post_inst(insn));
            }
            EvmMachineInstKind::EvmUmod(_) => basic_op(ctx, &[OpCode::MOD]),
            EvmMachineInstKind::EvmSmod(_) => basic_op(ctx, &[OpCode::SMOD]),
            EvmMachineInstKind::EvmAddMod(_) => basic_op(ctx, &[OpCode::ADDMOD]),
            EvmMachineInstKind::EvmMulMod(_) => basic_op(ctx, &[OpCode::MULMOD]),
            EvmMachineInstKind::EvmExp(_) => basic_op(ctx, &[OpCode::EXP]),
            EvmMachineInstKind::EvmSignExtend(_) => basic_op(ctx, &[OpCode::SIGNEXTEND]),
            EvmMachineInstKind::EvmByte(_) => basic_op(ctx, &[OpCode::BYTE]),
            EvmMachineInstKind::EvmClz(_) => basic_op(ctx, &[OpCode::CLZ]),
            EvmMachineInstKind::EvmKeccak256(_) => basic_op(ctx, &[OpCode::KECCAK256]),
            EvmMachineInstKind::EvmAddress(_) => basic_op(ctx, &[OpCode::ADDRESS]),
            EvmMachineInstKind::EvmBalance(_) => basic_op(ctx, &[OpCode::BALANCE]),
            EvmMachineInstKind::EvmOrigin(_) => basic_op(ctx, &[OpCode::ORIGIN]),
            EvmMachineInstKind::EvmCaller(_) => basic_op(ctx, &[OpCode::CALLER]),
            EvmMachineInstKind::EvmCallValue(_) => basic_op(ctx, &[OpCode::CALLVALUE]),
            EvmMachineInstKind::EvmCalldataLoad(_) => basic_op(ctx, &[OpCode::CALLDATALOAD]),
            EvmMachineInstKind::EvmCalldataCopy(_) => basic_op(ctx, &[OpCode::CALLDATACOPY]),
            EvmMachineInstKind::EvmCalldataSize(_) => basic_op(ctx, &[OpCode::CALLDATASIZE]),
            EvmMachineInstKind::EvmCodeSize(_) => basic_op(ctx, &[OpCode::CODESIZE]),
            EvmMachineInstKind::EvmCodeCopy(_) => basic_op(ctx, &[OpCode::CODECOPY]),
            EvmMachineInstKind::EvmGasPrice(_) => basic_op(ctx, &[OpCode::GASPRICE]),
            EvmMachineInstKind::EvmExtCodeSize(_) => basic_op(ctx, &[OpCode::EXTCODESIZE]),
            EvmMachineInstKind::EvmExtCodeCopy(_) => basic_op(ctx, &[OpCode::EXTCODECOPY]),
            EvmMachineInstKind::EvmReturnDataSize(_) => basic_op(ctx, &[OpCode::RETURNDATASIZE]),
            EvmMachineInstKind::EvmReturnDataCopy(_) => basic_op(ctx, &[OpCode::RETURNDATACOPY]),
            EvmMachineInstKind::EvmExtCodeHash(_) => basic_op(ctx, &[OpCode::EXTCODEHASH]),
            EvmMachineInstKind::EvmBlockHash(_) => basic_op(ctx, &[OpCode::BLOCKHASH]),
            EvmMachineInstKind::EvmCoinBase(_) => basic_op(ctx, &[OpCode::COINBASE]),
            EvmMachineInstKind::EvmTimestamp(_) => basic_op(ctx, &[OpCode::TIMESTAMP]),
            EvmMachineInstKind::EvmNumber(_) => basic_op(ctx, &[OpCode::NUMBER]),
            EvmMachineInstKind::EvmPrevRandao(_) => basic_op(ctx, &[OpCode::PREVRANDAO]),
            EvmMachineInstKind::EvmGasLimit(_) => basic_op(ctx, &[OpCode::GASLIMIT]),
            EvmMachineInstKind::EvmChainId(_) => basic_op(ctx, &[OpCode::CHAINID]),
            EvmMachineInstKind::EvmSelfBalance(_) => basic_op(ctx, &[OpCode::SELFBALANCE]),
            EvmMachineInstKind::EvmBaseFee(_) => basic_op(ctx, &[OpCode::BASEFEE]),
            EvmMachineInstKind::EvmBlobHash(_) => basic_op(ctx, &[OpCode::BLOBHASH]),
            EvmMachineInstKind::EvmBlobBaseFee(_) => basic_op(ctx, &[OpCode::BLOBBASEFEE]),
            EvmMachineInstKind::EvmMload(_) => basic_op(ctx, &[OpCode::MLOAD]),
            EvmMachineInstKind::EvmMstore(_) => basic_op(ctx, &[OpCode::MSTORE]),
            EvmMachineInstKind::EvmMstore8(_) => basic_op(ctx, &[OpCode::MSTORE8]),
            EvmMachineInstKind::EvmSload(_) => basic_op(ctx, &[OpCode::SLOAD]),
            EvmMachineInstKind::EvmSstore(_) => basic_op(ctx, &[OpCode::SSTORE]),
            EvmMachineInstKind::EvmMsize(_) => basic_op(ctx, &[OpCode::MSIZE]),
            EvmMachineInstKind::EvmGas(_) => basic_op(ctx, &[OpCode::GAS]),
            EvmMachineInstKind::EvmTload(_) => basic_op(ctx, &[OpCode::TLOAD]),
            EvmMachineInstKind::EvmTstore(_) => basic_op(ctx, &[OpCode::TSTORE]),
            EvmMachineInstKind::EvmLog0(_) => basic_op(ctx, &[OpCode::LOG0]),
            EvmMachineInstKind::EvmLog1(_) => basic_op(ctx, &[OpCode::LOG1]),
            EvmMachineInstKind::EvmLog2(_) => basic_op(ctx, &[OpCode::LOG2]),
            EvmMachineInstKind::EvmLog3(_) => basic_op(ctx, &[OpCode::LOG3]),
            EvmMachineInstKind::EvmLog4(_) => basic_op(ctx, &[OpCode::LOG4]),
            EvmMachineInstKind::EvmCreate(_) => basic_op(ctx, &[OpCode::CREATE]),
            EvmMachineInstKind::EvmCall(_) => basic_op(ctx, &[OpCode::CALL]),
            EvmMachineInstKind::EvmCallCode(_) => basic_op(ctx, &[OpCode::CALLCODE]),
            EvmMachineInstKind::EvmReturn(_) => basic_op(ctx, &[OpCode::RETURN]),
            EvmMachineInstKind::EvmDelegateCall(_) => basic_op(ctx, &[OpCode::DELEGATECALL]),
            EvmMachineInstKind::EvmCreate2(_) => basic_op(ctx, &[OpCode::CREATE2]),
            EvmMachineInstKind::EvmStaticCall(_) => basic_op(ctx, &[OpCode::STATICCALL]),
            EvmMachineInstKind::EvmRevert(_) => basic_op(ctx, &[OpCode::REVERT]),
            EvmMachineInstKind::EvmSelfDestruct(_) => basic_op(ctx, &[OpCode::SELFDESTRUCT]),
            EvmMachineInstKind::GetFunctionPtr(get_fn) => {
                let func = *get_fn.func();
                emit_pre_actions(ctx, alloc.pre_inst(insn));
                ctx.push_jump_target(OpCode::PUSH1, Label::Function(func));
                emit_post_actions(ctx, alloc.post_inst(insn));
            }
            EvmMachineInstKind::EvmInvalid(_) => basic_op(ctx, &[OpCode::INVALID]),
            EvmMachineInstKind::SymAddr(sym_addr) => {
                let sym = sym_addr.sym().clone();
                emit_pre_actions(ctx, alloc.pre_inst(insn));
                ctx.push_sym_fixup(
                    OpCode::PUSH0,
                    SymFixup {
                        kind: SymFixupKind::Addr,
                        sym,
                    },
                );
                emit_post_actions(ctx, alloc.post_inst(insn));
            }
            EvmMachineInstKind::SymSize(sym_size) => {
                let sym = sym_size.sym().clone();
                emit_pre_actions(ctx, alloc.pre_inst(insn));
                ctx.push_sym_fixup(
                    OpCode::PUSH0,
                    SymFixup {
                        kind: SymFixupKind::Size,
                        sym,
                    },
                );
                emit_post_actions(ctx, alloc.post_inst(insn));
            }
        }
    }
}
