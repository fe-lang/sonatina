#![allow(unused_variables, dead_code)] // XXX

pub mod opcode;
use opcode::OpCode;

use crate::{
    machinst::{
        lower::{Lower, LowerBackend},
        vcode::Label,
    },
    stackalloc::{Action, Allocator},
};
use smallvec::{smallvec, SmallVec};
use sonatina_ir::{
    inst::evm::inst_set::EvmInstKind,
    isa::{evm::Evm, Isa},
    BlockId, Function, Immediate, InstId, InstSetExt, U256,
};

const FRAME_POINTER_OFFSET: u8 = 0x0;

pub struct EvmBackend {
    isa: Evm,
}
impl EvmBackend {
    pub fn new(isa: Evm) -> Self {
        Self { isa }
    }
}

impl LowerBackend for EvmBackend {
    type MInst = OpCode;

    fn enter_function(
        &self,
        ctx: &mut Lower<Self::MInst>,
        alloc: &mut dyn Allocator,
        function: &Function,
    ) {
        perform_actions(ctx, &alloc.enter_function(function));
    }

    fn enter_block(
        &self,
        ctx: &mut Lower<Self::MInst>,
        _alloc: &mut dyn Allocator,
        block: BlockId,
    ) {
        // Every block start is a jumpdest unless
        //  - all incoming edges are fallthroughs (TODO)
        //  - it's the entry block of the main fn (TODO)
        ctx.push(OpCode::JUMPDEST);
    }

    fn lower(&self, ctx: &mut Lower<Self::MInst>, alloc: &mut dyn Allocator, insn: InstId) {
        let result = ctx.insn_result(insn);
        let args = ctx.insn_data(insn).collect_values();
        let data = self.isa.inst_set().resolve_inst(ctx.insn_data(insn));

        let basic_op = |ctx: &mut Lower<Self::MInst>, ops: &[OpCode]| {
            perform_actions(ctx, &alloc.read(insn, &args));
            for op in ops {
                ctx.push(*op);
            }
            perform_actions(ctx, &alloc.write(insn, result));
        };

        match &data {
            EvmInstKind::Neg(_) => basic_op(ctx, &[OpCode::PUSH0, OpCode::SUB]),
            EvmInstKind::Add(_) => basic_op(ctx, &[OpCode::ADD]),
            EvmInstKind::Mul(_) => basic_op(ctx, &[OpCode::MUL]),
            EvmInstKind::Sub(_) => basic_op(ctx, &[OpCode::SUB]),
            EvmInstKind::Shl(_) => basic_op(ctx, &[OpCode::SHL]),
            EvmInstKind::Shr(_) => basic_op(ctx, &[OpCode::SHR]),
            EvmInstKind::Sar(_) => basic_op(ctx, &[OpCode::SAR]),
            EvmInstKind::Sext(_) => todo!(),
            EvmInstKind::Zext(_) => todo!(),
            EvmInstKind::Trunc(_) => todo!(),
            EvmInstKind::Bitcast(_) => todo!(),
            EvmInstKind::IntToPtr(_) => todo!(),
            EvmInstKind::PtrToInt(_) => todo!(),
            EvmInstKind::Lt(_) => basic_op(ctx, &[OpCode::LT]),
            EvmInstKind::Gt(_) => basic_op(ctx, &[OpCode::GT]),
            EvmInstKind::Slt(_) => basic_op(ctx, &[OpCode::SLT]),
            EvmInstKind::Sgt(_) => basic_op(ctx, &[OpCode::SGT]),
            EvmInstKind::Le(_) => basic_op(ctx, &[OpCode::GT, OpCode::ISZERO]),
            EvmInstKind::Ge(_) => basic_op(ctx, &[OpCode::LT, OpCode::ISZERO]),
            EvmInstKind::Sge(_) => basic_op(ctx, &[OpCode::SLT, OpCode::ISZERO]),
            EvmInstKind::Eq(_) => basic_op(ctx, &[OpCode::EQ]),
            EvmInstKind::Ne(_) => basic_op(ctx, &[OpCode::EQ, OpCode::ISZERO]),
            EvmInstKind::IsZero(_) => basic_op(ctx, &[OpCode::ISZERO]),

            EvmInstKind::Not(_) => basic_op(ctx, &[OpCode::NOT]),
            EvmInstKind::And(_) => basic_op(ctx, &[OpCode::AND]),
            EvmInstKind::Or(_) => basic_op(ctx, &[OpCode::OR]),
            EvmInstKind::Xor(_) => basic_op(ctx, &[OpCode::XOR]),

            EvmInstKind::Jump(jump) => {
                let dest = *jump.dest();
                perform_actions(ctx, &alloc.read(insn, &[]));

                if !ctx.is_next_block(dest) {
                    let push_op = ctx.push(OpCode::PUSH1);
                    ctx.add_label_reference(push_op, Label::Block(dest));
                    ctx.push(OpCode::JUMP);
                }
            }
            EvmInstKind::Br(br) => {
                let nz_dest = *br.nz_dest();
                let z_dest = *br.z_dest();

                // JUMPI: dest is top of stack, bool val is next
                perform_actions(ctx, &alloc.read(insn, &args));

                ctx.push_jump_target(OpCode::PUSH1, Label::Block(nz_dest));
                ctx.push(OpCode::JUMPI);

                if !ctx.is_next_block(z_dest) {
                    ctx.push_jump_target(OpCode::PUSH1, Label::Block(z_dest));
                    ctx.push(OpCode::JUMP);
                }
            }
            EvmInstKind::Phi(_) => {}

            EvmInstKind::BrTable(br) => {
                let table = br.table();
                let lhs = *br.scrutinee();
                let default = *br.default();

                for (arg, dest) in table.clone().iter() {
                    perform_actions(ctx, &alloc.read(insn, &[*arg]));
                    ctx.push(OpCode::EQ);

                    let p = ctx.push(OpCode::PUSH1);
                    ctx.add_label_reference(p, Label::Block(*dest));
                    ctx.push(OpCode::JUMPI);
                }

                if let Some(dest) = default {
                    if !ctx.is_next_block(dest) {
                        let p = ctx.push(OpCode::PUSH1);
                        ctx.add_label_reference(p, Label::Block(dest));
                        ctx.push(OpCode::JUMP);
                    }
                }
            }

            EvmInstKind::Call(call) => {
                // xxx if func uses memory, store new fp

                let callee = *call.callee();
                let mut actions = alloc.read(insn, &args);

                assert_eq!(actions.remove(0), Action::PushContinuationOffset);
                let push_callback = ctx.push(OpCode::PUSH1);

                // Move fn args onto stack
                perform_actions(ctx, &actions);

                // Push fn address onto stack and jump
                let p = ctx.push(OpCode::PUSH1);
                ctx.add_label_reference(p, Label::Function(callee));
                ctx.push(OpCode::JUMP);

                // Mark return pc as jumpdest
                let jumpdest_op = ctx.push(OpCode::JUMPDEST);
                ctx.add_label_reference(push_callback, Label::Insn(jumpdest_op));
            }

            EvmInstKind::Return(_) => {
                perform_actions(ctx, &alloc.read(insn, &args));

                // Caller pushes return location onto stack prior to call.
                if !args.is_empty() {
                    // Swap the return loc to the top.
                    ctx.push(OpCode::SWAP1);
                }
                ctx.push(OpCode::JUMP);
            }
            EvmInstKind::Mload(_) => basic_op(ctx, &[OpCode::MLOAD]),
            EvmInstKind::Mstore(mstore) => {
                let ty_size = self
                    .isa
                    .type_layout()
                    .size_of(*mstore.ty(), ctx.module)
                    .unwrap();

                perform_actions(ctx, &alloc.read(insn, &args));
                if ty_size == 0 {
                    // TODO: optimize away mstores of size 0
                    // Pop the args, and don't do an mstore.
                    ctx.push(OpCode::POP);
                    ctx.push(OpCode::POP);
                } else if ty_size < 32 {
                    // Value to write to mem is in stack slot 1.
                    ctx.push(OpCode::SWAP1);
                    // NOTE: This assumes that the useful bytes are on the right.
                    ctx.push_with_imm(OpCode::PUSH1, &[((32 - ty_size) * 8) as u8]);
                    ctx.push(OpCode::SHL);
                    ctx.push(OpCode::SWAP1);
                }

                ctx.push(OpCode::MSTORE);
            }
            EvmInstKind::EvmMcopy(_) => todo!(),
            EvmInstKind::Gep(_) => todo!(),
            EvmInstKind::Alloca(_) => todo!(),

            EvmInstKind::EvmStop(_) => basic_op(ctx, &[OpCode::STOP]),

            EvmInstKind::EvmSdiv(_) => basic_op(ctx, &[OpCode::SDIV]),
            EvmInstKind::EvmUdiv(_) => basic_op(ctx, &[OpCode::DIV]),
            EvmInstKind::EvmUmod(_) => basic_op(ctx, &[OpCode::MOD]),
            EvmInstKind::EvmSmod(_) => basic_op(ctx, &[OpCode::SMOD]),
            EvmInstKind::EvmAddMod(_) => basic_op(ctx, &[OpCode::ADDMOD]),
            EvmInstKind::EvmMulMod(_) => basic_op(ctx, &[OpCode::MULMOD]),
            EvmInstKind::EvmExp(_) => basic_op(ctx, &[OpCode::EXP]),
            EvmInstKind::EvmByte(_) => basic_op(ctx, &[OpCode::BYTE]),
            EvmInstKind::EvmKeccak256(_) => basic_op(ctx, &[OpCode::KECCAK256]),
            EvmInstKind::EvmAddress(_) => basic_op(ctx, &[OpCode::ADDRESS]),
            EvmInstKind::EvmBalance(_) => basic_op(ctx, &[OpCode::BALANCE]),
            EvmInstKind::EvmOrigin(_) => basic_op(ctx, &[OpCode::ORIGIN]),
            EvmInstKind::EvmCaller(_) => basic_op(ctx, &[OpCode::CALLER]),
            EvmInstKind::EvmCallValue(_) => basic_op(ctx, &[OpCode::CALLVALUE]),
            EvmInstKind::EvmCallDataLoad(_) => basic_op(ctx, &[OpCode::CALLDATALOAD]),
            EvmInstKind::EvmCallDataCopy(_) => todo!(),
            EvmInstKind::EvmCallDataSize(_) => basic_op(ctx, &[OpCode::CALLDATALOAD]),
            EvmInstKind::EvmCodeSize(_) => basic_op(ctx, &[OpCode::CODESIZE]),
            EvmInstKind::EvmCodeCopy(_) => todo!(),
            EvmInstKind::EvmExtCodeCopy(_) => todo!(),
            EvmInstKind::EvmReturnDataSize(_) => basic_op(ctx, &[OpCode::RETURNDATASIZE]),
            EvmInstKind::EvmReturnDataCopy(_) => todo!(),
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
            EvmInstKind::EvmCreate(_) => todo!(),
            EvmInstKind::EvmCall(_) => todo!(),
            EvmInstKind::EvmCallCode(_) => todo!(),
            EvmInstKind::EvmReturn(_) => basic_op(ctx, &[OpCode::RETURN]),
            EvmInstKind::EvmDelegateCall(_) => todo!(),
            EvmInstKind::EvmCreate2(_) => todo!(),
            EvmInstKind::EvmStaticCall(_) => todo!(),
            EvmInstKind::EvmRevert(_) => todo!(),
            EvmInstKind::EvmSelfDestruct(_) => todo!(),

            EvmInstKind::EvmMalloc(_) => todo!(),
            EvmInstKind::InsertValue(_) => todo!(),
            EvmInstKind::ExtractValue(_) => todo!(),
            EvmInstKind::GetFunctionPtr(_) => todo!(),
            EvmInstKind::EvmContractSize(_) => todo!(),
            EvmInstKind::EvmInvalid(_) => todo!(),
        }
    }

    fn update_opcode_with_immediate_bytes(
        &self,
        opcode: &mut OpCode,
        bytes: &mut SmallVec<[u8; 8]>,
    ) {
        while bytes.first() == Some(&0) {
            bytes.pop();
        }
        *opcode = push_op(bytes.len());
    }

    fn update_opcode_with_label(
        &self,
        opcode: &mut OpCode,
        label_offset: u32,
    ) -> SmallVec<[u8; 4]> {
        let bytes = label_offset
            .to_be_bytes()
            .into_iter()
            .skip_while(|b| *b == 0)
            .collect::<SmallVec<_>>();

        *opcode = push_op(bytes.len());
        bytes
    }

    fn emit_opcode(&self, opcode: &OpCode, buf: &mut Vec<u8>) {
        buf.push(*opcode as u8);
    }

    fn emit_immediate_bytes(&self, bytes: &[u8], buf: &mut Vec<u8>) {
        buf.extend_from_slice(bytes);
    }
    fn emit_label(&self, address: u32, buf: &mut Vec<u8>) {
        buf.extend(address.to_be_bytes().into_iter().skip_while(|b| *b == 0));
    }
}

fn perform_actions(ctx: &mut Lower<OpCode>, actions: &[Action]) {
    for action in actions {
        match action {
            Action::StackDup(slot) => {
                ctx.push(dup_op(*slot));
            }
            Action::StackSwap(n) => {
                ctx.push(swap_op(*n));
            }
            Action::Push(imm) => {
                if imm.is_zero() {
                    ctx.push(OpCode::PUSH0);
                } else {
                    let bytes = match imm {
                        Immediate::I1(v) => smallvec![*v as u8],
                        Immediate::I8(v) => SmallVec::from_slice(&v.to_be_bytes()),
                        Immediate::I16(v) => shrink_bytes(&v.to_be_bytes()),
                        Immediate::I32(v) => shrink_bytes(&v.to_be_bytes()),
                        Immediate::I64(v) => shrink_bytes(&v.to_be_bytes()),
                        Immediate::I128(v) => shrink_bytes(&v.to_be_bytes()),
                        Immediate::I256(v) => todo!(),
                    };
                    push_bytes(ctx, &bytes);

                    // Sign-extend negative numbers to 32 bytes
                    // TODO: signextend isn't always needed (eg push then mstore8)
                    if imm.is_negative() && bytes.len() < 32 {
                        push_bytes(ctx, &u32_to_be((bytes.len() - 1) as u32));
                        ctx.push(OpCode::SIGNEXTEND);
                    }
                }
            }
            Action::Pop => {
                ctx.push(OpCode::POP);
            }
            Action::MemLoadAbs(offset) => {
                let bytes = u32_to_be(*offset);
                push_bytes(ctx, &bytes);
                ctx.push(OpCode::MLOAD);
            }
            Action::MemLoadFrameSlot(offset) => {
                push_bytes(ctx, &[FRAME_POINTER_OFFSET]);
                ctx.push(OpCode::MLOAD);
                if *offset != 0 {
                    let bytes = u32_to_be(*offset);
                    push_bytes(ctx, &bytes);
                    ctx.push(OpCode::ADD);
                }
                ctx.push(OpCode::MLOAD);
            }
            Action::MemStoreAbs(offset) => {
                let bytes = u32_to_be(*offset);
                push_bytes(ctx, &bytes);
                ctx.push(OpCode::MSTORE);
            }
            Action::MemStoreFrameSlot(offset) => {
                push_bytes(ctx, &[FRAME_POINTER_OFFSET]);
                ctx.push(OpCode::MLOAD);
                if *offset != 0 {
                    let bytes = u32_to_be(*offset);
                    push_bytes(ctx, &bytes);
                    ctx.push(OpCode::ADD);
                }
                ctx.push(OpCode::MSTORE);
            }
            Action::PushContinuationOffset => {
                panic!("handle PushContinuationOffset elsewhere");
            }
        }
    }
}

fn push_bytes(ctx: &mut Lower<OpCode>, bytes: &[u8]) {
    assert!(!bytes.is_empty());
    if bytes == [0] {
        ctx.push(OpCode::PUSH0);
    } else {
        ctx.push_with_imm(push_op(bytes.len()), bytes);
    }
}

/// Remove unnecessary leading bytes of the big-endian two's complement
/// representation of a number.
fn shrink_bytes(bytes: &[u8]) -> SmallVec<[u8; 8]> {
    assert!(!bytes.is_empty());

    let is_neg = bytes[0].leading_ones() > 0;
    let skip = if is_neg { 0xff } else { 0x00 };
    let mut bytes = bytes
        .iter()
        .copied()
        .skip_while(|b| *b == skip)
        .collect::<SmallVec<[u8; 8]>>();

    // Negative numbers need a leading 1 bit for sign-extension
    if is_neg && bytes.first().map(|&b| b < 0x80).unwrap_or(true) {
        bytes.insert(0, 0xff);
    }
    bytes
}

fn imm_to_be_bytes(imm: &Immediate) -> SmallVec<[u8; 4]> {
    match imm {
        Immediate::I1(v) => smallvec![*v as u8],
        Immediate::I8(v) => smallvec![*v as u8],
        Immediate::I16(v) => todo!(),
        Immediate::I32(v) => todo!(),
        Immediate::I64(v) => todo!(),
        Immediate::I128(v) => todo!(),
        Immediate::I256(v) => todo!(),
    }
}
fn u32_to_be(num: u32) -> SmallVec<[u8; 4]> {
    if num == 0 {
        smallvec![0]
    } else {
        num.to_be_bytes()
            .into_iter()
            .skip_while(|b| *b == 0)
            .collect()
    }
}

fn u256_to_be(num: &U256) -> SmallVec<[u8; 8]> {
    if num.is_zero() {
        smallvec![0]
    } else {
        let b = num.to_big_endian();
        b.into_iter().skip_while(|b| *b == 0).collect()
    }
}

fn dup_op(n: u8) -> OpCode {
    match n + 1 {
        1 => OpCode::DUP1,
        2 => OpCode::DUP2,
        3 => OpCode::DUP3,
        4 => OpCode::DUP4,
        5 => OpCode::DUP5,
        6 => OpCode::DUP6,
        7 => OpCode::DUP7,
        8 => OpCode::DUP8,
        9 => OpCode::DUP9,
        10 => OpCode::DUP10,
        11 => OpCode::DUP11,
        12 => OpCode::DUP12,
        13 => OpCode::DUP13,
        14 => OpCode::DUP14,
        15 => OpCode::DUP15,
        16 => OpCode::DUP16,
        _ => unreachable!(),
    }
}

fn swap_op(n: u8) -> OpCode {
    match n {
        1 => OpCode::SWAP1,
        2 => OpCode::SWAP2,
        3 => OpCode::SWAP3,
        4 => OpCode::SWAP4,
        5 => OpCode::SWAP5,
        6 => OpCode::SWAP6,
        7 => OpCode::SWAP7,
        8 => OpCode::SWAP8,
        9 => OpCode::SWAP9,
        10 => OpCode::SWAP10,
        11 => OpCode::SWAP11,
        12 => OpCode::SWAP12,
        13 => OpCode::SWAP13,
        14 => OpCode::SWAP14,
        15 => OpCode::SWAP15,
        16 => OpCode::SWAP16,
        _ => unreachable!(),
    }
}

fn push_op(bytes: usize) -> OpCode {
    match bytes {
        0 => OpCode::PUSH0,
        1 => OpCode::PUSH1,
        2 => OpCode::PUSH2,
        3 => OpCode::PUSH3,
        4 => OpCode::PUSH4,
        5 => OpCode::PUSH5,
        6 => OpCode::PUSH6,
        7 => OpCode::PUSH7,
        8 => OpCode::PUSH8,
        9 => OpCode::PUSH9,
        10 => OpCode::PUSH10,
        11 => OpCode::PUSH11,
        12 => OpCode::PUSH12,
        13 => OpCode::PUSH13,
        14 => OpCode::PUSH14,
        15 => OpCode::PUSH15,
        16 => OpCode::PUSH16,
        17 => OpCode::PUSH17,
        18 => OpCode::PUSH18,
        19 => OpCode::PUSH19,
        20 => OpCode::PUSH20,
        21 => OpCode::PUSH21,
        22 => OpCode::PUSH22,
        23 => OpCode::PUSH23,
        24 => OpCode::PUSH24,
        25 => OpCode::PUSH25,
        26 => OpCode::PUSH26,
        27 => OpCode::PUSH27,
        28 => OpCode::PUSH28,
        29 => OpCode::PUSH29,
        30 => OpCode::PUSH30,
        31 => OpCode::PUSH31,
        32 => OpCode::PUSH32,
        _ => unreachable!(),
    }
}
