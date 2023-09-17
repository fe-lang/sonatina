use std::ops::{Add, BitAnd, BitOr, BitXor, Mul, Neg, Not, Sub};

use sonatina_ir::{
    insn::{BinaryOp, CastOp, UnaryOp},
    module::FuncRef,
    Block, DataLocationKind, Immediate, InsnData, Module, I256,
};

use crate::{Frame, ProgramCounter};

pub struct State {
    module: Module,
    frames: Vec<Frame>,
    pc: ProgramCounter,
    prev_block: Option<Block>,
}

impl State {
    pub fn new(module: Module, entry_func: FuncRef) -> Self {
        let func = &module.funcs[entry_func];
        let pc = ProgramCounter::new(entry_func, &func.layout);
        let entry_frame = Frame::new(func, pc, vec![]);
        let frames = vec![entry_frame];

        Self {
            module,
            frames,
            pc,
            prev_block: None,
        }
    }

    pub fn repl(mut self) -> Option<I256> {
        loop {
            if let Some(arg) = self.step() {
                return arg;
            }
        }
    }

    pub fn step(&mut self) -> Option<Option<I256>> {
        let frame = self.frames.last_mut().unwrap();
        let insn = self.pc.insn;
        let ctx = &self.module.ctx;
        let func = &self.module.funcs[self.pc.func_ref];

        let dfg = &func.dfg;
        let layout = &func.layout;

        let insn_data = dfg.insn_data(insn);

        use InsnData::*;
        match insn_data {
            Unary { code, args } => {
                let arg = frame.load(ctx, args[0], dfg);
                use UnaryOp::*;
                let result = match code {
                    Not => arg.not(),
                    Neg => arg.neg(),
                };

                frame.map(result, insn, dfg);

                self.pc.next_insn(layout);
                None
            }
            Binary { code, args } => {
                let lhs: Immediate = frame.load(ctx, args[0], dfg).into();
                let rhs: Immediate = frame.load(ctx, args[1], dfg).into();
                use BinaryOp::*;
                let result = match code {
                    Add => lhs.add(rhs),
                    Sub => lhs.sub(rhs),
                    Mul => lhs.mul(rhs),
                    Udiv => lhs.udiv(rhs),
                    Sdiv => lhs.sdiv(rhs),
                    Lt => lhs.lt(rhs),
                    Gt => lhs.gt(rhs),
                    Slt => lhs.slt(rhs),
                    Sgt => lhs.sgt(rhs),
                    Le => lhs.le(rhs),
                    Ge => lhs.ge(rhs),
                    Sle => lhs.sle(rhs),
                    Sge => lhs.sge(rhs),
                    Eq => lhs.imm_eq(rhs),
                    Ne => lhs.imm_ne(rhs),
                    And => lhs.bitand(rhs),
                    Or => lhs.bitor(rhs),
                    Xor => lhs.bitxor(rhs),
                }
                .as_i256();

                frame.map(result, insn, dfg);

                self.pc.next_insn(layout);
                None
            }
            Cast { code, args, .. } => {
                let arg = frame.load(ctx, args[0], dfg);
                use CastOp::*;
                let result = match code {
                    Zext => arg.neg(),
                    Sext | Trunc | BitCast => arg,
                };

                frame.map(result, insn, dfg);

                self.pc.next_insn(layout);
                None
            }
            Load { args, loc } => {
                use DataLocationKind::*;
                match loc {
                    Memory => {
                        frame.ldr(ctx, args[0], insn, dfg);
                    }
                    Storage => todo!(),
                }

                self.pc.next_insn(layout);
                None
            }
            Store { args, loc } => {
                use DataLocationKind::*;
                match loc {
                    Memory => {
                        frame.str(ctx, args[0], args[1], dfg);
                    }
                    Storage => todo!(),
                }

                self.pc.next_insn(layout);
                None
            }
            Call { func, args, .. } => {
                let mut literal_args = Vec::with_capacity(args.len());
                for arg in args {
                    let arg = frame.load(ctx, *arg, dfg);
                    literal_args.push(arg)
                }

                // Function prologue

                let ret_addr = self.pc;

                let callee = &self.module.funcs[*func];
                let new_frame = Frame::new(callee, ret_addr, literal_args);
                self.frames.push(new_frame);

                self.pc.call(*func, &callee.layout);
                None
            }
            Jump { dests, .. } => {
                let block = layout.insn_block(insn);
                self.prev_block = Some(block);

                self.pc.branch_to(dests[0], layout);
                None
            }
            Branch { args, dests } => {
                let arg = frame.load(ctx, args[0], dfg);
                let idx = arg.not().to_u256().as_usize();

                let block = layout.insn_block(insn);
                self.prev_block = Some(block);
                self.pc.branch_to(dests[idx], layout);
                None
            }
            BrTable {
                args,
                default,
                table,
            } => {
                let block = layout.insn_block(insn);
                self.prev_block = Some(block);

                let cond = args[0];
                for (idx, arg) in args[1..].iter().enumerate() {
                    if frame.eq(ctx, cond, *arg, dfg) {
                        self.pc.branch_to(table[idx], layout);
                        return None;
                    }
                }
                if let Some(block) = *default {
                    self.pc.branch_to(block, layout);
                }
                None
            }
            Alloca { ty } => {
                frame.alloca(ctx, *ty, insn, dfg);

                self.pc.next_insn(layout);
                None
            }
            Return { args } => {
                let arg = args.map(|arg| frame.load(ctx, arg, dfg));

                let frame = self.frames.pop().unwrap(); // pop returning frame
                match self.frames.last_mut() {
                    Some(caller_frame) => {
                        // Function epilogue

                        self.pc.resume_frame_at(frame.ret_addr);

                        let caller = &self.module.funcs[self.pc.func_ref];
                        if let Some(lit) = arg {
                            caller_frame.map(lit, self.pc.insn, &caller.dfg);
                        }

                        self.pc.next_insn(&caller.layout);
                        None
                    }
                    None => Some(arg),
                }
            }
            Gep { args } => {
                let ptr = frame.gep(ctx, args, dfg);

                frame.map(ptr, insn, dfg);

                self.pc.next_insn(layout);
                None
            }
            Phi { values, blocks, .. } => {
                let prev_block = self.prev_block.unwrap();
                for (v, block) in values.iter().zip(blocks.iter()) {
                    if prev_block == *block {
                        let lit = frame.load(ctx, *v, dfg);
                        frame.map(lit, insn, dfg);
                        break;
                    }
                }
                self.pc.next_insn(layout);
                None
            }
        }
    }
}

#[cfg(test)]
mod test {
    use sonatina_ir::I256;
    use sonatina_parser::parser::Parser;

    use super::*;

    fn parse_module_make_state(input: &str) -> State {
        let parser = Parser::default();
        let module = parser.parse(input).unwrap().module;
        let func_ref = module.iter_functions().next().unwrap();

        State::new(module, func_ref)
    }

    #[test]
    fn unary() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i32:
            block0:
                v1.i32 = not 0.i32;
                v2.i32 = neg v1;
                return v2;
        ";

        let state = parse_module_make_state(input);

        let result = state.repl();

        assert_eq!(result.unwrap(), I256::all_one().neg());
    }

    #[test]
    fn binary_arithmetic() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i16:
            block0:
                v0.i16 = add 3.i16 4.i16;
                v1.i16 = sub v0 1.i16;
                v2.i16 = udiv v1 2.i16;
                v3.i8 =  sdiv v2 65535.i16;
                return v3;
        ";

        let state = parse_module_make_state(input);

        let result = state.repl();

        assert_eq!(result.unwrap(), (-3).into());
    }

    #[test]
    fn cast_sext() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i16:
            block0:
                v0.i16 = sext -128.i8;
                return v0;
        ";

        let state = parse_module_make_state(input);

        let result = state.repl();

        const NEG_128: i16 = i16::from_be_bytes([0xff, 0x80]);

        assert_eq!(result.unwrap(), NEG_128.into());
    }

    #[test]
    fn cast_zext() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i16:
            block0:
                v0.i16 = zext -128.i8;
                return v0;
        ";

        let state = parse_module_make_state(input);

        let elem_ptr = state.repl();

        let result = i16::from_be_bytes([0x0, 0x80]);

        assert_eq!(elem_ptr.unwrap(), result.into());
    }

    #[test]
    fn load_store() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i32:
            block0:
                v0.*i32 = alloca i32;
                store @memory v0 1.i32;
                v1.*i32 = load @memory v0;
                return v1;
        ";

        let state = parse_module_make_state(input);

        let data = state.repl();

        assert_eq!(data.unwrap(), 1.into());
    }

    #[test]
    fn call() {
        let input = "
        target = \"evm-ethereum-london\"

        func public %test_callee(v0.i8) -> i8:
            block0:
                v1.i8 = mul v0 1.i8;
                return v1; 

        func public %test() -> i8:
            block0:
                v0.i8 = call %test_callee 0.i8;
                return v0;
        ";

        let parser = Parser::default();
        let module = parser.parse(input).unwrap().module;
        let func_ref = module.iter_functions().nth(1).unwrap();

        let state = State::new(module, func_ref);

        let data = state.repl();

        assert_eq!(data.unwrap(), 0.into());
    }

    #[test]
    fn jump() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i1:
            block0:
                jump block2;
            block1:
                return 1.i1;
            block2:
                return 0.i1;
        ";

        let state = parse_module_make_state(input);

        let boolean = state.repl().unwrap();

        assert_eq!(boolean, I256::zero())
    }

    #[test]
    fn branch() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i8:
            block0:
                br 1.i1 block1 block2;
            block1:
                return 1.i8;
            block2:
                return 2.i8;
        ";

        let state = parse_module_make_state(input);

        let result = state.repl().unwrap();

        assert_eq!(result, 1.into());
    }

    #[test]
    fn br_table() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i64:
            block0:
                br_table 1.i64 undef (0.i64 block1) (1.i64 block2);
            block1:
                return 1.i64;
            block2:
                return 2.i64;
            block3:
                return 3.i64;
        ";

        let state = parse_module_make_state(input);

        let result = state.repl().unwrap();

        assert_eq!(result, 2.into());
    }

    #[test]
    fn phi() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i8:
            block0:
                jump block1;
            block1:
                jump block2;
            block2:
                v0.i8 = phi (1.i8 block0) (-1.i8 block1);
                return v0;
        ";

        let state = parse_module_make_state(input);

        let result = state.repl().unwrap();

        assert_eq!(result, (-1).into());
    }

    #[test]
    fn gep() {
        let input = "
        target = \"evm-ethereum-london\"

        type %s1 = {i32, i64, i1};

        func private %test() -> *i1:
            block0:
                v0.*%s1 = alloca %s1;
                v1.*i1 = gep v0 2.i8;
                return v1;
        ";

        let state = parse_module_make_state(input);

        let elem_ptr = state.repl();

        assert_eq!(elem_ptr.unwrap(), 12.into());
    }

    #[test]
    fn ret_void() {
        let input = "
        target = \"evm-ethereum-london\"

        type %s1 = {i32, i64, i1};

        func private %test() -> void:
            block0:
                return;
        ";

        let state = parse_module_make_state(input);

        let arg = state.repl();

        assert!(arg.is_none());
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn gep_ptr_ty() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> *i1:
            block0:
                v0.*[*i32; 3] = alloca [*i32; 3];
                v1.*i32 = gep v0 2.i8;
                return v1;
        ";

        let state = parse_module_make_state(input);

        let elem_ptr = state.repl();

        assert_eq!(elem_ptr.unwrap(), 16.into());
    }

    #[test]
    fn gep_nested_aggr_ty() {
        let input = "
        target = \"evm-ethereum-london\"

        type %s1 = {i32, [i16; 3], [i8; 2]};

        func private %test() -> *i1:
            block0:
                v0.*%s1 = alloca %s1;
                v1.*i1 = gep v0 2.i8 1.i8;
                return v1;
        ";

        let state = parse_module_make_state(input);

        let elem_ptr = state.repl();

        assert_eq!(elem_ptr.unwrap(), 11.into());
    }
}
