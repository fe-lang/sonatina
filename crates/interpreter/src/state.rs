use std::ops::{Add, BitAnd, BitOr, BitXor, Mul, Neg, Not, Sub};

use sonatina_ir::{
    insn::{BinaryOp, CastOp, UnaryOp},
    module::FuncRef,
    Block, DataLocationKind, Immediate, InsnData, Module, Value,
};

use crate::{types, EvalResult, Frame, ProgramCounter};

pub struct State {
    module: Module,
    frames: Vec<Frame>,
    pc: ProgramCounter,
    prev_block: Option<Block>,
}

impl State {
    pub fn new(module: Module, entry_func: FuncRef, args: &[Value]) -> Self {
        let func = &module.funcs[entry_func];
        let pc = ProgramCounter::new(entry_func, &func.layout);

        let mut entry_frame = Frame::new();
        debug_assert!(func.arg_values.len() == args.len());
        for arg in args {
            entry_frame.load(*arg, &func.dfg);
        }
        let frames = vec![entry_frame];

        Self {
            module,
            frames,
            pc,
            prev_block: None,
        }
    }

    pub fn run(mut self) -> EvalResult {
        loop {
            if let Some(arg) = self.step() {
                return arg;
            }
        }
    }

    pub fn step(&mut self) -> Option<EvalResult> {
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
                let arg = frame.load(args[0], dfg);
                use UnaryOp::*;
                let result = match code {
                    Not => arg.not(),
                    Neg => arg.neg(),
                };

                let v = dfg.insn_result(insn).unwrap();
                frame.map(result, v);

                self.pc.next_insn(layout);
                None
            }
            Binary { code, args } => {
                let lhs: Immediate = frame.load(args[0], dfg).into();
                let rhs: Immediate = frame.load(args[1], dfg).into();
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

                let v = dfg.insn_result(insn).unwrap();
                frame.map(result, v);

                self.pc.next_insn(layout);
                None
            }
            Cast { code, args, .. } => {
                let arg = frame.load(args[0], dfg);
                use CastOp::*;
                let result = match code {
                    Zext => arg.neg(),
                    Sext | Trunc | BitCast => arg,
                };

                let v = dfg.insn_result(insn).unwrap();
                frame.map(result, v);

                self.pc.next_insn(layout);
                None
            }
            Load { args, loc } => {
                use DataLocationKind::*;
                match loc {
                    Memory => {
                        let addr = frame.load(args[0], dfg);
                        let v = dfg.insn_result(insn).unwrap();
                        let ty = dfg.insn_result_ty(insn).unwrap();
                        frame.ldr(ctx, addr, v, ty);
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
                        let addr = frame.load(args[0], dfg);
                        let data = frame.load(args[1], dfg);
                        let ty = dfg.value_ty(args[1]);
                        frame.str(ctx, addr, data, ty);
                    }
                    Storage => todo!(),
                }

                self.pc.next_insn(layout);
                None
            }
            Call { func, args, .. } => {
                let arg_literals = args.iter().map(|arg| frame.load(*arg, dfg));

                // Function prologue

                let ret_addr = self.pc;

                let callee = &self.module.funcs[*func];
                let mut new_frame = Frame::new();
                debug_assert!(callee.arg_values.len() == args.len());
                new_frame.load_args(&callee.arg_values, arg_literals);
                new_frame.set_ret_addr(ret_addr);
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
                let arg = frame.load(args[0], dfg);
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
                    let cond = frame.load(cond, dfg);
                    let arg = frame.load(*arg, dfg);
                    if cond == arg {
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
                let v = dfg.insn_result(insn).unwrap();
                frame.alloca(ctx, *ty, v);

                self.pc.next_insn(layout);
                None
            }
            Return { args } => {
                let mut frame = self.frames.pop().unwrap(); // pop returning frame

                match self.frames.last_mut() {
                    Some(caller_frame) => {
                        // Function epilogue

                        self.pc.resume_frame_at(frame.ret_addr.unwrap());

                        let caller = &self.module.funcs[self.pc.func_ref];
                        if let Some(arg) = *args {
                            let arg_literal = frame.load(arg, dfg);
                            let v = caller.dfg.insn_result(self.pc.insn).unwrap();
                            caller_frame.map(arg_literal, v);
                        }

                        self.pc.next_insn(&caller.layout);
                        None
                    }
                    None => {
                        let Some(arg) = *args else {
                            return Some(EvalResult::Void);
                        };
                        let arg_literal = frame.load(arg, dfg);
                        let ty = dfg.value_ty(arg);
                        Some(EvalResult::from_i256(ctx, arg_literal, ty))
                    }
                }
            }
            Gep { args } => {
                let mut arg_literals = args.iter().map(|arg| frame.load(*arg, dfg));
                let base_addr = arg_literals.next().unwrap();
                let ty = dfg.value_ty(args[0]);
                debug_assert!(ctx.with_ty_store(|s| s.is_ptr(ty)));

                let elem_ptr = types::gep(ctx, base_addr, ty, arg_literals);

                let v = dfg.insn_result(insn).unwrap();
                frame.map(elem_ptr, v);

                self.pc.next_insn(layout);
                None
            }
            Phi { values, blocks, .. } => {
                let prev_block = self.prev_block.unwrap();
                for (v, block) in values.iter().zip(blocks.iter()) {
                    if prev_block == *block {
                        let lit = frame.load(*v, dfg);
                        let v = dfg.insn_result(insn).unwrap();
                        frame.map(lit, v);
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
    use super::*;

    fn parse_module(input: &str) -> Module {
        match sonatina_parser::parse_module(input) {
            Ok(pm) => pm.module,
            Err(errs) => {
                for err in errs {
                    eprintln!("{}", err.print_to_string("[test]", input, true));
                }
                panic!("parsing failed");
            }
        }
    }

    fn parse_module_make_state(input: &str) -> State {
        let module = parse_module(input);
        let func_ref = module.iter_functions().next().unwrap();

        State::new(module, func_ref, &[])
    }

    #[test]
    fn unary() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i32 {
            block0:
                v1.i32 = not 0.i32;
                v2.i32 = neg v1;
                return v2;
        }
        ";

        let state = parse_module_make_state(input);

        let result = state.run();

        assert_eq!(result.into_i32(), 1i32);
    }

    #[test]
    fn binary_arithmetic() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i16 {
            block0:
                v0.i16 = add 3.i16 4.i16;
                v1.i16 = sub v0 1.i16;
                v2.i16 = udiv v1 2.i16;
                v3.i16 =  sdiv v2 65535.i16;
                return v3;
        }
        ";

        let state = parse_module_make_state(input);

        let result = state.run();

        assert_eq!(result.into_i16(), -3i16);
    }

    #[test]
    fn cast_sext() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i16 {
            block0:
                v0.i16 = sext -128.i8;
                return v0;
        }
        ";

        let state = parse_module_make_state(input);

        let result = state.run();

        assert_eq!(result.into_i16(), -128i16);
    }

    #[test]
    fn cast_zext() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i16 {
            block0:
                v0.i16 = zext -128.i8;
                return v0;
        }
        ";

        let state = parse_module_make_state(input);

        let elem_ptr = state.run();

        assert_eq!(elem_ptr.into_i16(), 128i16);
    }

    #[test]
    fn load_store() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i32 {
            block0:
                v0.*i32 = alloca i32;
                store @memory v0 1.i32;
                v1.i32 = load @memory v0;
                return v1;
        }
        ";

        let state = parse_module_make_state(input);

        let data = state.run();

        assert_eq!(data.into_i32(), 1i32);
    }

    #[test]
    fn call() {
        let input = "
        target = \"evm-ethereum-london\"

        func public %test_callee(v0.i8) -> i8 {
            block0:
                v1.i8 = mul v0 1.i8;
                return v1;
        }

        func public %test() -> i8 {
            block0:
                v0.i8 = call %test_callee 0.i8;
                return v0;
        }
        ";

        let module = parse_module(input);
        let func_ref = module.iter_functions().nth(1).unwrap();

        let state = State::new(module, func_ref, &[]);

        let data = state.run();

        assert_eq!(data.into_i8(), 0i8);
    }

    #[test]
    fn jump() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i1 {
            block0:
                jump block2;
            block1:
                return 1.i1;
            block2:
                return 0.i1;
        }
        ";

        let state = parse_module_make_state(input);

        let boolean = state.run();

        assert!(!boolean.into_bool())
    }

    #[test]
    fn branch() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i8 {
            block0:
                br 1.i1 block1 block2;
            block1:
                return 1.i8;
            block2:
                return 2.i8;
        }
        ";

        let state = parse_module_make_state(input);

        let result = state.run();

        assert_eq!(result.into_i8(), 1i8);
    }

    #[test]
    fn br_table() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i64 {
            block0:
                br_table 1.i64 (0.i64 block1) (1.i64 block2);
            block1:
                return 1.i64;
            block2:
                return 2.i64;
            block3:
                return 3.i64;
        }
        ";

        let state = parse_module_make_state(input);

        let result = state.run();

        assert_eq!(result.into_i64(), 2i64);
    }

    #[test]
    fn phi() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> i8 {
            block0:
                jump block1;
            block1:
                jump block2;
            block2:
                v0.i8 = phi (1.i8 block0) (-1.i8 block1);
                return v0;
        }
        ";

        let state = parse_module_make_state(input);

        let result = state.run();

        assert_eq!(result.into_i8(), -1i8);
    }

    #[test]
    fn gep() {
        let input = "
        target = \"evm-ethereum-london\"

        type %s1 = {i32, i64, i1};

        func private %test() -> *i1 {
            block0:
                v0.*%s1 = alloca %s1;
                v1.*i1 = gep v0 2.i8;
                return v1;
        }
        ";

        let state = parse_module_make_state(input);

        let elem_ptr = state.run();

        assert_eq!(elem_ptr.into_usize(), 12usize);
    }

    #[test]
    fn ret_void() {
        let input = "
        target = \"evm-ethereum-london\"

        type %s1 = {i32, i64, i1};

        func private %test() -> void {
            block0:
                return;
        }
        ";

        let state = parse_module_make_state(input);

        let arg = state.run();

        arg.into_void();
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn gep_ptr_ty() {
        let input = "
        target = \"evm-ethereum-london\"

        func private %test() -> **i32 {
            block0:
                v0.*[*i32; 3] = alloca [*i32; 3];
                v1.**i32 = gep v0 2.i8;
                return v1;
        }
        ";

        let state = parse_module_make_state(input);

        let elem_ptr = state.run();

        assert_eq!(elem_ptr.into_usize(), 16usize);
    }

    #[test]
    fn gep_nested_aggr_ty() {
        let input = "
        target = \"evm-ethereum-london\"

        type %s1 = {i32, [i16; 3], [i8; 2]};

        func private %test() -> *i8 {
            block0:
                v0.*%s1 = alloca %s1;
                v1.*i8 = gep v0 2.i8 1.i8;
                return v1;
        }
        ";

        let state = parse_module_make_state(input);

        let elem_ptr = state.run();

        assert_eq!(elem_ptr.into_usize(), 11usize);
    }
}
