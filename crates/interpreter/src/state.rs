use std::ops::{Add, BitAnd, BitOr, BitXor, Mul, Neg, Not, Sub};

use sonatina_ir::{
    insn::{BinaryOp, CastOp, UnaryOp},
    module::FuncRef,
    Block, DataLocationKind, Immediate, InsnData, Module,
};

use crate::{Frame, Literal, ProgramCounter};

struct State {
    module: Module,
    frames: Vec<Frame>,
    pc: ProgramCounter,
    prev_block: Option<Block>,
}

impl State {
    // the cpu
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

    pub fn repl(mut self) -> Option<Literal> {
        loop {
            if let Some(arg) = self.step() {
                return arg;
            }
        }
    }

    pub fn step(&mut self) -> Option<Option<Literal>> {
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
                let arg = frame.load(args[0], dfg).0;
                use UnaryOp::*;
                let result = Literal(match code {
                    Not => arg.not(),
                    Neg => arg.neg(),
                });

                frame.map(result, insn, dfg);

                self.pc.next_insn(layout);
                None
            }
            Binary { code, args } => {
                let lhs: Immediate = frame.load(args[0], dfg).0.into();
                let rhs: Immediate = frame.load(args[1], dfg).0.into();
                use BinaryOp::*;
                let result = Literal(
                    match code {
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
                    .as_i256(),
                );

                frame.map(result, insn, dfg);

                self.pc.next_insn(layout);
                None
            }
            Cast { code, args, ty } => {
                let arg: Immediate = frame.load(args[0], dfg).0.into();
                use CastOp::*;
                let result = Literal(
                    match code {
                        Sext => arg.sext(*ty),
                        Zext => arg.zext(*ty),
                        Trunc => arg.trunc(*ty),
                        BitCast => arg,
                    }
                    .as_i256(),
                );

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
                    let arg = frame.load(*arg, dfg);
                    literal_args.push(arg.clone())
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
                let arg = frame.load(args[0], dfg).0;
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
                    if frame.eq(cond, *arg, dfg) {
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
                let arg = args.map(|arg| frame.load(arg, dfg).clone());

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
                    None => return Some(arg),
                }
            }
            Gep { args } => {
                let ptr = frame.gep(ctx, &args, dfg);

                frame.map(ptr, insn, dfg);

                self.pc.next_insn(layout);
                None
            }
            Phi { values, blocks, .. } => {
                let _block = layout.insn_block(insn);
                let prev_block = self.prev_block.unwrap();
                for (v, block) in values.iter().zip(blocks.iter()) {
                    if prev_block == *block {
                        let lit = frame.load(*v, dfg).clone();
                        frame.map(lit, insn, dfg);
                        break;
                    }
                }
                None
            }
        }
    }
}
