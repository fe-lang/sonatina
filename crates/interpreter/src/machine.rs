use cranelift_entity::SecondaryMap;
use sonatina_ir::{
    interpret::{Action, EvalValue, Interpret, Interpretable, State},
    isa::Endian,
    module::FuncRef,
    prelude::*,
    BlockId, Function, Immediate, InstId, Module, Type, Value, ValueId, I256,
};

pub struct Machine {
    frames: Vec<Frame>,
    pc: InstId,
    action: Action,
    // FIXME: Machine shouldn't have `Module`.
    module: Module,
    memory: Vec<u8>,
}

impl Machine {
    fn top_frame(&self) -> &Frame {
        self.frames.last().unwrap()
    }

    fn top_frame_mut(&mut self) -> &mut Frame {
        self.frames.last_mut().unwrap()
    }

    fn top_func(&self) -> &Function {
        &self.module.funcs[self.top_frame().func]
    }

    fn run_on_func(&mut self) -> EvalValue {
        let layout = &self.top_func().layout;

        let entry_block = layout.entry_block().unwrap();
        self.pc = layout.first_inst_of(entry_block).unwrap();

        loop {
            let inst = self.top_func().dfg.inst(self.pc);
            let Some(interpretable) = Interpretable::downcast(self.top_func().inst_set(), inst)
            else {
                panic!("{} is not yet intepretable", inst.as_text());
            };

            let e_val = interpretable.interpret(self);
            if let Some(inst_result) = self.top_func().dfg.inst_result(self.pc) {
                self.top_frame_mut().map_val(inst_result, e_val);
            };

            match self.action {
                Action::Continue => {
                    self.pc = self.top_func().layout.next_inst_of(self.pc).unwrap();
                }

                Action::JumpTo(next_block) => {
                    let current_block = self.top_func().layout.inst_block(self.pc);
                    self.top_frame_mut().prev_block = Some(current_block);
                    self.pc = self.top_func().layout.first_inst_of(next_block).unwrap();
                }

                Action::FallThrough => {
                    panic!("fall through detected!")
                }

                Action::Return(e_val) => return e_val,
            }
        }
    }
}

pub struct Frame {
    func: FuncRef,
    locals: SecondaryMap<ValueId, EvalValue>,
    prev_block: Option<BlockId>,
}

impl Frame {
    fn new(func: FuncRef, module: &Module, arg_e_values: Vec<EvalValue>) -> Self {
        let arg_values = &module.funcs[func].arg_values;
        assert_eq!(arg_values.len(), arg_e_values.len());

        let mut frame = Self {
            func,
            locals: SecondaryMap::default(),
            prev_block: None,
        };

        for (arg_val, arg_e_val) in arg_values.iter().zip(arg_e_values.into_iter()) {
            frame.map_val(*arg_val, arg_e_val);
        }

        frame
    }

    fn map_val(&mut self, val: ValueId, e_val: EvalValue) {
        self.locals[val] = e_val;
    }
}

impl State for Machine {
    fn lookup_val(&mut self, value_id: ValueId) -> EvalValue {
        let value = self.top_func().dfg.value(value_id);
        match value {
            Value::Immediate { imm, .. } => (*imm).into(),
            Value::Global { .. } => {
                todo!()
            }
            _ => self.top_frame().locals[value_id],
        }
    }

    fn call_func(&mut self, func: FuncRef, args: Vec<EvalValue>) -> EvalValue {
        let ret_addr = self.pc;

        let new_frame = Frame::new(func, &self.module, args);
        self.frames.push(new_frame);

        let result = self.run_on_func();

        self.frames.pop();
        self.pc = ret_addr;

        result
    }

    fn set_action(&mut self, action: Action) {
        self.action = action
    }

    fn prev_block(&mut self) -> BlockId {
        let frame = self.top_frame();
        frame.prev_block.unwrap()
    }

    fn load(&mut self, addr: EvalValue, ty: Type) -> EvalValue {
        if !(ty.is_integral() || ty.is_pointer(&self.module.ctx)) {
            // TODO: we need to decide how to handle load of aggregate type when it fits
            // into register/stack-slot size.
            todo!();
        }

        let Some(addr) = addr.as_imm() else {
            panic!("udnef address in load")
        };
        let addr = addr.as_usize();
        let size = self.module.ctx.size_of(ty);
        if addr + size > self.memory.len() {
            panic!("uninitialized memory access is detected");
        }

        let slice = &self.memory[addr..addr + size];
        let value_i256 = match self.module.ctx.endian() {
            Endian::Be => I256::from_be_bytes(&slice),
            Endian::Le => I256::from_le_bytes(&slice),
        };

        let imm = Immediate::from_i256(value_i256, ty);
        EvalValue::Imm(imm)
    }

    fn store(&mut self, addr: EvalValue, value: EvalValue, ty: Type) -> EvalValue {
        if !(ty.is_integral() || ty.is_pointer(&self.module.ctx)) {
            // TODO: we need to decide how to handle load of aggregate type when it fits
            // into register/stack-slot size.
            todo!();
        }

        let Some(addr) = addr.as_imm() else {
            panic!("udnef address in store")
        };
        let addr = addr.as_usize();
        let size = self.module.ctx.size_of(ty);
        if addr + size > self.memory.len() {
            self.memory.resize(addr + size, 0);
        }

        let Some(value) = value.as_imm() else {
            panic!("undef value in store");
        };

        match self.module.ctx.endian() {
            Endian::Be => {
                let v = value.as_i256().to_u256();
                let bytes = v.to_big_endian();
                let slice = &bytes[bytes.len() - size..];
                self.memory[addr..addr + size].copy_from_slice(&slice);
            }
            Endian::Le => {
                let v = value.as_i256().to_u256();
                let bytes = v.to_little_endian();
                let slice = &bytes[..size];
                self.memory[addr..addr + size].copy_from_slice(&slice);
            }
        }

        EvalValue::Undef
    }
}
