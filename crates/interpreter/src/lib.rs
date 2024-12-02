use cranelift_entity::SecondaryMap;
use sonatina_ir::{
    interpret::{Action, EvalValue, Interpret, State},
    isa::Endian,
    module::{FuncRef, ModuleCtx, RoFuncStore},
    prelude::*,
    types::CompoundType,
    BlockId, DataFlowGraph, Function, Immediate, InstId, Module, Type, Value, ValueId, I256,
};

pub struct Machine {
    frames: Vec<Frame>,
    pc: InstId,
    action: Action,
    pub funcs: RoFuncStore,
    pub module_ctx: ModuleCtx,
    memory: Vec<u8>,
    free_region: usize,
}

impl Machine {
    pub fn new(module: Module) -> Self {
        Self {
            frames: Vec::new(),
            // Dummy pc
            pc: InstId(0),
            action: Action::Continue,
            funcs: module.func_store.into_read_only(),
            module_ctx: module.ctx,
            memory: Vec::new(),
            free_region: 0,
        }
    }

    pub fn run(&mut self, func_ref: FuncRef, args: Vec<EvalValue>) -> EvalValue {
        let func = self.funcs.get(&func_ref).unwrap();
        let frame = Frame::new(func_ref, func, args);
        self.frames.push(frame);
        self.action = Action::Continue;
        self.run_on_func()
    }

    pub fn clear_state(&mut self) {
        self.frames.clear();
        self.memory.clear();
    }

    fn top_frame(&self) -> &Frame {
        self.frames.last().unwrap()
    }

    fn top_frame_mut(&mut self) -> &mut Frame {
        self.frames.last_mut().unwrap()
    }

    fn top_func(&self) -> &Function {
        self.funcs.get(&self.top_frame().func).unwrap()
    }

    fn run_on_func(&mut self) -> EvalValue {
        let layout = &self.top_func().layout;
        let entry_block = layout.entry_block().unwrap();
        let first_inst = layout.first_inst_of(entry_block).unwrap();
        self.pc = first_inst;

        loop {
            let inst = self.top_func().dfg.inst(self.pc);
            let inst = dyn_clone::clone_box(inst);
            let Some(interpretable): Option<&dyn Interpret> =
                InstDowncast::downcast(self.top_func().inst_set(), inst.as_ref())
            else {
                panic!("`Intepret is not yet implemented for `{}`", inst.as_text());
            };

            let e_val = interpretable.interpret(self);
            if let Some(inst_result) = self.top_func().dfg.inst_result(self.pc) {
                self.top_frame_mut().map_val(inst_result, e_val);
            };

            match self.action.clone() {
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
    fn new(func_ref: FuncRef, func: &Function, arg_e_values: Vec<EvalValue>) -> Self {
        let arg_values = &func.arg_values;
        assert_eq!(arg_values.len(), arg_e_values.len());

        let mut frame = Self {
            func: func_ref,
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
            _ => self.top_frame().locals[value_id].clone(),
        }
    }

    fn call_func(&mut self, func_ref: FuncRef, args: Vec<EvalValue>) -> EvalValue {
        let ret_addr = self.pc;

        let func = self.funcs.get(&func_ref).unwrap();
        let new_frame = Frame::new(func_ref, func, args);
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
        let Some(addr) = addr.as_imm() else {
            return EvalValue::Undef;
        };

        let addr = addr.as_usize();
        let size = self.module_ctx.size_of_unchecked(ty);
        if addr + size > self.memory.len() {
            return EvalValue::Undef;
        }

        // Store a value of aggregate type.
        if !(ty.is_integral() || ty.is_pointer(&self.module_ctx)) {
            let mut fields = Vec::new();

            match ty.resolve_compound(&self.module_ctx).unwrap() {
                CompoundType::Array { elem: elem_ty, len } => {
                    let mut addr = addr;
                    let elem_size = self.module_ctx.size_of_unchecked(elem_ty);
                    for _ in 0..len {
                        let elem_addr = EvalValue::Imm(Immediate::I256(I256::from(addr)));
                        let elem = self.load(elem_addr, elem_ty);
                        fields.push(elem);
                        addr += elem_size;
                    }
                }

                CompoundType::Struct(s) => {
                    let mut addr = addr;
                    for field_ty in s.fields.into_iter() {
                        let elem_addr = EvalValue::Imm(Immediate::I256(I256::from(addr)));
                        let field = self.load(elem_addr, field_ty);
                        fields.push(field);
                        addr += self.module_ctx.size_of_unchecked(field_ty);
                    }
                }

                CompoundType::Ptr(_) => {
                    unreachable!()
                }

                CompoundType::Func { .. } => {
                    panic!("function type can't be placed in memory");
                }
            }

            return EvalValue::Aggregate { fields, ty };
        }

        // Store a value of integer/pointer type.
        let slice = &self.memory[addr..addr + size];
        let value_i256 = match self.module_ctx.endian() {
            Endian::Be => I256::from_be_bytes(slice),
            Endian::Le => I256::from_le_bytes(slice),
        };

        let imm = Immediate::from_i256(value_i256, ty);
        EvalValue::Imm(imm)
    }

    fn store(&mut self, addr: EvalValue, value: EvalValue, ty: Type) -> EvalValue {
        if value.is_undef() {
            return EvalValue::Undef;
        }

        let Some(addr) = addr.as_imm() else {
            panic!("udnef address in store")
        };
        let addr = addr.as_usize();
        let size = self.module_ctx.size_of_unchecked(ty);
        if addr + size > self.memory.len() {
            self.memory.resize(addr + size, 0);
        }

        // Store a value of aggregate type.
        if !(ty.is_integral() || ty.is_pointer(&self.module_ctx)) {
            let EvalValue::Aggregate { fields, ty } = value else {
                unreachable!();
            };
            match ty.resolve_compound(&self.module_ctx).unwrap() {
                CompoundType::Array { elem: elem_ty, .. } => {
                    let mut addr = addr;
                    let elem_size = self.module_ctx.size_of_unchecked(elem_ty);
                    for field in &fields {
                        let elem_addr = EvalValue::Imm(Immediate::I256(I256::from(addr)));
                        self.store(field.clone(), elem_addr, elem_ty);
                        addr += elem_size;
                    }
                }

                CompoundType::Struct(s) => {
                    let mut addr = addr;
                    for (i, field_ty) in s.fields.into_iter().enumerate() {
                        let elem_addr = EvalValue::Imm(Immediate::I256(I256::from(addr)));
                        self.store(fields[i].clone(), elem_addr, field_ty);
                        addr += self.module_ctx.size_of_unchecked(field_ty);
                    }
                }

                CompoundType::Ptr(_) => {
                    unreachable!()
                }

                CompoundType::Func { .. } => {
                    panic!("Function can't be stored in memory");
                }
            }

            return EvalValue::Undef;
        }

        // Store a value of integer/pointer type.
        let Some(value) = value.as_imm() else {
            panic!("undef value in store");
        };

        match self.module_ctx.endian() {
            Endian::Be => {
                let v = value.as_i256().to_u256();
                let bytes = v.to_big_endian();
                let slice = &bytes[bytes.len() - size..];
                self.memory[addr..addr + size].copy_from_slice(slice);
            }
            Endian::Le => {
                let v = value.as_i256().to_u256();
                let bytes = v.to_little_endian();
                let slice = &bytes[..size];
                self.memory[addr..addr + size].copy_from_slice(slice);
            }
        }

        EvalValue::Undef
    }

    fn alloca(&mut self, ty: Type) -> EvalValue {
        let ptr = self.free_region;
        self.free_region += self.module_ctx.size_of_unchecked(ty);
        EvalValue::Imm(Immediate::I256(I256::from(ptr)))
    }

    fn dfg(&self) -> &DataFlowGraph {
        &self.top_func().dfg
    }
}
