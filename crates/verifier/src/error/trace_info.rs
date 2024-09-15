use std::fmt;

use cranelift_entity::packed_option::PackedOption;
use sonatina_ir::{
    function::DisplaySignature,
    global_variable::DisplayGlobalVariable,
    insn::DisplayInsn,
    module::{DisplayCalleeFuncRef, FuncRef},
    types::{CompoundType, DisplayCompoundType, DisplayType},
    value::DisplayArgValue,
    Block, Function, GlobalVariable, Insn, Type, Value,
};

/// Execution context.
#[derive(Debug, Clone, Copy)]
pub struct TraceInfo {
    func: PackedOption<FuncRef>,
    block: PackedOption<Block>,
    insn: PackedOption<Insn>,
    callee: PackedOption<FuncRef>,
    value: PackedOption<Value>,
    gv: PackedOption<GlobalVariable>,
    ty: Option<Type>,
    cmpd_ty: PackedOption<CompoundType>,
}

impl TraceInfo {
    pub fn func(&self) -> Option<FuncRef> {
        self.func.expand()
    }

    pub fn block(&self) -> Option<Block> {
        self.block.expand()
    }

    pub fn insn(&self) -> Option<Insn> {
        self.insn.expand()
    }

    pub fn callee(&self) -> Option<FuncRef> {
        self.callee.expand()
    }

    pub fn value(&self) -> Option<Value> {
        self.value.expand()
    }

    pub fn gv(&self) -> Option<GlobalVariable> {
        self.gv.expand()
    }

    pub fn ty(&self) -> Option<Type> {
        self.ty
    }

    pub fn cmpd_ty(&self) -> Option<CompoundType> {
        self.cmpd_ty.expand()
    }
}

pub struct DisplayTraceInfo<'a, 'b> {
    trace_info: &'a TraceInfo,
    func: &'b Function,
}

impl<'a, 'b> DisplayTraceInfo<'a, 'b> {
    pub fn new(trace_info: &'a TraceInfo, func: &'b Function) -> Self {
        Self { trace_info, func }
    }
}

impl<'a, 'b> fmt::Display for DisplayTraceInfo<'a, 'b> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { trace_info, func } = *self;
        let TraceInfo {
            block,
            insn,
            value,
            gv,
            ty,
            cmpd_ty,
            ..
        } = trace_info;

        let dfg = &func.dfg;

        "trace_info:".fmt(f)?;

        let mut line = 0;

        if let Some(cmpd_ty) = cmpd_ty.expand() {
            let cmpd_ty = DisplayCompoundType::new(cmpd_ty, dfg);
            write!(f, "\n{line}: {cmpd_ty}")?;
            line += 1;
        }
        if let Some(ty) = ty {
            let cmpd_ty = DisplayType::new(*ty, dfg);
            write!(f, "\n{line}: {cmpd_ty}")?;
            line += 1;
        }
        if let Some(gv) = gv.expand() {
            let gv = DisplayGlobalVariable::new(gv, dfg);
            write!(f, "\n{line}: {gv}")?;
            line += 1;
        }
        if let Some(value) = value.expand() {
            let value = DisplayArgValue::new(value, dfg);
            write!(f, "\n{line}: {value}")?;
            line += 1;
        }
        if let Some(callee) = trace_info.callee.expand() {
            let callee = DisplayCalleeFuncRef::new(callee, func);
            write!(f, "\n{line}: {callee}")?;
            line += 1;
        }
        if let Some(insn) = insn.expand() {
            let insn = DisplayInsn::new(insn, func);
            write!(f, "\n{line}: {insn}")?;
            line += 1;
        }
        if let Some(block) = block.expand() {
            write!(f, "\n{line}: {block}")?;
            line += 1;
        }
        let func = DisplaySignature::new(&func.sig, dfg);
        write!(f, "\n{line}: {func}")
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TraceInfoBuilder {
    func: PackedOption<FuncRef>,
    block: PackedOption<Block>,
    insn: PackedOption<Insn>,
    callee: PackedOption<FuncRef>,
    value: PackedOption<Value>,
    gv: PackedOption<GlobalVariable>,
    ty: Option<Type>,
    cmpd_ty: PackedOption<CompoundType>,
}

impl TraceInfoBuilder {
    pub fn new(func: FuncRef) -> Self {
        Self {
            func: func.into(),
            block: None.into(),
            insn: None.into(),
            callee: None.into(),
            value: None.into(),
            gv: None.into(),
            ty: None,
            cmpd_ty: None.into(),
        }
    }

    pub fn block(mut self, block: Block) -> Self {
        self.block = block.into();
        self
    }

    pub fn insn(mut self, insn: Insn) -> Self {
        self.insn = insn.into();
        self
    }

    pub fn value(mut self, v: Value) -> Self {
        self.value = v.into();
        self
    }

    pub fn nullify_value(mut self) -> Self {
        self.value = None.into();
        self
    }

    pub fn gv(mut self, gv: GlobalVariable) -> Self {
        self.gv = gv.into();
        self
    }

    pub fn ty(mut self, ty: Type) -> Self {
        self.ty = ty.into();
        self
    }

    pub fn cmpd_ty(mut self, cmpd_ty: CompoundType) -> Self {
        self.cmpd_ty = cmpd_ty.into();
        self
    }

    pub fn callee(mut self, callee: FuncRef) -> Self {
        self.callee = callee.into();
        self
    }

    pub fn build(self) -> TraceInfo {
        let Self {
            func,
            block,
            insn,
            callee,
            value,
            gv,
            ty,
            cmpd_ty,
        } = self;

        TraceInfo {
            func,
            block,
            insn,
            callee,
            value,
            gv,
            ty,
            cmpd_ty,
        }
    }
}
