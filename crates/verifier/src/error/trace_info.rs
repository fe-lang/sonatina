use std::fmt;

use cranelift_entity::packed_option::PackedOption;
use sonatina_ir::{
    ir_writer::{FuncWriteCtx, InstStatement, IrWrite, ValueWithTy},
    module::FuncRef,
    types::CompoundTypeRef,
    BlockId, Function, GlobalVariableRef, InstId, Type, ValueId,
};

/// Execution context.
#[derive(Debug, Clone, Copy)]
pub struct TraceInfo {
    func: PackedOption<FuncRef>,
    block: PackedOption<BlockId>,
    inst_id: PackedOption<InstId>,
    callee: PackedOption<FuncRef>,
    value: PackedOption<ValueId>,
    gv: PackedOption<GlobalVariableRef>,
    ty: Option<Type>,
    cmpd_ty: PackedOption<CompoundTypeRef>,
}

impl TraceInfo {
    pub fn func(&self) -> Option<FuncRef> {
        self.func.expand()
    }

    pub fn block(&self) -> Option<BlockId> {
        self.block.expand()
    }

    pub fn inst_id(&self) -> Option<InstId> {
        self.inst_id.expand()
    }

    pub fn callee(&self) -> Option<FuncRef> {
        self.callee.expand()
    }

    pub fn value(&self) -> Option<ValueId> {
        self.value.expand()
    }

    pub fn gv(&self) -> Option<GlobalVariableRef> {
        self.gv.expand()
    }

    pub fn ty(&self) -> Option<Type> {
        self.ty
    }

    pub fn cmpd_ty(&self) -> Option<CompoundTypeRef> {
        self.cmpd_ty.expand()
    }
}

pub struct DisplayTraceInfo<'a, 'b> {
    trace_info: &'a TraceInfo,
    ctx: FuncWriteCtx<'b>,
}

impl<'a, 'b> DisplayTraceInfo<'a, 'b> {
    pub fn new(trace_info: &'a TraceInfo, func: &'b Function, func_ref: FuncRef) -> Self {
        let ctx = FuncWriteCtx::new(func, func_ref);
        Self { trace_info, ctx }
    }
}

impl fmt::Display for DisplayTraceInfo<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let TraceInfo {
            block,
            inst_id,
            value,
            gv,
            ty,
            cmpd_ty,
            ..
        } = self.trace_info;

        let dfg = &self.ctx.func.dfg;

        "trace_info:".fmt(f)?;

        let mut line = 0;

        if let Some(cmpd_ty) = cmpd_ty.expand() {
            let cmpd_ty = cmpd_ty.dump_string(&dfg.ctx);
            write!(f, "\n{line}: {cmpd_ty}")?;
            line += 1;
        }
        if let Some(ty) = ty {
            let ty = ty.dump_string(&dfg.ctx);
            write!(f, "\n{line}: {ty}")?;
            line += 1;
        }
        if let Some(gv) = gv.expand() {
            let gv = gv.dump_string(&dfg.ctx);
            write!(f, "\n{line}: {gv}")?;
            line += 1;
        }
        if let Some(value) = value.expand() {
            let value_with_ty = ValueWithTy(value).dump_string(&self.ctx);
            write!(f, "\n{line}: {value_with_ty}")?;
            line += 1;
        }
        if let Some(callee) = self.trace_info.callee.expand() {
            self.ctx.func.ctx().func_sig(callee, |sig| {
                let callee = sig.name();
                write!(f, "\n{line}: %{callee}")
            })?;
            line += 1;
        }
        if let Some(inst_id) = inst_id.expand() {
            let inst_stmt = InstStatement(inst_id).dump_string(&self.ctx);
            write!(f, "\n{line}: {inst_stmt}")?;
            line += 1;
        }
        if let Some(block) = block.expand() {
            write!(f, "\n{line}: {block}")?;
            line += 1;
        }

        let sig = self.ctx.func.sig.dump_string(&self.ctx);
        write!(f, "\n{line}: {sig}")
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TraceInfoBuilder {
    func: PackedOption<FuncRef>,
    block: PackedOption<BlockId>,
    inst_id: PackedOption<InstId>,
    callee: PackedOption<FuncRef>,
    value: PackedOption<ValueId>,
    gv: PackedOption<GlobalVariableRef>,
    ty: Option<Type>,
    cmpd_ty: PackedOption<CompoundTypeRef>,
}

impl TraceInfoBuilder {
    pub fn new(func: FuncRef) -> Self {
        Self {
            func: func.into(),
            block: None.into(),
            inst_id: None.into(),
            callee: None.into(),
            value: None.into(),
            gv: None.into(),
            ty: None,
            cmpd_ty: None.into(),
        }
    }

    pub fn block(mut self, block: BlockId) -> Self {
        self.block = block.into();
        self
    }

    pub fn inst_id(mut self, inst_id: InstId) -> Self {
        self.inst_id = inst_id.into();
        self
    }

    pub fn value(mut self, v: ValueId) -> Self {
        self.value = v.into();
        self
    }

    pub fn nullify_value(mut self) -> Self {
        self.value = None.into();
        self
    }

    pub fn gv(mut self, gv: GlobalVariableRef) -> Self {
        self.gv = gv.into();
        self
    }

    pub fn ty(mut self, ty: Type) -> Self {
        self.ty = ty.into();
        self
    }

    pub fn cmpd_ty(mut self, cmpd_ty: CompoundTypeRef) -> Self {
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
            inst_id,
            callee,
            value,
            gv,
            ty,
            cmpd_ty,
        } = self;

        TraceInfo {
            func,
            block,
            inst_id,
            callee,
            value,
            gv,
            ty,
            cmpd_ty,
        }
    }
}
