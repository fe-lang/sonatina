use std::io;

use super::{BlockId, Function};
use crate::{
    module::{FuncRef, ModuleCtx},
    DataFlowGraph, InstId, Module, Value, ValueId,
};

pub struct ModuleWriter<'a> {
    pub module: &'a Module,
    pub dbg: &'a dyn DebugProvider,
}

impl<'a> ModuleWriter<'a> {
    pub fn new(module: &'a Module) -> Self {
        Self::with_debug_provider(module, &DEFAULT_PROVIDER)
    }

    pub fn with_debug_provider(module: &'a Module, dbg: &'a dyn DebugProvider) -> Self {
        Self { module, dbg }
    }

    pub fn write(&mut self, w: &mut impl io::Write) -> io::Result<()> {
        // Write target.
        writeln!(w, "target = {}", self.module.ctx.triple)?;

        // Write struct types defined in the module.
        self.module.ctx.with_ty_store(|s| {
            for s in s.all_struct_data() {
                s.write(&self.module.ctx, &mut *w)?;
            }
            io::Result::Ok(())
        })?;

        // Write module level global variables.
        self.module.ctx.with_gv_store(|s| {
            for gv in s.all_gv_data() {
                gv.write(&self.module.ctx, &mut *w)?;
            }

            io::Result::Ok(())
        })?;

        for func_ref in self.module.funcs.keys() {
            let func = &self.module.funcs[func_ref];
            let mut writer = FuncWriter::with_debug_provider(func, func_ref, self.dbg);
            writer.write(&mut *w)?;
        }

        Ok(())
    }

    pub fn dump_string(&mut self) -> String {
        let mut s = Vec::new();
        self.write(&mut s).unwrap();
        unsafe { String::from_utf8_unchecked(s) }
    }
}

pub struct FuncWriteCtx<'a> {
    pub func: &'a Function,
    pub func_ref: FuncRef,
    pub dbg: &'a dyn DebugProvider,
}

impl<'a> FuncWriteCtx<'a> {
    pub fn with_debug_provider(
        func: &'a Function,
        func_ref: FuncRef,
        dbg: &'a dyn DebugProvider,
    ) -> Self {
        Self {
            func,
            func_ref,
            dbg,
        }
    }

    pub fn new(func: &'a Function, func_ref: FuncRef) -> Self {
        Self::with_debug_provider(func, func_ref, &DEFAULT_PROVIDER)
    }

    pub fn write_value(&self, value: ValueId, w: &mut impl io::Write) -> io::Result<()> {
        if let Some(name) = self.dbg.value_name(self.func, self.func_ref, value) {
            write!(w, "{name}")
        } else {
            match self.func.dfg.value(value) {
                Value::Immediate { imm, ty } => {
                    write!(w, "{}.", imm)?;
                    ty.write(self.func.ctx(), w)
                }
                Value::Global { gv, .. } => self
                    .func
                    .dfg
                    .ctx
                    .with_gv_store(|s| write!(w, "%{}", s.gv_data(*gv).symbol)),
                _ => {
                    write!(w, "v{}", value.0)
                }
            }
        }
    }

    pub fn dump_value_string(&self, value: ValueId) -> String {
        let mut s = Vec::new();
        self.write_value(value, &mut s).unwrap();
        unsafe { String::from_utf8_unchecked(s) }
    }

    pub fn dfg(&self) -> &DataFlowGraph {
        &self.func.dfg
    }

    pub fn module_ctx(&self) -> &ModuleCtx {
        self.func.ctx()
    }
}

pub struct FuncWriter<'a> {
    ctx: FuncWriteCtx<'a>,
    level: u8,
}

impl<'a> FuncWriter<'a> {
    pub fn new(func: &'a Function, func_ref: FuncRef) -> Self {
        Self::with_debug_provider(func, func_ref, &DEFAULT_PROVIDER)
    }

    pub fn with_debug_provider(
        func: &'a Function,
        func_ref: FuncRef,
        dbg: &'a dyn DebugProvider,
    ) -> Self {
        let ctx = FuncWriteCtx::with_debug_provider(func, func_ref, dbg);
        Self { ctx, level: 0 }
    }

    pub fn write(&mut self, w: &mut impl io::Write) -> io::Result<()> {
        w.write_fmt(format_args!(
            "func {} %{}(",
            self.ctx.func.sig.linkage(),
            self.ctx.func.sig.name()
        ))?;
        write_iter_with_delim(
            &mut *w,
            &self.ctx,
            self.ctx.func.arg_values.iter().map(|v| ValueWithTy(*v)),
            ", ",
        )?;
        write!(w, ") -> ")?;
        self.ctx
            .func
            .sig
            .ret_ty()
            .write(self.ctx.module_ctx(), &mut *w)?;
        writeln!(w, " {{")?;

        self.level += 1;
        for block in self.ctx.func.layout.iter_block() {
            self.write_block_with_inst(block, &mut *w)?;
        }

        self.level -= 1;
        writeln!(w, "}}")
    }

    pub fn dump_string(&mut self) -> String {
        let mut s = Vec::new();
        self.write(&mut s).unwrap();
        unsafe { String::from_utf8_unchecked(s) }
    }

    fn write_block_with_inst(&mut self, block: BlockId, w: &mut impl io::Write) -> io::Result<()> {
        self.indent(&mut *w)?;
        block.write(&self.ctx, &mut *w)?;

        self.enter(&mut *w)?;
        for inst in self.ctx.func.layout.iter_inst(block) {
            self.write_inst_in_block(inst, &mut *w)?;
        }
        self.leave();

        self.newline(w)
    }

    fn write_inst_in_block(&mut self, inst: InstId, w: &mut impl io::Write) -> io::Result<()> {
        self.indent(&mut *w)?;
        let inst_with_res = InstStatement(inst);
        inst_with_res.write(&self.ctx, &mut *w)?;
        writeln!(w)
    }

    fn indent(&self, mut w: impl io::Write) -> io::Result<()> {
        write!(w, "{}", " ".repeat(self.level as usize * 4))
    }

    fn newline(&self, mut w: impl io::Write) -> io::Result<()> {
        writeln!(w)
    }

    fn enter(&mut self, mut w: impl io::Write) -> io::Result<()> {
        self.level += 1;
        writeln!(w, ":")
    }

    fn leave(&mut self) {
        self.level -= 1;
    }
}

pub trait WriteWithModule {
    fn write(&self, module: &ModuleCtx, w: &mut impl io::Write) -> io::Result<()>;

    fn dump_string(&self, module: &ModuleCtx) -> String {
        let mut s = Vec::new();
        self.write(module, &mut s).unwrap();
        unsafe { String::from_utf8_unchecked(s) }
    }
}

impl<T> WriteWithModule for &T
where
    T: WriteWithModule,
{
    fn write(&self, module: &ModuleCtx, w: &mut impl io::Write) -> io::Result<()> {
        (*self).write(module, w)
    }
}

pub trait WriteWithFunc {
    fn write(&self, ctx: &FuncWriteCtx, w: &mut impl io::Write) -> io::Result<()>;

    fn dump_string(&self, ctx: &FuncWriteCtx) -> String {
        let mut s = Vec::new();
        self.write(ctx, &mut s).unwrap();
        unsafe { String::from_utf8_unchecked(s) }
    }
}

impl<T> WriteWithFunc for &T
where
    T: WriteWithFunc,
{
    fn write(&self, ctx: &FuncWriteCtx, w: &mut impl io::Write) -> io::Result<()> {
        (*self).write(ctx, w)
    }
}

#[derive(Clone, Copy)]
pub struct ValueWithTy(pub ValueId);
impl WriteWithFunc for ValueWithTy {
    fn write(&self, ctx: &FuncWriteCtx, w: &mut impl io::Write) -> io::Result<()> {
        let value = self.0;
        ctx.write_value(value, w)?;
        if let Value::Immediate { .. } = ctx.dfg().value(self.0) {
            Ok(())
        } else {
            let ty = ctx.dfg().value_ty(self.0);
            write!(w, ".")?;
            ty.write(ctx.module_ctx(), &mut *w)
        }
    }
}

pub struct InstStatement(pub InstId);
impl WriteWithFunc for InstStatement {
    fn write(&self, ctx: &FuncWriteCtx, w: &mut impl io::Write) -> io::Result<()> {
        if let Some(result) = ctx.func.dfg.inst_result(self.0) {
            let result_with_ty = ValueWithTy(result);
            result_with_ty.write(ctx, &mut *w)?;
            write!(w, " = ")?;
        };

        self.0.write(ctx, w)?;
        write!(w, ";")
    }
}

pub fn write_iter_with_delim<T>(
    w: &mut impl io::Write,
    ctx: &FuncWriteCtx,
    iter: impl Iterator<Item = T>,
    delim: &str,
) -> io::Result<()>
where
    T: WriteWithFunc,
{
    let mut iter = iter.peekable();
    while let Some(item) = iter.next() {
        item.write(ctx, &mut *w)?;
        if iter.peek().is_some() {
            write!(w, "{delim}")?;
        }
    }

    Ok(())
}

pub trait DebugProvider {
    #[allow(unused)]
    fn value_name(&self, func: &Function, func_ref: FuncRef, value: ValueId) -> Option<&str> {
        None
    }
}

const DEFAULT_PROVIDER: DefaultDebugProvider = DefaultDebugProvider {};

struct DefaultDebugProvider {}
impl DebugProvider for DefaultDebugProvider {}
