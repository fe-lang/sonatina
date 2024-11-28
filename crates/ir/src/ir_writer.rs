use std::io;

use smallvec::{Array, SmallVec};

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
        writeln!(w)?;

        // Write struct types defined in the module.
        self.module.ctx.with_ty_store(|s| {
            let mut has_type_def = false;
            for s in s.all_struct_data() {
                has_type_def = true;
                s.write(w, &self.module.ctx)?;
                writeln!(w)?;
            }

            if has_type_def {
                writeln!(w)?;
            }

            io::Result::Ok(())
        })?;

        // Write module level global variables.
        self.module.ctx.with_gv_store(|s| {
            for gv in s.all_gv_data() {
                gv.write(w, &self.module.ctx)?;
                writeln!(w)?;
            }

            if !s.is_empty() {
                writeln!(w)?;
            }

            io::Result::Ok(())
        })?;

        for func_ref in self.module.func_store.funcs() {
            self.module.func_store.view(func_ref, |func| {
                let mut writer = FuncWriter::with_debug_provider(func, func_ref, self.dbg);
                writer.write(&mut *w)
            })?;
            writeln!(w)?;
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

impl<'a> AsRef<ModuleCtx> for FuncWriteCtx<'a> {
    fn as_ref(&self) -> &ModuleCtx {
        self.module_ctx()
    }
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
    pub fn new(func_ref: FuncRef, func: &'a Function) -> Self {
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
        let func = &self.ctx.func;
        write!(w, "func ")?;
        func.sig.linkage().write(w, &self.ctx)?;
        write!(w, " %{}(", func.sig.name())?;
        let arg_values: SmallVec<[ValueWithTy; 8]> = self
            .ctx
            .func
            .arg_values
            .iter()
            .map(|value| ValueWithTy(*value))
            .collect();
        arg_values.write_with_delim(w, ", ", &self.ctx)?;

        write!(w, ") -> ")?;
        func.sig.ret_ty().write(w, &self.ctx)?;
        writeln!(w, " {{")?;

        self.level += 1;

        for block in self.ctx.func.layout.iter_block() {
            self.write_block_with_inst(w, block)?;
            if !self.ctx.func.layout.is_last_block(block) {
                writeln!(w)?;
            }
        }

        self.level -= 1;
        writeln!(w, "}}")
    }

    pub fn dump_string(&mut self) -> String {
        let mut s = Vec::new();
        self.write(&mut s).unwrap();
        unsafe { String::from_utf8_unchecked(s) }
    }

    fn write_block_with_inst(&mut self, w: &mut impl io::Write, block: BlockId) -> io::Result<()> {
        self.indent(w)?;
        block.write(w, &self.ctx)?;

        self.enter(&mut *w)?;
        for inst in self.ctx.func.layout.iter_inst(block) {
            self.write_inst_in_block(w, inst)?;
        }
        self.leave();

        Ok(())
    }

    fn write_inst_in_block(&mut self, w: &mut impl io::Write, inst: InstId) -> io::Result<()> {
        self.indent(&mut *w)?;
        let inst_with_res = InstStatement(inst);
        inst_with_res.write(w, &self.ctx)?;
        writeln!(w)
    }

    fn indent(&self, w: &mut impl io::Write) -> io::Result<()> {
        write!(w, "{}", " ".repeat(self.level as usize * 4))
    }

    fn enter(&mut self, mut w: impl io::Write) -> io::Result<()> {
        self.level += 1;
        writeln!(w, ":")
    }

    fn leave(&mut self) {
        self.level -= 1;
    }
}

pub trait IrWrite<Ctx> {
    fn write<W>(&self, w: &mut W, ctx: &Ctx) -> io::Result<()>
    where
        W: io::Write;

    fn write_with_delim<W>(&self, w: &mut W, _delim: &str, ctx: &Ctx) -> io::Result<()>
    where
        W: io::Write,
    {
        self.write(w, ctx)
    }

    fn dump_string(&self, ctx: &Ctx) -> String {
        let mut bytes = Vec::new();
        self.write(&mut bytes, ctx).unwrap();
        unsafe { String::from_utf8_unchecked(bytes) }
    }

    fn has_content(&self) -> bool {
        true
    }
}

impl<Ctx, T, U> IrWrite<Ctx> for (T, U)
where
    T: IrWrite<Ctx>,
    U: IrWrite<Ctx>,
{
    fn write<W>(&self, w: &mut W, ctx: &Ctx) -> io::Result<()>
    where
        W: io::Write,
    {
        self.write_with_delim(w, " ", ctx)
    }

    fn write_with_delim<W>(&self, w: &mut W, delim: &str, ctx: &Ctx) -> io::Result<()>
    where
        W: io::Write,
    {
        write!(w, "(")?;
        self.0.write(w, ctx)?;
        if self.has_content() {
            write!(w, "{delim}")?;
            self.1.write(w, ctx)?;
        }
        write!(w, ")")
    }

    fn has_content(&self) -> bool {
        self.1.has_content() || self.has_content()
    }
}

impl<T, Ctx> IrWrite<Ctx> for [T]
where
    T: IrWrite<Ctx>,
{
    fn write<W>(&self, w: &mut W, ctx: &Ctx) -> io::Result<()>
    where
        W: io::Write,
    {
        self.write_with_delim(w, " ", ctx)
    }

    fn write_with_delim<W>(&self, w: &mut W, delim: &str, ctx: &Ctx) -> io::Result<()>
    where
        W: io::Write,
    {
        let mut iter = self.iter();
        let mut has_written = false;

        if let Some(value) = iter.next() {
            has_written |= value.has_content();
            value.write(w, ctx)?;
        }

        for value in iter {
            if has_written {
                write!(w, "{delim}")?;
            }
            value.write_with_delim(w, delim, ctx)?;
            has_written |= value.has_content();
        }

        Ok(())
    }

    fn has_content(&self) -> bool {
        self.iter().any(|x| x.has_content())
    }
}

impl<T, Ctx> IrWrite<Ctx> for Vec<T>
where
    T: IrWrite<Ctx>,
{
    fn write<W>(&self, w: &mut W, ctx: &Ctx) -> io::Result<()>
    where
        W: io::Write,
    {
        self.as_slice().write(w, ctx)
    }

    fn write_with_delim<W>(&self, w: &mut W, delim: &str, ctx: &Ctx) -> io::Result<()>
    where
        W: io::Write,
    {
        self.as_slice().write_with_delim(w, delim, ctx)
    }

    fn has_content(&self) -> bool {
        self.as_slice().has_content()
    }
}

impl<T, Ctx, const N: usize> IrWrite<Ctx> for SmallVec<[T; N]>
where
    [T; N]: Array<Item = T>,
    T: IrWrite<Ctx>,
{
    fn write<W>(&self, w: &mut W, ctx: &Ctx) -> io::Result<()>
    where
        W: io::Write,
    {
        self.as_slice().write(w, ctx)
    }

    fn write_with_delim<W>(&self, w: &mut W, delim: &str, ctx: &Ctx) -> io::Result<()>
    where
        W: io::Write,
    {
        self.as_slice().write_with_delim(w, delim, ctx)
    }

    fn has_content(&self) -> bool {
        self.as_slice().has_content()
    }
}

impl<T, Ctx> IrWrite<Ctx> for Option<T>
where
    T: IrWrite<Ctx>,
{
    fn write<W>(&self, w: &mut W, ctx: &Ctx) -> io::Result<()>
    where
        W: io::Write,
    {
        if let Some(content) = self {
            content.write(w, ctx)?;
        }

        Ok(())
    }

    fn has_content(&self) -> bool {
        self.as_ref().map(|x| x.has_content()).unwrap_or_default()
    }
}

#[derive(Clone, Copy)]
pub struct ValueWithTy(pub ValueId);
impl<'a> IrWrite<FuncWriteCtx<'a>> for ValueWithTy {
    fn write<W>(&self, w: &mut W, ctx: &FuncWriteCtx) -> io::Result<()>
    where
        W: io::Write,
    {
        let value = self.0;
        value.write(w, ctx)?;
        if let Value::Immediate { .. } = ctx.dfg().value(self.0) {
            Ok(())
        } else {
            let ty = ctx.dfg().value_ty(self.0);
            write!(w, ".")?;
            ty.write(w, ctx)
        }
    }
}

pub struct InstStatement(pub InstId);
impl<'a> IrWrite<FuncWriteCtx<'a>> for InstStatement {
    fn write<W>(&self, w: &mut W, ctx: &FuncWriteCtx) -> io::Result<()>
    where
        W: io::Write,
    {
        if let Some(result) = ctx.func.dfg.inst_result(self.0) {
            let result_with_ty = ValueWithTy(result);
            result_with_ty.write(w, ctx)?;
            write!(w, " = ")?;
        };

        self.0.write(w, ctx)?;
        write!(w, ";")
    }
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
