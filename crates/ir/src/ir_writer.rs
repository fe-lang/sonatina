use std::io;

use smallvec::{Array, SmallVec};

use super::{BlockId, Function};
use crate::{
    DataFlowGraph, InstId, Module, Value, ValueId,
    module::{FuncRef, ModuleCtx},
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
        writeln!(w, "target = \"{}\"", self.module.ctx.triple)?;
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

        let (func_defs, func_decls): (Vec<_>, Vec<_>) = self
            .module
            .func_store
            .funcs()
            .into_iter()
            .partition(|func_ref| {
                self.module
                    .ctx
                    .func_sig(*func_ref, |sig| sig.linkage().has_definition())
            });
        // Write an external functions.
        for &func_ref in &func_decls {
            self.module.ctx.func_sig(func_ref, |sig| {
                write!(w, "declare ")?;
                sig.write(w, &self.module.ctx)?;
                writeln!(w, ";")
            })?;
        }
        if !func_decls.is_empty() && !func_defs.is_empty() {
            writeln!(w)?;
        }

        for func_ref in func_defs {
            self.module.func_store.view(func_ref, |func| {
                let mut writer = FuncWriter::with_debug_provider(func, func_ref, self.dbg);
                writer.write(&mut *w)
            })?;
            writeln!(w)?;
        }

        if !self.module.objects.is_empty() {
            let mut objects: Vec<_> = self.module.objects.values().collect();
            objects.sort_by(|a, b| a.name.0.as_str().cmp(b.name.0.as_str()));

            writeln!(w)?;
            for (i, object) in objects.iter().enumerate() {
                object.write(w, &self.module.ctx)?;
                if i + 1 != objects.len() {
                    writeln!(w)?;
                    writeln!(w)?;
                }
            }
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

impl AsRef<ModuleCtx> for FuncWriteCtx<'_> {
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
        FunctionSignature.write(w, &self.ctx)?;
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
pub struct FunctionSignature;
impl IrWrite<FuncWriteCtx<'_>> for FunctionSignature {
    fn write<W>(&self, w: &mut W, ctx: &FuncWriteCtx) -> io::Result<()>
    where
        W: io::Write,
    {
        let func_ref = ctx.func_ref;
        let m_ctx = ctx.module_ctx();

        write!(w, "func ")?;
        m_ctx.func_sig(func_ref, |sig| {
            sig.linkage().write(w, ctx)?;
            write!(w, " %{}(", sig.name())?;
            io::Result::Ok(())
        })?;
        let arg_values: SmallVec<[ValueWithTy; 8]> = ctx
            .func
            .arg_values
            .iter()
            .map(|value| ValueWithTy(*value))
            .collect();
        arg_values.write_with_delim(w, ", ", ctx)?;
        write!(w, ")")?;

        m_ctx.func_sig(func_ref, |sig| {
            let ret_ty = sig.ret_ty();
            if !ret_ty.is_unit() {
                write!(w, " -> ")?;
                ret_ty.write(w, ctx)
            } else {
                Ok(())
            }
        })
    }
}

#[derive(Clone, Copy)]
pub struct ValueWithTy(pub ValueId);
impl IrWrite<FuncWriteCtx<'_>> for ValueWithTy {
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
impl IrWrite<FuncWriteCtx<'_>> for InstStatement {
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
