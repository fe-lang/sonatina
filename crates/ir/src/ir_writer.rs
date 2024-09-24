use std::{fmt, io};

use crate::{
    module::{FuncRef, ModuleCtx},
    types::{CompoundType, CompoundTypeData, StructData},
    GlobalVariableData, InstId, Module, Value,
};

use super::{BlockId, Function, Inst, Type, ValueId};

pub trait DebugProvider {
    fn value_name(&self, _func: FuncRef, _value: ValueId) -> Option<&str> {
        None
    }
}
impl DebugProvider for () {}

pub struct ModuleWriter<'a> {
    module: &'a Module,
    debug: Option<&'a dyn DebugProvider>,
}

impl<'a> ModuleWriter<'a> {}

impl<'a> ModuleWriter<'a> {
    pub fn new(module: &'a Module) -> Self {
        Self {
            module,
            debug: None,
        }
    }

    pub fn with_debug_provider(module: &'a Module, debug: &'a dyn DebugProvider) -> Self {
        Self {
            module,
            debug: Some(debug),
        }
    }

    pub fn write(&mut self, mut w: impl io::Write) -> io::Result<()> {
        // Write target.
        writeln!(w, "target = {}", self.module.ctx.isa.triple())?;

        // Write struct types defined in the module.
        self.module.ctx.with_ty_store(|s| {
            for s in s.all_struct_data() {
                s.ir_write(&self.module.ctx, &mut w)?;
            }
            io::Result::Ok(())
        })?;

        // Write module level global variables.
        self.module.ctx.with_gv_store(|s| {
            for gv in s.all_gv_data() {
                gv.ir_write(&self.module.ctx, &mut w)?;
            }

            io::Result::Ok(())
        })?;

        for func_ref in self.module.funcs.keys() {
            let func = &self.module.funcs[func_ref];
            let mut func_writer = FuncWriter::new(func_ref, func, self.debug);
            func_writer.write(&mut w)?;
            writeln!(w)?;
        }

        Ok(())
    }

    pub fn dump_string(&mut self) -> io::Result<String> {
        let mut s = Vec::new();
        self.write(&mut s)?;
        unsafe { Ok(String::from_utf8_unchecked(s)) }
    }
}

pub struct FuncWriter<'a> {
    pub(crate) func_ref: FuncRef,
    pub(crate) func: &'a Function,
    level: u8,
    debug: Option<&'a dyn DebugProvider>,
}

impl<'a> FuncWriter<'a> {
    pub fn new(
        func_ref: FuncRef,
        func: &'a Function,
        debug: Option<&'a dyn DebugProvider>,
    ) -> Self {
        Self {
            func_ref,
            func,
            level: 0,
            debug,
        }
    }

    pub fn write(&mut self, mut w: impl io::Write) -> io::Result<()> {
        w.write_fmt(format_args!(
            "func {} %{}(",
            self.func.sig.linkage(),
            self.func.sig.name()
        ))?;
        self.write_iter_with_delim(
            self.func.arg_values.iter().map(|v| ValueWithTy(*v)),
            ", ",
            &mut w,
        )?;
        write!(w, ") -> ")?;
        self.func.sig.ret_ty().ir_write(self.ctx(), &mut w)?;

        writeln!(w, " {{")?;
        self.level += 1;

        for block in self.func.layout.iter_block() {
            self.write_block_with_inst(block, &mut w)?;
            self.newline(&mut w)?;
            self.newline(&mut w)?;
        }

        self.level -= 1;
        writeln!(w, "}}")?;

        Ok(())
    }

    pub fn ctx(&self) -> &ModuleCtx {
        &self.func.dfg.ctx
    }

    pub fn dump_string(&mut self) -> io::Result<String> {
        let mut s = Vec::new();
        self.write(&mut s)?;
        unsafe { Ok(String::from_utf8_unchecked(s)) }
    }

    pub fn value_name(&self, value: ValueId) -> Option<&str> {
        self.debug.and_then(|d| d.value_name(self.func_ref, value))
    }

    pub fn write_block_with_inst(
        &mut self,
        block: BlockId,
        mut w: impl io::Write,
    ) -> io::Result<()> {
        self.indent(&mut w)?;
        block.write(self, &mut w)?;

        self.enter(&mut w)?;
        let insts = self.func.layout.iter_inst(block);
        self.write_iter_with_delim(insts, ";\n", &mut w)?;
        write!(w, ";");
        self.leave();

        Ok(())
    }

    pub fn write_inst_values(&mut self, inst: &dyn Inst, mut w: impl io::Write) -> io::Result<()> {
        let values = inst.collect_values();

        self.write_iter_with_delim(values.iter(), " ", &mut w)
    }

    pub fn write_iter_with_delim<T>(
        &mut self,
        iter: impl Iterator<Item = T>,
        delim: &str,
        mut w: impl io::Write,
    ) -> io::Result<()>
    where
        T: IrWrite,
    {
        let mut iter = iter.peekable();
        while let Some(item) = iter.next() {
            item.write(self, &mut w)?;
            if iter.peek().is_some() {
                w.write_all(delim.as_bytes())?;
            }
        }

        Ok(())
    }

    pub fn indent(&self, mut w: impl io::Write) -> io::Result<()> {
        w.write_all(" ".repeat(self.level as usize * 4).as_bytes())
    }

    pub fn newline(&self, mut w: impl io::Write) -> io::Result<()> {
        w.write_all(b"\n")
    }

    pub fn space(&self, mut w: impl io::Write) -> io::Result<()> {
        w.write_all(b" ")
    }

    fn enter(&mut self, mut w: impl io::Write) -> io::Result<()> {
        self.level += 1;
        w.write_all(b":\n")
    }

    fn leave(&mut self) {
        self.level -= 1;
    }
}

impl DisplayWithFunc for ValueId {
    fn fmt(&self, func: &Function, formatter: &mut fmt::Formatter) -> fmt::Result {
        let value = *self;
        match func.dfg.value(*self) {
            Value::Immediate { imm, ty } => {
                let ty = DisplayableWithFunc(ty, func);
                write!(formatter, "{}.{}", imm, ty)
            }
            Value::Global { gv, .. } => func
                .dfg
                .ctx
                .with_gv_store(|s| write!(formatter, "%{}", s.gv_data(*gv).symbol)),
            _ => {
                write!(formatter, "v{}", value.0)
            }
        }
    }
}

impl GlobalVariableData {
    fn ir_write(&self, ctx: &ModuleCtx, w: &mut impl io::Write) -> io::Result<()> {
        let const_ = if self.is_const { " const" } else { "" };
        write! {w, "gv {}{const_} %{}:", self.linkage, self.symbol}?;
        self.ty.ir_write(ctx, w)?;

        if let Some(data) = &self.data {
            write!(w, " = {};", data)
        } else {
            write!(w, ";")
        }
    }
}

impl DisplayWithFunc for BlockId {
    fn fmt(&self, func: &Function, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "block{}", self.0)
    }
}

impl StructData {
    fn ir_write(&self, ctx: &ModuleCtx, w: &mut dyn io::Write) -> io::Result<()> {
        write!(w, "type %{} = ", self.name)?;
        if self.packed {
            write!(w, "<{{")?;
        } else {
            write!(w, "{{")?;
        }

        let mut delim = "";
        for &ty in &self.fields {
            write!(w, "{}", delim)?;
            ty.ir_write(ctx, w)?;
            delim = ", ";
        }

        if self.packed {
            writeln!(w, "}}>;")
        } else {
            writeln!(w, "}};")
        }
    }
}

#[derive(Clone)]
struct ValueWithTy(ValueId);

impl DisplayWithFunc for ValueWithTy {
    fn fmt(&self, func: &Function, formatter: &mut fmt::Formatter) -> fmt::Result {
        let value = DisplayableWithFunc(self.0, func);
        let ty = func.dfg.value_ty(self.0);
        let ty = DisplayableWithFunc(ty, func);
        write!(formatter, "{value}.{ty}")
    }
}

pub trait DisplayWithFunc {
    fn fmt(&self, func: &Function, formatter: &mut fmt::Formatter) -> fmt::Result;
}

impl<T> DisplayWithFunc for &T
where
    T: DisplayWithFunc,
{
    fn fmt(&self, func: &Function, formatter: &mut fmt::Formatter) -> fmt::Result {
        (*self).fmt(func, formatter)
    }
}

impl DisplayWithFunc for InstId {
    fn fmt(&self, func: &Function, formatter: &mut fmt::Formatter) -> fmt::Result {
        let inst = func.dfg.inst(*self);
        inst.fmt(func, formatter)
    }
}

pub(crate) struct DisplayFuncHelper<'a> {
    pub(crate) func: &'a Function,
}
impl<'a> DisplayFuncHelper<'a> {
    pub(crate) fn new(func: &'a Function) -> Self {
        Self { func }
    }
}

pub fn write_iter_with_delim<T>(
    func: &Function,
    f: &mut fmt::Formatter,
    iter: impl Iterator<Item = T>,
    delim: &str,
) -> fmt::Result
where
    T: DisplayWithFunc,
{
    let mut iter = iter.peekable();
    while let Some(item) = iter.next() {
        item.fmt(func, f);
        if iter.peek().is_some() {
            f.write_str(delim)?;
        }
    }

    Ok(())
}

pub(crate) struct DisplayableWithFunc<'f, T>(pub(crate) T, pub(crate) &'f Function);
impl<'f, T> fmt::Display for DisplayableWithFunc<'f, T>
where
    T: DisplayWithFunc,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(self.1, f)
    }
}
