use std::{fmt, io};

use crate::{
    module::{FuncRef, ModuleCtx},
    InstId, Module, Value,
};

use super::{BlockId, Function, ValueId};

pub trait DebugProvider {
    fn value_name(&self, _func: FuncRef, _value: ValueId) -> Option<&str> {
        None
    }
}
impl DebugProvider for () {}

pub struct ModuleWriter<'a> {
    module: &'a Module,
}

impl<'a> ModuleWriter<'a> {}

impl<'a> ModuleWriter<'a> {
    pub fn new(module: &'a Module) -> Self {
        Self { module }
    }

    pub fn write(&mut self, mut w: impl io::Write) -> io::Result<()> {
        // Write target.
        writeln!(w, "target = {}", self.module.ctx.isa.triple())?;

        // Write struct types defined in the module.
        self.module.ctx.with_ty_store(|s| {
            for s in s.all_struct_data() {
                let s = DisplayableWithModule(s, &self.module.ctx);
                write!(w, "{s}")?;
            }
            io::Result::Ok(())
        })?;

        // Write module level global variables.
        self.module.ctx.with_gv_store(|s| {
            for gv in s.all_gv_data() {
                let gv = DisplayableWithModule(gv, &self.module.ctx);
                write!(w, "{gv}")?;
            }

            io::Result::Ok(())
        })?;

        for func_ref in self.module.funcs.keys() {
            let func = &self.module.funcs[func_ref];
            writeln!(w, "{func}")?;
        }

        Ok(())
    }

    pub fn dump_string(&mut self) -> io::Result<String> {
        let mut s = Vec::new();
        self.write(&mut s)?;
        unsafe { Ok(String::from_utf8_unchecked(s)) }
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut fw = FuncWriter::new(self);
        fw.write(f)
    }
}

struct FuncWriter<'a> {
    pub(crate) func: &'a Function,
    level: u8,
}

impl<'a> FuncWriter<'a> {
    fn new(func: &'a Function) -> Self {
        Self { func, level: 0 }
    }

    // TODO: fix.
    fn write(&mut self, mut f: &mut fmt::Formatter) -> fmt::Result {
        f.write_fmt(format_args!(
            "func {} %{}(",
            self.func.sig.linkage(),
            self.func.sig.name()
        ))?;
        display_iter_with_delim(
            f,
            self.func
                .arg_values
                .iter()
                .map(|v| DisplayableWithFunc(ValueWithTy(*v), self.func)),
            ", ",
        )?;
        let ret_ty = DisplayableWithModule(self.func.sig.ret_ty(), self.func.ctx());
        write!(f, ") -> {ret_ty} {{")?;

        self.level += 1;
        for block in self.func.layout.iter_block() {
            self.write_block_with_inst(block, f)?;
            self.newline(&mut f)?;
            self.newline(&mut f)?;
        }

        self.level -= 1;
        writeln!(f, "}}")?;

        Ok(())
    }

    pub fn write_block_with_inst(&mut self, block: BlockId, f: &mut fmt::Formatter) -> fmt::Result {
        self.indent(f)?;
        write!(f, "{}", DisplayableWithFunc(block, self.func))?;

        self.enter(f)?;
        let insts = self
            .func
            .layout
            .iter_inst(block)
            .map(|inst| DisplayableWithFunc(inst, self.func));
        display_iter_with_delim(f, insts, ";\n")?;
        write!(f, ";")?;
        self.leave();

        Ok(())
    }

    pub fn indent(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", " ".repeat(self.level as usize * 4))
    }

    pub fn newline(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "\n")
    }

    fn enter(&mut self, f: &mut fmt::Formatter) -> fmt::Result {
        self.level += 1;
        write!(f, ":\n")
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
                let ty = DisplayableWithModule(ty, func.ctx());
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

pub trait DisplayWithModule {
    fn fmt(&self, module: &ModuleCtx, formatter: &mut fmt::Formatter) -> fmt::Result;
}

impl<T> DisplayWithModule for &T
where
    T: DisplayWithModule,
{
    fn fmt(&self, module: &ModuleCtx, formatter: &mut fmt::Formatter) -> fmt::Result {
        (*self).fmt(module, formatter)
    }
}
pub(crate) struct DisplayableWithModule<'m, T>(pub(crate) T, pub(crate) &'m ModuleCtx);
impl<'m, T> fmt::Display for DisplayableWithModule<'m, T>
where
    T: DisplayWithModule,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(self.1, f)
    }
}

#[derive(Clone)]
struct ValueWithTy(ValueId);

impl DisplayWithFunc for ValueWithTy {
    fn fmt(&self, func: &Function, formatter: &mut fmt::Formatter) -> fmt::Result {
        let value = DisplayableWithFunc(self.0, func);
        let ty = func.dfg.value_ty(self.0);
        let ty = DisplayableWithModule(ty, func.ctx());
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

pub(crate) struct DisplayableWithFunc<'f, T>(pub(crate) T, pub(crate) &'f Function);
impl<'f, T> fmt::Display for DisplayableWithFunc<'f, T>
where
    T: DisplayWithFunc,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(self.1, f)
    }
}

pub fn display_iter_with_delim<T>(
    f: &mut fmt::Formatter,
    iter: impl Iterator<Item = T>,
    delim: &str,
) -> fmt::Result
where
    T: fmt::Display,
{
    let mut iter = iter.peekable();
    while let Some(item) = iter.next() {
        write!(f, "{item}")?;
        if iter.peek().is_some() {
            f.write_str(delim)?;
        }
    }

    Ok(())
}
