use std::{fmt, io};

use super::{BlockId, Function};
use crate::{module::ModuleCtx, InstId, Module, Value, ValueId};

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
        writeln!(w, "target = {}", self.module.ctx.triple)?;

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
        let mut fw = FuncDisplayHelper::new(self);
        fw.display(f)
    }
}

struct FuncDisplayHelper<'a> {
    pub(crate) func: &'a Function,
    level: u8,
}

impl<'a> FuncDisplayHelper<'a> {
    fn new(func: &'a Function) -> Self {
        Self { func, level: 0 }
    }

    fn display(&mut self, f: &mut fmt::Formatter) -> fmt::Result {
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
        write!(f, ") -> {ret_ty} {{\n")?;

        self.level += 1;
        for block in self.func.layout.iter_block() {
            self.write_block_with_inst(block, f)?;
        }

        self.level -= 1;
        writeln!(f, "}}")
    }

    fn write_block_with_inst(&mut self, block: BlockId, f: &mut fmt::Formatter) -> fmt::Result {
        self.indent(f)?;
        write!(f, "{}", DisplayableWithFunc(block, self.func))?;

        self.enter(f)?;
        for inst in self.func.layout.iter_inst(block) {
            self.write_inst_in_block(inst, f)?;
        }
        self.leave();

        self.newline(f)
    }

    fn write_inst_in_block(&mut self, inst: InstId, f: &mut fmt::Formatter) -> fmt::Result {
        self.indent(f)?;
        let inst_with_res = InstStatement(inst);
        write!(f, "{}\n", DisplayableWithFunc(inst_with_res, self.func))
    }

    fn indent(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", " ".repeat(self.level as usize * 4))
    }

    fn newline(&self, f: &mut fmt::Formatter) -> fmt::Result {
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
pub struct DisplayableWithModule<'m, T>(pub T, pub &'m ModuleCtx);
impl<'m, T> fmt::Display for DisplayableWithModule<'m, T>
where
    T: DisplayWithModule,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(self.1, f)
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

pub struct DisplayableWithFunc<'f, T>(pub T, pub &'f Function);

impl<'f, T> fmt::Display for DisplayableWithFunc<'f, T>
where
    T: DisplayWithFunc,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(self.1, f)
    }
}

#[derive(Clone, Copy)]
pub struct ValueWithTy(pub ValueId);
impl DisplayWithFunc for ValueWithTy {
    fn fmt(&self, func: &Function, formatter: &mut fmt::Formatter) -> fmt::Result {
        let value = DisplayableWithFunc(self.0, func);
        if let Value::Immediate { .. } = func.dfg.value(self.0) {
            write!(formatter, "{value}")
        } else {
            let ty = func.dfg.value_ty(self.0);
            let ty = DisplayableWithModule(ty, func.ctx());
            write!(formatter, "{value}.{ty}")
        }
    }
}

pub struct InstStatement(pub InstId);
impl DisplayWithFunc for InstStatement {
    fn fmt(&self, func: &Function, formatter: &mut fmt::Formatter) -> fmt::Result {
        if let Some(result) = func.dfg.inst_result(self.0) {
            let result_with_ty = ValueWithTy(result);
            write!(
                formatter,
                "{} = ",
                DisplayableWithFunc(result_with_ty, func)
            )?;
        };

        write!(formatter, "{};", DisplayableWithFunc(self.0, func))
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
