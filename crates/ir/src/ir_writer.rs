use std::io;

use super::{BlockId, Function};
use crate::{
    module::{FuncRef, ModuleCtx},
    InstId, Module, Value, ValueId,
};

pub struct ModuleWriter<'a> {
    module: &'a Module,
}

impl<'a> ModuleWriter<'a> {}

impl<'a> ModuleWriter<'a> {
    pub fn new(module: &'a Module) -> Self {
        Self { module }
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
            let mut writer = FuncWriterImpl::new(func, func_ref);
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

pub struct FuncWriter<'a> {
    func: &'a Function,
    func_ref: FuncRef,
}

impl<'a> FuncWriter<'a> {
    pub fn new(func: &'a Function, func_ref: FuncRef) -> Self {
        Self { func, func_ref }
    }

    pub fn write(&self, w: &mut impl io::Write) -> io::Result<()> {
        FuncWriterImpl::new(self.func, self.func_ref).write(w)
    }

    pub fn dump_string(&self) -> String {
        let mut s = Vec::new();
        self.write(&mut s).unwrap();
        unsafe { String::from_utf8_unchecked(s) }
    }
}

struct FuncWriterImpl<'a> {
    func: &'a Function,
    level: u8,
}

impl<'a> FuncWriterImpl<'a> {
    fn new(func: &'a Function, _func_ref: FuncRef) -> Self {
        Self { func, level: 0 }
    }

    fn write(&mut self, w: &mut impl io::Write) -> io::Result<()> {
        w.write_fmt(format_args!(
            "func {} %{}(",
            self.func.sig.linkage(),
            self.func.sig.name()
        ))?;
        write_iter_with_delim(
            &mut *w,
            self.func,
            self.func.arg_values.iter().map(|v| ValueWithTy(*v)),
            ", ",
        )?;
        write!(w, ") -> ")?;
        self.func.sig.ret_ty().write(self.func.ctx(), &mut *w)?;
        write!(w, " {{\n")?;

        self.level += 1;
        for block in self.func.layout.iter_block() {
            self.write_block_with_inst(block, &mut *w)?;
        }

        self.level -= 1;
        writeln!(w, "}}")
    }

    fn write_block_with_inst(&mut self, block: BlockId, w: &mut impl io::Write) -> io::Result<()> {
        self.indent(&mut *w)?;
        block.write(self.func, &mut *w)?;

        self.enter(&mut *w)?;
        for inst in self.func.layout.iter_inst(block) {
            self.write_inst_in_block(inst, &mut *w)?;
        }
        self.leave();

        self.newline(w)
    }

    fn write_inst_in_block(&mut self, inst: InstId, w: &mut impl io::Write) -> io::Result<()> {
        self.indent(&mut *w)?;
        let inst_with_res = InstStatement(inst);
        inst_with_res.write(self.func, &mut *w)?;
        write!(w, "\n")
    }

    fn indent(&self, mut w: impl io::Write) -> io::Result<()> {
        write!(w, "{}", " ".repeat(self.level as usize * 4))
    }

    fn newline(&self, mut w: impl io::Write) -> io::Result<()> {
        write!(w, "\n")
    }

    fn enter(&mut self, mut w: impl io::Write) -> io::Result<()> {
        self.level += 1;
        write!(w, ":\n")
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
    fn write(&self, func: &Function, w: &mut impl io::Write) -> io::Result<()>;

    fn dump_string(&self, func: &Function) -> String {
        let mut s = Vec::new();
        self.write(func, &mut s).unwrap();
        unsafe { String::from_utf8_unchecked(s) }
    }
}

impl<T> WriteWithFunc for &T
where
    T: WriteWithFunc,
{
    fn write(&self, func: &Function, w: &mut impl io::Write) -> io::Result<()> {
        (*self).write(func, w)
    }
}

#[derive(Clone, Copy)]
pub struct ValueWithTy(pub ValueId);
impl WriteWithFunc for ValueWithTy {
    fn write(&self, func: &Function, w: &mut impl io::Write) -> io::Result<()> {
        let value = self.0;
        value.write(func, &mut *w)?;
        if let Value::Immediate { .. } = func.dfg.value(self.0) {
            Ok(())
        } else {
            let ty = func.dfg.value_ty(self.0);
            write!(w, ".")?;
            ty.write(func.ctx(), &mut *w)
        }
    }
}

pub struct InstStatement(pub InstId);
impl WriteWithFunc for InstStatement {
    fn write(&self, func: &Function, w: &mut impl io::Write) -> io::Result<()> {
        if let Some(result) = func.dfg.inst_result(self.0) {
            let result_with_ty = ValueWithTy(result);
            result_with_ty.write(func, &mut *w)?;
            write!(w, " = ")?;
        };

        self.0.write(func, w)?;
        write!(w, ";")
    }
}

pub fn write_iter_with_delim<T>(
    w: &mut impl io::Write,
    func: &Function,
    iter: impl Iterator<Item = T>,
    delim: &str,
) -> io::Result<()>
where
    T: WriteWithFunc,
{
    let mut iter = iter.peekable();
    while let Some(item) = iter.next() {
        item.write(func, &mut *w)?;
        if iter.peek().is_some() {
            write!(w, "{delim}")?;
        }
    }

    Ok(())
}
