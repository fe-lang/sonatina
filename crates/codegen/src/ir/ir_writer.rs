use std::io;

use super::{Block, Function, Insn, InsnData, Type, Value};

pub struct FuncWriter<'a> {
    func: &'a Function,
    level: u8,
}

impl<'a> FuncWriter<'a> {
    pub fn new(func: &'a Function) -> Self {
        Self { func, level: 0 }
    }

    pub fn write(&mut self, mut w: impl io::Write) -> io::Result<()> {
        w.write_fmt(format_args!("func %{}(", self.func.name))?;
        let sig = &self.func.sig;
        self.write_iter_with_delim(sig.args().iter(), ", ", &mut w)?;

        let mut rets = sig.returns().iter().peekable();
        if rets.peek().is_some() {
            w.write_all(b") -> ")?;
        } else {
            w.write_all(b")")?;
        }

        self.write_iter_with_delim(rets, ", ", &mut w)?;

        self.enter_item(&mut w)?;
        for block in self.func.layout.iter_block() {
            self.write_block_with_insn(block, &mut w)?;
            self.newline(&mut w)?;
            self.newline(&mut w)?;
        }
        self.leave_item();

        Ok(())
    }

    pub fn dump_string(&mut self) -> io::Result<String> {
        let mut s = Vec::new();
        self.write(&mut s)?;
        unsafe { Ok(String::from_utf8_unchecked(s)) }
    }

    fn write_block_with_insn(&mut self, block: Block, mut w: impl io::Write) -> io::Result<()> {
        self.indent(&mut w)?;
        self.write_block(block, &mut w)?;

        self.enter_item(&mut w)?;
        let insns = self.func.layout.iter_insn(block);
        self.write_iter_with_delim(insns, "\n", &mut w)?;
        self.leave_item();

        Ok(())
    }

    fn write_block<'b>(&mut self, block: Block, mut w: impl io::Write) -> io::Result<()> {
        w.write_fmt(format_args!("%block{}", block.0))
    }

    fn write_insn_args(&mut self, args: &[Value], mut w: impl io::Write) -> io::Result<()> {
        self.write_iter_with_delim(args.iter(), " ", &mut w)
    }

    fn write_iter_with_delim<T>(
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

    fn indent(&self, mut w: impl io::Write) -> io::Result<()> {
        w.write_all(" ".repeat(self.level as usize * 4).as_bytes())
    }

    fn newline(&self, mut w: impl io::Write) -> io::Result<()> {
        w.write_all(b"\n")
    }

    fn space(&self, mut w: impl io::Write) -> io::Result<()> {
        w.write_all(b" ")
    }

    fn enter_item(&mut self, mut w: impl io::Write) -> io::Result<()> {
        self.level += 1;
        w.write_all(b":\n")
    }

    fn leave_item(&mut self) {
        self.level -= 1;
    }
}

trait IrWrite {
    fn write(&self, writer: &mut FuncWriter, w: impl io::Write) -> io::Result<()>;
}

impl IrWrite for Value {
    fn write(&self, writer: &mut FuncWriter, mut w: impl io::Write) -> io::Result<()> {
        let value = writer.func.dfg.resolve_alias(*self);
        w.write_fmt(format_args!(
            "%v{}.{}",
            value.0,
            writer.func.dfg.value_ty(value),
        ))
    }
}

impl IrWrite for Type {
    fn write(&self, _: &mut FuncWriter, mut w: impl io::Write) -> io::Result<()> {
        write!(w, "{}", self)
    }
}

impl IrWrite for Insn {
    fn write(&self, writer: &mut FuncWriter, mut w: impl io::Write) -> io::Result<()> {
        use InsnData::*;

        writer.indent(&mut w)?;
        let ret_val = writer.func.dfg.insn_result(*self);
        if let Some(ret_val) = ret_val {
            ret_val.write(writer, &mut w)?;
            w.write_all(b" = ")?;
        }

        let insn_data = writer.func.dfg.insn_data(*self);
        match insn_data {
            Immediate { code } => w.write_all(code.to_string().as_bytes())?,
            Binary { code, args } => {
                w.write_fmt(format_args!("{} ", code.as_str()))?;
                writer.write_insn_args(args, &mut w)?;
            }
            Cast { code, args, .. } => {
                w.write_fmt(format_args!("{} ", code.as_str()))?;
                writer.write_insn_args(args, &mut w)?;
            }
            Load { args, .. } => {
                w.write_all(b"load ")?;
                writer.write_insn_args(args, &mut w)?;
            }
            Store { args } => {
                w.write_all(b"store ")?;
                writer.write_insn_args(args, &mut w)?;
            }
            Jump { code, dest } => {
                w.write_fmt(format_args!("{} ", code.as_str()))?;
                writer.write_block(*dest, &mut w)?;
            }
            Branch { code, args, dest } => {
                w.write_fmt(format_args!("{} ", code.as_str()))?;
                writer.write_insn_args(args, &mut w)?;
                writer.space(&mut w)?;
                writer.write_block(*dest, &mut w)?;
            }
            Phi { args, .. } => {
                w.write_all(b"phi ")?;
                writer.write_insn_args(args, &mut w)?;
            }
        }

        Ok(())
    }
}

impl<T> IrWrite for &T
where
    T: IrWrite,
{
    fn write(&self, f: &mut FuncWriter, w: impl io::Write) -> io::Result<()> {
        (*self).write(f, w)
    }
}
