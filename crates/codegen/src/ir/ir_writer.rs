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
        self.write_iter_with_delim(
            self.func.arg_values.iter().map(|v| ValueWithTy(*v)),
            ", ",
            &mut w,
        )?;

        let mut rets = self.func.sig.returns().iter().peekable();
        if rets.peek().is_some() {
            w.write_all(b") -> ")?;
        } else {
            w.write_all(b")")?;
        }

        self.write_iter_with_delim(rets, ", ", &mut w)?;

        self.enter(&mut w)?;
        for block in self.func.layout.iter_block() {
            self.write_block_with_insn(block, &mut w)?;
            self.newline(&mut w)?;
            self.newline(&mut w)?;
        }
        self.leave();

        Ok(())
    }

    pub fn dump_string(&mut self) -> io::Result<String> {
        let mut s = Vec::new();
        self.write(&mut s)?;
        unsafe { Ok(String::from_utf8_unchecked(s)) }
    }

    fn write_block_with_insn(&mut self, block: Block, mut w: impl io::Write) -> io::Result<()> {
        self.indent(&mut w)?;
        block.write(self, &mut w)?;

        self.enter(&mut w)?;
        let insns = self.func.layout.iter_insn(block);
        self.write_iter_with_delim(insns, "\n", &mut w)?;
        self.leave();

        Ok(())
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

    fn enter(&mut self, mut w: impl io::Write) -> io::Result<()> {
        self.level += 1;
        w.write_all(b":\n")
    }

    fn leave(&mut self) {
        self.level -= 1;
    }
}

trait IrWrite {
    fn write(&self, writer: &mut FuncWriter, w: impl io::Write) -> io::Result<()>;
}

impl IrWrite for Value {
    fn write(&self, writer: &mut FuncWriter, mut w: impl io::Write) -> io::Result<()> {
        let value = writer.func.dfg.resolve_alias(*self);
        if let Some(imm) = writer.func.dfg.value_imm(value) {
            write!(w, "{}.", imm)?;
            let ty = writer.func.dfg.value_ty(value);
            ty.write(writer, w)
        } else {
            write!(w, "v{}", value.0)
        }
    }
}

impl IrWrite for Block {
    fn write(&self, _: &mut FuncWriter, mut w: impl io::Write) -> io::Result<()> {
        w.write_fmt(format_args!("block{}", self.0))
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
        if let Some(insn_result) = writer.func.dfg.insn_result(*self) {
            insn_result.write(writer, &mut w)?;
            w.write_all(b".")?;
            let ty = writer.func.dfg.value_ty(insn_result);
            ty.write(writer, &mut w)?;
            w.write_all(b" = ")?;
        }

        let insn_data = writer.func.dfg.insn_data(*self);
        match insn_data {
            Immediate { code } => w.write_all(code.to_string().as_bytes())?,
            Binary { code, args } => {
                w.write_fmt(format_args!("{}", code.as_str()))?;
                writer.space(&mut w)?;
                writer.write_insn_args(args, &mut w)?;
            }
            Cast { code, args, .. } => {
                w.write_fmt(format_args!("{}", code.as_str()))?;
                writer.space(&mut w)?;
                writer.write_insn_args(args, &mut w)?;
            }
            Load { args, ty } => {
                w.write_all(b"load")?;
                writer.space(&mut w)?;
                writer.write_insn_args(args, &mut w)?;
                writer.space(&mut w)?;
                ty.write(writer, &mut w)?;
            }
            Store { args } => {
                w.write_all(b"store")?;
                writer.write_insn_args(args, &mut w)?;
            }
            Jump { code, dests } => {
                w.write_fmt(format_args!("{}", code.as_str()))?;
                writer.space(&mut w)?;
                writer.write_iter_with_delim(dests.iter(), " ", &mut w)?;
            }
            Branch { args, dests } => {
                w.write_all(b"br")?;
                writer.space(&mut w)?;
                writer.write_insn_args(args, &mut w)?;
                writer.space(&mut w)?;
                writer.write_iter_with_delim(dests.iter(), " ", &mut w)?;
            }
            Return { args } => {
                w.write_all(b"return")?;
                if !args.is_empty() {
                    writer.space(&mut w)?;
                }
                writer.write_insn_args(args, &mut w)?;
            }
            Phi { values, blocks, .. } => {
                w.write_all(b"phi")?;
                writer.space(&mut w)?;
                let mut args = vec![];
                for (value, block) in values.iter().zip(blocks.iter()) {
                    let mut arg = vec![b'('];
                    value.write(writer, &mut arg)?;
                    writer.space(&mut arg)?;
                    block.write(writer, &mut arg)?;
                    arg.push(b')');
                    args.push(arg);
                }

                writer.write_iter_with_delim(args.iter(), " ", &mut w)?;
            }
        }

        w.write_all(b";")?;

        Ok(())
    }
}
#[derive(Clone)]
struct ValueWithTy(Value);

impl IrWrite for ValueWithTy {
    fn write(&self, f: &mut FuncWriter, mut w: impl io::Write) -> io::Result<()> {
        let ty = f.func.dfg.value_ty(self.0);
        self.0.write(f, &mut w)?;
        w.write_all(b".")?;
        ty.write(f, w)
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

impl IrWrite for Vec<u8> {
    fn write(&self, _: &mut FuncWriter, mut w: impl io::Write) -> io::Result<()> {
        w.write_all(self)
    }
}
