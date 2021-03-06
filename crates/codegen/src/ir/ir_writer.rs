use std::io;

use crate::ir::DataLocationKind;

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
        self.func.sig.ret_ty().write(self, &mut w)?;

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
            Unary { code, args } => {
                write!(w, "{}", code)?;
                writer.space(&mut w)?;
                writer.write_insn_args(args, &mut w)?;
            }

            Binary { code, args } => {
                write!(w, "{}", code)?;
                writer.space(&mut w)?;
                writer.write_insn_args(args, &mut w)?;
            }

            Cast { code, args, .. } => {
                write!(w, "{}", code)?;
                writer.space(&mut w)?;
                writer.write_insn_args(args, &mut w)?;
            }

            Load { args, loc } => {
                write!(w, "load")?;
                writer.space(&mut w)?;
                match loc {
                    DataLocationKind::Memory => write!(w, "@memory")?,
                    DataLocationKind::Storage => write!(w, "@storage")?,
                }
                writer.space(&mut w)?;
                writer.write_insn_args(args, &mut w)?;
            }

            Store { args, loc } => {
                write!(w, "store")?;
                writer.space(&mut w)?;
                match loc {
                    DataLocationKind::Memory => write!(w, "@memory")?,
                    DataLocationKind::Storage => write!(w, "@storage")?,
                }
                writer.space(&mut w)?;
                writer.write_insn_args(args, &mut w)?;
            }

            Call { func, args, .. } => {
                write!(w, "call")?;
                writer.space(&mut w)?;
                write!(w, "%{}", writer.func.callees[func].name())?;
                writer.space(&mut w)?;
                writer.write_insn_args(args, &mut w)?;
            }

            Jump { code, dests } => {
                write!(w, "{}", code)?;
                writer.space(&mut w)?;
                writer.write_iter_with_delim(dests.iter(), " ", &mut w)?;
            }

            Branch { args, dests } => {
                write!(w, "br")?;
                writer.space(&mut w)?;
                writer.write_insn_args(args, &mut w)?;
                writer.space(&mut w)?;
                writer.write_iter_with_delim(dests.iter(), " ", &mut w)?;
            }

            BrTable {
                args,
                default,
                table,
            } => {
                write!(w, "br_table")?;
                writer.space(&mut w)?;
                args[0].write(writer, &mut w)?;
                writer.space(&mut w)?;
                if let Some(default) = default {
                    default.write(writer, &mut w)?;
                } else {
                    write!(w, "undef")?;
                }
                writer.space(&mut w)?;

                let mut table_args = vec![];
                for (value, block) in args[1..].iter().zip(table.iter()) {
                    let mut arg = vec![b'('];
                    value.write(writer, &mut arg)?;
                    writer.space(&mut arg)?;
                    block.write(writer, &mut arg)?;
                    arg.push(b')');
                    table_args.push(arg);
                }

                writer.write_iter_with_delim(table_args.iter(), " ", &mut w)?;
            }

            Alloca { ty } => {
                write!(w, "alloca")?;
                writer.space(&mut w)?;
                ty.write(writer, &mut w)?;
            }

            Return { args } => {
                write!(w, "return")?;
                if let Some(arg) = args {
                    writer.space(&mut w)?;
                    arg.write(writer, &mut w)?;
                }
            }

            Phi { values, blocks, .. } => {
                write!(w, "phi")?;
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

        write!(w, ";")?;
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
