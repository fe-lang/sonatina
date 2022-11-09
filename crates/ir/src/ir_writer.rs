use std::io;

use crate::{
    module::ModuleCtx,
    types::{CompoundType, CompoundTypeData, StructData},
    DataLocationKind, GlobalVariableData, Module,
};

use super::{Block, Function, Insn, InsnData, Type, Value};

pub struct ModuleWriter<'a> {
    module: &'a Module,
}

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
            let mut func_writer = FuncWriter::new(func);
            func_writer.write(&mut w)?;
            writeln!(w)?;
        }

        Ok(())
    }
}

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
        self.func.sig.ret_ty().ir_write(self.ctx(), &mut w)?;

        self.enter(&mut w)?;
        for block in self.func.layout.iter_block() {
            self.write_block_with_insn(block, &mut w)?;
            self.newline(&mut w)?;
            self.newline(&mut w)?;
        }
        self.leave();

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
    fn write(&self, writer: &mut FuncWriter, w: &mut impl io::Write) -> io::Result<()>;
}

impl IrWrite for Value {
    fn write(&self, writer: &mut FuncWriter, w: &mut impl io::Write) -> io::Result<()> {
        let value = writer.func.dfg.resolve_alias(*self);
        if let Some(imm) = writer.func.dfg.value_imm(value) {
            write!(w, "{}.", imm)?;
            let ty = writer.func.dfg.value_ty(value);
            ty.ir_write(writer.ctx(), w)
        } else if let Some(gv) = writer.func.dfg.value_gv(value) {
            writer
                .ctx()
                .with_gv_store(|s| write!(w, "%{}", s.gv_data(gv).symbol))
        } else {
            write!(w, "v{}", value.0)
        }
    }
}

impl GlobalVariableData {
    fn ir_write(&self, ctx: &ModuleCtx, w: &mut impl io::Write) -> io::Result<()> {
        let const_ = if self.is_const { " const" } else { "" };
        write! {w, "gv{const_} {} %{}: ", self.linkage, self.symbol}?;
        self.ty.ir_write(ctx, w)?;

        if let Some(data) = &self.data {
            write!(w, " = {}", data)
        } else {
            Ok(())
        }
    }
}

impl IrWrite for Block {
    fn write(&self, _: &mut FuncWriter, w: &mut impl io::Write) -> io::Result<()> {
        w.write_fmt(format_args!("block{}", self.0))
    }
}

impl Type {
    fn ir_write(&self, ctx: &ModuleCtx, w: &mut impl io::Write) -> io::Result<()> {
        match self {
            Self::I1 => write!(w, "i1"),
            Self::I8 => write!(w, "i8"),
            Self::I16 => write!(w, "i16"),
            Self::I32 => write!(w, "i32"),
            Self::I64 => write!(w, "i64"),
            Self::I128 => write!(w, "i128"),
            Self::I256 => write!(w, "i256"),
            Self::Void => write!(w, "void"),
            Self::Compound(compound) => compound.ir_write(ctx, w),
        }
    }
}

impl CompoundType {
    fn ir_write(&self, ctx: &ModuleCtx, w: &mut impl io::Write) -> io::Result<()> {
        let comp_data = ctx.with_ty_store(|s| s.resolve_compound(*self).clone());

        match comp_data {
            CompoundTypeData::Array { elem, len } => {
                write!(w, "[")?;
                elem.ir_write(ctx, &mut *w)?;
                write!(w, "; {}]", len)
            }
            CompoundTypeData::Ptr(elem) => {
                write!(w, "*")?;
                elem.ir_write(ctx, w)
            }
            CompoundTypeData::Struct(def) => {
                write!(w, "%{}", def.name)
            }
        }
    }
}

impl StructData {
    fn ir_write(&self, ctx: &ModuleCtx, w: &mut impl io::Write) -> io::Result<()> {
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
            write!(w, "}}>")
        } else {
            write!(w, "}}")
        }
    }
}

impl IrWrite for Insn {
    fn write(&self, writer: &mut FuncWriter, w: &mut impl io::Write) -> io::Result<()> {
        use InsnData::*;

        writer.indent(&mut *w)?;
        if let Some(insn_result) = writer.func.dfg.insn_result(*self) {
            insn_result.write(writer, &mut *w)?;
            w.write_all(b".")?;
            let ty = writer.func.dfg.value_ty(insn_result);
            ty.ir_write(writer.ctx(), &mut *w)?;
            w.write_all(b" = ")?;
        }

        let insn_data = writer.func.dfg.insn_data(*self);
        match insn_data {
            Unary { code, args } => {
                write!(w, "{}", code)?;
                writer.space(&mut *w)?;
                writer.write_insn_args(args, &mut *w)?;
            }

            Binary { code, args } => {
                write!(w, "{}", code)?;
                writer.space(&mut *w)?;
                writer.write_insn_args(args, &mut *w)?;
            }

            Cast { code, args, .. } => {
                write!(w, "{}", code)?;
                writer.space(&mut *w)?;
                writer.write_insn_args(args, &mut *w)?;
            }

            Load { args, loc } => {
                write!(w, "load")?;
                writer.space(&mut *w)?;
                match loc {
                    DataLocationKind::Memory => write!(w, "@memory")?,
                    DataLocationKind::Storage => write!(w, "@storage")?,
                }
                writer.space(&mut *w)?;
                writer.write_insn_args(args, &mut *w)?;
            }

            Store { args, loc } => {
                write!(w, "store")?;
                writer.space(&mut *w)?;
                match loc {
                    DataLocationKind::Memory => write!(w, "@memory")?,
                    DataLocationKind::Storage => write!(w, "@storage")?,
                }
                writer.space(&mut *w)?;
                writer.write_insn_args(args, &mut *w)?;
            }

            Call { func, args, .. } => {
                write!(w, "call")?;
                writer.space(&mut *w)?;
                write!(w, "%{}", writer.func.callees[func].name())?;
                writer.space(&mut *w)?;
                writer.write_insn_args(args, &mut *w)?;
            }

            Jump { code, dests } => {
                write!(w, "{}", code)?;
                writer.space(&mut *w)?;
                writer.write_iter_with_delim(dests.iter(), " ", &mut *w)?;
            }

            Branch { args, dests } => {
                write!(w, "br")?;
                writer.space(&mut *w)?;
                writer.write_insn_args(args, &mut *w)?;
                writer.space(&mut *w)?;
                writer.write_iter_with_delim(dests.iter(), " ", &mut *w)?;
            }

            BrTable {
                args,
                default,
                table,
            } => {
                write!(w, "br_table")?;
                writer.space(&mut *w)?;
                args[0].write(writer, &mut *w)?;
                writer.space(&mut *w)?;
                if let Some(default) = default {
                    default.write(writer, &mut *w)?;
                } else {
                    write!(w, "undef")?;
                }
                writer.space(&mut *w)?;

                let mut table_args = vec![];
                for (value, block) in args[1..].iter().zip(table.iter()) {
                    let mut arg = vec![b'('];
                    value.write(writer, &mut arg)?;
                    writer.space(&mut arg)?;
                    block.write(writer, &mut arg)?;
                    arg.push(b')');
                    table_args.push(arg);
                }

                writer.write_iter_with_delim(table_args.iter(), " ", &mut *w)?;
            }

            Alloca { ty } => {
                write!(w, "alloca")?;
                writer.space(&mut *w)?;
                ty.ir_write(writer.ctx(), &mut *w)?;
            }

            Return { args } => {
                write!(w, "return")?;
                if let Some(arg) = args {
                    writer.space(&mut *w)?;
                    arg.write(writer, &mut *w)?;
                }
            }

            Gep { args } => {
                write!(w, "gep")?;
                writer.space(&mut *w)?;
                writer.write_insn_args(args, &mut *w)?;
            }

            Phi { values, blocks, .. } => {
                write!(w, "phi")?;
                writer.space(&mut *w)?;
                let mut args = vec![];
                for (value, block) in values.iter().zip(blocks.iter()) {
                    let mut arg = vec![b'('];
                    value.write(writer, &mut arg)?;
                    writer.space(&mut arg)?;
                    block.write(writer, &mut arg)?;
                    arg.push(b')');
                    args.push(arg);
                }

                writer.write_iter_with_delim(args.iter(), " ", &mut *w)?;
            }
        }

        write!(w, ";")?;
        Ok(())
    }
}
#[derive(Clone)]
struct ValueWithTy(Value);

impl IrWrite for ValueWithTy {
    fn write(&self, f: &mut FuncWriter, w: &mut impl io::Write) -> io::Result<()> {
        let ty = f.func.dfg.value_ty(self.0);
        self.0.write(f, &mut *w)?;
        w.write_all(b".")?;
        ty.ir_write(f.ctx(), w)
    }
}

impl<T> IrWrite for &T
where
    T: IrWrite,
{
    fn write(&self, f: &mut FuncWriter, w: &mut impl io::Write) -> io::Result<()> {
        (*self).write(f, w)
    }
}

impl IrWrite for Vec<u8> {
    fn write(&self, _: &mut FuncWriter, w: &mut impl io::Write) -> io::Result<()> {
        w.write_all(self)
    }
}
