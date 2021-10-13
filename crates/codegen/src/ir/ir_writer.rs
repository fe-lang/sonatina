use std::io;

use super::{Block, Function, Insn, InsnData, Type, Value};

pub struct FuncWriter<'a> {
    func: &'a Function,
}

impl<'a> FuncWriter<'a> {
    pub fn new(func: &'a Function) -> Self {
        Self { func }
    }

    pub fn write(&self, mut w: impl io::Write) -> io::Result<()> {
        w.write_fmt(format_args!("func %{}(", self.func.name))?;
        let sig = &self.func.sig;
        let mut args = sig.args.iter().peekable();
        while let Some(arg) = args.next() {
            self.write_type(arg, &mut w)?;
            if args.peek().is_some() {
                w.write_all(b", ")?;
            }
        }
        w.write_all(b") -> ")?;
        let mut rets = sig.rets.iter().peekable();
        while let Some(ret) = rets.next() {
            self.write_type(ret, &mut w)?;
            if rets.peek().is_some() {
                w.write_all(b", ")?;
            }
        }
        w.write_all(b":\n")?;

        for block in self.func.layout.iter_block() {
            w.write_all(b":\n")?;
            self.write_block_with_insn(block, &mut w)?;
        }
        Ok(())
    }

    fn write_value(&self, value: Value, mut w: impl io::Write) -> io::Result<()> {
        w.write_fmt(format_args!(
            "%v{}.{}",
            self.func.dfg.value_ty(value),
            value.index()
        ))
    }

    fn write_block_with_insn(&self, block: Block, mut w: impl io::Write) -> io::Result<()> {
        w.write_fmt(format_args!("block{}(", block.index()))?;

        let params = self.func.dfg.block_params(block).peekable();
        self.write_block(block, params, &mut w)?;
        w.write_all(b":\n")?;

        for insn in self.func.layout.iter_insn(block) {
            w.write_all(b"\t")?;
            self.write_insn(insn, &mut w)?;
            w.write_all(b"\n")?;
        }

        Ok(())
    }

    fn write_insn(&self, insn: Insn, mut w: impl io::Write) -> io::Result<()> {
        use InsnData::*;

        let ret_val = self.func.dfg.insn_result(insn);
        if let Some(ret_val) = ret_val {
            self.write_value(ret_val, &mut w)?;
            w.write_all(b" = ")?;
        }

        let insn_data = self.func.dfg.insn_data(insn);
        match insn_data {
            Immediate { code } => w.write_all(code.to_string().as_bytes())?,
            Binary { code, args } => {
                w.write_fmt(format_args!("{} ", code.as_str()))?;
                self.write_insn_args(args, &mut w)?;
            }
            Cast { code, args, .. } => {
                w.write_fmt(format_args!("{} ", code.as_str()))?;
                self.write_insn_args(args, &mut w)?;
            }
            Load { args, .. } => {
                w.write_all(b"load ")?;
                self.write_insn_args(args, &mut w)?;
            }
            Store { args } => {
                w.write_all(b"store ")?;
                self.write_insn_args(args, &mut w)?;
            }
            Jump { code, dest, params } => {
                w.write_fmt(format_args!("{} ", code.as_str()))?;
                self.write_block(*dest, params.iter(), &mut w)?;
            }
            Branch {
                code,
                args,
                dest,
                params,
            } => {
                w.write_fmt(format_args!("{} ", code.as_str()))?;
                self.write_insn_args(args, &mut w)?;
                w.write_all(b" ")?;
                self.write_block(*dest, params.iter(), &mut w)?;
            }
        }

        Ok(())
    }

    fn write_block<'b>(
        &self,
        block: Block,
        params: impl Iterator<Item = &'b Value>,
        mut w: impl io::Write,
    ) -> io::Result<()> {
        w.write_fmt(format_args!("block{}(", block.index()))?;

        let mut params = params.peekable();
        while let Some(param) = params.next() {
            self.write_value(*param, &mut w)?;
            if params.peek().is_some() {
                w.write_all(b", ")?;
            }
        }
        w.write_all(b")")
    }

    fn write_insn_args(&self, args: &[Value], mut w: impl io::Write) -> io::Result<()> {
        for arg in args {
            w.write_all(b" ")?;
            self.write_value(*arg, &mut w)?;
        }

        Ok(())
    }

    fn write_type(&self, ty: &Type, mut w: impl io::Write) -> io::Result<()> {
        write!(w, "{}", ty)
    }
}
