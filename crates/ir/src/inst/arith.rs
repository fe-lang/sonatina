use macros::Inst;

use crate::{impl_display_with_func, ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Neg {
    #[inst(value)]
    arg: ValueId,
}
impl_display_with_func!(Neg);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Add {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(Add);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Mul {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(Mul);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sub {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(Sub);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct Sdiv {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(Sdiv);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct Udiv {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(Udiv);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct Umod {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(Umod);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct Smod {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(Smod);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Shl {
    #[inst(value)]
    bits: ValueId,
    #[inst(value)]
    value: ValueId,
}
impl_display_with_func!(Shl);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Shr {
    #[inst(value)]
    bits: ValueId,
    #[inst(value)]
    value: ValueId,
}
impl_display_with_func!(Shr);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sar {
    #[inst(value)]
    bits: ValueId,
    #[inst(value)]
    value: ValueId,
}
impl_display_with_func!(Sar);
// impl IrWrite for Insn {
//     fn write(&self, writer: &mut FuncWriter, w: &mut impl io::Write) -> io::Result<()> {
//         use InsnData::*;
//
//         writer.indent(&mut *w)?;
//         if let Some(insn_result) = writer.func.dfg.insn_result(*self) {
//             insn_result.write(writer, &mut *w)?;
//             w.write_all(b".")?;
//             let ty = writer.func.dfg.value_ty(insn_result);
//             ty.ir_write(writer.ctx(), &mut *w)?;
//             w.write_all(b" = ")?;
//         }
//
//         let insn_data = writer.func.dfg.insn_data(*self);
//         match insn_data {
//             Unary { code, args } => {
//                 write!(w, "{}", code)?;
//                 writer.space(&mut *w)?;
//                 writer.write_insn_args(args, &mut *w)?;
//             }
//
//             Binary { code, args } => {
//                 write!(w, "{}", code)?;
//                 writer.space(&mut *w)?;
//                 writer.write_insn_args(args, &mut *w)?;
//             }
//
//             Cast { code, args, .. } => {
//                 write!(w, "{}", code)?;
//                 writer.space(&mut *w)?;
//                 writer.write_insn_args(args, &mut *w)?;
//             }
//
//             Load { args, loc } => {
//                 write!(w, "load")?;
//                 writer.space(&mut *w)?;
//                 match loc {
//                     DataLocationKind::Memory => write!(w, "@memory")?,
//                     DataLocationKind::Storage => write!(w, "@storage")?,
//                 }
//                 writer.space(&mut *w)?;
//                 writer.write_insn_args(args, &mut *w)?;
//             }
//
//             Store { args, loc } => {
//                 write!(w, "store")?;
//                 writer.space(&mut *w)?;
//                 match loc {
//                     DataLocationKind::Memory => write!(w, "@memory")?,
//                     DataLocationKind::Storage => write!(w, "@storage")?,
//                 }
//                 writer.space(&mut *w)?;
//                 writer.write_insn_args(args, &mut *w)?;
//             }
//
//             Call { func, args, .. } => {
//                 write!(w, "call")?;
//                 writer.space(&mut *w)?;
//                 write!(w, "%{}", writer.func.callees[func].name())?;
//                 writer.space(&mut *w)?;
//                 writer.write_insn_args(args, &mut *w)?;
//             }
//
//             Jump { dests } => {
//                 write!(w, "jump")?;
//                 writer.space(&mut *w)?;
//                 writer.write_iter_with_delim(dests.iter(), " ", &mut *w)?;
//             }
//
//             Branch { args, dests } => {
//                 write!(w, "br")?;
//                 writer.space(&mut *w)?;
//                 writer.write_insn_args(args, &mut *w)?;
//                 writer.space(&mut *w)?;
//                 writer.write_iter_with_delim(dests.iter(), " ", &mut *w)?;
//             }
//
//             BrTable {
//                 args,
//                 default,
//                 table,
//             } => {
//                 write!(w, "br_table")?;
//                 writer.space(&mut *w)?;
//                 args[0].write(writer, &mut *w)?;
//                 writer.space(&mut *w)?;
//                 if let Some(default) = default {
//                     default.write(writer, &mut *w)?;
//                 } else {
//                     write!(w, "undef")?;
//                 }
//                 writer.space(&mut *w)?;
//
//                 let mut table_args = vec![];
//                 for (value, block) in args[1..].iter().zip(table.iter()) {
//                     let mut arg = vec![b'('];
//                     value.write(writer, &mut arg)?;
//                     writer.space(&mut arg)?;
//                     block.write(writer, &mut arg)?;
//                     arg.push(b')');
//                     table_args.push(arg);
//                 }
//
//                 writer.write_iter_with_delim(table_args.iter(), " ", &mut *w)?;
//             }
//
//             Alloca { ty } => {
//                 write!(w, "alloca")?;
//                 writer.space(&mut *w)?;
//                 ty.ir_write(writer.ctx(), &mut *w)?;
//             }
//
//             Return { args } => {
//                 write!(w, "return")?;
//                 if let Some(arg) = args {
//                     writer.space(&mut *w)?;
//                     arg.write(writer, &mut *w)?;
//                 }
//             }
//
//             Gep { args } => {
//                 write!(w, "gep")?;
//                 writer.space(&mut *w)?;
//                 writer.write_insn_args(args, &mut *w)?;
//             }
//
//             Phi { values, blocks, .. } => {
//                 write!(w, "phi")?;
//                 writer.space(&mut *w)?;
//                 let mut args = vec![];
//                 for (value, block) in values.iter().zip(blocks.iter()) {
//                     let mut arg = vec![b'('];
//                     value.write(writer, &mut arg)?;
//                     writer.space(&mut arg)?;
//                     block.write(writer, &mut arg)?;
//                     arg.push(b')');
//                     args.push(arg);
//                 }
//
//                 writer.write_iter_with_delim(args.iter(), " ", &mut *w)?;
//             }
//         }
//
//         write!(w, ";")?;
//         Ok(())
//     }
// }
