use ir::inst::arith::*;

super::impl_inst_build! {Neg, (arg: ValueId)}
super::impl_inst_build! {Add, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Mul, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Sub, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Sdiv, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Udiv, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Umod, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Smod, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Shl, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Shr, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Sar, (lhs: ValueId, rhs: ValueId)}
