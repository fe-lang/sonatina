use ir::inst::arith::*;

super::impl_inst_build! {Neg, has_neg, (arg: ValueId)}
super::impl_inst_build! {Add, has_add, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Mul, has_mul, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Sub, has_sub, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Sdiv, has_sdiv, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Udiv, has_udiv, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Umod, has_umod, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Smod, has_smod, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Shl, has_shl, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Shr, has_shr, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Sar, has_sar, (lhs: ValueId, rhs: ValueId)}
