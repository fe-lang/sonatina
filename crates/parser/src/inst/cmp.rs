use ir::inst::cmp::*;

super::impl_inst_build! {Lt, has_lt, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Gt, has_gt, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Slt, has_slt, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Sgt, has_sgt, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Le, has_le, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Ge, has_ge, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Sle, has_sle, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Sge, has_sge, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Eq, has_eq, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Ne, has_ne, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {IsZero, has_is_zero, (lhs: ValueId)}
