use ir::inst::cmp::*;

super::impl_inst_build! {Lt, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Gt, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Slt, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Sgt, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Le, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Ge, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Sle,  (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Sge,  (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Eq,  (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Ne,  (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {IsZero, (lhs: ValueId)}
