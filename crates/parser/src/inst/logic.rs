use ir::inst::logic::*;

super::impl_inst_build! {Not, has_not, (arg: ValueId)}
super::impl_inst_build! {And, has_and, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Or, has_or, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Xor, has_xor, (lhs: ValueId, rhs: ValueId)}
