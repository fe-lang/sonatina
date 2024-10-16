use ir::inst::logic::*;

super::impl_inst_build! {Not, (arg: ValueId)}
super::impl_inst_build! {And, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Or, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Xor, (lhs: ValueId, rhs: ValueId)}
