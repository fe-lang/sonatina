use ir::inst::logic::*;

super::impl_inst_build! {Not, (arg: ValueId)}
super::impl_inst_build! {And, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Or, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Xor, (lhs: ValueId, rhs: ValueId)}
super::impl_inst_build! {Select, (cond: ValueId, then_value: ValueId, else_value: ValueId)}
super::impl_inst_build! {Bswap, (arg: ValueId)}
super::impl_inst_build! {Clz, (arg: ValueId)}
super::impl_inst_build! {Ctz, (arg: ValueId)}
