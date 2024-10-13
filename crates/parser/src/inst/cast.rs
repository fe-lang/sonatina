use ir::inst::cast::*;

super::impl_inst_build! {Sext, has_sext, (from: ValueId, ty: Type)}
super::impl_inst_build! {Zext, has_zext, (from: ValueId, ty: Type)}
super::impl_inst_build! {Trunc, has_trunc, (from: ValueId, ty: Type)}
super::impl_inst_build! {Bitcast, has_bitcast, (from: ValueId, ty: Type)}
super::impl_inst_build! {IntToPtr, has_int_to_ptr, (from: ValueId, ty: Type)}
