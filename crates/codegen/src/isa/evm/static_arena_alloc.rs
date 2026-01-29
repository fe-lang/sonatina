use cranelift_entity::entity_impl;

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct StackObjId(u32);
entity_impl!(StackObjId);
