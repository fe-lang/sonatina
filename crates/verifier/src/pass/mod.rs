use cranelift_entity::entity_impl;

#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub struct PassRef(pub u32);
entity_impl!(PassRef, "pass");
