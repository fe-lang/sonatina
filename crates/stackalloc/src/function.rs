pub trait Function {
    fn num_insts(&self) -> u32;
    fn num_blocks(&self) -> u32;
}
