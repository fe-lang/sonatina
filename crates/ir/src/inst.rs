use crate::Value;

pub trait Inst {
    fn args(&self) -> &[Value];
    fn args_mut(&mut self) -> &mut [Value];
    fn has_side_effect(&self) -> bool;
    fn as_str(&self) -> &'static str;
}
