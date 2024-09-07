use crate::Value;

pub trait Inst {
    fn args(&self) -> &[Value];
    fn args_mut(&mut self) -> &mut [Value];
    fn has_side_effect(&self) -> bool;
    fn as_str(&self) -> &'static str;
}

macro_rules! define_inst {
    ($(($purity:ident, $ty:ident, $name:literal, $arity:literal)),* $(,)?) => {
        $(
            define_inst!($purity, $ty, $name, $arity);
        )*
    };

    ($purity: ident, $ty: ident, $name:literal, $arity:literal) => {
        pub struct $ty {
            args: [Value; $arity],
        }

        impl Inst for $ty {
            fn args(&self) -> &[Value] {
                &self.args
            }

            fn args_mut(&mut self) -> &mut [Value] {
                &mut self.args
            }

            fn has_side_effect(&self) -> bool {
                define_inst!(has_side_effect_impl $purity)
            }

            fn as_str(&self) -> &'static str {
                $name
            }
        }
    };

   (has_side_effect_impl pure) => {
       true
   };

   (has_side_effect_impl non_pure) => {
       true
   };
}
