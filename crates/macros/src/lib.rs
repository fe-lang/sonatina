mod inst;
mod inst_set;
mod inst_set_base;

#[proc_macro_derive(Inst, attributes(inst))]
pub fn derive_inst(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    inst::derive_inst(item)
}

#[proc_macro]
pub fn define_inst_set_base(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    inst_set_base::define_inst_set_base(input)
}

#[proc_macro_attribute]
pub fn inst_set(
    attr: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    inst_set::define_inst_set(attr, input)
}

fn convert_to_snake(s: &str) -> String {
    let mut res = String::new();
    let mut is_upper = false;
    for (i, c) in s.chars().enumerate() {
        if c.is_uppercase() {
            if !is_upper && i != 0 {
                res.push('_');
            }
            is_upper = true;
        } else {
            is_upper = false;
        }

        res.push(c.to_ascii_lowercase());
    }

    res
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_convert_to_snake() {
        let snake = "foo_bar_baz";
        assert_eq!(convert_to_snake("FooBarBaz"), snake);
        assert_eq!(convert_to_snake("FOoBarBaz"), snake);
        assert_eq!(convert_to_snake("FOoBArBAZ"), snake);
    }

    #[test]
    fn test_convert_to_snake2() {
        let snake = "foo";
        assert_eq!(convert_to_snake("Foo"), snake);
    }
}
