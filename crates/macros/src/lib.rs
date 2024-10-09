mod inst;
mod inst_prop;
mod inst_set;
mod inst_set_base;

/// A derive macro to define each instruction type.
/// This macro dervies the `Isnt` trait for the macro,
/// and implements a consructor and acccessors for each fields.
///
/// # Usage
/// ```rust, ignore
/// use sonatina_macros::Inst;
///
/// #[derive(Inst)]
/// #[inst(has_side_effect)]
/// struct MStore {
///     #[inst(value)]
///     lhs: Value,
///     #[inst(value)]
///     rhs: Value,
/// }
/// ```
///
/// # Arguments
/// - `has_side_effect`: Marks the instruction as having a side effect.
/// - `value`: Marks the field that contains value, the specified field must
///   implements `sonatina-ir::inst::ValueVisitable` trait.
///
/// # Usage
#[proc_macro_derive(Inst, attributes(inst))]
pub fn derive_inst(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    inst::derive_inst(item)
}

#[proc_macro]
pub fn define_inst_set_base(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    inst_set_base::define_inst_set_base(input)
}

/// A macro to define an instruction set that is specific to an target arch.
/// In sonatina, an InstructionSet is defined as a type that implements
/// `HasInst<{Inst}>` for all `{Inst}` it contains, and also implements
/// `InstSetBase` and `InstSetExt`. This macro automatically implements these
/// traits and modify the type definition to enable an effective cast of
/// instruction.
///
/// # Usage
/// ```rust, ignore
/// #[inst_set(InstKind = "TestInstKind")]
/// struct TestInstSet(Add, Sub);
/// ```
///
/// # Arguments
/// ##  InstKind = "TestInstKind"`
/// This arguments specifies an `enum` used in `InstSetExt::InstKind`. This enum
/// is also generated automatically. In the abobe example, the below enum is
/// generated, and can be obtained via `InstSetExt::resolve_inst` method.
/// ```rust, ignore
/// enum TestInstKind<'i> {
///     Add(&'i Add),
///     Sub(&'i Sub),
/// }
/// ```
#[proc_macro_attribute]
pub fn inst_set(
    attr: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    inst_set::define_inst_set(attr, input)
}

#[proc_macro_attribute]
pub fn inst_prop(
    attr: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    inst_prop::define_inst_prop(attr, input)
}

/// Converts a given string to snake case.
///
/// The function iterates through each character in the string. If the character
/// is uppercase, it checks if the previous character was also uppercase. If it
/// wasn't, it adds an underscore before the current character. It then converts
/// the character to lowercase and adds it to the result string. e.g.,
/// * `FooBar -> foo_bar`
/// * `FooBAR -> foo_bar`
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

fn subset_variant_name_from_path<'a>(p: &'a syn::Path) -> &'a syn::Ident {
    &p.segments.last().unwrap().ident
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
