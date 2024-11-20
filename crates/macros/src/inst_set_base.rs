use quote::quote;

use crate::convert_to_snake;

pub fn define_inst_set_base(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let def = syn::parse_macro_input! {input as TraitDefinition};
    match def.build() {
        Ok(ts) => quote! {#ts}.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

struct TraitDefinition {
    attrs: Vec<syn::Attribute>,
    insts: syn::punctuated::Punctuated<syn::Path, syn::Token!(,)>,
}

impl TraitDefinition {
    fn build(self) -> syn::Result<proc_macro2::TokenStream> {
        let trait_def = self.define_trait();
        let impls = self.impl_registered();
        let macros = self.define_macros();

        Ok(quote! {
            #trait_def
            #impls
            #macros
        })
    }

    fn define_trait(&self) -> proc_macro2::TokenStream {
        let methods = self.insts.iter().map(|path| {
            let method_name = path_to_method_name(path);
            quote! {
                #[doc(hidden)]
                fn #method_name(&self) -> Option<&dyn crate::HasInst<#path>> { None }
            }
        });
        let attrs = &self.attrs;

        quote! {
            #(#attrs)*
            pub trait InstSetBase: crate::HasInst<crate::inst::control_flow::Phi> + crate::HasInst<crate::inst::control_flow::Jump> + Send + Sync {
                #(#methods)*

                fn phi(&self) -> &dyn crate::HasInst<crate::inst::control_flow::Phi> {
                    self.has_phi().unwrap()
                }

                fn jump(&self) -> &dyn crate::HasInst<crate::inst::control_flow::Jump> {
                    self.has_jump().unwrap()
                }
            }
        }
    }

    fn impl_registered(&self) -> proc_macro2::TokenStream {
        let impls = self.insts.iter().map(|path| {
            quote! {
                impl crate::inst::inst_set::sealed::Registered for #path {}
            }
        });

        quote! {
            #(#impls)*
        }
    }

    fn define_macros(&self) -> proc_macro2::TokenStream {
        // Define match_string_to_inst.
        let arms = self.insts.iter().map(|path| {
            quote! {
                s if s == $crate::inst::#path::inst_name() => {
                    $func::<$crate::inst::#path>($($args),*)
                }
            }
        });

        let match_string_to_inst = quote! {
            /// This macro matches a given string to a specific instruction type
            /// and invokes the provided function with the matched type as a generic argument.
            ///
            /// # Arguments
            ///
            /// * `$inst_str`: The string representing the instruction type name. This string is compared
            ///                against the instruction type's `inst_name()` function.
            /// * `$func`: The function to be invoked. It will be called with the matched instruction type
            ///            as a generic argument.
            /// * `$args`: The arguments passed to the function after it is matched to an instruction type.
            /// * `$fallback`: The fallback expression to execute when the string does not match any known
            ///                instruction type.
            ///
            /// # Example
            ///
            /// ```ignore
            /// fn process_instruction<T>(arg1: u32, arg2: u32) {
            ///     ...
            /// }
            ///
            /// match_string_to_inst!("add", process_instruction(arg1, arg2), {
            ///     // Fallback behavior if no match is found
            ///     println!("Instruction type not found");
            /// });
            /// ```
            ///
            /// In this example, if the string "add" matches the instruction type `Add`, the macro
            /// calls the `process_instruction` function with [`crate::inst::arith::Add`] as a generic parameter and passes
            /// the arguments `arg1` and `arg2`(i.e, `process_function::<crate::inst::arith::Add>(arg1, arg2)`).
            /// If the string does not match any known instruction,
            /// the fallback block will be executed.
            #[macro_export]
            macro_rules! match_string_to_inst {
                ($inst_str: expr, $func:ident($($args: expr),*), $fallback: expr) => {
                    match $inst_str{
                        #(#arms)*
                        _ => $fallback,
                    }
                };
            }
        };

        let (arms, arms_mut): (Vec<_>, Vec<_>) = self.insts.iter().map(|path| {
            (quote!{
                s if s == std::any::TypeId::of::<$crate::inst::#path>() => {
                    <&#path as $crate::prelude::InstDowncast>::map(isb, inst, |inst| inst as &dyn $prop)
                }
            },
            quote!{
                s if s == std::any::TypeId::of::<$crate::inst::#path>() => {
                    <&mut #path as $crate::prelude::InstDowncastMut>::map_mut(isb, inst, |inst| inst as &mut dyn $prop)
                }
            })}).unzip();

        let inst_downcast_from_all_insts = quote! {
            #[macro_export]
            /// Macro to implement downcasting for all instruction types to a specific trait that
            /// is defined as `inst_prop`.
            ///
            /// This macro is intended to be invoked from the `[inst_prop]` macro and.
            macro_rules! inst_downcast_from_all_insts {
                (&dyn $prop:path) => {
                    impl $crate::prelude::InstDowncast for &dyn $prop {
                        fn downcast(isb: &dyn $crate::prelude::InstSetBase, inst: &dyn $crate::prelude::Inst) -> Option<Self> {
                            match inst.type_id() {
                                #(#arms)*
                                _ => None

                            }
                        }
                    }
                };

                (&mut dyn $prop:path) => {
                    impl $crate::prelude::InstDowncastMut for &mut dyn $prop {
                        fn downcast_mut(isb: &dyn $crate::prelude::InstSetBase, inst: &mut dyn $crate::prelude::Inst) -> Option<Self> {
                            match inst.type_id() {
                                #(#arms_mut)*
                                _ => None

                            }
                        }
                    }
                };
            }

        };

        let apply = self.insts.iter().map(|path| {
            quote! {
                $macro_to_apply!{ $crate::inst::#path }
            }
        });

        let apply_macro_to_all_insts = quote! {
            #[macro_export]
            /// Macro to apply a given macro to all types that implement the `Inst` trait.
            ///
            /// This macro applies a user-specified macro (`$macro_to_apply`) to all types that implement
            /// the `Inst` trait. The user macro will be invoked for each type in the set of `Inst`-implementing types.
            ///
            /// The macro expands a list of types, applying the provided macro to each one.
            ///
            /// # Arguments
            ///
            /// * `$macro_to_apply`: The macro that will be applied to each type implementing `Inst`.
            ///
            /// # Examples
            ///
            /// ```ignore
            /// apply_macro_to_all_insts!(my_macro);
            /// ```
            /// In this example, `my_macro` will be invoked for each type that implements the `Inst` trait.
            #[macro_export]
            macro_rules! apply_macro_to_all_insts {
                ($macro_to_apply:ident) => {
                    #(#apply)*
                }
            }
        };

        quote! {
            #match_string_to_inst
            #inst_downcast_from_all_insts
            #apply_macro_to_all_insts
        }
    }
}

impl syn::parse::Parse for TraitDefinition {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let attrs = input.call(syn::Attribute::parse_outer)?;
        input.parse::<syn::Token![trait]>()?;
        let ident = input.parse::<syn::Ident>()?;
        if ident != "InstSetBase" {
            return Err(syn::Error::new_spanned(
                ident,
                "the trait name must be `InstSetBase`",
            ));
        }
        let content;
        syn::braced!(content in input);

        let insts =
            syn::punctuated::Punctuated::<syn::Path, syn::Token!(,)>::parse_terminated(&content)?;

        Ok(Self { attrs, insts })
    }
}

/// convert path to the inst struct to `has_inst` method name.
/// e.g., `foo::Add` => `has_add`
pub(super) fn path_to_method_name(p: &syn::Path) -> syn::Ident {
    let ident = &p.segments.last().as_ref().unwrap().ident;
    ty_name_to_method_name(ident)
}

pub(super) fn ty_name_to_method_name(ident: &syn::Ident) -> syn::Ident {
    let s_ident = convert_to_snake(&ident.to_string());
    quote::format_ident!("has_{s_ident}")
}
