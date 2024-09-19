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

        Ok(quote! {
            #trait_def
            #impls
        })
    }

    fn define_trait(&self) -> proc_macro2::TokenStream {
        let methods = self.insts.iter().map(|path| {
            let method_name = path_to_method_name(path);
            quote! {
                fn #method_name(&self) -> Option<&dyn crate::HasInst<#path>> { None }
            }
        });
        let attrs = &self.attrs;

        quote! {
            #(#attrs)*
            pub trait InstSetBase: crate::HasInst<crate::inst::control_flow::Phi>  {
                #(#methods)*

                fn upcast(&self) -> &dyn crate::HasInst<crate::inst::control_flow::Phi> {
                    self.has_phi().unwrap()
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
