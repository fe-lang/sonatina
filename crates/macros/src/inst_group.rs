use quote::quote;

use crate::convert_to_snake;

pub fn define_dyn_inst_group(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let def = syn::parse_macro_input! {input as TraitDefinition};
    match def.build() {
        Ok(ts) => quote! {#ts}.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

struct TraitDefinition(syn::punctuated::Punctuated<syn::Path, syn::Token!(,)>);

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
        let methods = self.0.iter().map(|path| {
            let method_name = path_to_method_name(path);
            quote! {
                fn #method_name(&self) -> Option<&dyn crate::HasInst<#path>> { None }
            }
        });
        quote! {
            pub trait DynInstGroup {
                #(#methods)*
            }
        }
    }

    fn impl_registered(&self) -> proc_macro2::TokenStream {
        let impls = self.0.iter().map(|path| {
            quote! {
                impl crate::inst::inst_group::sealed::Registered for #path {}
            }
        });

        quote! {
            #(#impls)*
        }
    }
}

impl syn::parse::Parse for TraitDefinition {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let insts =
            syn::punctuated::Punctuated::<syn::Path, syn::Token!(,)>::parse_terminated(input)?;
        Ok(Self(insts))
    }
}

fn path_to_method_name(p: &syn::Path) -> syn::Ident {
    let ident = &p.segments.last().as_ref().unwrap().ident;
    let s_ident = convert_to_snake(&ident.to_string());
    quote::format_ident!("has_{s_ident}")
}
