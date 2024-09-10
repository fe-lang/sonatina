use quote::quote;

use crate::inst_set_base;

pub fn define_inst_set(
    _attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let item_struct = syn::parse_macro_input!(item as syn::ItemStruct);
    match InstSet::new(item_struct).and_then(InstSet::build) {
        Ok(impls) => quote! {
            #impls
        }
        .into(),

        Err(e) => e.to_compile_error().into(),
    }
}

struct InstSet {
    vis: syn::Visibility,
    ident: syn::Ident,
    insts: Vec<syn::Path>,
}

impl InstSet {
    fn new(s: syn::ItemStruct) -> syn::Result<Self> {
        let ident = s.ident;
        let vis = s.vis;
        let insts = Self::parse_insts(&s.fields)?;
        Ok(Self { vis, ident, insts })
    }

    fn build(self) -> syn::Result<proc_macro2::TokenStream> {
        let inst_set = self.define_inst_set();
        let has_inst_impls = self.impl_has_inst();
        let inst_set_base_impl = self.impl_inst_set_base();
        Ok(quote! {
            #inst_set
            #has_inst_impls
            #inst_set_base_impl
        })
    }

    fn parse_insts(fields: &syn::Fields) -> syn::Result<Vec<syn::Path>> {
        let syn::Fields::Unnamed(fields) = fields else {
            return Err(syn::Error::new_spanned(
                fields,
                "only tuple struct is allowed",
            ));
        };

        let mut insts = Vec::with_capacity(fields.unnamed.len());
        for f in fields.unnamed.iter() {
            let syn::Type::Path(p) = &f.ty else {
                return Err(syn::Error::new_spanned(
                    f,
                    "expected path to inst type here",
                ));
            };
            insts.push(p.path.clone());
        }

        Ok(insts)
    }

    fn define_inst_set(&self) -> proc_macro2::TokenStream {
        let ident = &self.ident;
        let vis = &self.vis;
        quote! {
            #vis struct #ident {}
        }
    }

    fn impl_has_inst(&self) -> proc_macro2::TokenStream {
        let ident = &self.ident;
        let impls = self.insts.iter().map(|p| {
            quote! {
                impl crate::HasInst<#p> for #ident {}
            }
        });

        quote! {
            #(#impls)*
        }
    }

    fn impl_inst_set_base(&self) -> proc_macro2::TokenStream {
        let methods = self.insts.iter().map(|p| {
            let method_name = inst_set_base::path_to_method_name(p);
            quote! {
                fn #method_name(&self) -> Option<&dyn crate::HasInst<#p>> {
                    Some(self)
                }
            }
        });

        let ident = &self.ident;
        quote! {
            impl crate::InstSetBase for #ident {
                #(#methods)*
            }
        }
    }
}
