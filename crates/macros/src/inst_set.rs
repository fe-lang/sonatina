use quote::quote;

use crate::inst_set_base;

pub fn define_inst_set(
    _attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let attr_args = syn::parse_macro_input!(_attr as syn::AttributeArgs);
    let item_struct = syn::parse_macro_input!(item as syn::ItemStruct);

    match InstSet::new(attr_args, item_struct).and_then(InstSet::build) {
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
    inst_kind_name: syn::Ident,
}

impl InstSet {
    fn new(args: Vec<syn::NestedMeta>, s: syn::ItemStruct) -> syn::Result<Self> {
        let ident = s.ident;
        let vis = s.vis;
        let insts = Self::parse_insts(&s.fields)?;
        let inst_kind_name = Self::parse_inst_kind_name(&args)?;

        Ok(Self {
            vis,
            ident,
            insts,
            inst_kind_name,
        })
    }

    fn build(self) -> syn::Result<proc_macro2::TokenStream> {
        let inst_set = self.define_inst_set();
        let has_inst_impls = self.impl_has_inst();
        let inst_set_base_impl = self.impl_inst_set_base();

        let inst_kind = self.define_inst_kind();

        Ok(quote! {
            #inst_set
            #has_inst_impls
            #inst_set_base_impl
            #inst_kind
        })
    }

    fn parse_inst_kind_name(args: &[syn::NestedMeta]) -> syn::Result<syn::Ident> {
        let make_err = || {
            Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                "`#[inst_set(InstKind = \"{InstKindName}\")]` is required",
            ))
        };

        if args.len() != 1 {
            return make_err();
        }

        let syn::NestedMeta::Meta(syn::Meta::NameValue(name_value)) = &args[0] else {
            return make_err();
        };

        let inst_kind_name = match (name_value.path.get_ident(), &name_value.lit) {
            (Some(ident), syn::Lit::Str(s)) if ident == "InstKind" => s.value(),
            _ => return make_err(),
        };

        Ok(syn::Ident::new(
            &inst_kind_name,
            proc_macro2::Span::call_site(),
        ))
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

    fn define_inst_kind(&self) -> proc_macro2::TokenStream {
        let lt = syn::Lifetime::new("'i", proc_macro2::Span::call_site());

        let variants = self.insts.iter().map(|p| {
            let variant_name = p.segments.last().unwrap();
            quote! { #variant_name(&#lt #p) }
        });

        let variants_mut = self.insts.iter().map(|p| {
            let variant_name = p.segments.last().unwrap();
            quote! { #variant_name(&#lt mut #p) }
        });

        let inst_kind_name = &self.inst_kind_name;
        let inst_kind_mut_name = quote::format_ident!("{inst_kind_name}Mut");

        let vis = &self.vis;

        quote! {
             #vis enum #inst_kind_name<#lt> {
                 #(#variants),*
             }

             #vis enum #inst_kind_mut_name<#lt> {
                 #(#variants_mut),*
             }
        }
    }
}
