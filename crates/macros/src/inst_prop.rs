use quote::quote;

use crate::subset_variant_name_from_path;

pub fn define_inst_prop(
    attr: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let arg = syn::parse_macro_input!(attr as syn::Meta);
    let item_trait = syn::parse_macro_input!(input as syn::ItemTrait);

    match InstProp::new(arg, item_trait).and_then(InstProp::build) {
        Ok(impls) => quote! {
            #impls
        }
        .into(),
        Err(e) => e.to_compile_error().into(),
    }
}

struct InstProp {
    item_trait: syn::ItemTrait,
    members: Vec<syn::Path>,
    subset_name: syn::Ident,
}

impl InstProp {
    fn new(arg: syn::Meta, mut item_trait: syn::ItemTrait) -> syn::Result<Self> {
        const ERR_MSG: &str = "`type Members = (ty_1, ty_2, .., ty_n)` is required";
        let mut members_opt = None;
        for it in item_trait.items.iter() {
            if let syn::TraitItem::Type(assoc_ty) = it {
                if assoc_ty.ident != "Members" {
                    continue;
                }

                let Some((_, syn::Type::Tuple(tuple_ty))) = &assoc_ty.default else {
                    return Err(syn::Error::new_spanned(assoc_ty, ERR_MSG));
                };

                let mut members = Vec::with_capacity(tuple_ty.elems.len());
                for elem_ty in &tuple_ty.elems {
                    let syn::Type::Path(p) = elem_ty else {
                        return Err(syn::Error::new_spanned(elem_ty, "path is requried"));
                    };

                    members.push(p.path.clone());
                }

                if members_opt.replace(members).is_some() {
                    return Err(syn::Error::new_spanned(it, "`members` should be unique"));
                }
            }
        }

        let Some(members) = members_opt else {
            return Err(syn::Error::new(proc_macro2::Span::call_site(), ERR_MSG));
        };

        let subset_name = Self::parse_subset_name(arg)?;
        Ok(Self {
            item_trait,
            members,
            subset_name,
        })
    }

    fn build(self) -> syn::Result<proc_macro2::TokenStream> {
        let sealed_trait = self.impl_sealed_trait();
        let prop_trait = self.define_prop_trait();
        let subset_def = self.define_subset();
        //let subset_impl = self.define_subset_impl();

        Ok(quote! {
            #sealed_trait
            #prop_trait
            #subset_def
            //#subset_impl
        })
    }

    fn impl_sealed_trait(&self) -> proc_macro2::TokenStream {
        let mod_name = self.sealed_module_name();
        let sealed_trait_name = self.sealed_trait_name();
        let impls = self.members.iter().map(|path| {
            quote! {
                impl #sealed_trait_name for #path {}
            }
        });

        quote! {
            mod #mod_name {
                use super::*;

                pub trait #sealed_trait_name {}
                #(#impls)*

            }
        }
    }

    fn define_prop_trait(&self) -> proc_macro2::TokenStream {
        let mut item_trait = self.item_trait.clone();
        item_trait.items.retain(|item| {
            let syn::TraitItem::Type(ty) = item else {
                return true;
            };
            ty.ident != "Members"
        });

        let mut sealed_trait = syn::Path::from(self.sealed_module_name());
        sealed_trait.segments.push(self.sealed_trait_name().into());
        let sealed_trait_bound = syn::TraitBound {
            paren_token: None,
            modifier: syn::TraitBoundModifier::None,
            lifetimes: None,
            path: sealed_trait,
        };

        item_trait
            .supertraits
            .push(syn::TypeParamBound::Trait(sealed_trait_bound));

        quote! {
            #item_trait
        }
    }

    fn define_subset(&self) -> proc_macro2::TokenStream {
        let lt = syn::Lifetime::new("'i", proc_macro2::Span::call_site());
        let vis = &self.item_trait.vis;

        let variants = self.members.iter().map(|p| {
            let variant_name = subset_variant_name_from_path(p);
            quote! { #variant_name(&#lt mut #p) }
        });
        let subset_name = &self.subset_name;

        quote! {
             #vis enum #subset_name<#lt> {
                 #(#variants),*
             }
        }
    }

    fn sealed_module_name(&self) -> syn::Ident {
        let trait_name = &self.item_trait.ident;
        quote::format_ident! {"sealed_{trait_name}"}
    }

    fn sealed_trait_name(&self) -> syn::Ident {
        let trait_name = &self.item_trait.ident;
        quote::format_ident! {"Sealed{trait_name}"}
    }

    fn parse_subset_name(args: syn::Meta) -> syn::Result<syn::Ident> {
        let make_err = || {
            Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                "`#[inst_prop(Subset = \"{SubsetName}\")]` is required",
            ))
        };

        let syn::Meta::NameValue(name_value) = args else {
            return make_err();
        };

        let inst_kind_name = match (name_value.path.get_ident(), &name_value.value) {
            (Some(ident), syn::Expr::Lit(lit)) if ident == "Subset" => {
                if let syn::Lit::Str(s) = &lit.lit {
                    s
                } else {
                    return make_err();
                }
            }
            _ => return make_err(),
        };

        Ok(syn::Ident::new(
            &inst_kind_name.value(),
            proc_macro2::Span::call_site(),
        ))
    }
}
