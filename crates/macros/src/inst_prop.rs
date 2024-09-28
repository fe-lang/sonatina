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
    fn new(arg: syn::Meta, item_trait: syn::ItemTrait) -> syn::Result<Self> {
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

    fn build(mut self) -> syn::Result<proc_macro2::TokenStream> {
        let sealed_trait = self.impl_sealed_trait();
        let prop_trait = self.define_prop_trait()?;
        let subset_def = self.define_subset();
        let subset_impl = self.define_subset_impl();

        Ok(quote! {
            #sealed_trait
            #prop_trait
            #subset_def
            #subset_impl
        })
    }

    fn impl_sealed_trait(&self) -> proc_macro2::TokenStream {
        let mod_name = self.sealed_module_name();
        let sealed_trait_name = self.sealed_trait_name();
        let impl_for_members = self.members.iter().map(|path| {
            quote! {
                impl #sealed_trait_name for #path {}
            }
        });

        let subset_name = &self.subset_name;
        let lt = syn::Lifetime::new("'i", proc_macro2::Span::call_site());
        let impl_for_susbet = quote! {
            impl<#lt> #sealed_trait_name for #subset_name<#lt> {}
        };

        quote! {
            mod #mod_name {
                use super::*;

                #[doc(hidden)]
                pub trait #sealed_trait_name {}
                #(#impl_for_members)*
                #impl_for_susbet
            }
        }
    }

    fn define_prop_trait(&mut self) -> syn::Result<proc_macro2::TokenStream> {
        self.item_trait.items.retain(|item| {
            let syn::TraitItem::Type(ty) = item else {
                return true;
            };
            ty.ident != "Members"
        });
        if let Some(item) = self
            .item_trait
            .items
            .iter()
            .find(|item| !matches!(item, syn::TraitItem::Fn(_)))
        {
            return Err(syn::Error::new_spanned(
                item,
                "only trait method is allowed",
            ));
        }

        let mut sealed_trait = syn::Path::from(self.sealed_module_name());
        sealed_trait.segments.push(self.sealed_trait_name().into());
        let sealed_trait_bound = syn::TraitBound {
            paren_token: None,
            modifier: syn::TraitBoundModifier::None,
            lifetimes: None,
            path: sealed_trait,
        };

        self.item_trait
            .supertraits
            .push(syn::TypeParamBound::Trait(sealed_trait_bound));

        let item_trait = &self.item_trait;
        Ok(quote! {
            #item_trait
        })
    }

    fn define_subset(&self) -> proc_macro2::TokenStream {
        let lt = syn::Lifetime::new("'i", proc_macro2::Span::call_site());
        let vis = &self.item_trait.vis;

        let variants = self.members.iter().map(|p| {
            let variant_name = subset_variant_name_from_path(p);
            quote! { #variant_name(&#lt #p) }
        });

        let constraints = self.members.iter().map(|p| {
            let trait_name = &self.item_trait.ident;
            quote! { #p: #trait_name }
        });
        let subset_name = &self.subset_name;

        quote! {
            #vis enum #subset_name<#lt>
            where #(#constraints,)*
             {
                 #(#variants),*
             }
        }
    }

    fn define_subset_impl(&self) -> proc_macro2::TokenStream {
        let subset_name = &self.subset_name;
        let arms = self.members.iter().map(|p| {
            let variant_name = subset_variant_name_from_path(p);
            quote!(
                id if id == std::any::TypeId::of::<#p>() => {
                    <&#p as crate::prelude::InstDowncast>::map(isb, inst, Self::#variant_name)
                }
            )
        });

        let lt = syn::Lifetime::new("'i", proc_macro2::Span::call_site());
        let inst_downcast_impl = quote! {
            impl<#lt> crate::prelude::InstDowncast for #subset_name<#lt> {
                fn downcast(isb: &dyn crate::prelude::InstSetBase, inst: &dyn crate::Inst) -> Option<Self> {
                    match inst.type_id() {
                        #(#arms)*
                        _ => None

                    }
                }
           }
        };

        let method_impls = self.item_trait.items.iter().map(|item| {
            let syn::TraitItem::Fn(f) = item else {
                unreachable!();
            };
            let sig = &f.sig;
            let func_name = &sig.ident;
            let args: Vec<_> = sig
                .inputs
                .iter()
                .filter_map(|input| {
                    if let syn::FnArg::Typed(pat_ty) = input {
                        Some(&pat_ty.pat)
                    } else {
                        None
                    }
                })
                .collect();

            let arms = self.members.iter().map(|p| {
                let variant_name = subset_variant_name_from_path(p);
                quote!(
                    Self::#variant_name(inner) => inner.#func_name(#(#args,)*)
                )
            });

            quote! {
                $sig {
                    match self {
                        #(#arms,)*


                    }
                }
            }
        });

        let trait_name = &self.item_trait.ident;
        let trait_impl = quote! {
            impl<#lt> #trait_name for #subset_name<#lt> {
                #(#method_impls)*
            }
        };

        quote! {
            #inst_downcast_impl
            #trait_impl
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
