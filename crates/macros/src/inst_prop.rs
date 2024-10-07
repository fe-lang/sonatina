use quote::quote;

pub fn define_inst_prop(
    _attr: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let item_trait = syn::parse_macro_input!(input as syn::ItemTrait);

    match InstProp::new(item_trait).and_then(InstProp::build) {
        Ok(impls) => quote! {
            #impls
        }
        .into(),
        Err(e) => e.to_compile_error().into(),
    }
}

struct InstProp {
    item_trait: syn::ItemTrait,
    config: PropConfig,
}

impl InstProp {
    fn new(item_trait: syn::ItemTrait) -> syn::Result<Self> {
        let (item_trait, config) = Self::check_trait_items(item_trait)?;

        Ok(Self { item_trait, config })
    }

    fn check_trait_items(
        mut item_trait: syn::ItemTrait,
    ) -> syn::Result<(syn::ItemTrait, PropConfig)> {
        let mut members_opt = None;
        const MISSING_MEMBERS: &str = "`type Members = (ty_1, ty_2, .., ty_n)` is required";

        for it in item_trait.items.iter() {
            if let syn::TraitItem::Type(assoc_ty) = it {
                if assoc_ty.ident != "Members" {
                    continue;
                }

                let Some((_, syn::Type::Tuple(tuple_ty))) = &assoc_ty.default else {
                    return Err(syn::Error::new_spanned(assoc_ty, MISSING_MEMBERS));
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
            return Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                MISSING_MEMBERS,
            ));
        };

        item_trait.items.retain(|item| {
            let syn::TraitItem::Type(ty) = item else {
                return true;
            };
            ty.ident != "Members"
        });

        let mut mutability = false;
        for item in &item_trait.items {
            let syn::TraitItem::Fn(method) = item else {
                return Err(syn::Error::new_spanned(
                    item,
                    "only trait method is allowed",
                ));
            };

            let Some(syn::FnArg::Receiver(r)) = method.sig.inputs.first() else {
                return Err(syn::Error::new_spanned(
                    &method.sig.inputs,
                    "method receiver is required",
                ));
            };
            mutability |= r.mutability.is_some();
        }

        let config = PropConfig {
            members,
            mutability,
        };

        Ok((item_trait, config))
    }

    fn build(mut self) -> syn::Result<proc_macro2::TokenStream> {
        let sealed_trait = self.impl_sealed_trait();
        let prop_trait = self.define_prop_trait()?;
        let downcast_impl = self.impl_downcast();

        Ok(quote! {
            #sealed_trait
            #prop_trait
            #downcast_impl
        })
    }

    fn impl_sealed_trait(&self) -> proc_macro2::TokenStream {
        let mod_name = self.sealed_module_name();
        let sealed_trait_name = self.sealed_trait_name();
        let impl_for_members = self.config.members.iter().map(|path| {
            quote! {
                impl #sealed_trait_name for #path {}
            }
        });

        quote! {
            mod #mod_name {
                use super::*;

                #[doc(hidden)]
                pub trait #sealed_trait_name {}
                #(#impl_for_members)*
            }
        }
    }

    fn define_prop_trait(&mut self) -> syn::Result<proc_macro2::TokenStream> {
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

    fn impl_downcast(&self) -> proc_macro2::TokenStream {
        let path_prefix = self.path_to_ir_crate();
        let trait_name = &self.item_trait.ident;

        let arms = self.config.members.iter().map(|p| {
            let arm_body = if self.config.mutability {
                quote!(<&mut #p as #path_prefix::prelude::InstDowncastMut>::map_mut(isb, inst, |inst| inst as &mut dyn #trait_name))
            } else {
                quote!(<&#p as #path_prefix::prelude::InstDowncast>::map(isb, inst, |inst| inst as &dyn #trait_name))
            };

            quote!(
                id if id == std::any::TypeId::of::<#p>() => {
                    #arm_body
                }
            )
        });

        let inst_downcast_impl = if self.config.mutability {
            quote! {
                impl #path_prefix::prelude::InstDowncastMut for &mut dyn #trait_name {
                    fn downcast_mut(isb: &dyn #path_prefix::prelude::InstSetBase, inst: &mut dyn #path_prefix::prelude::Inst) -> Option<Self> {
                        match inst.type_id() {
                            #(#arms)*
                            _ => None

                        }
                    }
                }
            }
        } else {
            quote! {
                impl #path_prefix::prelude::InstDowncast for &dyn #trait_name {
                    fn downcast(isb: &dyn #path_prefix::prelude::InstSetBase, inst: &dyn #path_prefix::prelude::Inst) -> Option<Self> {
                        match inst.type_id() {
                            #(#arms)*
                            _ => None

                        }
                    }
                }
            }
        };

        quote! {
            #inst_downcast_impl
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

    fn path_to_ir_crate(&self) -> syn::Path {
        let crate_name = std::env::var("CARGO_PKG_NAME").unwrap();
        if crate_name == "sonatina-ir" {
            syn::parse_quote!(crate)
        } else {
            syn::parse_quote!(::sonatina_ir)
        }
    }
}

struct PropConfig {
    /// `true` if one of trait method receiver is `mut`.
    mutability: bool,

    members: Vec<syn::Path>,
}
