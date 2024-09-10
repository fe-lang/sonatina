use quote::quote;

use crate::{convert_to_snake, inst_set_base};

pub fn define_inst_set(
    attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let attr_args = syn::parse_macro_input!(attr as syn::AttributeArgs);
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
    inst_kind_mut_name: syn::Ident,
}

impl InstSet {
    fn new(args: Vec<syn::NestedMeta>, s: syn::ItemStruct) -> syn::Result<Self> {
        let ident = s.ident;
        let vis = s.vis;
        let insts = Self::parse_insts(&s.fields)?;
        let inst_kind_ident = Self::parse_inst_kind_name(&args)?;
        let inst_kind_mut_ident = quote::format_ident!("{inst_kind_ident}Mut");

        Ok(Self {
            vis,
            ident,
            insts,
            inst_kind_name: inst_kind_ident,
            inst_kind_mut_name: inst_kind_mut_ident,
        })
    }

    fn build(self) -> syn::Result<proc_macro2::TokenStream> {
        let inst_set = self.define_inst_set();
        let inherent_methods = self.impl_inherent_methods();

        let has_inst_impls = self.impl_has_inst();
        let inst_set_base_impl = self.impl_inst_set_base();
        let inst_set_ext_impl = self.impl_inst_set_ext();

        let inst_kind = self.define_inst_kind();

        Ok(quote! {
            #inst_set
            #inherent_methods

            #has_inst_impls
            #inst_set_base_impl
            #inst_set_ext_impl

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
            #vis struct #ident {
                #[allow(clippy::type_complexity)]
                table: ::rustc_hash::FxHashMap<
                    std::any::TypeId,
                    (
                        &'static for<'i> fn(&Self, &'i dyn Inst) -> <Self as crate::InstSetExt>::InstKind<'i>,
                        &'static for<'i> fn(
                            &Self,
                            &'i mut dyn Inst,
                        ) -> <Self as crate::InstSetExt>::InstKindMut<'i>,
                    ),
                >,

            }
        }
    }

    fn define_inst_kind(&self) -> proc_macro2::TokenStream {
        let lt = syn::Lifetime::new("'i", proc_macro2::Span::call_site());

        let variants = self.insts.iter().map(|p| {
            let variant_name = self.variant_name_from_inst_path(p);
            quote! { #variant_name(&#lt #p) }
        });
        let variants_mut = self.insts.iter().map(|p| {
            let variant_name = self.variant_name_from_inst_path(p);
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

    fn impl_inherent_methods(&self) -> proc_macro2::TokenStream {
        let insert_table_ent = |p: &syn::Path| {
            let inst_name_snake = convert_to_snake(&p.segments.last().unwrap().ident.to_string());
            let cast_fn_name = quote::format_ident!("cast_{inst_name_snake}");
            let cast_mut_fn_name = quote::format_ident!("{cast_fn_name}_mut");
            let ident = &self.ident;
            let inst_kind_name = &self.inst_kind_name;
            let inst_kind_mut_name = &self.inst_kind_mut_name;
            let variant_name = self.variant_name_from_inst_path(p);

            quote! {
                let tid = std::any::TypeId::of::<#p>();
                fn #cast_fn_name<'i>(self_: &#ident, inst: &'i dyn Inst) -> #inst_kind_name<'i> {
                    let inst = #p::cast(self_, inst).unwrap();
                    #inst_kind_name::#variant_name(inst)
                }
                fn #cast_mut_fn_name<'i>(self_: &#ident, inst: &'i mut dyn Inst) -> #inst_kind_mut_name<'i> {
                    let inst = #p::cast_mut(self_, inst).unwrap();
                    #inst_kind_mut_name::#variant_name(inst)
                }

                let f: &'static for<'a, 'i> fn(&'a #ident, &'i dyn Inst) -> #inst_kind_name<'i> =
                    &(#cast_fn_name as for<'a, 'i> fn(&'a #ident, &'i dyn Inst) -> #inst_kind_name<'i>);
                let f_mut: &'static for<'a, 'i> fn(&'a #ident, &'i mut dyn Inst) -> #inst_kind_mut_name<'i> =
                    &(#cast_mut_fn_name as for<'a, 'i> fn(&'a #ident, &'i mut dyn Inst) -> #inst_kind_mut_name<'i>);
                table.insert(tid, (f, f_mut));

            }
        };

        let insert_ents = self.insts.iter().map(insert_table_ent);
        let ctor = quote! {
            pub(crate) fn new() -> Self {
                let mut table = ::rustc_hash::FxHashMap::default();
                #(#insert_ents)*
                Self { table }
            }
        };

        let ident = &self.ident;
        quote! {
            impl #ident {
                #ctor
            }
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

    fn impl_inst_set_ext(&self) -> proc_macro2::TokenStream {
        let ident = &self.ident;
        let inst_kind_name = &self.inst_kind_name;
        let inst_kind_mut_name = &self.inst_kind_mut_name;

        quote! {
            impl crate::prelude::InstSetExt for #ident {
                type InstKind<'i> = #inst_kind_name<'i>;
                type InstKindMut<'i> = #inst_kind_mut_name<'i>;

                fn resolve_inst<'i>(&self, inst: &'i dyn Inst) -> Self::InstKind<'i> {
                    let tid = inst.type_id();
                    debug_assert!(self.table.contains_key(&tid));
                    self.table[&tid].0(self, inst)
                }

                fn resolve_inst_mut<'i>(&self, inst: &'i mut dyn Inst) -> Self::InstKindMut<'i> {
                    let tid = inst.type_id();
                    debug_assert!(self.table.contains_key(&tid));
                    self.table[&tid].1(self, inst)
                }
            }
        }
    }

    fn variant_name_from_inst_path<'a>(&self, p: &'a syn::Path) -> &'a syn::Ident {
        &p.segments.last().unwrap().ident
    }
}
