use crate::inst_set_base::ty_name_to_method_name;

use super::convert_to_snake;

use quote::quote;

pub fn derive_inst(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let item_struct = syn::parse_macro_input!(item as syn::ItemStruct);

    match InstStruct::new(item_struct).and_then(InstStruct::build) {
        Ok(impls) => quote! {
            #impls
        }
        .into(),

        Err(e) => e.to_compile_error().into(),
    }
}

struct InstStruct {
    struct_name: syn::Ident,
    has_side_effect: bool,
    is_terminator: bool,
    fields: Vec<InstField>,
}

struct InstField {
    ident: syn::Ident,
    ty: syn::Type,
    value: bool,
}

impl InstStruct {
    fn new(item_struct: syn::ItemStruct) -> syn::Result<Self> {
        let (has_side_effect, is_terminator) = Self::check_attr(&item_struct)?;

        let struct_ident = item_struct.ident;

        let fields = Self::parse_fields(&item_struct.fields)?;

        if item_struct.generics.lt_token.is_some() {
            return Err(syn::Error::new_spanned(
                item_struct.generics,
                "generics is not allowed for inst types",
            ));
        }

        Ok(Self {
            struct_name: struct_ident,
            has_side_effect,
            is_terminator,
            fields,
        })
    }

    fn build(self) -> syn::Result<proc_macro2::TokenStream> {
        let ctor = self.make_ctor();
        let accessors = self.make_accessors();

        let struct_name = &self.struct_name;
        let impl_inst = self.impl_inst();
        let impl_inst_cast = self.impl_inst_cast();
        Ok(quote! {
            impl #struct_name {
                #ctor

                #accessors

            }

           #impl_inst_cast
            #impl_inst
        })
    }

    fn check_attr(item_struct: &syn::ItemStruct) -> syn::Result<(bool, bool)> {
        let mut has_side_effect = false;
        let mut is_terminator = false;

        for attr in &item_struct.attrs {
            if attr.path().is_ident("inst") {
                let meta = attr.parse_args::<syn::Meta>()?;
                if let syn::Meta::Path(path) = &meta {
                    if path.is_ident("has_side_effect") {
                        has_side_effect = true;
                    }
                }
                if let syn::Meta::Path(path) = &meta {
                    if path.is_ident("terminator") {
                        is_terminator = true;
                    }
                }
            }
        }

        Ok((has_side_effect, is_terminator))
    }

    fn parse_fields(fields: &syn::Fields) -> syn::Result<Vec<InstField>> {
        let syn::Fields::Named(fields) = fields else {
            return Err(syn::Error::new_spanned(
                fields,
                "tuple struct is not allowed for inst types",
            ));
        };

        let mut inst_fields = Vec::new();

        for field in &fields.named {
            let mut value = false;

            if !matches!(field.vis, syn::Visibility::Inherited) {
                return Err(syn::Error::new_spanned(
                    field,
                    "public visibility is not allowed",
                ));
            }

            for attr in &field.attrs {
                if attr.path().is_ident("inst") {
                    let meta = attr.parse_args::<syn::Meta>()?;
                    if let syn::Meta::Path(path) = meta {
                        if path.is_ident("value") {
                            value = true;
                        } else {
                            return Err(syn::Error::new_spanned(attr, "only `value` is allowed"));
                        }
                    }
                }
            }

            inst_fields.push(InstField {
                ident: field.ident.clone().unwrap(),
                ty: field.ty.clone(),
                value,
            });
        }

        Ok(inst_fields)
    }

    fn make_ctor(&self) -> proc_macro2::TokenStream {
        let ctor_args = self.fields.iter().map(|f| {
            let ident = &f.ident;
            let ty = &f.ty;
            quote! {#ident: #ty}
        });

        let field_names = self.fields.iter().map(|f| &f.ident);
        quote! {
            #[allow(clippy::too_many_arguments)]
            pub fn new(hi: &dyn crate::HasInst<Self>, #(#ctor_args),*) -> Self {
                Self {
                    #(#field_names: #field_names),*
                }
            }
        }
    }

    fn make_accessors(&self) -> proc_macro2::TokenStream {
        let accessors = self.fields.iter().map(|f| {
            let ident = &f.ident;
            let ty = &f.ty;
            let getter = quote::format_ident!("{ident}");
            let get_mut = quote::format_ident!("{ident}_mut");
            quote! {
                pub fn #getter(&self) -> &#ty {
                    &self.#ident
                }

                pub fn #get_mut(&mut self) -> &mut #ty{
                    &mut self.#ident
                }
            }
        });

        quote! {
            #(#accessors)*
        }
    }

    fn impl_inst_cast(&self) -> proc_macro2::TokenStream {
        let struct_name = &self.struct_name;
        let has_inst_method = ty_name_to_method_name(struct_name);
        quote! {
            impl crate::InstCast for #struct_name {
                fn downcast<'i>(hi: &dyn crate::HasInst<Self>, inst: &'i dyn crate::Inst) -> Option<&'i Self> {
                    if hi.is(inst) {
                        unsafe { Some(&*(inst as *const dyn crate::Inst as *const Self)) }
                    } else {
                        None
                    }
                }

                fn downcast_mut<'i>(
                    hi: &dyn crate::HasInst<Self>,
                    inst: &'i mut dyn crate::Inst,
                ) -> Option<&'i mut Self> {
                    if hi.is(inst) {
                        unsafe { Some(&mut *(inst as *mut dyn crate::Inst as *mut Self)) }
                    } else {
                        None
                    }
                }

                fn downcast_with_isb<'i>(is: &dyn crate::InstSetBase, inst: &'i dyn crate::Inst) -> Option<&'i Self> {
                    let hi = is.#has_inst_method()?;
                    Self::downcast(hi, inst)
                }

                fn downcast_mut_with_isb<'i>(is: &dyn crate::InstSetBase, inst: &'i mut dyn crate::Inst) -> Option<&'i mut Self> {
                    let hi = is.#has_inst_method()?;
                    Self::downcast_mut(hi, inst)
                }
            }
        }
    }

    fn impl_inst(&self) -> proc_macro2::TokenStream {
        let struct_name = &self.struct_name;
        let has_side_effect = self.has_side_effect;
        let is_terminator = self.is_terminator;
        let visit_fields: Vec<_> = self
            .fields
            .iter()
            .filter(|f| f.value)
            .map(|f| &f.ident)
            .collect();
        let text_form = convert_to_snake(&self.struct_name.to_string());

        quote! {
            impl crate::Inst for #struct_name {
                fn visit_values(&self, f: &mut dyn Fn(crate::Value)) {
                    #(crate::ValueVisitable::visit_with(&self.#visit_fields, (f));)*
                }

                fn visit_values_mut(&mut self, f: &mut dyn Fn(&mut crate::Value)) {
                    #(crate::ValueVisitable::visit_mut_with(&mut self.#visit_fields, (f));)*
                }

                fn has_side_effect(&self) -> bool {
                    #has_side_effect
                }

                fn is_terminator(&self) -> bool {
                    #is_terminator
                }


                fn as_text(&self) -> &'static str {
                    #text_form
                }
            }
        }
    }
}
