use quote::quote;

#[proc_macro_derive(Inst)]
pub fn derive_inst(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let item_struct = syn::parse_macro_input!(item as syn::ItemStruct);

    match InstBuilder::new(item_struct).and_then(InstBuilder::build) {
        Ok(impls) => quote! {
            #impls
        }
        .into(),

        Err(e) => e.to_compile_error().into(),
    }
}

struct InstBuilder {
    struct_name: syn::Ident,
    fields: syn::FieldsNamed,
}

impl InstBuilder {
    fn new(item_struct: syn::ItemStruct) -> syn::Result<Self> {
        let struct_ident = item_struct.ident;
        let syn::Fields::Named(fields) = item_struct.fields else {
            return Err(syn::Error::new_spanned(
                item_struct.fields,
                "tuple struct is not allowed for inst types",
            ));
        };

        if item_struct.generics.lt_token.is_some() {
            Err(syn::Error::new_spanned(
                item_struct.generics,
                "generics is not allowed for inst types",
            ))
        } else {
            Ok(Self {
                struct_name: struct_ident,
                fields,
            })
        }
    }

    fn build(self) -> syn::Result<proc_macro2::TokenStream> {
        let mut fields = Vec::with_capacity(self.fields.named.len());

        for f in &self.fields.named {
            if !matches!(f.vis, syn::Visibility::Inherited) {
                return Err(syn::Error::new_spanned(
                    &f.vis,
                    "all members of inst types should be private",
                ));
            };

            fields.push((f.ident.clone().unwrap(), f.ty.clone()));
        }

        let ctor = self.make_ctor(&fields);
        let accessors = self.make_accessors(&fields);
        let cast_fn = self.make_cast_fn();

        let struct_name = &self.struct_name;
        Ok(quote! {
            impl #struct_name {
                #ctor

                #accessors

                #cast_fn
            }
        })
    }

    fn make_ctor(&self, fields: &[(syn::Ident, syn::Type)]) -> proc_macro2::TokenStream {
        let ctor_args = fields.iter().map(|(ident, ty)| quote! {#ident: #ty});
        let field_names = fields.iter().map(|(ident, _)| ident);
        quote! {
            pub fn new(hi: &dyn crate::HasInst<Self>, #(#ctor_args),*) -> Self {
                Self {
                    #(#field_names: #field_names),*
                }
            }
        }
    }

    fn make_cast_fn(&self) -> proc_macro2::TokenStream {
        quote! {
            pub fn cast<'i>(hi: &dyn crate::HasInst<Self>, inst: &'i dyn Inst) -> Option<&'i Self> {
                if hi.is(inst) {
                    unsafe { Some(&*(inst as *const dyn Inst as *const Self)) }
                } else {
                    None
                }
            }

            pub fn cast_mut<'i>(
                hi: &dyn HasInst<Self>,
                inst: &'i mut dyn Inst,
            ) -> Option<&'i mut Self> {
                if hi.is(inst) {
                    unsafe { Some(&mut *(inst as *mut dyn Inst as *mut Self)) }
                } else {
                    None
                }
            }
        }
    }

    fn make_accessors(&self, fields: &[(syn::Ident, syn::Type)]) -> proc_macro2::TokenStream {
        let accessors = fields.iter().map(|(ident, ty)| {
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
}
