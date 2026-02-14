use quote::quote;

use super::convert_to_snake;
use crate::inst_set_base::ty_name_to_method_name;

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
    side_effect: Option<syn::Path>,
    is_terminator: bool,
    arity: InstAritySpec,
    fields: Vec<InstField>,
}

struct InstField {
    ident: syn::Ident,
    ty: syn::Type,
}

enum InstAritySpec {
    Exact(usize),
    AtLeast(usize),
    AtMost(usize),
    Range { min: usize, max: usize },
}

impl InstAritySpec {
    fn parse_usize_expr(expr: &syn::Expr, usage: &str) -> syn::Result<usize> {
        let syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(int),
            ..
        }) = expr
        else {
            return Err(syn::Error::new_spanned(expr, usage));
        };

        int.base10_parse()
            .map_err(|_| syn::Error::new_spanned(expr, usage))
    }

    fn parse_call_args(
        call: &syn::ExprCall,
        expected: usize,
        usage: &str,
    ) -> syn::Result<Vec<usize>> {
        if call.args.len() != expected {
            return Err(syn::Error::new_spanned(call, usage));
        }

        call.args
            .iter()
            .map(|arg| Self::parse_usize_expr(arg, usage))
            .collect()
    }

    fn parse(expr: syn::Expr) -> syn::Result<Self> {
        if let syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(int),
            ..
        }) = &expr
        {
            return Ok(Self::Exact(int.base10_parse().map_err(|_| {
                syn::Error::new_spanned(&expr, "expected integer literal")
            })?));
        }

        let syn::Expr::Call(call) = expr else {
            return Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                "expected `arity(N)`, `arity(exact(N))`, `arity(at_least(N))`, `arity(at_most(N))`, or `arity(range(M, N))`",
            ));
        };

        let syn::Expr::Path(path) = &*call.func else {
            return Err(syn::Error::new_spanned(
                &call.func,
                "expected `exact`, `at_least`, `at_most`, or `range`",
            ));
        };
        let Some(kind) = path.path.get_ident().map(|ident| ident.to_string()) else {
            return Err(syn::Error::new_spanned(
                path,
                "expected `exact`, `at_least`, `at_most`, or `range`",
            ));
        };

        match kind.as_str() {
            "exact" => {
                let args = Self::parse_call_args(
                    &call,
                    1,
                    "expected `arity(exact(N))` where `N` is an integer literal",
                )?;
                Ok(Self::Exact(args[0]))
            }
            "at_least" => {
                let args = Self::parse_call_args(
                    &call,
                    1,
                    "expected `arity(at_least(N))` where `N` is an integer literal",
                )?;
                Ok(Self::AtLeast(args[0]))
            }
            "at_most" => {
                let args = Self::parse_call_args(
                    &call,
                    1,
                    "expected `arity(at_most(N))` where `N` is an integer literal",
                )?;
                Ok(Self::AtMost(args[0]))
            }
            "range" => {
                let usage = "expected `arity(range(M, N))` where `M` and `N` are integer literals";
                let args = Self::parse_call_args(&call, 2, usage)?;
                let [min, max] = [args[0], args[1]];
                if min > max {
                    return Err(syn::Error::new_spanned(
                        call,
                        "invalid range: min must be <= max",
                    ));
                }
                Ok(Self::Range { min, max })
            }
            _ => Err(syn::Error::new_spanned(
                path,
                "expected `exact`, `at_least`, `at_most`, or `range`",
            )),
        }
    }

    fn to_tokens(&self) -> proc_macro2::TokenStream {
        match self {
            Self::Exact(n) => quote!(crate::inst::InstArity::Exact(#n)),
            Self::AtLeast(n) => quote!(crate::inst::InstArity::AtLeast(#n)),
            Self::AtMost(n) => quote!(crate::inst::InstArity::AtMost(#n)),
            Self::Range { min, max } => {
                quote!(crate::inst::InstArity::Range { min: #min, max: #max })
            }
        }
    }
}

impl InstStruct {
    fn new(item_struct: syn::ItemStruct) -> syn::Result<Self> {
        let (side_effect, is_terminator, arity) = Self::check_attr(&item_struct)?;

        let struct_ident = item_struct.ident;

        let fields = Self::parse_fields(&item_struct.fields)?;
        let arity = arity.unwrap_or(InstAritySpec::Exact(fields.len()));

        if item_struct.generics.lt_token.is_some() {
            return Err(syn::Error::new_spanned(
                item_struct.generics,
                "generics is not allowed for inst types",
            ));
        }

        Ok(Self {
            struct_name: struct_ident,
            side_effect,
            is_terminator,
            arity,
            fields,
        })
    }

    fn build(self) -> syn::Result<proc_macro2::TokenStream> {
        let impl_method = self.impl_method();
        let impl_inst = self.impl_inst();
        let impl_inst_ext = self.impl_inst_ext();
        let impl_inst_cast = self.impl_inst_cast();
        let impl_visitable = self.impl_visitable();
        let impl_inst_write = self.impl_inst_write();
        Ok(quote! {
           #impl_method
           #impl_inst_cast
           #impl_inst
           #impl_inst_ext
           #impl_inst_write
           #impl_visitable
        })
    }

    fn check_attr(
        item_struct: &syn::ItemStruct,
    ) -> syn::Result<(Option<syn::Path>, bool, Option<InstAritySpec>)> {
        let mut side_effect = None;
        let mut is_terminator = false;
        let mut arity = None;

        for attr in &item_struct.attrs {
            if attr.path().is_ident("inst") {
                let meta = attr.parse_args::<syn::Meta>()?;
                if let syn::Meta::List(ml) = &meta
                    && ml.path.is_ident("side_effect")
                {
                    if !matches!(ml.delimiter, syn::MacroDelimiter::Paren(..)) {
                        return Err(syn::Error::new_spanned(ml, "`side_effect(...) is requried"));
                    }

                    side_effect = Some(syn::parse2(ml.tokens.clone())?);
                }
                if let syn::Meta::Path(path) = &meta
                    && path.is_ident("terminator")
                {
                    is_terminator = true;
                }
                if let syn::Meta::List(ml) = &meta
                    && ml.path.is_ident("arity")
                {
                    if arity.is_some() {
                        return Err(syn::Error::new_spanned(
                            ml,
                            "duplicate `arity(...)` attribute",
                        ));
                    }

                    let expr = syn::parse2(ml.tokens.clone())?;
                    arity = Some(InstAritySpec::parse(expr)?);
                }
            }
        }

        Ok((side_effect, is_terminator, arity))
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
            if !matches!(field.vis, syn::Visibility::Inherited) {
                return Err(syn::Error::new_spanned(
                    field,
                    "public visibility is not allowed",
                ));
            }

            inst_fields.push(InstField {
                ident: field.ident.clone().unwrap(),
                ty: field.ty.clone(),
            });
        }

        Ok(inst_fields)
    }

    fn make_ctor(&self) -> proc_macro2::TokenStream {
        let ctor_args: Vec<_> = self
            .fields
            .iter()
            .map(|f| {
                let ident = &f.ident;
                let ty = &f.ty;
                quote! {#ident: #ty}
            })
            .collect();

        let field_names: Vec<_> = self.fields.iter().map(|f| &f.ident).collect();
        let has_inst_method = ty_name_to_method_name(&self.struct_name);
        quote! {
            #[allow(clippy::too_many_arguments)]
            pub fn new(hi: &dyn crate::HasInst<Self>, #(#ctor_args),*) -> Self {
                Self {
                    #(#field_names: #field_names),*
                }
            }

            #[allow(clippy::too_many_arguments)]
            pub fn new_unchecked(isb: &dyn crate::InstSetBase, #(#ctor_args),*) -> Self {
                isb.#has_inst_method().unwrap();
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
            impl<'a> crate::InstDowncast<'a> for &'a #struct_name {
                fn downcast(isb: &dyn crate::InstSetBase, inst: &'a dyn crate::Inst) -> Option<Self> {
                    let hi = isb.#has_inst_method()?;
                    if hi.is(inst) {
                        unsafe { Some(&*(inst as *const dyn crate::Inst as *const #struct_name)) }
                    } else {
                        None
                    }
                }
            }

            impl<'a> crate::InstDowncastMut<'a> for &'a mut #struct_name {
                fn downcast_mut(isb: &dyn crate::InstSetBase, inst: &'a mut dyn crate::Inst) -> Option<Self> {
                    let hi = isb.#has_inst_method()?;
                    if hi.is(inst) {
                        unsafe { Some(&mut *(inst as *mut dyn crate::Inst as *mut #struct_name)) }
                    } else {
                        None
                    }
                }
            }
        }
    }

    fn impl_method(&self) -> proc_macro2::TokenStream {
        let struct_name = &self.struct_name;
        let text_form = convert_to_snake(&self.struct_name.to_string());
        let arity = self.arity.to_tokens();
        let ctor = self.make_ctor();
        let accessors = self.make_accessors();

        quote! {
            impl #struct_name {
                pub const fn inst_name() -> &'static str {
                    #text_form

                }

                pub const fn inst_arity() -> crate::inst::InstArity {
                    #arity
                }

                #ctor

                #accessors
            }
        }
    }

    fn impl_inst(&self) -> proc_macro2::TokenStream {
        let struct_name = &self.struct_name;
        let side_effect = match &self.side_effect {
            Some(se) => quote!(#se),
            None => quote!(crate::inst::SideEffect::None),
        };
        let is_terminator = self.is_terminator;
        quote! {
            impl crate::Inst for #struct_name {
                fn side_effect(&self) -> crate::inst::SideEffect {
                    #side_effect
                }

                fn arity(&self) -> crate::inst::InstArity {
                    Self::inst_arity()
                }

                fn is_terminator(&self) -> bool {
                    #is_terminator
                }

                fn as_text(&self) -> &'static str {
                    Self::inst_name()
                }
            }
        }
    }

    fn impl_inst_write(&self) -> proc_macro2::TokenStream {
        let struct_name = &self.struct_name;
        let fields = self.fields.iter().map(|f| {
            let f = &f.ident;
            quote!{
                if crate::ir_writer::IrWrite::<crate::ir_writer::FuncWriteCtx>::has_content(self.#f()) {
                    write!(&mut w, " ")?;
                    crate::ir_writer::IrWrite::write(self.#f(), &mut w, ctx)?;
                }
            }
        });

        quote! {
            impl crate::inst::InstWrite for #struct_name {
                fn write(&self, mut w: &mut dyn std::io::Write, ctx: &crate::ir_writer::FuncWriteCtx) -> std::io::Result<()> {
                    write!(w, "{}", crate::Inst::as_text(self))?;
                    #(#fields)*
                    Ok(())
                }
            }
        }
    }

    fn impl_visitable(&self) -> proc_macro2::TokenStream {
        let fields_accept = self.fields.iter().map(|f| {
            let method = &f.ident;
            quote! {
                self.#method().accept(v);
            }
        });

        let fields_accept_mut = self.fields.iter().map(|f| {
            let method_mut = quote::format_ident!("{}_mut", &f.ident);
            quote! {
                self.#method_mut().accept_mut(v);
            }
        });

        let struct_name = &self.struct_name;

        quote! {
            impl crate::visitor::Visitable for #struct_name {
                fn accept(&self, v: &mut dyn crate::visitor::Visitor) {
                    #(#fields_accept)*
                }
            }

            impl crate::visitor::VisitableMut for #struct_name {
                fn accept_mut(&mut self, v: &mut dyn crate::visitor::VisitorMut) {
                    #(#fields_accept_mut)*
                }
            }
        }
    }

    fn impl_inst_ext(&self) -> proc_macro2::TokenStream {
        let struct_name = &self.struct_name;
        let has_inst_method = ty_name_to_method_name(struct_name);

        quote! {
            impl crate::InstExt for #struct_name {
                fn belongs_to(isb: &dyn crate::InstSetBase) -> Option<&dyn crate::HasInst<Self>> {
                    isb.#has_inst_method()
                }
            }
        }
    }
}
