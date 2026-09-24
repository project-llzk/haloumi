//! Derive implementations for cell-based I/O traits.

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{Data, DataStruct, DeriveInput, Fields, GenericParam, Ident, Path, parse_quote};

use crate::{
    attrs::{find_attr_or_code, get_haloumi_integration_module},
    keys::FIELD_KEY,
};

/// Internal implementation of [`super::derive_cell_repr_size`].
pub fn derive_cell_repr_size_impl(input: DeriveInput) -> syn::Result<TokenStream> {
    let module = get_haloumi_integration_module()?;
    let cell_repr_size = quote! { #module::core::table::CellReprSize };
    let fields = struct_fields(&input)?;
    let mut generics = input.generics.clone();

    for field in fields {
        let ty = &field.ty;
        generics
            .make_where_clause()
            .predicates
            .push(parse_quote! { #ty: #cell_repr_size });
    }

    let name = &input.ident;
    let (impl_generics, _, where_clause) = generics.split_for_impl();
    let (_, ty_generics, _) = input.generics.split_for_impl();
    let sizes = fields.iter().map(|field| {
        let ty = &field.ty;
        quote! { <#ty as #cell_repr_size>::SIZE }
    });

    Ok(quote! {
        impl #impl_generics #cell_repr_size for #name #ty_generics #where_clause {
            const SIZE: usize = 0 #( + #sizes )*;
        }
    })
}

/// Internal implementation of [`super::derive_load_from_cells`].
pub fn derive_load_from_cells_impl(input: DeriveInput) -> syn::Result<TokenStream> {
    let module = get_haloumi_integration_module()?;
    let field_trait = find_attr_or_code::<Path>(&input, FIELD_KEY, "ff::Field")?;
    let fields = struct_fields(&input)?;
    let parameters = IoParameters::new(&input);
    let load_from_cells = parameters.load_from_cells(&module);
    let mut generics = parameters.extend_generics(input.generics.clone(), &field_trait, &module);

    for field in fields {
        let ty = &field.ty;
        generics
            .make_where_clause()
            .predicates
            .push(parse_quote! { #ty: #load_from_cells });
    }

    let name = &input.ident;
    let (impl_generics, _, where_clause) = generics.split_for_impl();
    let (_, ty_generics, _) = input.generics.split_for_impl();
    let body = load_body(fields);
    let field = &parameters.field;
    let chip = &parameters.chip;
    let types = &parameters.types;

    Ok(quote! {
        impl #impl_generics #load_from_cells for #name #ty_generics #where_clause {
            fn load(
                ctx: &mut #module::extractor::core::io::ctx::input::ICtx<#field, #types>,
                chip: &#chip,
                layouter: &mut #module::core::layouter::LayoutAdaptor<'_, impl #module::core::layouter::Layouter<#field, #types::Error>>,
                injected_ir: &mut #module::ir::inject::InjectedIR<#types::RegionIndex, #types::Expression>,
            ) -> Result<Self, #types::Error> {
                #body
            }
        }
    })
}

/// Internal implementation of [`super::derive_store_into_cells`].
pub fn derive_store_into_cells_impl(input: DeriveInput) -> syn::Result<TokenStream> {
    let module = get_haloumi_integration_module()?;
    let field_trait = find_attr_or_code::<Path>(&input, FIELD_KEY, "ff::Field")?;
    let fields = struct_fields(&input)?;
    let parameters = IoParameters::new(&input);
    let store_into_cells = parameters.store_into_cells(&module);
    let mut generics = parameters.extend_generics(input.generics.clone(), &field_trait, &module);

    for field in fields {
        let ty = &field.ty;
        generics
            .make_where_clause()
            .predicates
            .push(parse_quote! { #ty: #store_into_cells });
    }

    let name = &input.ident;
    let (impl_generics, _, where_clause) = generics.split_for_impl();
    let (_, ty_generics, _) = input.generics.split_for_impl();
    let body = store_body(fields, &store_into_cells);
    let field = &parameters.field;
    let chip = &parameters.chip;
    let types = &parameters.types;

    Ok(quote! {
        impl #impl_generics #store_into_cells for #name #ty_generics #where_clause {
            fn store(
                self,
                ctx: &mut #module::extractor::core::io::ctx::output::OCtx<#field, #types>,
                chip: &#chip,
                layouter: &mut #module::core::layouter::LayoutAdaptor<'_, impl #module::core::layouter::Layouter<#field, #types::Error>>,
                injected_ir: &mut #module::ir::inject::InjectedIR<#types::RegionIndex, #types::Expression>,
            ) -> Result<(), #types::Error> {
                #body
            }
        }
    })
}

fn struct_fields(input: &DeriveInput) -> syn::Result<&Fields> {
    match &input.data {
        Data::Struct(DataStruct { fields, .. }) => Ok(fields),
        Data::Enum(_) => Err(syn::Error::new_spanned(
            input,
            "this derive only supports structs; enums require an explicit cell representation",
        )),
        Data::Union(_) => Err(syn::Error::new_spanned(
            input,
            "this derive only supports structs; unions require an explicit cell representation",
        )),
    }
}

fn load_body(fields: &Fields) -> TokenStream {
    match fields {
        Fields::Named(fields) => {
            let loads = fields.named.iter().map(|field| {
                let name = field.ident.as_ref().unwrap();
                quote! { #name: ctx.load(chip, layouter, injected_ir)? }
            });
            quote! { Ok(Self { #(#loads),* }) }
        }
        Fields::Unnamed(fields) => {
            let loads = fields
                .unnamed
                .iter()
                .map(|_| quote! { ctx.load(chip, layouter, injected_ir)? });
            quote! { Ok(Self(#(#loads),*)) }
        }
        Fields::Unit => quote! { Ok(Self) },
    }
}

fn store_body(fields: &Fields, store_into_cells: &TokenStream) -> TokenStream {
    match fields {
        Fields::Named(fields) => {
            let names = fields
                .named
                .iter()
                .map(|field| field.ident.as_ref().unwrap());
            let stores = fields.named.iter().map(|field| {
                let name = field.ident.as_ref().unwrap();
                let ty = &field.ty;
                quote! { <#ty as #store_into_cells>::store(#name, ctx, chip, layouter, injected_ir)?; }
            });
            quote! {
                let Self { #(#names),* } = self;
                #(#stores)*
                Ok(())
            }
        }
        Fields::Unnamed(fields) => {
            let names =
                (0..fields.unnamed.len()).map(|index| format_ident!("__haloumi_field_{index}"));
            let stores = fields.unnamed.iter().enumerate().map(|(index, field)| {
                let name = format_ident!("__haloumi_field_{index}");
                let ty = &field.ty;
                quote! { <#ty as #store_into_cells>::store(#name, ctx, chip, layouter, injected_ir)?; }
            });
            quote! {
                let Self(#(#names),*) = self;
                #(#stores)*
                Ok(())
            }
        }
        Fields::Unit => quote! { Ok(()) },
    }
}

struct IoParameters {
    field: Ident,
    chip: Ident,
    types: Ident,
}

impl IoParameters {
    fn new(input: &DeriveInput) -> Self {
        let mut used = input
            .generics
            .type_params()
            .map(|parameter| parameter.ident.to_string())
            .collect::<Vec<_>>();
        let field = fresh_ident("__HaloumiField", &mut used);
        let chip = fresh_ident("__HaloumiChip", &mut used);
        let types = fresh_ident("__HaloumiTypes", &mut used);
        Self { field, chip, types }
    }

    fn extend_generics(
        &self,
        mut generics: syn::Generics,
        field_trait: &Path,
        module: &Ident,
    ) -> syn::Generics {
        let field = &self.field;
        let chip = &self.chip;
        let types = &self.types;
        generics
            .params
            .push(GenericParam::Type(parse_quote! { #field }));
        generics
            .params
            .push(GenericParam::Type(parse_quote! { #chip }));
        generics
            .params
            .push(GenericParam::Type(parse_quote! { #types }));
        let where_clause = generics.make_where_clause();
        where_clause
            .predicates
            .push(parse_quote! { #field: #field_trait });
        where_clause
            .predicates
            .push(parse_quote! { #types: #module::Types<#field> });
        generics
    }

    fn load_from_cells(&self, module: &Ident) -> TokenStream {
        let field = &self.field;
        let chip = &self.chip;
        let types = &self.types;
        quote! { #module::extractor::core::io::load::LoadFromCells<#field, #chip, #types> }
    }

    fn store_into_cells(&self, module: &Ident) -> TokenStream {
        let field = &self.field;
        let chip = &self.chip;
        let types = &self.types;
        quote! { #module::extractor::core::io::store::StoreIntoCells<#field, #chip, #types> }
    }
}

fn fresh_ident(base: &str, used: &mut Vec<String>) -> Ident {
    let mut suffix = 0;
    loop {
        let candidate = if suffix == 0 {
            base.to_owned()
        } else {
            format!("{base}{suffix}")
        };
        if !used.contains(&candidate) {
            used.push(candidate.clone());
            return format_ident!("{candidate}");
        }
        suffix += 1;
    }
}
