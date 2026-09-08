use proc_macro2::TokenStream;
use quote::{ToTokens, format_ident, quote};
use syn::{Data, DataEnum, DeriveInput, Fields, Index, Path};

use crate::{
    attrs::{find_attr_or_code, get_haloumi_integration_module},
    keys::{CELL_KEY, DEFAULT_CELL_TYPE},
};

/// Internal implementation of [`super::derive_decompose_in_cells`].
pub fn derive_decompose_in_cells_impl(input: DeriveInput) -> syn::Result<TokenStream> {
    // Default to the current crate, but downstream clients (i.e. custom types used in circuits)
    // will have to provide the cell type.
    let cell = find_attr_or_code::<Path>(&input, CELL_KEY, DEFAULT_CELL_TYPE)?;
    let module = get_haloumi_integration_module()?;
    let decompose_in_cell = quote! { #module::core::table::DecomposeIn<#cell> };
    let name = input.ident;
    let generics = input.generics;

    // Collect field types for where bounds
    let mut bounds = Vec::new();

    // Split generics into (impl generics) (ty generics) (where clause)
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let body = if cell.is_ident("Self") {
        // Special case for deriving itself. This case should be implemented for the `Cell` type
        // that all the other types use for their implementations.
        quote! { std::iter::once(*self) }
    } else {
        match &input.data {
            Data::Struct(data) => handle_fields(
                &data.fields,
                &mut bounds,
                Some(quote! { self. }),
                None,
                &decompose_in_cell,
            ),
            Data::Enum(data) => handle_enum(data, &mut bounds, &decompose_in_cell),
            Data::Union(_) => {
                unimplemented!("Unions are not supported")
            }
        }
    };

    Ok(quote! {
        impl #impl_generics #decompose_in_cell for #name #ty_generics
        where
            #(#bounds,)*
            #where_clause
        {
            fn cells(&self) -> impl IntoIterator<Item = #cell> {
                #body
            }
        }
    })
}

/// Creates the tokens for referencing a tuple field.
///
/// If `bind` is true then the tuple field is referenced by an identifier instead of the index.
/// This is done to be able to handle the two possible cases; a tuple struct and a tuple enum variant.
/// For former doesn't bind and is expected to do `self.{idx}` and the latter will bind the field
/// to an identifier with the format `f{idx}`.
fn format_tuple_field(idx: usize, bind: bool) -> TokenStream {
    if bind {
        format_ident!("__{idx}").into_token_stream()
    } else {
        Index::from(idx).into_token_stream()
    }
}

/// Gathers all the emitted code for handling the fields of a type.
///
/// Returns the body of the method required by the trait as a chained iterators calling the method
/// on each inner field. The where-clause bounds for each type are gathered in `bounds` and,
/// optionally, if it's necessary to create bindings they will get written to `var_names`. You
/// must pass a value for either `receiver` or `var_names`. Cannot pass both at the same time.
///
/// # Panics
///
/// If both `receiver` and `var_names` are [`Some`].
fn handle_fields(
    fields: &Fields,
    bounds: &mut Vec<TokenStream>,
    receiver: Option<TokenStream>,
    mut var_names: Option<&mut Vec<TokenStream>>,
    decompose_in_cell: &TokenStream,
) -> TokenStream {
    assert!(!(receiver.is_some() && var_names.is_some()));
    let field_calls = fields
        .iter()
        .enumerate()
        .filter(|(_, f)| !f.attrs.iter().any(|a| a.path().is_ident("skip")))
        .map(|(idx, f)| {
            let ty = &f.ty;
            let ident = f.ident.as_ref().map(ToTokens::to_token_stream);

            bounds.push(quote! { #ty: #decompose_in_cell });
            if let Some(var_names) = &mut var_names {
                var_names.push(
                    ident
                        .clone()
                        .unwrap_or_else(|| format_tuple_field(idx, true)),
                );
            }

            ident.unwrap_or_else(|| format_tuple_field(idx, receiver.is_none()))
        })
        .map(|f| quote! { .chain(#receiver #f.cells()) });
    quote! {
            std::iter::empty() #(#field_calls)*
    }
}

fn handle_enum(
    data: &DataEnum,
    bounds: &mut Vec<TokenStream>,
    decompose_in_cell: &TokenStream,
) -> TokenStream {
    let variants = data.variants.iter().map(|v| {
        let name = &v.ident;
        let mut var_names = vec![];
        let body = handle_fields(
            &v.fields,
            bounds,
            None,
            Some(&mut var_names),
            decompose_in_cell,
        );
        let var_names = match v.fields {
            Fields::Named(_) => Some(quote! { { #( #var_names ),* } }),
            Fields::Unnamed(_) => Some(quote! { ( #( #var_names ),* ) }),
            Fields::Unit => None,
        };

        quote! {
            Self::#name #var_names => { #body }
        }
    });

    quote! {
        match self {
            #(#variants),*
        }
    }
}
