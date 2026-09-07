use proc_macro2::TokenStream;
use quote::{ToTokens, format_ident, quote};
use syn::{Data, DataEnum, DeriveInput, Fields, Ident, Index, parse::Parse, parse_str};

use crate::{
    attrs::{find_attr_or, find_attr_or_code, get_attr, get_haloumi_integration_module},
    keys::{EXPRESSION_KEY, FIELD_KEY, KIND_KEY, NEW_KEY, ROTATION_KEY},
};

/// Internal implementation of [`super::derive_selector_info`].
pub fn derive_selector_info_impl(input: DeriveInput) -> syn::Result<TokenStream> {
    let module = get_haloumi_integration_module(&input)?;
    let name = input.ident;

    Ok(quote! {
        #module :: __impl_selector_info_for_selector!(#name);
    })
}

/// Internal implementation of [`super::derive_challenge_info`].
pub fn derive_challenge_info_impl(input: DeriveInput) -> syn::Result<TokenStream> {
    let module = get_haloumi_integration_module(&input)?;
    let name = input.ident;

    Ok(quote! {
        #module :: __impl_challenge_info_for_challenge!(#name);
    })
}

/// Internal implementation of [`super::derive_query_info`].
pub fn derive_query_info_impl(input: DeriveInput) -> syn::Result<TokenStream> {
    let module = get_haloumi_integration_module(&input)?;
    let kind =
        get_attr::<Ident>(&input, KIND_KEY).and_then(|kind| match format!("{kind}").as_str() {
            "Advice" | "Instance" | "Fixed" => Ok(kind),
            other => Err(syn::Error::new_spanned(
                kind,
                format!("Unrecognized kind: {other}"),
            )),
        })?;
    let name = input.ident;

    Ok(quote! {
        #module :: __impl_query_info!(#name, #kind);
    })
}

/// Internal implementation of [`super::derive_create_query`].
pub fn derive_create_query_impl(input: DeriveInput) -> syn::Result<TokenStream> {
    let module = get_haloumi_integration_module(&input)?;
    let field = find_attr_or_code::<syn::Path>(&input, FIELD_KEY, "ff::Field")?;
    let expr = find_attr_or_code::<syn::Path>(&input, EXPRESSION_KEY, "crate::plonk::Expression")?;
    let rotation = find_attr_or_code::<syn::Type>(&input, ROTATION_KEY, "crate::poly::Rotation")?;
    let new = get_attr::<syn::Expr>(&input, NEW_KEY)?;
    let name = input.ident;

    Ok(quote! {
        #module :: __impl_create_query!(#name, #field, #rotation, #new, #expr);
    })
}

/// Internal implementation of [`super::derive_gate_info`].
pub fn derive_gate_info_impl(input: DeriveInput) -> syn::Result<TokenStream> {
    let module = get_haloumi_integration_module(&input)?;
    let field = find_attr_or_code::<syn::Path>(&input, FIELD_KEY, "ff::Field")?;
    let expr = find_attr_or_code::<syn::Path>(&input, EXPRESSION_KEY, "crate::plonk::Expression")?;
    let name = input.ident;

    Ok(quote! {
        #module :: __impl_gate_info_for_gate!(#name, #field, #expr);
    })
}
/// Internal implementation of [`super::derive_constraint_system_info`].
pub fn derive_constraint_system_info_impl(input: DeriveInput) -> syn::Result<TokenStream> {
    let module = get_haloumi_integration_module(&input)?;
    let field = find_attr_or_code::<syn::Path>(&input, FIELD_KEY, "ff::Field")?;
    let expr = find_attr_or_code::<syn::Path>(&input, EXPRESSION_KEY, "crate::plonk::Expression")?;
    let name = input.ident;

    Ok(quote! {
        #module :: __impl_constraint_system_info_for_constraint_system!(#name, #field, #expr);
    })
}
