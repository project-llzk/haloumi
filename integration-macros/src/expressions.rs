use proc_macro2::TokenStream;
use quote::quote;
use syn::DeriveInput;

use crate::{
    attrs::{find_attr_or_code, get_haloumi_integration_module},
    keys::{
        ADVICE_QUERY_KEY, CHALLENGE_KEY, FIELD_KEY, FIXED_QUERY_KEY, INSTANCE_QUERY_KEY,
        SELECTOR_KEY,
    },
};

/// Internal implementation of [`super::derive_expression_traits`].
pub fn derive_expression_traits_impl(input: DeriveInput) -> syn::Result<TokenStream> {
    let module = get_haloumi_integration_module()?;
    let field = find_attr_or_code::<syn::Path>(&input, FIELD_KEY, "ff::Field")?;
    let selector = find_attr_or_code::<syn::Path>(&input, SELECTOR_KEY, "crate::plonk::Selector")?;
    let fixed_query =
        find_attr_or_code::<syn::Path>(&input, FIXED_QUERY_KEY, "crate::plonk::FixedQuery")?;
    let advice_query =
        find_attr_or_code::<syn::Path>(&input, ADVICE_QUERY_KEY, "crate::plonk::AdviceQuery")?;
    let instance_query =
        find_attr_or_code::<syn::Path>(&input, INSTANCE_QUERY_KEY, "crate::plonk::InstanceQuery")?;
    let challenge =
        find_attr_or_code::<syn::Path>(&input, CHALLENGE_KEY, "crate::plonk::Challenge")?;
    let name = input.ident;

    Ok(quote! {
        #module :: __impl_expression_support!(#name, #field, #selector, #fixed_query, #advice_query, #instance_query, #challenge);
    })
}
