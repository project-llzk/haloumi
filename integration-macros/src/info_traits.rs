use proc_macro2::TokenStream;
use quote::{ToTokens, format_ident, quote};
use syn::{Data, DataEnum, DeriveInput, Fields, Ident, Index};

const HALOUMI_KEY: &str = "haloumi";
const HALOUMI_INTEGRATION: &str = "haloumi_integration";

fn get_haloumi_integration_module(input: &DeriveInput) -> syn::Result<Ident> {
    input
        .attrs
        .iter()
        .find_map(|attr| attr.path().is_ident(HALOUMI_KEY).then(|| attr.parse_args()))
        .unwrap_or(Ok(format_ident!("{HALOUMI_INTEGRATION}")))
}

/// Internal implementation of [`super::derive_selector_info`].
pub fn derive_selector_info_impl(input: DeriveInput) -> syn::Result<TokenStream> {
    let module = get_haloumi_integration_module(&input)?;
    let name = input.ident;

    Ok(quote! {
        #module :: __impl_selector_info_for_selector(#name);
    })
}
