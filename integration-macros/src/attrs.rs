use crate::keys::{HALOUMI_INTEGRATION, HALOUMI_KEY};
use quote::format_ident;
use syn::{DeriveInput, Ident, parse::Parse, parse_str};

pub fn find_attr<T: Parse>(input: &DeriveInput, key: &str) -> syn::Result<Option<T>> {
    input
        .attrs
        .iter()
        .find_map(|attr| attr.path().is_ident(key).then(|| attr.parse_args()))
        .transpose()
}

pub fn find_attr_or<T: Parse>(input: &DeriveInput, key: &str, default: T) -> syn::Result<T> {
    find_attr(input, key).map(|i| i.unwrap_or(default))
}

pub fn find_attr_or_code<T: Parse>(
    input: &DeriveInput,
    key: &str,
    default: &str,
) -> syn::Result<T> {
    find_attr_or(input, key, parse_str(default).unwrap())
}

pub fn get_attr<T: Parse>(input: &DeriveInput, key: &str) -> syn::Result<T> {
    find_attr(input, key).and_then(|kind| {
        kind.ok_or_else(|| {
            syn::Error::new_spanned(input.clone(), format!("missing attribute: {key}"))
        })
    })
}

pub fn get_haloumi_integration_module(input: &DeriveInput) -> syn::Result<Ident> {
    find_attr_or(input, HALOUMI_KEY, format_ident!("{HALOUMI_INTEGRATION}"))
}
