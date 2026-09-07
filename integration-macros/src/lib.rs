#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

use proc_macro::TokenStream;
use syn::{DeriveInput, ItemFn, parse_macro_input};

mod info_traits;

/// Derive macro for the `SelectorInfo` trait.
#[proc_macro_derive(SelectorInfo, attributes(haloumi))]
pub fn derive_selector_info(input: TokenStream) -> TokenStream {
    match info_traits::derive_selector_info_impl(parse_macro_input!(input as DeriveInput)) {
        Ok(tok) => tok,
        Err(e) => e.to_compile_error(),
    }
    .into()
}
