#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

use proc_macro::TokenStream;
use syn::{DeriveInput, parse_macro_input};

mod attrs;
mod expressions;
mod info_traits;
mod keys;

macro_rules! unwrap_result {
    ($e:expr) => {
        match $e {
            Ok(tok) => tok,
            Err(e) => e.to_compile_error(),
        }
        .into()
    };
}

/// Derive macro for the `SelectorInfo` trait.
#[proc_macro_derive(SelectorInfo, attributes(haloumi))]
pub fn derive_selector_info(input: TokenStream) -> TokenStream {
    unwrap_result!(info_traits::derive_selector_info_impl(parse_macro_input!(
        input as DeriveInput
    )))
}

/// Derive macro for the `ChallengeInfo` trait.
#[proc_macro_derive(ChallengeInfo, attributes(haloumi))]
pub fn derive_challenge_info(input: TokenStream) -> TokenStream {
    unwrap_result!(info_traits::derive_challenge_info_impl(parse_macro_input!(
        input as DeriveInput
    )))
}

/// Derive macro for the `QueryInfo` trait.
#[proc_macro_derive(QueryInfo, attributes(haloumi, kind))]
pub fn derive_query_info(input: TokenStream) -> TokenStream {
    unwrap_result!(info_traits::derive_query_info_impl(parse_macro_input!(
        input as DeriveInput
    )))
}

/// Derive macro for the `CreateQuery` trait.
#[proc_macro_derive(CreateQuery, attributes(haloumi, field, expression, rotation, new))]
pub fn derive_create_query(input: TokenStream) -> TokenStream {
    unwrap_result!(info_traits::derive_create_query_impl(parse_macro_input!(
        input as DeriveInput
    )))
}

/// Derive macro for the `GateInfo` trait.
#[proc_macro_derive(GateInfo, attributes(haloumi, field, expression))]
pub fn derive_gate_info(input: TokenStream) -> TokenStream {
    unwrap_result!(info_traits::derive_gate_info_impl(parse_macro_input!(
        input as DeriveInput
    )))
}

/// Derive macro for the `ConstraintSystemInfo` trait.
#[proc_macro_derive(ConstraintSystemInfo, attributes(haloumi, field, expression))]
pub fn derive_constraint_system_info(input: TokenStream) -> TokenStream {
    unwrap_result!(info_traits::derive_constraint_system_info_impl(
        parse_macro_input!(input as DeriveInput)
    ))
}

/// Derive macro for the `Expression` traits.
#[proc_macro_derive(
    Expression,
    attributes(
        haloumi,
        field,
        selector,
        fixed_query,
        advice_query,
        instance_query,
        challenge
    )
)]
pub fn derive_expression_traits(input: TokenStream) -> TokenStream {
    unwrap_result!(expressions::derive_expression_traits_impl(
        parse_macro_input!(input as DeriveInput)
    ))
}
