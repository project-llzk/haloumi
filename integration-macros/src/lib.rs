#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

use proc_macro::TokenStream;
use syn::{DeriveInput, ItemFn, ItemTrait, parse_macro_input};

use crate::parse::{group_args::GroupArgs, hooks::Hooks};

mod attrs;
mod decompose;
mod expressions;
mod groups;
mod info_traits;
mod io;
mod keys;
mod parse;
mod trait_ext;

macro_rules! unwrap_result {
    ($e:expr) => {
        match $e {
            Ok(tok) => tok,
            Err(e) => e.to_compile_error(),
        }
        .into()
    };
}

/// Creates a group annotation around the body of a function.
///
/// The function's `layouter` argument is used to open the group unless another
/// identifier argument is annotated with `#[layouter]`. Arguments annotated
/// with `#[input]` and `#[output]` are annotated with the corresponding group
/// roles, and the function return value is always annotated as an output.
#[proc_macro_attribute]
pub fn group(attr: TokenStream, item: TokenStream) -> TokenStream {
    unwrap_result!(groups::group_impl(
        parse_macro_input!(item as ItemFn),
        parse_macro_input!(attr as GroupArgs)
    ))
}

/// Derive macro for the `SelectorInfo` trait.
#[proc_macro_derive(SelectorInfo)]
pub fn derive_selector_info(input: TokenStream) -> TokenStream {
    unwrap_result!(info_traits::derive_selector_info_impl(parse_macro_input!(
        input as DeriveInput
    )))
}

/// Derive macro for the `ChallengeInfo` trait.
#[proc_macro_derive(ChallengeInfo)]
pub fn derive_challenge_info(input: TokenStream) -> TokenStream {
    unwrap_result!(info_traits::derive_challenge_info_impl(parse_macro_input!(
        input as DeriveInput
    )))
}

/// Derive macro for the `QueryInfo` trait.
#[proc_macro_derive(QueryInfo, attributes(kind))]
pub fn derive_query_info(input: TokenStream) -> TokenStream {
    unwrap_result!(info_traits::derive_query_info_impl(parse_macro_input!(
        input as DeriveInput
    )))
}

/// Derive macro for the `CreateQuery` trait.
#[proc_macro_derive(CreateQuery, attributes(field, expression, rotation, new))]
pub fn derive_create_query(input: TokenStream) -> TokenStream {
    unwrap_result!(info_traits::derive_create_query_impl(parse_macro_input!(
        input as DeriveInput
    )))
}

/// Derive macro for the `GateInfo` trait.
#[proc_macro_derive(GateInfo, attributes(field, expression))]
pub fn derive_gate_info(input: TokenStream) -> TokenStream {
    unwrap_result!(info_traits::derive_gate_info_impl(parse_macro_input!(
        input as DeriveInput
    )))
}

/// Derive macro for the `ConstraintSystemInfo` trait.
#[proc_macro_derive(
    ConstraintSystemInfo,
    attributes(field, expression, instance, advice, fixed, any)
)]
pub fn derive_constraint_system_info(input: TokenStream) -> TokenStream {
    unwrap_result!(info_traits::derive_constraint_system_info_impl(
        parse_macro_input!(input as DeriveInput)
    ))
}

/// Derive macro for the `Expression` traits.
#[proc_macro_derive(
    Expression,
    attributes(field, selector, fixed_query, advice_query, instance_query, challenge)
)]
pub fn derive_expression_traits(input: TokenStream) -> TokenStream {
    unwrap_result!(expressions::derive_expression_traits_impl(
        parse_macro_input!(input as DeriveInput)
    ))
}

/// Derive macro for the `DecomposeIn<Cell>` trait.
///
/// Requires that every inner element implements the trait and unions are
/// currently not supported.
#[proc_macro_derive(DecomposeInCells, attributes(cell, skip))]
pub fn derive_decompose_in_cells(input: TokenStream) -> TokenStream {
    unwrap_result!(decompose::derive_decompose_in_cells_impl(
        parse_macro_input!(input as DeriveInput)
    ))
}

/// Derive macro for the `CellReprSize` trait.
///
/// Only structs are supported. Every field must implement `CellReprSize`.
#[proc_macro_derive(CellReprSize)]
pub fn derive_cell_repr_size(input: TokenStream) -> TokenStream {
    unwrap_result!(io::derive_cell_repr_size_impl(parse_macro_input!(
        input as DeriveInput
    )))
}

/// Derive macro for the extractor-core `LoadFromCells` trait.
///
/// Only structs are supported. The target type must independently implement
/// `CellReprSize`, either manually or through its derive macro.
#[proc_macro_derive(LoadFromCells, attributes(field))]
pub fn derive_load_from_cells(input: TokenStream) -> TokenStream {
    unwrap_result!(io::derive_load_from_cells_impl(parse_macro_input!(
        input as DeriveInput
    )))
}

/// Derive macro for the extractor-core `StoreIntoCells` trait.
///
/// Only structs are supported. The target type must independently implement
/// `CellReprSize`, either manually or through its derive macro.
#[proc_macro_derive(StoreIntoCells, attributes(field))]
pub fn derive_store_into_cells(input: TokenStream) -> TokenStream {
    unwrap_result!(io::derive_store_into_cells_impl(parse_macro_input!(
        input as DeriveInput
    )))
}

/// Macro for patching the `Layouter` trait to require the `RegionsGroupHooks`
/// trait .
#[proc_macro_attribute]
pub fn require_group_hooks(attr: TokenStream, item: TokenStream) -> TokenStream {
    unwrap_result!(trait_ext::require_group_hooks_impl(
        parse_macro_input!(item as ItemTrait),
        parse_macro_input!(attr as Hooks)
    ))
}

/// Derive macro for the `RegionsGroupHooks` trait.
#[proc_macro_derive(RegionsGroupHooks, attributes(error, root, delegate, cell))]
pub fn derive_region_group_hooks(input: TokenStream) -> TokenStream {
    unwrap_result!(trait_ext::derive_region_group_hooks_impl(
        parse_macro_input!(input as DeriveInput)
    ))
}
