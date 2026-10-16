//! Proc macros for the `e2e` testing framework.

#![deny(missing_docs)]

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{
    Attribute, Error, Expr, FnArg, ItemFn, MetaNameValue, Pat, Result, Token,
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    spanned::Spanned,
};

/// Generates a standard test that runs the Haloumi CLI before executing the annotated body.
///
/// The attribute requires `target = <expr>` and accepts optional `args = <expr>` and
/// `copy = <expr>` arguments, which default to `[]` and `true`, respectively. The function
/// takes either one typed result parameter or a typed `Test` parameter followed by a typed result
/// parameter.
#[proc_macro_attribute]
pub fn test(attr: TokenStream, item: TokenStream) -> TokenStream {
    match test_impl(
        parse_macro_input!(attr as TestArgs),
        parse_macro_input!(item as ItemFn),
    ) {
        Ok(tokens) => tokens.into(),
        Err(error) => error.into_compile_error().into(),
    }
}

struct TestArgs {
    target: Expr,
    args: Expr,
    copy: Expr,
}

impl Parse for TestArgs {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let values = Punctuated::<MetaNameValue, Token![,]>::parse_terminated(input)?;
        let mut target = None;
        let mut args = None;
        let mut copy = None;

        for value in values {
            let Some(key) = value.path.get_ident() else {
                return Err(Error::new_spanned(
                    value.path,
                    "expected `target`, `args`, or `copy`",
                ));
            };

            match key.to_string().as_str() {
                "target" => set_once(&mut target, value.value, key, "target")?,
                "args" => set_once(&mut args, value.value, key, "args")?,
                "copy" => set_once(&mut copy, value.value, key, "copy")?,
                _ => {
                    return Err(Error::new_spanned(
                        key,
                        "unsupported e2e test argument; expected `target`, `args`, or `copy`",
                    ));
                }
            }
        }

        Ok(Self {
            target: target.ok_or_else(|| Error::new(input.span(), "missing `target` argument"))?,
            args: args.unwrap_or_else(|| syn::parse_quote!([])),
            copy: copy.unwrap_or_else(|| syn::parse_quote!(true)),
        })
    }
}

fn set_once(slot: &mut Option<Expr>, value: Expr, key: &syn::Ident, name: &str) -> Result<()> {
    if slot.replace(value).is_some() {
        Err(Error::new_spanned(
            key,
            format!("duplicate `{name}` argument"),
        ))
    } else {
        Ok(())
    }
}

fn test_impl(args: TestArgs, mut function: ItemFn) -> Result<TokenStream2> {
    reject_existing_test_attribute(&function.attrs)?;
    let closure_args = closure_args(&function.sig.inputs)?;
    function.sig.inputs.clear();

    let body = function.block;
    let target = args.target;
    let command_args = args.args;
    let copy = args.copy;
    function.block = Box::new(syn::parse2(quote! {{
        e2e::__test_impl!(#target, #command_args, #copy, |#closure_args| #body)
    }})?);
    function.attrs.push(syn::parse_quote!(#[test]));

    Ok(quote!(#function))
}

fn reject_existing_test_attribute(attrs: &[Attribute]) -> Result<()> {
    if let Some(attr) = attrs.iter().find(|attr| attr.path().is_ident("test")) {
        Err(Error::new_spanned(
            attr,
            "`#[e2e::test]` already generates `#[test]`",
        ))
    } else {
        Ok(())
    }
}

fn closure_args(inputs: &Punctuated<FnArg, Token![,]>) -> Result<TokenStream2> {
    let input_span = inputs.span();
    let mut inputs = inputs.iter();
    let first = inputs.next();
    let second = inputs.next();
    let third = inputs.next();

    match (first, second, third) {
        (Some(FnArg::Typed(result)), None, None) => {
            let (result_name, result_type) = parameter_name_and_type(result, "result")?;
            Ok(quote!(#result_name: #result_type))
        }
        (Some(FnArg::Typed(test)), Some(FnArg::Typed(result)), None) => {
            let (test_name, test_type) = parameter_name_and_type(test, "Test")?;
            let (result_name, result_type) = parameter_name_and_type(result, "result")?;
            Ok(quote!(#test_name: #test_type, #result_name: #result_type))
        }
        (Some(FnArg::Receiver(receiver)), _, _) => Err(Error::new_spanned(
            receiver,
            "`#[e2e::test]` does not support receiver parameters",
        )),
        _ => Err(Error::new(
            input_span,
            "`#[e2e::test]` functions must take one result parameter or `Test` plus a result parameter",
        )),
    }
}

fn parameter_name_and_type<'a>(
    parameter: &'a syn::PatType,
    role: &str,
) -> Result<(&'a syn::Ident, &'a syn::Type)> {
    let Pat::Ident(pattern) = &*parameter.pat else {
        return Err(Error::new_spanned(
            &parameter.pat,
            format!("the {role} parameter must be an identifier"),
        ));
    };
    Ok((&pattern.ident, &parameter.ty))
}
