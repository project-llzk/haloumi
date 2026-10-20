//! Proc macros for the `e2e` testing framework.

#![deny(missing_docs)]

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::{
    Attribute, Error, Expr, FnArg, ItemFn, MetaNameValue, Pat, Result, Token,
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    spanned::Spanned,
};

/// Generates a standard test that runs the Haloumi CLI before executing the annotated body.
///
/// The attribute requires `target = <expr>` and accepts optional `args = <expr>`,
/// `copy = <expr>`, and `before = <identifier>` arguments. The first two default to `[]` and
/// `true`, respectively. The function takes either one typed result parameter or a typed `Test`
/// parameter followed by a typed result parameter. When `before` is present, parameters after the
/// result receive its return value (or the elements of its returned tuple).
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
    before: Option<syn::Ident>,
}

impl Parse for TestArgs {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let values = Punctuated::<MetaNameValue, Token![,]>::parse_terminated(input)?;
        let mut target = None;
        let mut args = None;
        let mut copy = None;
        let mut before = None;

        for value in values {
            let Some(key) = value.path.get_ident() else {
                return Err(Error::new_spanned(
                    value.path,
                    "expected `target`, `args`, `copy`, or `before`",
                ));
            };

            match key.to_string().as_str() {
                "target" => set_once(&mut target, value.value, key, "target")?,
                "args" => set_once(&mut args, value.value, key, "args")?,
                "copy" => set_once(&mut copy, value.value, key, "copy")?,
                "before" => set_once(&mut before, value.value, key, "before")?,
                _ => {
                    return Err(Error::new_spanned(
                        key,
                        "unsupported e2e test argument; expected `target`, `args`, `copy`, or `before`",
                    ));
                }
            }
        }

        Ok(Self {
            target: target.ok_or_else(|| Error::new(input.span(), "missing `target` argument"))?,
            args: args.unwrap_or_else(|| syn::parse_quote!([])),
            copy: copy.unwrap_or_else(|| syn::parse_quote!(true)),
            before: before
                .map(|before| match before {
                    Expr::Path(path) if path.qself.is_none() && path.path.segments.len() == 1 => {
                        Ok(path.path.segments.into_iter().next().unwrap().ident)
                    }
                    before => Err(Error::new_spanned(before, "`before` must be an identifier")),
                })
                .transpose()?,
        })
    }
}

fn set_once<T>(slot: &mut Option<T>, value: T, key: &syn::Ident, name: &str) -> Result<()> {
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
    let closure_args = closure_args(&function.sig.inputs, args.before.is_some())?;
    function.sig.inputs.clear();

    let body = function.block;
    let target = args.target;
    let command_args = args.args;
    let copy = args.copy;
    let invocation = if let Some(before) = args.before {
        quote!(e2e::__test_impl!(#target, #command_args, #copy, #before, |#closure_args| #body))
    } else {
        quote!(e2e::__test_impl!(#target, #command_args, #copy, |#closure_args| #body))
    };
    function.block = Box::new(syn::parse2(quote! {{ #invocation }})?);
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

fn closure_args(inputs: &Punctuated<FnArg, Token![,]>, has_before: bool) -> Result<TokenStream2> {
    if has_before {
        before_closure_args(inputs)
    } else {
        standard_closure_args(inputs)
    }
}

fn standard_closure_args(inputs: &Punctuated<FnArg, Token![,]>) -> Result<TokenStream2> {
    let input_span = inputs.span();
    let mut inputs = inputs.iter();
    let first = inputs.next();
    let second = inputs.next();
    let third = inputs.next();

    match (first, second, third) {
        (Some(FnArg::Typed(result)), None, None) => result_parameter(result),
        (Some(FnArg::Typed(test)), Some(FnArg::Typed(result)), None) => {
            let (test_name, test_type) = parameter_name_and_type(test, "Test")?;
            let result = result_parameter(result)?;
            Ok(quote!(#test_name: #test_type, #result))
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

fn before_closure_args(inputs: &Punctuated<FnArg, Token![,]>) -> Result<TokenStream2> {
    let input_span = inputs.span();
    let mut parameters = inputs.iter();
    let Some(first) = parameters.next() else {
        return Err(Error::new(
            input_span,
            "`#[e2e::test]` functions must take a result parameter",
        ));
    };
    let FnArg::Typed(first) = first else {
        return Err(Error::new_spanned(
            first,
            "`#[e2e::test]` does not support receiver parameters",
        ));
    };

    let (test, result) = if is_test_parameter(first) {
        let Some(result) = parameters.next() else {
            return Err(Error::new_spanned(
                first,
                "a `Test` parameter must be followed by a result parameter",
            ));
        };
        let FnArg::Typed(result) = result else {
            return Err(Error::new_spanned(
                result,
                "`#[e2e::test]` does not support receiver parameters",
            ));
        };
        let (test_name, test_type) = parameter_name_and_type(first, "Test")?;
        (quote!(#test_name: #test_type), result)
    } else {
        (quote!(__e2e_test: e2e::Test), first)
    };
    let result = result_parameter(result)?;
    let before_parameters = parameters
        .enumerate()
        .map(|(index, parameter)| match parameter {
            FnArg::Typed(parameter) => parameter_with_wildcard(
                parameter,
                format_ident!("__e2e_before_{index}"),
                "before-hook",
            ),
            FnArg::Receiver(receiver) => Err(Error::new_spanned(
                receiver,
                "`#[e2e::test]` does not support receiver parameters",
            )),
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(quote!(#test, #result #(, #before_parameters)*))
}

fn is_test_parameter(parameter: &syn::PatType) -> bool {
    matches!(&*parameter.ty, syn::Type::Path(path) if path.qself.is_none() && path.path.segments.last().is_some_and(|segment| segment.ident == "Test"))
}

fn result_parameter(parameter: &syn::PatType) -> Result<TokenStream2> {
    parameter_with_wildcard(parameter, format_ident!("__e2e_result"), "result")
}

fn parameter_with_wildcard(
    parameter: &syn::PatType,
    wildcard_name: syn::Ident,
    role: &str,
) -> Result<TokenStream2> {
    let result_type = &parameter.ty;
    match &*parameter.pat {
        Pat::Ident(pattern) => {
            let result_name = &pattern.ident;
            Ok(quote!(#result_name: #result_type))
        }
        Pat::Wild(_) => Ok(quote!(#wildcard_name: #result_type)),
        _ => Err(Error::new_spanned(
            &parameter.pat,
            format!("the {role} parameter must be an identifier or `_`"),
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
