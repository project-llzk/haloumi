//! Implementation of the `group` attribute macro.

use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{
    Attribute, Block, Expr, FnArg, Ident, ItemFn, Lifetime, Pat, PatType, ReturnType, Visibility,
    parse2,
    spanned::Spanned,
    visit_mut::{self, VisitMut},
};

use crate::{attrs::get_haloumi_integration_module, parse::group_args::GroupArgs};

const INPUT_ATTR: &str = "input";
const OUTPUT_ATTR: &str = "output";
const LAYOUTER_ATTR: &str = "layouter";

/// Internal implementation of [`crate::group`].
pub fn group_impl(input_fn: ItemFn, _: GroupArgs) -> syn::Result<TokenStream> {
    validate_signature(&input_fn)?;
    let fn_ident = &input_fn.sig.ident;
    let (impl_generics, _, where_clause) = input_fn.sig.generics.split_for_impl();
    let group_ident = format_ident!("__{fn_ident}__group");
    let return_label = Lifetime::new("'__group_return", Span::mixed_site());
    let integration = get_haloumi_integration_module()?;

    let (layouter, io) = locate_attributes(&input_fn)?;
    let layouter = select_layouter(&layouter, input_fn.sig.span())?;
    let (input_annotations, output_annotations) =
        generate_io_annotations(io, &group_ident, &integration)?;
    let cleaned_inputs = clean_inputs(input_fn.sig.inputs.iter());
    let mut body = input_fn.block.clone();
    ReturnRewriter::new(return_label.clone()).visit_block_mut(&mut body);

    Ok(emit_wrapped_fn(
        &input_fn.attrs,
        &input_fn.vis,
        &input_fn.sig.safety,
        &input_fn.sig.abi,
        fn_ident,
        cleaned_inputs,
        &input_fn.sig.output,
        layouter,
        &group_ident,
        input_annotations.into_iter(),
        output_annotations.into_iter(),
        &body,
        &return_label,
        &integration,
        &impl_generics,
        where_clause,
    ))
}

fn validate_signature(input_fn: &ItemFn) -> syn::Result<()> {
    if let Some(asyncness) = input_fn.sig.asyncness {
        return Err(syn::Error::new_spanned(
            asyncness,
            "async functions are not supported by #[group]",
        ));
    }
    if let Some(constness) = input_fn.sig.constness {
        return Err(syn::Error::new_spanned(
            constness,
            "const functions are not supported by #[group]",
        ));
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn emit_wrapped_fn(
    fn_attrs: &[Attribute],
    vis: &Visibility,
    safety: &syn::Safety,
    abi: &Option<syn::Abi>,
    fn_ident: &Ident,
    cleaned_inputs: impl Iterator<Item = FnArg>,
    output: &ReturnType,
    layouter: Ident,
    group_ident: &Ident,
    input_annotations: impl Iterator<Item = TokenStream>,
    output_annotations: impl Iterator<Item = TokenStream>,
    user_block: &Block,
    return_label: &Lifetime,
    integration: &Ident,
    impl_generics: &syn::ImplGenerics,
    where_clause: Option<&syn::WhereClause>,
) -> TokenStream {
    quote! {
        #(#fn_attrs)*
        #vis #safety #abi fn #fn_ident #impl_generics (#(#cleaned_inputs, )*) #output #where_clause {
            #integration::__group!(
                #layouter,
                || stringify!(#fn_ident),
                #integration::core::default_group_key!(),
                |#layouter, #group_ident| {
                    #(#input_annotations)*
                    let inner_result = (|| #return_label: #user_block)();
                    #(#output_annotations)*
                    #integration::__annotate_output_cells!(#group_ident, inner_result);
                    inner_result
                }
            )
        }
    }
}

type AnnotatedPat<'a> = (ArgAttributes, &'a PatType);

fn locate_attributes(
    input_fn: &ItemFn,
) -> syn::Result<(Vec<AnnotatedPat<'_>>, Vec<AnnotatedPat<'_>>)> {
    input_fn
        .sig
        .inputs
        .iter()
        .filter_map(ArgAttributes::try_from_arg)
        .collect::<syn::Result<Vec<_>>>()
        .map(|attrs| {
            attrs
                .into_iter()
                .partition(|(attr, _)| matches!(attr, ArgAttributes::Layouter))
        })
}

fn select_layouter(layouters: &[AnnotatedPat], span: Span) -> syn::Result<Ident> {
    match layouters {
        [] => Ok(format_ident!("layouter")),
        [(_, pat)] => match &*pat.pat {
            Pat::Ident(ident) => Ok(ident.ident.clone()),
            _ => Err(syn::Error::new(
                span,
                "argument annotated with #[layouter] must be an identifier",
            )),
        },
        _ => Err(syn::Error::new(
            span,
            "more than one #[layouter] annotation is not allowed",
        )),
    }
}

fn generate_io_annotations(
    io: Vec<AnnotatedPat>,
    group_ident: &Ident,
    integration: &Ident,
) -> syn::Result<(Vec<TokenStream>, Vec<TokenStream>)> {
    io.into_iter().try_fold(
        (Vec::new(), Vec::new()),
        |(mut inputs, mut outputs), (attr, pat)| -> syn::Result<_> {
            if let Some(input) = attr.emit_input_code(&pat.pat, group_ident, integration) {
                inputs.push(input?);
            }
            if let Some(output) = attr.emit_output_code(&pat.pat, group_ident, integration) {
                outputs.push(output?);
            }
            Ok((inputs, outputs))
        },
    )
}

fn clean_inputs<'a>(inputs: impl Iterator<Item = &'a FnArg>) -> impl Iterator<Item = FnArg> {
    inputs.cloned().map(|input| match input {
        FnArg::Typed(mut pat_type) => {
            pat_type.attrs.retain(|attr| {
                attr.path()
                    .get_ident()
                    .map(|ident| {
                        ident != INPUT_ATTR && ident != OUTPUT_ATTR && ident != LAYOUTER_ATTR
                    })
                    .unwrap_or(true)
            });
            FnArg::Typed(pat_type)
        }
        other => other,
    })
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum ArgAttributes {
    Input,
    Output,
    InputOutput,
    Layouter,
}

impl ArgAttributes {
    fn try_combine(self, other: Self) -> Result<Self, (Self, Self)> {
        match (self, other) {
            (Self::Input, Self::Input) => Ok(Self::Input),
            (Self::Output, Self::Output) => Ok(Self::Output),
            (Self::Input | Self::Output | Self::InputOutput, Self::InputOutput)
            | (Self::InputOutput, Self::Input | Self::Output)
            | (Self::Input, Self::Output)
            | (Self::Output, Self::Input) => Ok(Self::InputOutput),
            (Self::Layouter, Self::Layouter) => Ok(Self::Layouter),
            (Self::Layouter, _) | (_, Self::Layouter) => Err((self, other)),
        }
    }

    fn from_attr(attr: &Attribute) -> Option<Self> {
        match attr.path().get_ident()?.to_string().as_str() {
            INPUT_ATTR => Some(Self::Input),
            OUTPUT_ATTR => Some(Self::Output),
            LAYOUTER_ATTR => Some(Self::Layouter),
            _ => None,
        }
    }

    fn try_from_attrs(attrs: &[Attribute], span: Span) -> Option<syn::Result<Self>> {
        attrs
            .iter()
            .filter_map(Self::from_attr)
            .try_fold(None::<Self>, |acc, attr| {
                Ok(Some(match acc {
                    Some(acc) => acc.try_combine(attr).map_err(|(lhs, rhs)| {
                        syn::Error::new(
                            span,
                            format!("incompatible attributes '{lhs}' and '{rhs}'"),
                        )
                    })?,
                    None => attr,
                }))
            })
            .transpose()
    }

    fn try_from_arg(arg: &FnArg) -> Option<syn::Result<(Self, &PatType)>> {
        let FnArg::Typed(pat) = arg else {
            return None;
        };
        Some(ArgAttributes::try_from_attrs(&pat.attrs, pat.span())?.map(|attr| (attr, pat)))
    }

    fn emit_input_code(
        self,
        pat: &Pat,
        group_ident: &Ident,
        integration: &Ident,
    ) -> Option<syn::Result<TokenStream>> {
        match self {
            Self::Input | Self::InputOutput => Some(annotation_value(pat).map(|value| {
                quote! { #integration::__annotate_input_cells!(#group_ident, #value); }
            })),
            Self::Output | Self::Layouter => None,
        }
    }

    fn emit_output_code(
        self,
        pat: &Pat,
        group_ident: &Ident,
        integration: &Ident,
    ) -> Option<syn::Result<TokenStream>> {
        match self {
            Self::Output | Self::InputOutput => Some(annotation_value(pat).map(|value| {
                quote! { #integration::__annotate_output_cells!(#group_ident, #value); }
            })),
            Self::Input | Self::Layouter => None,
        }
    }
}

fn annotation_value(pat: &Pat) -> syn::Result<TokenStream> {
    let mut bindings = vec![];
    collect_bindings(pat, &mut bindings);
    match bindings.as_slice() {
        [] => Err(syn::Error::new_spanned(
            pat,
            "annotated input and output patterns must bind at least one identifier",
        )),
        [binding] => Ok(quote! { #binding }),
        bindings => Ok(quote! { (#(&#bindings,)*) }),
    }
}

fn collect_bindings(pat: &Pat, bindings: &mut Vec<Ident>) {
    match pat {
        Pat::Ident(pat) => bindings.push(pat.ident.clone()),
        Pat::Or(pat) => pat
            .cases
            .iter()
            .for_each(|pat| collect_bindings(pat, bindings)),
        Pat::Paren(pat) => collect_bindings(&pat.pat, bindings),
        Pat::Reference(pat) => collect_bindings(&pat.pat, bindings),
        Pat::Slice(pat) => pat
            .elems
            .iter()
            .for_each(|pat| collect_bindings(pat, bindings)),
        Pat::Struct(pat) => pat
            .fields
            .iter()
            .for_each(|field| collect_bindings(&field.pat, bindings)),
        Pat::Tuple(pat) => pat
            .elems
            .iter()
            .for_each(|pat| collect_bindings(pat, bindings)),
        Pat::TupleStruct(pat) => pat
            .elems
            .iter()
            .for_each(|pat| collect_bindings(pat, bindings)),
        Pat::Type(pat) => collect_bindings(&pat.pat, bindings),
        _ => {}
    }
}

struct ReturnRewriter {
    label: Lifetime,
}

impl ReturnRewriter {
    fn new(label: Lifetime) -> Self {
        Self { label }
    }
}

impl VisitMut for ReturnRewriter {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        match expr {
            Expr::Return(return_expr) => {
                let label = &self.label;
                let value = return_expr
                    .expr
                    .as_deref()
                    .cloned()
                    .unwrap_or_else(|| parse2(quote! { () }).unwrap());
                *expr = parse2(quote! { break #label #value }).unwrap();
            }
            Expr::Closure(_) | Expr::Async(_) => {}
            _ => visit_mut::visit_expr_mut(self, expr),
        }
    }

    fn visit_item_mut(&mut self, _: &mut syn::Item) {}
}

impl std::fmt::Display for ArgAttributes {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Input => "#[input]",
            Self::Output => "#[output]",
            Self::InputOutput => "#[input] #[output]",
            Self::Layouter => "#[layouter]",
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use macro_expand::Context;
    use similar_asserts::assert_eq;

    fn transform(input: &str) -> String {
        let mut ctx = Context::new();
        ctx.register_proc_macro_attribute("group".into(), |input, attr| {
            group_impl(syn::parse2(input).unwrap(), syn::parse2(attr).unwrap()).unwrap()
        });
        prettyplease::unparse(&syn2::parse2(ctx.transform(input.parse().unwrap())).unwrap())
    }

    fn formatted(input: &str) -> String {
        prettyplease::unparse(&syn2::parse_str(input).unwrap())
    }

    fn do_test(input: &str, expected: &str) {
        assert_eq!(transform(input), formatted(expected));
    }

    fn do_error(input: &str, expected: &str) {
        let error = group_impl(syn::parse_str(input).unwrap(), GroupArgs).unwrap_err();
        assert_eq!(error.to_string(), expected);
    }

    #[test]
    fn wraps_a_function_and_annotates_inputs_and_output() {
        do_test(
            r#"
                #[group]
                fn foo(layouter: &mut impl Layouter<F>, #[input] inputs: &[AssignedNative<F>]) -> Result<AssignedNative<F>, Error> {
                    inputs.iter().try_fold(F::ZERO, |acc, i| self.bar(layouter, i, acc))
                }
                "#,
            r#"
            fn foo(layouter: &mut impl Layouter<F>, inputs: &[AssignedNative<F>],) -> Result<AssignedNative<F>, Error> {
                haloumi_integration::__group!(layouter, || stringify!(foo), haloumi_integration::core::default_group_key!(), |layouter, __foo__group| {
                    haloumi_integration::__annotate_input_cells!(__foo__group, inputs);
                    let inner_result = (|| '__group_return: { inputs.iter().try_fold(F::ZERO, |acc, i| self.bar(layouter, i, acc)) })();
                    haloumi_integration::__annotate_output_cells!(__foo__group, inner_result);
                    inner_result
                })
            }
            "#,
        );
    }

    #[test]
    fn supports_generic_functions() {
        do_test(
            r#"
                #[group]
                fn foo<const M: usize>(layouter: &mut impl Layouter<F>, #[input] inputs: &[AssignedNative<F>; M]) -> Result<AssignedNative<F>, Error> {
                    inputs.iter().try_fold(F::ZERO, |acc, i| self.bar(layouter, i, acc))
                }
                "#,
            r#"
            fn foo<const M: usize>(layouter: &mut impl Layouter<F>, inputs: &[AssignedNative<F>; M],) -> Result<AssignedNative<F>, Error> {
                haloumi_integration::__group!(layouter, || stringify!(foo), haloumi_integration::core::default_group_key!(), |layouter, __foo__group| {
                    haloumi_integration::__annotate_input_cells!(__foo__group, inputs);
                    let inner_result = (|| '__group_return: { inputs.iter().try_fold(F::ZERO, |acc, i| self.bar(layouter, i, acc)) })();
                    haloumi_integration::__annotate_output_cells!(__foo__group, inner_result);
                    inner_result
                })
            }
            "#,
        );
    }

    #[test]
    fn annotates_output_parameters_after_the_function_body() {
        do_test(
            r#"
                #[group]
                fn foo(
                    layouter: &mut impl Layouter<F>,
                    #[input] input: &AssignedNative<F>,
                    #[output] output: &mut Option<AssignedNative<F>>,
                    #[input] #[output] input_output: &mut Option<AssignedNative<F>>,
                ) -> Result<(), Error> {
                    *output = Some(self.bar(layouter, input)?);
                    *input_output = Some(self.bar(layouter, input)?);
                    Ok(())
                }
                "#,
            r#"
            fn foo(
                layouter: &mut impl Layouter<F>,
                input: &AssignedNative<F>,
                output: &mut Option<AssignedNative<F>>,
                input_output: &mut Option<AssignedNative<F>>,
            ) -> Result<(), Error> {
                haloumi_integration::__group!(layouter, || stringify!(foo), haloumi_integration::core::default_group_key!(), |layouter, __foo__group| {
                    haloumi_integration::__annotate_input_cells!(__foo__group, input);
                    haloumi_integration::__annotate_input_cells!(__foo__group, input_output);
                    let inner_result = (|| '__group_return: {
                        *output = Some(self.bar(layouter, input)?);
                        *input_output = Some(self.bar(layouter, input)?);
                        Ok(())
                    })();
                    haloumi_integration::__annotate_output_cells!(__foo__group, output);
                    haloumi_integration::__annotate_output_cells!(__foo__group, input_output);
                    haloumi_integration::__annotate_output_cells!(__foo__group, inner_result);
                    inner_result
                })
            }
            "#,
        );
    }

    #[test]
    fn annotations_use_the_binding_not_the_mut_pattern() {
        do_test(
            r#"
                #[group]
                fn foo(layouter: &mut impl Layouter<F>, #[input] mut input: AssignedNative<F>, #[output] mut output: AssignedNative<F>) -> Result<AssignedNative<F>, Error> {
                    output = input.clone();
                    Ok(input)
                }
            "#,
            r#"
            fn foo(layouter: &mut impl Layouter<F>, mut input: AssignedNative<F>, mut output: AssignedNative<F>,) -> Result<AssignedNative<F>, Error> {
                haloumi_integration::__group!(layouter, || stringify!(foo), haloumi_integration::core::default_group_key!(), |layouter, __foo__group| {
                    haloumi_integration::__annotate_input_cells!(__foo__group, input);
                    let inner_result = (|| '__group_return: {
                        output = input.clone();
                        Ok(input)
                    })();
                    haloumi_integration::__annotate_output_cells!(__foo__group, output);
                    haloumi_integration::__annotate_output_cells!(__foo__group, inner_result);
                    inner_result
                })
            }
            "#,
        );
    }

    #[test]
    fn annotations_borrow_destructured_bindings() {
        do_test(
            r#"
                #[group]
                fn foo(layouter: &mut impl Layouter<F>, #[input] (left, right): (AssignedNative<F>, AssignedNative<F>)) -> Result<(), Error> {
                    let _ = (left, right);
                    Ok(())
                }
            "#,
            r#"
            fn foo(layouter: &mut impl Layouter<F>, (left, right): (AssignedNative<F>, AssignedNative<F>),) -> Result<(), Error> {
                haloumi_integration::__group!(layouter, || stringify!(foo), haloumi_integration::core::default_group_key!(), |layouter, __foo__group| {
                    haloumi_integration::__annotate_input_cells!(__foo__group, (&left, &right,));
                    let inner_result = (|| '__group_return: {
                        let _ = (left, right);
                        Ok(())
                    })();
                    haloumi_integration::__annotate_output_cells!(__foo__group, inner_result);
                    inner_result
                })
            }
            "#,
        );
    }

    #[test]
    fn annotations_borrow_structured_bindings() {
        do_test(
            r#"
                #[group]
                fn foo(layouter: &mut impl Layouter<F>, #[input] Pair { left, right }: Pair) -> Result<(), Error> {
                    let _ = (left, right);
                    Ok(())
                }
            "#,
            r#"
            fn foo(layouter: &mut impl Layouter<F>, Pair { left, right }: Pair,) -> Result<(), Error> {
                haloumi_integration::__group!(layouter, || stringify!(foo), haloumi_integration::core::default_group_key!(), |layouter, __foo__group| {
                    haloumi_integration::__annotate_input_cells!(__foo__group, (&left, &right,));
                    let inner_result = (|| '__group_return: {
                        let _ = (left, right);
                        Ok(())
                    })();
                    haloumi_integration::__annotate_output_cells!(__foo__group, inner_result);
                    inner_result
                })
            }
            "#,
        );
    }

    #[test]
    fn rejects_annotated_patterns_without_bindings() {
        do_error(
            r#"
                    fn foo(layouter: &mut impl Layouter<F>, #[input] _: AssignedNative<F>) -> Result<(), Error> {
                        Ok(())
                    }
            "#,
            "annotated input and output patterns must bind at least one identifier",
        );
    }

    #[test]
    fn preserves_unsafe_extern_function_qualifiers() {
        do_test(
            r#"
                #[group]
                unsafe extern "C" fn foo(layouter: &mut impl Layouter<F>) -> Result<(), Error> {
                    let _ = layouter;
                    Ok(())
                }
            "#,
            r#"
            unsafe extern "C" fn foo(layouter: &mut impl Layouter<F>,) -> Result<(), Error> {
                haloumi_integration::__group!(layouter, || stringify!(foo), haloumi_integration::core::default_group_key!(), |layouter, __foo__group| {
                    let inner_result = (|| '__group_return: {
                        let _ = layouter;
                        Ok(())
                    })();
                    haloumi_integration::__annotate_output_cells!(__foo__group, inner_result);
                    inner_result
                })
            }
            "#,
        );
    }

    #[test]
    fn rejects_async_grouped_functions() {
        do_error(
            r#"
                    async fn foo(layouter: &mut impl Layouter<F>) -> Result<(), Error> {
                        let _ = layouter;
                        Ok(())
                    }
            "#,
            "async functions are not supported by #[group]",
        );
    }

    #[test]
    fn rejects_const_grouped_functions() {
        do_error(
            r#"
                    const fn foo(layouter: &mut impl Layouter<F>) -> Result<(), Error> {
                        let _ = layouter;
                        Ok(())
                    }
            "#,
            "const functions are not supported by #[group]",
        );
    }
}
