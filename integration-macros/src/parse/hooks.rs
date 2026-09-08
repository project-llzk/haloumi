use std::collections::HashSet;

use crate::keys::{DEFAULT_CELL_TYPE, DEFAULT_ERROR_TYPE};
use proc_macro2::Span;
use quote::format_ident;
use syn::{
    Ident, Path, PathSegment, Token, Type, TypePath,
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
};

const F_PARAM: &str = "F";
const CELL_PARAM: &str = "cell";
const ERROR_PARAM: &str = "error";

#[derive(Copy, Clone)]
enum HookParams {
    Field(Span),
    Cell(Span),
    Error(Span),
}

impl HookParams {
    fn name(&self) -> &str {
        match self {
            HookParams::Field(_) => F_PARAM,
            HookParams::Cell(_) => CELL_PARAM,
            HookParams::Error(_) => ERROR_PARAM,
        }
    }

    fn span(&self) -> Span {
        match self {
            HookParams::Field(span) | HookParams::Cell(span) | HookParams::Error(span) => *span,
        }
    }
}

impl Parse for HookParams {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let id: Ident = input.parse()?;
        let span = id.span();
        match id.to_string().as_str() {
            F_PARAM => Ok(Self::Field(span)),
            CELL_PARAM => Ok(Self::Cell(span)),
            ERROR_PARAM => Ok(Self::Error(span)),
            _ => Err(syn::Error::new(
                span,
                "expected parameters: {F_PARAM}, {CELL_PARAM}",
            )),
        }
    }
}

impl std::fmt::Display for HookParams {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl quote::ToTokens for HookParams {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        Ident::new(self.name(), self.span()).to_tokens(tokens);
    }
}

impl PartialEq for HookParams {
    fn eq(&self, other: &Self) -> bool {
        core::mem::discriminant(self) == core::mem::discriminant(other)
    }
}

impl Eq for HookParams {}

impl std::hash::Hash for HookParams {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
    }
}

pub struct Hooks {
    field: Option<Ident>,
    cell: Option<Path>,
    error: Option<Path>,
}

impl Hooks {
    pub fn field(&self) -> Type {
        let path = Path::from(self.field.clone().unwrap_or_else(|| format_ident!("F")));
        Type::Path(TypePath {
            attrs: vec![],
            qself: None,
            path,
        })
    }

    pub fn cell(&self) -> Type {
        let path = self.cell.clone().unwrap_or_else(|| Path {
            leading_colon: None,
            segments: Punctuated::from_iter(DEFAULT_CELL_TYPE.split("::").into_iter().map(|p| {
                PathSegment {
                    ident: format_ident!("{p}"),
                    arguments: syn::PathArguments::None,
                }
            })),
        });
        Type::Path(TypePath {
            attrs: vec![],
            qself: None,
            path,
        })
    }

    pub fn error(&self) -> Type {
        let path = self.error.clone().unwrap_or_else(|| Path {
            leading_colon: None,
            segments: Punctuated::from_iter(DEFAULT_ERROR_TYPE.split("::").into_iter().map(|p| {
                PathSegment {
                    ident: format_ident!("{p}"),
                    arguments: syn::PathArguments::None,
                }
            })),
        });
        Type::Path(TypePath {
            attrs: vec![],
            qself: None,
            path,
        })
    }
}

impl Parse for Hooks {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut hooks = Hooks {
            field: None,
            cell: None,
            error: None,
        };
        let mut seen = HashSet::<HookParams>::default();

        loop {
            if input.is_empty() {
                break;
            }
            let param: HookParams = input.parse()?;
            if seen.contains(&param) {
                return Err(syn::Error::new_spanned(
                    param,
                    format!("redefinition of parameter {param}"),
                ));
            }
            seen.insert(param);
            let _: Token![=] = input.parse()?;
            match param {
                HookParams::Field(_) => {
                    hooks.field = Some(input.parse()?);
                }
                HookParams::Cell(_) => {
                    hooks.cell = Some(input.parse()?);
                }
                HookParams::Error(_) => {
                    hooks.error = Some(input.parse()?);
                }
            }
            let la = input.lookahead1();
            if la.peek(Token![,]) {
                let _: Token![,] = input.parse()?;
            }
        }
        Ok(hooks)
    }
}
