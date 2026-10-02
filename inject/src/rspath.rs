//! Rust-style paths for locating attribute-bearing syntax nodes.

use syn::parse::Parser;

use crate::error::Error;

/// A deliberately small Rust-style path language.
#[derive(Debug)]
pub(crate) enum RustPath {
    Normal(Vec<String>),
    TraitImpl {
        self_ty: Vec<String>,
        trait_path: Vec<String>,
        member: String,
    },
}

impl RustPath {
    /// Parses a supported Rust-style target path.
    pub fn parse(source: &str) -> Result<Self, Error> {
        if source.starts_with('<') {
            let (self_ty, rest) = source
                .strip_prefix('<')
                .and_then(|source| source.split_once(" as "))
                .ok_or_else(|| Error::InvalidAttributePath(source.into()))?;
            let (trait_path, member) = rest
                .split_once(">::")
                .ok_or_else(|| Error::InvalidAttributePath(source.into()))?;
            if member.contains("::") || member.is_empty() {
                return Err(Error::InvalidAttributePath(source.into()));
            }
            return Ok(Self::TraitImpl {
                self_ty: parse_segments(self_ty, source)?,
                trait_path: parse_segments(trait_path, source)?,
                member: parse_single_ident(member, source)?,
            });
        }
        Ok(Self::Normal(parse_segments(source, source)?))
    }

    /// Counts matching attribute-bearing nodes in a file's top-level items.
    pub fn count(&self, items: &[syn::Item]) -> usize {
        match self {
            RustPath::Normal(segments) => count_normal(items, segments),
            RustPath::TraitImpl {
                self_ty,
                trait_path,
                member,
            } => count_trait_impl(items, self_ty, trait_path, member),
        }
    }
}

fn parse_segments(source: &str, whole: &str) -> Result<Vec<String>, Error> {
    let path = syn::Path::parse_mod_style
        .parse_str(source)
        .map_err(|_| Error::InvalidAttributePath(whole.into()))?;
    if path.leading_colon.is_some()
        || path.segments.is_empty()
        || path
            .segments
            .iter()
            .any(|segment| !matches!(segment.arguments, syn::PathArguments::None))
    {
        return Err(Error::InvalidAttributePath(whole.into()));
    }
    Ok(path
        .segments
        .into_iter()
        .map(|segment| segment.ident.to_string())
        .collect())
}

fn parse_single_ident(source: &str, whole: &str) -> Result<String, Error> {
    let ident = syn::parse_str::<syn::Ident>(source)
        .map_err(|_| Error::InvalidAttributePath(whole.into()))?;
    Ok(ident.to_string())
}

fn path_matches(ty: &syn::Type, expected: &[String]) -> bool {
    matches!(ty, syn::Type::Path(path) if path.qself.is_none()
    && path.path.leading_colon.is_none()
    && path.path.segments.len() == expected.len()
    && path.path.segments.iter().zip(expected).all(|(segment, expected)| {
        segment.ident == expected && matches!(segment.arguments, syn::PathArguments::None)
    }))
}

fn count_normal(items: &[syn::Item], segments: &[String]) -> usize {
    let Some((head, tail)) = segments.split_first() else {
        return 0;
    };
    items
        .iter()
        .map(|item| match item {
            syn::Item::Mod(item) if item.ident == head => {
                if tail.is_empty() {
                    1
                } else {
                    item.content
                        .as_ref()
                        .map_or(0, |(_, items)| count_normal(items, tail))
                }
            }
            syn::Item::Struct(item) if item.ident == head => {
                count_data_item(&item.fields, &item.generics, items, head, tail)
            }
            syn::Item::Union(item) if item.ident == head => {
                count_named_data_item(&item.fields, &item.generics, items, head, tail)
            }
            syn::Item::Enum(item) if item.ident == head => count_enum(item, items, head, tail),
            syn::Item::Fn(item) if item.sig.ident == head => count_signature(&item.sig, tail),
            syn::Item::Trait(item) if item.ident == head => count_trait(item, tail),
            syn::Item::Type(item) if item.ident == head => count_generics(&item.generics, tail),
            syn::Item::Const(item) if item.ident == head => count_generics(&item.generics, tail),
            syn::Item::Static(item) if item.ident == head && tail.is_empty() => 1,
            syn::Item::TraitAlias(item) if item.ident == head => {
                count_generics(&item.generics, tail)
            }
            syn::Item::ExternCrate(item) if item.ident == head && tail.is_empty() => 1,
            syn::Item::Macro(item)
                if item.ident.as_ref().is_some_and(|ident| ident == head) && tail.is_empty() =>
            {
                1
            }
            _ => 0,
        })
        .sum()
}

fn count_data_item(
    fields: &syn::Fields,
    generics: &syn::Generics,
    scope: &[syn::Item],
    ty: &str,
    tail: &[String],
) -> usize {
    if tail.is_empty() {
        return 1;
    }
    count_fields(fields, tail)
        + count_generics(generics, tail)
        + count_inherent_impl(scope, ty, tail)
}

fn count_named_data_item(
    fields: &syn::FieldsNamed,
    generics: &syn::Generics,
    scope: &[syn::Item],
    ty: &str,
    tail: &[String],
) -> usize {
    if tail.is_empty() {
        return 1;
    }
    count_named_fields(fields, tail)
        + count_generics(generics, tail)
        + count_inherent_impl(scope, ty, tail)
}

fn count_enum(item: &syn::ItemEnum, scope: &[syn::Item], ty: &str, tail: &[String]) -> usize {
    if tail.is_empty() {
        return 1;
    }
    let variants = tail.first().map_or(0, |name| {
        item.variants
            .iter()
            .filter(|variant| variant.ident == name)
            .map(|variant| {
                if tail.len() == 1 {
                    1
                } else {
                    count_fields(&variant.fields, &tail[1..])
                }
            })
            .sum()
    });
    variants + count_generics(&item.generics, tail) + count_inherent_impl(scope, ty, tail)
}

fn count_fields(fields: &syn::Fields, tail: &[String]) -> usize {
    if tail.len() != 1 {
        return 0;
    }
    fields
        .iter()
        .filter(|field| field.ident.as_ref().is_some_and(|ident| ident == &tail[0]))
        .count()
}

fn count_named_fields(fields: &syn::FieldsNamed, tail: &[String]) -> usize {
    if tail.len() != 1 {
        return 0;
    }
    fields
        .named
        .iter()
        .filter(|field| field.ident.as_ref().is_some_and(|ident| ident == &tail[0]))
        .count()
}

fn count_generics(generics: &syn::Generics, tail: &[String]) -> usize {
    if tail.is_empty() {
        return 1;
    }
    if tail.len() != 1 {
        return 0;
    }
    generics
        .params
        .iter()
        .filter(|param| generic_name(param).is_some_and(|name| name == tail[0]))
        .count()
}

fn count_signature(sig: &syn::Signature, tail: &[String]) -> usize {
    if tail.is_empty() {
        return 1;
    }
    if tail.len() != 1 {
        return 0;
    }
    count_generics(&sig.generics, tail)
        + sig
            .inputs
            .iter()
            .filter(|input| fn_arg_name(input).is_some_and(|name| name == tail[0]))
            .count()
}

fn count_trait(item: &syn::ItemTrait, tail: &[String]) -> usize {
    if tail.is_empty() {
        return 1;
    }
    count_generics(&item.generics, tail)
        + item
            .items
            .iter()
            .map(|item| count_trait_item(item, tail))
            .sum::<usize>()
}

fn count_trait_item(item: &syn::TraitItem, tail: &[String]) -> usize {
    match item {
        syn::TraitItem::Const(item) if item.ident == tail[0] => {
            if tail.len() == 1 {
                1
            } else {
                count_generics(&item.generics, &tail[1..])
            }
        }
        syn::TraitItem::Fn(item) if item.sig.ident == tail[0] => {
            if tail.len() == 1 {
                1
            } else {
                count_signature(&item.sig, &tail[1..])
            }
        }
        syn::TraitItem::Type(item) if item.ident == tail[0] => {
            if tail.len() == 1 {
                1
            } else {
                count_generics(&item.generics, &tail[1..])
            }
        }
        _ => 0,
    }
}

fn count_inherent_impl(scope: &[syn::Item], ty: &str, tail: &[String]) -> usize {
    scope
        .iter()
        .filter_map(|item| match item {
            syn::Item::Impl(item)
                if item.trait_.is_none() && path_matches(&item.self_ty, &[ty.into()]) =>
            {
                Some(
                    item.items
                        .iter()
                        .map(|item| count_impl_item(item, tail))
                        .sum::<usize>(),
                )
            }
            _ => None,
        })
        .sum()
}

fn count_impl_item(item: &syn::ImplItem, tail: &[String]) -> usize {
    match item {
        syn::ImplItem::Const(item) if item.ident == tail[0] => {
            if tail.len() == 1 {
                1
            } else {
                count_generics(&item.generics, &tail[1..])
            }
        }
        syn::ImplItem::Fn(item) if item.sig.ident == tail[0] => {
            if tail.len() == 1 {
                1
            } else {
                count_signature(&item.sig, &tail[1..])
            }
        }
        syn::ImplItem::Type(item) if item.ident == tail[0] => {
            if tail.len() == 1 {
                1
            } else {
                count_generics(&item.generics, &tail[1..])
            }
        }
        _ => 0,
    }
}

fn count_trait_impl(
    items: &[syn::Item],
    self_ty: &[String],
    trait_path: &[String],
    member: &str,
) -> usize {
    items
        .iter()
        .map(|item| match item {
            syn::Item::Mod(item) => item.content.as_ref().map_or(0, |(_, items)| {
                count_trait_impl(items, self_ty, trait_path, member)
            }),
            syn::Item::Impl(item)
                if path_matches(&item.self_ty, self_ty)
                    && item
                        .trait_
                        .as_ref()
                        .is_some_and(|(path, _)| path_segments_equal(path, trait_path)) =>
            {
                item.items
                    .iter()
                    .map(|item| count_impl_item(item, &[member.into()]))
                    .sum()
            }
            _ => 0,
        })
        .sum()
}

fn path_segments_equal(path: &syn::Path, expected: &[String]) -> bool {
    path.leading_colon.is_none()
        && path.segments.len() == expected.len()
        && path
            .segments
            .iter()
            .zip(expected)
            .all(|(segment, expected)| {
                segment.ident == expected && matches!(segment.arguments, syn::PathArguments::None)
            })
}

fn generic_name(param: &syn::GenericParam) -> Option<String> {
    match param {
        syn::GenericParam::Lifetime(param) => Some(format!("'{}", param.lifetime.ident)),
        syn::GenericParam::Type(param) => Some(param.ident.to_string()),
        syn::GenericParam::Const(param) => Some(param.ident.to_string()),
    }
}

fn fn_arg_name(arg: &syn::FnArg) -> Option<String> {
    match arg {
        syn::FnArg::Receiver(_) => Some("self".into()),
        syn::FnArg::Typed(arg) => match &*arg.pat {
            syn::Pat::Ident(pat) => Some(pat.ident.to_string()),
            _ => None,
        },
    }
}
