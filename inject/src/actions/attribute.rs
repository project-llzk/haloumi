//! Applies standalone attribute patches addressed by Rust-style paths.

use crate::{
    actions::InjectAction, crate_info::CrateMut, error::Error, rspath::RustPath, spec::Attribute,
};

/// Applies one standalone attribute patch.
pub struct AttributeAction<'a> {
    attribute: &'a Attribute,
}

impl<'a> AttributeAction<'a> {
    /// Creates an action for an attribute patch.
    pub fn boxed(attribute: &'a Attribute) -> Box<dyn InjectAction + 'a> {
        Box::new(Self { attribute })
    }
}

impl InjectAction for AttributeAction<'_> {
    fn apply(&self, dest_crate: &mut CrateMut) -> Result<(), Error> {
        let target = RustPath::parse(self.attribute.target())?;
        let file = dest_crate.open_rust_file(self.attribute.path())?;
        match target.count(&file.items) {
            0 => {
                return Err(Error::AttributePathTargetNotFound(
                    self.attribute.target().into(),
                ));
            }
            1 => {}
            count => {
                return Err(Error::AmbiguousAttributePathTarget(
                    self.attribute.target().into(),
                    count,
                ));
            }
        }
        debug_assert!(self.apply_target(&target, &mut file.items, self.attribute.attributes()?));
        Ok(())
    }
}

impl AttributeAction<'_> {
    fn apply_target(
        &self,
        target: &RustPath,
        items: &mut [syn::Item],
        attributes: Vec<syn::Attribute>,
    ) -> bool {
        match target {
            RustPath::Normal(segments) => apply_normal(items, segments, attributes),
            RustPath::TraitImpl {
                self_ty,
                trait_path,
                member,
            } => apply_trait_impl(items, self_ty, trait_path, member, attributes),
        }
    }
}

fn apply_normal(
    items: &mut [syn::Item],
    segments: &[String],
    attributes: Vec<syn::Attribute>,
) -> bool {
    let mut attributes = Some(attributes);
    apply_normal_inner(items, segments, &mut attributes)
}

fn apply_normal_inner(
    items: &mut [syn::Item],
    segments: &[String],
    attributes: &mut Option<Vec<syn::Attribute>>,
) -> bool {
    let Some((head, tail)) = segments.split_first() else {
        return false;
    };
    if !tail.is_empty() && apply_inherent_impl(items, head, tail, attributes) {
        return true;
    }
    for index in 0..items.len() {
        let applied = match &mut items[index] {
            syn::Item::Mod(item) if item.ident == head => {
                if tail.is_empty() {
                    extend(&mut item.attrs, attributes)
                } else {
                    item.content
                        .as_mut()
                        .is_some_and(|(_, items)| apply_normal_inner(items, tail, attributes))
                }
            }
            syn::Item::Struct(item) if item.ident == head => apply_data_item(
                &mut item.attrs,
                &mut item.fields,
                &mut item.generics,
                tail,
                attributes,
            ),
            syn::Item::Union(item) if item.ident == head => apply_named_data_item(
                &mut item.attrs,
                &mut item.fields,
                &mut item.generics,
                tail,
                attributes,
            ),
            syn::Item::Enum(item) if item.ident == head => apply_enum(item, tail, attributes),
            syn::Item::Fn(item) if item.sig.ident == head => {
                apply_signature(&mut item.attrs, &mut item.sig, tail, attributes)
            }
            syn::Item::Trait(item) if item.ident == head => apply_trait(item, tail, attributes),
            syn::Item::Type(item) if item.ident == head => {
                if tail.is_empty() {
                    extend(&mut item.attrs, attributes)
                } else {
                    apply_generics(&mut item.generics, tail, attributes)
                }
            }
            syn::Item::Const(item) if item.ident == head => {
                if tail.is_empty() {
                    extend(&mut item.attrs, attributes)
                } else {
                    apply_generics(&mut item.generics, tail, attributes)
                }
            }
            syn::Item::Static(item) if item.ident == head && tail.is_empty() => {
                extend(&mut item.attrs, attributes)
            }
            syn::Item::TraitAlias(item) if item.ident == head => {
                if tail.is_empty() {
                    extend(&mut item.attrs, attributes)
                } else {
                    apply_generics(&mut item.generics, tail, attributes)
                }
            }
            syn::Item::ExternCrate(item) if item.ident == head && tail.is_empty() => {
                extend(&mut item.attrs, attributes)
            }
            syn::Item::Macro(item)
                if item.ident.as_ref().is_some_and(|ident| ident == head) && tail.is_empty() =>
            {
                extend(&mut item.attrs, attributes)
            }
            _ => false,
        };
        if applied {
            return true;
        }
    }
    false
}

fn apply_data_item(
    attrs: &mut Vec<syn::Attribute>,
    fields: &mut syn::Fields,
    generics: &mut syn::Generics,
    tail: &[String],
    attributes: &mut Option<Vec<syn::Attribute>>,
) -> bool {
    if tail.is_empty() {
        return extend(attrs, attributes);
    }
    apply_fields(fields, tail, attributes) || apply_generics(generics, tail, attributes)
}

fn apply_named_data_item(
    attrs: &mut Vec<syn::Attribute>,
    fields: &mut syn::FieldsNamed,
    generics: &mut syn::Generics,
    tail: &[String],
    attributes: &mut Option<Vec<syn::Attribute>>,
) -> bool {
    if tail.is_empty() {
        return extend(attrs, attributes);
    }
    apply_named_fields(fields, tail, attributes) || apply_generics(generics, tail, attributes)
}

fn apply_enum(
    item: &mut syn::ItemEnum,
    tail: &[String],
    attributes: &mut Option<Vec<syn::Attribute>>,
) -> bool {
    if tail.is_empty() {
        return extend(&mut item.attrs, attributes);
    }
    if let Some(variant) = item
        .variants
        .iter_mut()
        .find(|variant| variant.ident == tail[0])
    {
        if tail.len() == 1 {
            return extend(&mut variant.attrs, attributes);
        }
        if apply_fields(&mut variant.fields, &tail[1..], attributes) {
            return true;
        }
    }
    apply_generics(&mut item.generics, tail, attributes)
}

fn apply_fields(
    fields: &mut syn::Fields,
    tail: &[String],
    attributes: &mut Option<Vec<syn::Attribute>>,
) -> bool {
    tail.len() == 1
        && fields
            .iter_mut()
            .find(|field| field.ident.as_ref().is_some_and(|ident| ident == &tail[0]))
            .is_some_and(|field| extend(&mut field.attrs, attributes))
}

fn apply_named_fields(
    fields: &mut syn::FieldsNamed,
    tail: &[String],
    attributes: &mut Option<Vec<syn::Attribute>>,
) -> bool {
    tail.len() == 1
        && fields
            .named
            .iter_mut()
            .find(|field| field.ident.as_ref().is_some_and(|ident| ident == &tail[0]))
            .is_some_and(|field| extend(&mut field.attrs, attributes))
}

fn apply_generics(
    generics: &mut syn::Generics,
    tail: &[String],
    attributes: &mut Option<Vec<syn::Attribute>>,
) -> bool {
    tail.len() == 1
        && generics
            .params
            .iter_mut()
            .find(|param| generic_name(param).is_some_and(|name| name == tail[0]))
            .is_some_and(|param| {
                let attrs = match param {
                    syn::GenericParam::Lifetime(param) => &mut param.attrs,
                    syn::GenericParam::Type(param) => &mut param.attrs,
                    syn::GenericParam::Const(param) => &mut param.attrs,
                };
                extend(attrs, attributes)
            })
}

fn apply_signature(
    attrs: &mut Vec<syn::Attribute>,
    sig: &mut syn::Signature,
    tail: &[String],
    attributes: &mut Option<Vec<syn::Attribute>>,
) -> bool {
    if tail.is_empty() {
        return extend(attrs, attributes);
    }
    apply_generics(&mut sig.generics, tail, attributes)
        || sig
            .inputs
            .iter_mut()
            .find(|input| fn_arg_name(input).is_some_and(|name| name == tail[0]))
            .is_some_and(|input| {
                if tail.len() != 1 {
                    return false;
                }
                match input {
                    syn::FnArg::Receiver(receiver) => extend(&mut receiver.attrs, attributes),
                    syn::FnArg::Typed(arg) => extend(&mut arg.attrs, attributes),
                }
            })
}

fn apply_trait(
    item: &mut syn::ItemTrait,
    tail: &[String],
    attributes: &mut Option<Vec<syn::Attribute>>,
) -> bool {
    if tail.is_empty() {
        return extend(&mut item.attrs, attributes);
    }
    apply_generics(&mut item.generics, tail, attributes)
        || item
            .items
            .iter_mut()
            .find_map(|item| apply_trait_item(item, tail, attributes).then_some(()))
            .is_some()
}

fn apply_trait_item(
    item: &mut syn::TraitItem,
    tail: &[String],
    attributes: &mut Option<Vec<syn::Attribute>>,
) -> bool {
    match item {
        syn::TraitItem::Const(item) if item.ident == tail[0] => {
            if tail.len() == 1 {
                extend(&mut item.attrs, attributes)
            } else {
                apply_generics(&mut item.generics, &tail[1..], attributes)
            }
        }
        syn::TraitItem::Fn(item) if item.sig.ident == tail[0] => {
            if tail.len() == 1 {
                extend(&mut item.attrs, attributes)
            } else {
                apply_signature(&mut item.attrs, &mut item.sig, &tail[1..], attributes)
            }
        }
        syn::TraitItem::Type(item) if item.ident == tail[0] => {
            if tail.len() == 1 {
                extend(&mut item.attrs, attributes)
            } else {
                apply_generics(&mut item.generics, &tail[1..], attributes)
            }
        }
        _ => false,
    }
}

fn apply_inherent_impl(
    scope: &mut [syn::Item],
    ty: &str,
    tail: &[String],
    attributes: &mut Option<Vec<syn::Attribute>>,
) -> bool {
    scope
        .iter_mut()
        .find_map(|item| match item {
            syn::Item::Impl(item)
                if item.trait_.is_none() && path_matches(&item.self_ty, &[ty.into()]) =>
            {
                item.items
                    .iter_mut()
                    .find_map(|item| apply_impl_item(item, tail, attributes).then_some(()))
            }
            _ => None,
        })
        .is_some()
}

fn apply_impl_item(
    item: &mut syn::ImplItem,
    tail: &[String],
    attributes: &mut Option<Vec<syn::Attribute>>,
) -> bool {
    match item {
        syn::ImplItem::Const(item) if item.ident == tail[0] => {
            if tail.len() == 1 {
                extend(&mut item.attrs, attributes)
            } else {
                apply_generics(&mut item.generics, &tail[1..], attributes)
            }
        }
        syn::ImplItem::Fn(item) if item.sig.ident == tail[0] => {
            if tail.len() == 1 {
                extend(&mut item.attrs, attributes)
            } else {
                apply_signature(&mut item.attrs, &mut item.sig, &tail[1..], attributes)
            }
        }
        syn::ImplItem::Type(item) if item.ident == tail[0] => {
            if tail.len() == 1 {
                extend(&mut item.attrs, attributes)
            } else {
                apply_generics(&mut item.generics, &tail[1..], attributes)
            }
        }
        _ => false,
    }
}

pub(crate) fn apply_trait_impl(
    items: &mut [syn::Item],
    self_ty: &[String],
    trait_path: &[String],
    member: &str,
    attributes: Vec<syn::Attribute>,
) -> bool {
    let mut attributes = Some(attributes);
    apply_trait_impl_inner(items, self_ty, trait_path, member, &mut attributes)
}

fn apply_trait_impl_inner(
    items: &mut [syn::Item],
    self_ty: &[String],
    trait_path: &[String],
    member: &str,
    attributes: &mut Option<Vec<syn::Attribute>>,
) -> bool {
    for item in items {
        let applied = match item {
            syn::Item::Mod(item) => item.content.as_mut().is_some_and(|(_, items)| {
                apply_trait_impl_inner(items, self_ty, trait_path, member, attributes)
            }),
            syn::Item::Impl(item)
                if path_matches(&item.self_ty, self_ty)
                    && item
                        .trait_
                        .as_ref()
                        .is_some_and(|(path, _)| path_segments_equal(path, trait_path)) =>
            {
                item.items
                    .iter_mut()
                    .find_map(|item| {
                        apply_impl_item(item, &[member.into()], attributes).then_some(())
                    })
                    .is_some()
            }
            _ => false,
        };
        if applied {
            return true;
        }
    }
    false
}

fn extend(target: &mut Vec<syn::Attribute>, attributes: &mut Option<Vec<syn::Attribute>>) -> bool {
    if let Some(attributes) = attributes.take() {
        target.extend(attributes);
        true
    } else {
        false
    }
}

fn path_matches(ty: &syn::Type, expected: &[String]) -> bool {
    matches!(ty, syn::Type::Path(path) if path.qself.is_none() && path.path.leading_colon.is_none()
        && path.path.segments.len() == expected.len() && path.path.segments.iter().zip(expected).all(|(segment, expected)| segment.ident == expected && matches!(segment.arguments, syn::PathArguments::None)))
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
