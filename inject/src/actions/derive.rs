use std::collections::BTreeMap;

use syn::parse_quote;

use crate::{
    actions::InjectAction,
    crate_info::CrateMut,
    error::Error,
    spec::{AttrsMap, Derive, DeriveAttributes, VariantAttributes},
};

/// Applies a derive patch.
pub struct DeriveAction<'a> {
    derive: &'a Derive,
}

impl<'a> DeriveAction<'a> {
    /// Creates a new action.
    pub fn boxed(derive: &'a Derive) -> Box<dyn InjectAction + 'a> {
        Box::new(Self::from(derive))
    }
}

impl<'a> From<&'a Derive> for DeriveAction<'a> {
    fn from(derive: &'a Derive) -> Self {
        Self { derive }
    }
}

impl InjectAction for DeriveAction<'_> {
    fn apply(&self, dest_crate: &mut CrateMut) -> Result<(), Error> {
        let file = dest_crate.open_rust_file(self.derive.path())?;
        let target_type = self.derive.target_type()?;
        let target_trait = self.derive.target_trait()?;
        let mut item =
            DeriveItem::find(file.items.iter_mut(), &Vec::from_iter(target_type.segments))
                .ok_or_else(|| {
                    Error::DeriveTargetNotFound(self.derive.target_type_as_str().to_owned())
                })?;
        let attributes = item.attributes();
        attributes.push(parse_quote! { #[derive(#target_trait)] });
        if let Some(config) = self.derive.attributes() {
            item.apply_attributes(config, self.derive.target_type_as_str())?;
        }

        Ok(())
    }
}

/// A type-erased representation of the items where we could add a `#[derive]` macro.
enum DeriveItem<'i> {
    Struct(&'i mut syn::ItemStruct),
    Union(&'i mut syn::ItemUnion),
    Enum(&'i mut syn::ItemEnum),
}

macro_rules! is_single_ident {
    ($item:expr, $target:expr) => {
        $target.first().is_some_and(|t| t.ident == $item.ident) && $target.len() == 1
    };
}

impl<'i> DeriveItem<'i> {
    /// Locates a type definition (struct, enum, or union) in the file.
    ///
    /// If the head of the path segment matches the name of a non-file module,
    /// the type is recursively searched inside that module.
    ///
    /// For example, the following will match `foo::Bar`:
    ///
    /// ```ignore
    /// mod foo {
    ///     struct Bar;
    /// }
    /// ```
    ///
    /// But the following wont, since the type is actually defined in another file.
    ///
    /// ```ignore
    /// mod foo; // Bar will be in foo.rs
    /// ```
    fn find(
        mut items: impl Iterator<Item = &'i mut syn::Item>,
        target: &[syn::PathSegment],
    ) -> Option<Self> {
        items.find_map(|item| match item {
            syn::Item::Enum(item_enum) if is_single_ident!(item_enum, target) => {
                Some(Self::Enum(item_enum))
            }
            syn::Item::Mod(item_mod)
                if target.first().is_some_and(|t| t.ident == item_mod.ident)
                    && item_mod.content.is_some() =>
            {
                Self::find(
                    item_mod
                        .content
                        .as_mut()
                        .map(|(_, items)| items)
                        .unwrap()
                        .iter_mut(),
                    target,
                )
            }
            syn::Item::Struct(item_struct) if is_single_ident!(item_struct, target) => {
                Some(Self::Struct(item_struct))
            }
            syn::Item::Union(item_union) if is_single_ident!(item_union, target) => {
                Some(Self::Union(item_union))
            }
            _ => None,
        })
    }

    fn attributes(&mut self) -> &mut Vec<syn::Attribute> {
        match self {
            DeriveItem::Struct(item_struct) => &mut item_struct.attrs,
            DeriveItem::Union(item_union) => &mut item_union.attrs,
            DeriveItem::Enum(item_enum) => &mut item_enum.attrs,
        }
    }

    fn apply_attributes(
        &mut self,
        config: &DeriveAttributes,
        target_type: &str,
    ) -> Result<(), Error> {
        self.attributes().extend(config.type_attributes()?);
        self.apply_params(config.params(), target_type)?;
        self.apply_fields(config.fields(), target_type, "fields")?;
        if let Some(variants) = config.variants() {
            self.apply_variants(variants, target_type)?;
        }
        Ok(())
    }

    fn apply_params(&mut self, attrs: AttrsMap, target_type: &str) -> Result<(), Error> {
        let params = match self {
            DeriveItem::Struct(item) => &mut item.generics.params,
            DeriveItem::Union(item) => &mut item.generics.params,
            DeriveItem::Enum(item) => &mut item.generics.params,
        };
        for (name, attributes) in attrs {
            let param = params
                .iter_mut()
                .find(|param| match param {
                    syn::GenericParam::Lifetime(param) => {
                        name.starts_with("'") && param.lifetime.ident == &name[1..]
                    }
                    syn::GenericParam::Type(param) => param.ident == name,
                    syn::GenericParam::Const(param) => param.ident == name,
                })
                .ok_or_else(|| attr_target_not_found_error(target_type, "generic_params", name))?;
            match param {
                syn::GenericParam::Lifetime(param) => &mut param.attrs,
                syn::GenericParam::Type(param) => &mut param.attrs,
                syn::GenericParam::Const(param) => &mut param.attrs,
            }
            .extend(attributes?);
        }
        Ok(())
    }

    fn apply_fields(
        &mut self,
        configured_fields: AttrsMap,
        target_type: &str,
        location: &str,
    ) -> Result<(), Error> {
        match self {
            DeriveItem::Struct(item) => {
                apply_fields(&mut item.fields, configured_fields, target_type, location)
            }
            DeriveItem::Union(item) => {
                apply_named_fields(&mut item.fields, configured_fields, target_type, location)
            }
            DeriveItem::Enum(_) if configured_fields.is_empty() => Ok(()),
            _ => Err(invalid_target_error(location, target_type)),
        }
    }

    fn apply_variants(
        &mut self,
        configured_variants: &BTreeMap<String, VariantAttributes>,
        target_type: &str,
    ) -> Result<(), Error> {
        let variants = match self {
            DeriveItem::Enum(item) => &mut item.variants,
            DeriveItem::Struct(_) | DeriveItem::Union(_) => {
                return Err(invalid_target_error("variants", target_type));
            }
        };
        for (name, config) in configured_variants {
            let variant = variants
                .iter_mut()
                .find(|variant| variant.ident == name)
                .ok_or_else(|| attr_target_not_found_error(target_type, "variants", name))?;
            variant.attrs.extend(config.attributes()?);
            apply_fields(
                &mut variant.fields,
                config.fields(),
                target_type,
                &format!("variants.{name}.fields"),
            )?;
        }
        Ok(())
    }
}

fn apply_fields(
    fields: &mut syn::Fields,
    configured_fields: AttrsMap,
    target_type: &str,
    location: &str,
) -> Result<(), Error> {
    for (key, attributes) in configured_fields {
        let field = match fields {
            syn::Fields::Named(fields) => fields
                .named
                .iter_mut()
                .find(|field| field.ident.as_ref().is_some_and(|ident| ident == key)),
            syn::Fields::Unnamed(fields) => key
                .parse::<usize>()
                .ok()
                .and_then(|index| fields.unnamed.iter_mut().nth(index)),
            syn::Fields::Unit => None,
        };
        let field = field.ok_or_else(|| attr_target_not_found_error(target_type, location, key))?;
        field.attrs.extend(attributes?);
    }
    Ok(())
}

fn apply_named_fields(
    fields: &mut syn::FieldsNamed,
    configured_fields: AttrsMap,
    target_type: &str,
    location: &str,
) -> Result<(), Error> {
    for (key, attributes) in configured_fields {
        let field = fields
            .named
            .iter_mut()
            .find(|field| field.ident.as_ref().is_some_and(|ident| ident == key));
        let field = field.ok_or_else(|| attr_target_not_found_error(target_type, location, key))?;
        field.attrs.extend(attributes?);
    }
    Ok(())
}

fn attr_target_not_found_error(
    target_type: impl ToString,
    location: impl std::fmt::Display,
    key: impl std::fmt::Display,
) -> Error {
    Error::AttributeTargetNotFound(format!("{location}.{key}"), target_type.to_string())
}

fn invalid_target_error(location: impl ToString, target_type: impl ToString) -> Error {
    Error::InvalidAttributeTarget(location.to_string(), target_type.to_string())
}
