use syn::parse_quote;

use crate::{actions::InjectAction, crate_info::CrateMut, error::Error, spec::Derive};

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
        let extra_attributes = self.derive.attributes()?;

        let mut item =
            DeriveItem::find(file.items.iter_mut(), &Vec::from_iter(target_type.segments))
                .ok_or_else(|| {
                    Error::DeriveTargetNotFound(format!("{}", self.derive.target_type_as_str()))
                })?;
        let attributes = item.attributes();
        attributes.push(parse_quote! { #[derive(#target_trait)] });
        attributes.extend_from_slice(&extra_attributes);

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
}
