//! Macros that extend traits on the fly.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{Ident, ItemTrait, TraitItem, Type, parse2};

use crate::{attrs::get_haloumi_integration_module, parse::hooks::Hooks};

/// Internal implementation of [`super::require_group_hooks`].
pub fn require_group_hooks_impl(mut input: ItemTrait, hooks: Hooks) -> syn::Result<TokenStream> {
    let module = get_haloumi_integration_module()?;
    let cell = hooks.cell();
    let field = hooks.field();
    let error = hooks.error();

    input.items.extend([emit_group_fn(&module, &cell)]);
    input.supertraits.push(parse2(quote! {
        #module::core::groups::RegionsGroupHooks<#field, #cell, RootHook = Self::Root, Error = #error>
    })?);

    Ok(quote! {
        #input
    })
}

fn emit_group_fn(module: &Ident, cell: &Type) -> TraitItem {
    parse2(quote! {

    /// Groups a set of regions together.
    ///
    /// Inside the closure the chip can use [`groups::GroupLayouter`] to define
    /// the regions that are part of the group and [`groups::RegionsGroup`]
    /// to add annotations to the group. See the documentation of that
    /// struct for more details about what can be annotated. These annotations
    /// are intended for upstream consumers and may have additional
    /// requirements the annotations must meet.
    ///
    /// Expects an implementation of [`groups::GroupKey`] with a key that
    /// uniquely identifies the group. The [`crate::default_group_key!`]
    /// macro offers an implementation based on the source code location
    /// where the group was created, which should be enough for most cases. If
    /// you have additional requirements for uniquely identifing your groups
    /// you can add your own implementation of [`groups::GroupKey`] and use
    /// that instead.
    ///
    /// This key is intended for upstream consumers that need to know what
    /// groups are equivalent.
    ///
    /// # Example
    ///
    /// ```ignore
    /// fn sum(&self,
    ///     layouter: &mut impl Layouter<F>,
    ///     lhs: &AssignedCell<F, F>,
    ///     rhs: &AssignedCell<F, F>
    /// ) -> Result<AssignedCell<F, F>, Error> { /*...*/ }
    ///
    /// fn sum3(
    ///     &self,
    ///     layouter: &mut impl Layouter<F>,
    ///     x: &AssignedCell<F, F>,
    ///     y: &AssignedCell<F, F>,
    ///     z: &AssignedCell<F, F>
    /// ) -> Result<AssignedCell<F, F>, Error> {
    ///     layouter.group(|| "sum3", default_group_key!(), |layouter, group| {
    ///         // Annotate the role of the input cells
    ///         group.annotate_inputs([x.cell(), y.cell(), z.cell()]);
    ///
    ///         let tmp = self.sum(layouter, x, y)?;
    ///         let o = self.sum(layouter, &tmp, z)?;
    ///
    ///         // Assign the output role to the result cell.
    ///         group.annotate_output(o.cell());
    ///         Ok(o)
    ///     });
    /// }
    /// ```
    fn group<A, AR, N, NR, K>(&mut self, name: N, key: K, mut assignment: A) -> Result<AR, Error>
    where
        A: FnMut(
            &mut #module::core::groups::GroupLayouter<'_, F, Self::Root>,
            &mut #module::core::groups::RegionsGroup<#cell>,
        ) -> Result<AR, Error>,
        NR: Into<String>,
        N: FnOnce() -> NR,
        K: #module::core::groups::GroupKey,
    {
        self.group_impl(name, key, assignment)
    }

    })
    .unwrap()
}
