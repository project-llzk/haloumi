//! Macros that extend traits on the fly.

use proc_macro2::TokenStream;
use quote::{ToTokens, format_ident, quote};
use syn::{
    Attribute, DataStruct, DeriveInput, Expr, Field, Ident, ImplGenerics, Index, ItemTrait, Path,
    TraitItem, Type, TypeGenerics, WhereClause, parse_str, parse2,
};

use crate::{
    attrs::{find_attr_or_code, get_haloumi_integration_module},
    keys::{CELL_KEY, DEFAULT_CELL_TYPE, DEFAULT_ERROR_TYPE, ERROR_KEY},
    parse::hooks::Hooks,
};

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

/// Internal implementation of [`super::derive_region_group_hooks`].
pub fn derive_region_group_hooks_impl(input: DeriveInput) -> syn::Result<TokenStream> {
    let cell = find_attr_or_code::<Path>(&input, CELL_KEY, DEFAULT_CELL_TYPE)?;
    let error = find_attr_or_code::<Path>(&input, ERROR_KEY, DEFAULT_ERROR_TYPE)?;
    let data = get_data(&input)?;

    let mut emitter = Emitter::new(cell, error, &input)?;

    match &data.fields {
        syn::Fields::Named(fields_named) => {
            if let Some(f) = fields_named.named.iter().find(is_delegate) {
                emitter.set_delegate(f.ident.as_ref().unwrap(), &f.ty);
            }
            if let Some(f) = fields_named.named.iter().find(is_root) {
                emitter.set_root(f.ident.as_ref().unwrap(), require_mut_ref(&f.ty)?);
            }
            //// Root floor-planner layouters conventionally keep their assignment
            //// backend in a field named `cs`. Treat it as the group-hook delegate
            //// when no explicit annotation was supplied.
            //if emitter.delegate_expr.is_none() {
            //    if let Some(f) = fields_named
            //        .named
            //        .iter()
            //        .find(|f| f.ident.as_ref().is_some_and(|ident| ident == "cs"))
            //    {
            //        emitter.set_assignment_delegate(f.ident.as_ref().unwrap());
            //    }
            //}
        }
        syn::Fields::Unnamed(fields_unnamed) => {
            if let Some((n, f)) = fields_unnamed
                .unnamed
                .iter()
                .enumerate()
                .find(|(_, f)| is_delegate(f))
            {
                emitter.set_delegate(Index::from(n), &f.ty);
            }
            if let Some((n, f)) = fields_unnamed
                .unnamed
                .iter()
                .enumerate()
                .find(|(_, f)| is_root(f))
            {
                emitter.set_root(Index::from(n), require_mut_ref(&f.ty)?);
            }
        }
        syn::Fields::Unit => {}
    }

    Ok(emitter.emit())
}

struct Emitter<'i> {
    module: Ident,
    cell: Path,
    error: Path,
    input: &'i DeriveInput,
    target: &'i Ident,
    impl_generics: ImplGenerics<'i>,
    ty_generics: TypeGenerics<'i>,
    where_clause: Option<&'i WhereClause>,
    bounds: Vec<TokenStream>,
    root_type: TokenStream,
    root_expr: TokenStream,
    delegate_expr: Option<TokenStream>,
    //assignment_delegate_expr: Option<TokenStream>,
}

impl<'i> Emitter<'i> {
    fn new(cell: Path, error: Path, input: &'i DeriveInput) -> syn::Result<Self> {
        let module = get_haloumi_integration_module()?;
        let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
        Ok(Self {
            module,
            cell,
            error,
            target: &input.ident,
            input,
            impl_generics,
            ty_generics,
            where_clause,
            bounds: Default::default(),
            root_type: quote! {Self},
            root_expr: quote! {self},
            delegate_expr: None,
        })
    }

    fn set_delegate(&mut self, name: impl ToTokens, ty: &Type) {
        assert!(self.delegate_expr.is_none());
        self.delegate_expr = Some(quote! {self.#name});
        let trait_name = self.trait_name();
        let ty = remove_ref(ty);
        self.bounds.push(quote! {#ty: #trait_name});
    }

    //fn set_assignment_delegate(&mut self, name: impl ToTokens) {
    //    assert!(self.delegate_expr.is_none());
    //    self.assignment_delegate_expr = Some(name.to_token_stream());
    //}

    fn set_root(&mut self, name: impl ToTokens, ty: &Type) {
        self.root_expr = quote! {self.#name.get_root_hook()};
        self.root_type = quote! {#ty::RootHook};
        let trait_name = self.trait_name();
        self.bounds.push(quote! {#ty: #trait_name});
    }

    fn find_field_generic(&self) -> Ident {
        self.input
            .generics
            .type_params()
            .find_map(|p| contains_attr_named("field", &p.attrs).then(|| p.ident.clone()))
            .unwrap_or_else(|| format_ident!("F"))
    }

    fn push_group_delegate_expr(&self) -> TokenStream {
        //if let Some(delegate) = &self.assignment_delegate_expr {
        //    return quote! { self.#delegate.enter_group(name, key); };
        //}
        self.make_delegate_expr(quote! {push_group(name, key)})
    }

    fn pop_group_delegate_expr(&self) -> TokenStream {
        //if let Some(delegate) = &self.assignment_delegate_expr {
        //    return quote! { self.#delegate.exit_group(meta); };
        //}
        self.make_delegate_expr(quote! {pop_group(meta)})
    }

    fn make_delegate_expr(&self, mthd: TokenStream) -> TokenStream {
        self.delegate_expr
            .as_ref()
            .map(|e| quote! { #e.#mthd; })
            .unwrap_or_else(|| quote! { unimplemented!() })
    }

    fn groups_module(&self) -> TokenStream {
        let module = self.module.clone();
        quote! { #module::core::groups }
    }

    fn trait_name(&self) -> TokenStream {
        let field = self.find_field_generic();
        let cell = &self.cell;
        let module = self.groups_module();
        quote! { #module::RegionsGroupHooks<#field, #cell> }
    }

    fn emit(self) -> TokenStream {
        let push_group_delegate_expr = self.push_group_delegate_expr();
        let pop_group_delegate_expr = self.pop_group_delegate_expr();
        let trait_name = self.trait_name();
        let module = self.groups_module();

        let cell = self.cell;
        let error = self.error;
        let target = self.target;
        let impl_generics = self.impl_generics;
        let ty_generics = self.ty_generics;
        let where_clause = self.where_clause;
        let bounds = self.bounds;
        let root_type = self.root_type;
        let root_expr = self.root_expr;

        quote! {
            impl #impl_generics #trait_name for #target #ty_generics
            where
                #(#bounds,)*
                #where_clause
            {
                type Error = #error;
                type RootHook = #root_type;

                fn get_root_hook(&mut self) -> &mut Self::RootHook {
                   #root_expr
                }

                fn push_group<N, NR, K>(&mut self, name: N, key: K)
                where
                    NR: Into<String>,
                    N: FnOnce() -> NR,
                    K: #module::GroupKey,
                {
                    #push_group_delegate_expr
                }

                fn pop_group(&mut self, meta: #module::RegionsGroup<#cell>) {
                    #pop_group_delegate_expr
                }
            }
        }
    }
}

fn get_data(input: &DeriveInput) -> syn::Result<&DataStruct> {
    match &input.data {
        syn::Data::Struct(data) => Ok(data),
        syn::Data::Enum(_) | syn::Data::Union(_) => Err(syn::Error::new_spanned(
            &input,
            "derive macro expects a struct",
        )),
    }
}

fn remove_ref(ty: &Type) -> &Type {
    match ty {
        Type::Reference(r) => &r.elem,
        ty => ty,
    }
}

fn require_mut_ref(ty: &Type) -> syn::Result<&Type> {
    match ty {
        Type::Reference(r) if r.mutability.is_some() => Ok(&r.elem),
        _ => Err(syn::Error::new_spanned(
            ty,
            "annotated type must be a &mut-reference",
        )),
    }
}

fn is_delegate(f: &&Field) -> bool {
    contains_attr_named("delegate", &f.attrs)
}

fn is_root(f: &&Field) -> bool {
    contains_attr_named("root", &f.attrs)
}

fn contains_attr_named(attr: &str, attrs: &[Attribute]) -> bool {
    attrs.iter().any(|a| a.path().is_ident(attr))
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
