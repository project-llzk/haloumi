//! Types for working with region groups.

use std::{
    cell::RefCell,
    collections::HashMap,
    fmt::Debug,
    hash::{DefaultHasher, Hash, Hasher as _},
    marker::PhantomData,
    ops::Deref,
    rc::Rc,
};

use crate::{info_traits::GroupInfo, table::Cell};

#[cfg(test)]
mod tests;

/// Marker trait that defines a key that uniquelly identifies a group.
///
/// The uniqueness comes from [`std::hash::Hash`].
///
/// For most cases the [`DefaultKey`] is enough, but you can define your own if
/// necessary.
pub trait GroupKey: Copy + Hash + Debug + Sized {}

/// Type erased group key.
///
/// Allows using different implementations of [`GroupKey`] together.
/// Can be constructed from any implementation of [`GroupKey`]
/// and stores only the resulting hash, erasing the original type.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct GroupKeyInstance(u64);

impl<K> From<K> for GroupKeyInstance
where
    K: GroupKey,
{
    fn from(value: K) -> Self {
        let mut h = DefaultHasher::new();
        // Salt the hash with the type's name
        std::any::type_name_of_val(&value).hash(&mut h);
        value.hash(&mut h);
        Self(h.finish())
    }
}

impl Deref for GroupKeyInstance {
    type Target = u64;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<GroupKeyInstance> for u64 {
    fn from(value: GroupKeyInstance) -> Self {
        value.0
    }
}

impl From<GroupKeyInstance> for usize {
    fn from(value: GroupKeyInstance) -> Self {
        value.0 as usize
    }
}

/// Alias to the default key type used by [`crate::default_group_key!`].
pub type DefaultKey = SourceLocKey;

/// This macro returns an instance of the default key.
#[macro_export]
macro_rules! default_group_key {
    () => {
        $crate::circuit::groups::DefaultKey {
            file: std::file!(),
            line: std::line!(),
            column: std::column!(),
        }
    };
}

/// [`GroupKey`] based on a source code location (file, line, col).
#[derive(Copy, Clone, Debug, Hash)]
pub struct SourceLocKey {
    /// Filename
    pub file: &'static str,
    /// Line number
    pub line: u32,
    /// Column number
    pub column: u32,
}

impl GroupKey for SourceLocKey {}

/// Flag for controlling the annotating of cells.
#[derive(Debug, Clone)]
pub struct AnnotationFlag(Rc<RefCell<bool>>);

impl AnnotationFlag {
    /// Creates a new flag.
    pub fn new() -> Self {
        Self(Rc::new(RefCell::new(true)))
    }

    /// Enables or disables the annotation of cells.
    pub fn set(&self, enabled: bool) {
        *self.0.borrow_mut() = enabled;
    }

    /// Enables the annotation of cells.
    pub fn enable(&self) {
        self.set(true)
    }

    /// Disables the annotation of cells.
    pub fn disable(&self) {
        self.set(false)
    }

    /// Returns whether disabled or not.
    pub fn disabled(&self) -> bool {
        !*self.0.borrow()
    }
}

impl Default for AnnotationFlag {
    fn default() -> Self {
        Self::new()
    }
}

/// Annotations associated with a group.
#[derive(Debug, Clone)]
pub struct RegionsGroup<C> {
    cells: Vec<C>,
    annotations: HashMap<C, RoleAnnotation>,
    enabled: AnnotationFlag,
}

impl<C> RegionsGroup<C> {
    /// Creates a new instance.
    pub fn new(enabled: AnnotationFlag) -> Self {
        Self {
            cells: Default::default(),
            annotations: Default::default(),
            enabled,
        }
    }
}

impl<C> RegionsGroup<C>
where
    C: Hash + Eq + Copy,
{
    /// Returns a list of cells of the given role in the order of their
    /// annotation.
    fn cells_of_role(&self, role: CellRole) -> impl Iterator<Item = C> + '_ {
        self.cells.iter().filter_map(move |cell| {
            if self.annotations[cell] == role {
                Some(*cell)
            } else {
                None
            }
        })
    }

    /// Returns a list of `C` annotated as [`CellRole::Input`] in
    /// annotation order.
    pub fn inputs(&self) -> impl Iterator<Item = C> + '_ {
        self.cells_of_role(CellRole::Input)
    }

    /// Returns a list of `C` annotated as [`CellRole::Output`] in
    /// annotation order.
    pub fn outputs(&self) -> impl Iterator<Item = C> + '_ {
        self.cells_of_role(CellRole::Output)
    }

    /// Annotates a `C` with a [`CellRole`].
    ///
    /// Any cell can be annotated, even cells from regions outside the group.
    /// Upstream consumers of these annotations may require that cells from
    /// outside that are annotated with a role must have transitive copy
    /// constrains to at least one cell from the regions of the group. This
    /// requirement is not enforced by this type.
    #[inline]
    pub fn annotate_cell(&mut self, cell: C, role: CellRole) {
        if self.enabled.disabled() {
            return;
        }
        let entry = self.annotations.entry(cell);
        if matches!(entry, std::collections::hash_map::Entry::Vacant(_)) {
            self.cells.push(cell);
        }
        entry.or_default().annotate(role);
    }

    /// Annotates a `C` with a [`CellRole::Input`].
    ///
    /// See the documentation in [`RegionsGroup::annotate_cell`] for
    /// requirements annotated cells must meet.
    #[inline]
    pub fn annotate_input(&mut self, cell: C) {
        self.annotate_cell(cell, CellRole::Input)
    }

    /// Annotates a `C` with a [`CellRole::Output`].
    ///
    /// See the documentation in [`RegionsGroup::annotate_cell`] for
    /// requirements annotated cells must meet.
    #[inline]
    pub fn annotate_output(&mut self, cell: C) {
        self.annotate_cell(cell, CellRole::Output)
    }

    /// Annotates a list of `C` with a [`CellRole::Input`].
    ///
    /// See the documentation in [`RegionsGroup::annotate_cell`] for
    /// requirements annotated cells must meet.
    #[inline]
    pub fn annotate_inputs(&mut self, cells: impl IntoIterator<Item = C>) {
        for cell in cells {
            self.annotate_cell(cell, CellRole::Input);
        }
    }

    /// Annotates a list of `C` with a [`CellRole::Output`].
    ///
    /// See the documentation in [`RegionsGroup::annotate_cell`] for
    /// requirements annotated cells must meet.
    #[inline]
    pub fn annotate_outputs(&mut self, cells: impl IntoIterator<Item = C>) {
        for cell in cells {
            self.annotate_cell(cell, CellRole::Output);
        }
    }

    ///// Annotates the list of `C` that represent the given value with
    ///// [`CellRole::Input`].
    /////
    ///// See the documentation in [`RegionsGroup::annotate_cell`] for
    ///// requirements annotated cells must meet.
    //#[cfg(feature = "decompose-in-cells")]
    //#[inline]
    //pub fn annotate_as_input(
    //    &mut self,
    //    value: &impl picus_support::DecomposeIn<Cell>,
    //) -> Result<(), Error> {
    //    self.annotate_inputs(value.cells())
    //}
    //
    ///// Annotates the list of `C` that represent the given value with
    ///// [`CellRole::Output`].
    /////
    ///// See the documentation in [`RegionsGroup::annotate_cell`] for
    ///// requirements annotated cells must meet.
    //#[cfg(feature = "decompose-in-cells")]
    //#[inline]
    //pub fn annotate_as_output(
    //    &mut self,
    //    value: &impl picus_support::DecomposeIn<Cell>,
    //) -> Result<(), Error> {
    //    self.annotate_outputs(value.cells())
    //}
}

impl<C> GroupInfo for RegionsGroup<C>
where
    C: Into<Cell> + Copy + Hash + Eq,
{
    fn inputs(&self) -> impl Iterator<Item = Cell> + '_ {
        self.inputs().map(Into::into)
    }

    fn outputs(&self) -> impl Iterator<Item = Cell> + '_ {
        self.outputs().map(Into::into)
    }
}

/// Possible roles of a cell inside a group.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum CellRole {
    /// Input role
    Input,
    /// Output role
    Output,
    /// Internal role
    Internal,
}

/// Records the annotations of a cell.
#[derive(Copy, Clone, Debug, Default)]
enum RoleAnnotation {
    #[default]
    Empty,
    Input,
    Output,
    InputOutput,
    Internal,
}

impl RoleAnnotation {
    /// Annotates a role, updating internally based on the existing roles and
    /// the given one.
    ///
    /// Follows these rules for updating:
    /// - `{}, R -> {R}`: If its empty just adds the role.
    /// - `{IN}, OUT -> {IN, OUT}`: If it's an input and is annotated as an
    ///   output, combine them.
    /// - `{OUT}, IN -> {IN, OUT}`: If it's an output and is annotated as an
    ///   input, combine them.
    /// - `{R*}, INT -> {INT}`: Annotating as internal overrides preexisting
    ///   roles.
    /// - `{INT}, R -> {R}`: If it's annotated as internal overrides it with the
    ///   new role.
    fn annotate(&mut self, role: CellRole) {
        match (*self, role) {
            (RoleAnnotation::Empty | RoleAnnotation::Internal, r) => *self = r.into(),
            (RoleAnnotation::Input, CellRole::Input) => {}
            (RoleAnnotation::Input, CellRole::Output) => *self = RoleAnnotation::InputOutput,
            (RoleAnnotation::Output, CellRole::Output) => {}
            (RoleAnnotation::Output, CellRole::Input) => *self = RoleAnnotation::InputOutput,
            (RoleAnnotation::InputOutput, CellRole::Input | CellRole::Output) => {}
            (_, CellRole::Internal) => *self = RoleAnnotation::Internal,
        }
    }
}

impl From<CellRole> for RoleAnnotation {
    fn from(value: CellRole) -> Self {
        match value {
            CellRole::Input => RoleAnnotation::Input,
            CellRole::Output => RoleAnnotation::Output,
            CellRole::Internal => RoleAnnotation::Internal,
        }
    }
}

impl PartialEq<CellRole> for RoleAnnotation {
    fn eq(&self, other: &CellRole) -> bool {
        matches!(
            (self, other),
            (
                RoleAnnotation::Input | RoleAnnotation::InputOutput,
                CellRole::Input
            ) | (
                RoleAnnotation::Output | RoleAnnotation::InputOutput,
                CellRole::Output
            ) | (RoleAnnotation::Internal, CellRole::Internal)
        )
    }
}

/// Trait defining the hooks for interfacing with groups at the layouter level.
pub trait RegionsGroupHooks<F, C> {
    /// Error type.
    type Error;

    /// Root layouter.
    type RootHook: RegionsGroupHooks<F, C>;

    /// Returns the root layouter.
    fn get_root_hook(&mut self) -> &mut Self::RootHook;

    /// Creates a new group and enters into it.
    ///
    /// Not intended for downstream consumption; use [`Layouter::group`]
    /// instead.
    fn push_group<N, NR, K>(&mut self, name: N, key: K)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
        K: GroupKey;

    /// Exits out of the group.
    ///
    /// Not intended for downstream consumption; use [`Layouter::group`]
    /// instead.
    fn pop_group(&mut self, meta: RegionsGroup<C>);

    /// Groups a set of regions together.
    ///
    /// Inside the closure the chip can use [`GroupLayouter`] to define
    /// the regions that are part of the group and [`RegionsGroup`]
    /// to add annotations to the group. See the documentation of that
    /// struct for more details about what can be annotated. These annotations
    /// are intended for upstream consumers and may have additional
    /// requirements the annotations must meet.
    ///
    /// Expects an implementation of [`GroupKey`] with a key that
    /// uniquely identifies the group. The [`default_group_key!`]
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
    fn group_impl<A, AR, N, NR, K>(
        &mut self,
        name: N,
        key: K,
        mut assignment: A,
    ) -> Result<AR, Self::Error>
    where
        A: FnMut(
            &mut GroupLayouter<'_, F, Self::RootHook>,
            &mut RegionsGroup<C>,
        ) -> Result<AR, Self::Error>,
        NR: Into<String>,
        N: FnOnce() -> NR,
        K: GroupKey,
    {
        self.get_root_hook().push_group(name, key);

        let mut scope = GroupScope::new(self.get_root_hook());
        assignment(&mut scope.layouter, &mut scope.meta)
    }
}

/// Trait defining the hooks for interfacing with groups at the assignment level.
pub trait RegionsGroupAssignmentHooks<C> {
    /// Creates a new group and enters into it.
    ///
    /// Not intended for downstream consumption; use [`RegionsGroupHooks::group`]
    /// instead.
    ///
    /// [`RegionsGroupHooks::group`]: crate::groups::RegionsGroupHooks#method.group
    #[allow(unused_variables)]
    fn enter_group<NR, N, K>(&mut self, name_fn: N, key: K)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
        K: GroupKey,
    {
    }

    /// Exits the current group.
    ///
    /// Not intended for downstream consumption; use [`RegionsGroupHooks::group`]
    /// instead.
    ///
    /// [`RegionsGroupHooks::group`]: crate::groups::RegionsGroupHooks#method.group
    #[allow(unused_variables)]
    fn exit_group(&mut self, meta: RegionsGroup<C>) {}
}

/// Tracks regions and cell roles in a group.
///
/// Implements [`Layouter`] and can be used as a drop-in replacement.
#[derive(Debug)]
pub struct GroupLayouter<'l, F, L> {
    /// Parent layouter.
    pub parent: &'l mut L,
    /// Shared with RegionGroup for tracking if annotating is enabled or not.
    enabled: AnnotationFlag,
    _marker: PhantomData<F>,
}

impl<'l, F, L> GroupLayouter<'l, F, L> {
    fn new(parent: &'l mut L, enabled: AnnotationFlag) -> Self {
        Self {
            parent,
            enabled,
            _marker: Default::default(),
        }
    }

    /// Returns the annotation flag.
    pub fn flag(&self) -> AnnotationFlag {
        self.enabled.clone()
    }
}

impl<'l, F, L, C> RegionsGroupHooks<F, C> for GroupLayouter<'l, F, L>
where
    L: RegionsGroupHooks<F, C>,
{
    type Error = L::Error;

    type RootHook = L::RootHook;

    fn get_root_hook(&mut self) -> &mut Self::RootHook {
        self.parent.get_root_hook()
    }

    fn push_group<N, NR, K>(&mut self, name: N, key: K)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
        K: GroupKey,
    {
        self.parent.push_group(name, key);
    }

    fn pop_group(&mut self, meta: RegionsGroup<C>) {
        self.parent.pop_group(meta);
    }
}

/// RAII handler used by the [`RegionsGroupHooks::group`] method.
///
/// [`RegionsGroupHooks::group`]: crate::groups::RegionsGroupHooks#method.group
struct GroupScope<'l, F, L, C>
where
    L: RegionsGroupHooks<F, C>,
{
    layouter: GroupLayouter<'l, F, L>,
    meta: RegionsGroup<C>,
}

impl<'l, F, L, C> GroupScope<'l, F, L, C>
where
    L: RegionsGroupHooks<F, C>,
{
    pub fn new(parent: &'l mut L) -> Self {
        let enabled = AnnotationFlag::new();
        Self {
            layouter: GroupLayouter::new(parent, enabled.clone()),
            meta: RegionsGroup::new(enabled),
        }
    }
}

impl<F, L, C> Drop for GroupScope<'_, F, L, C>
where
    L: RegionsGroupHooks<F, C>,
{
    fn drop(&mut self) {
        let meta = std::mem::replace(&mut self.meta, RegionsGroup::new(Default::default()));
        self.layouter.pop_group(meta)
    }
}
