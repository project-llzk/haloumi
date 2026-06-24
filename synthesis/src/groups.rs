//! Types related to groups.

use std::{
    borrow::Borrow,
    collections::HashMap,
    ops::{Deref, DerefMut},
};

use ff::Field;

use crate::io::{AdviceIO, CircuitIO, IOCell, InstanceIO};
use haloumi_core::{
    expressions::ExprBuilder,
    query::{Advice, Instance},
    table::{Any, Cell, ColumnType, RegionIndex, Rotation, RotationExt},
};

use super::regions::{RegionData, Regions};

/// Alias to the type representing any group key.
pub type GroupKey = u64;

/// A group can either represent the circuit itself (the top level)
/// or a group declared during synthesis, identified by its key.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum GroupKind {
    /// Top-level group, the entry point of the circuit.
    TopLevel,
    /// An inner group, identified by its key.
    Group(GroupKey),
}

/// A cell that could be either assigned during synthesis or declared as circuit IO.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum GroupCell {
    /// A cell that comes from an assigned cell during synthesis.
    Assigned(Cell),
    /// An instance cell that was declared as part of the circuit's IO.
    InstanceIO(IOCell<Instance>),
    /// An advice cell that was declared as part of the circuit's IO.
    AdviceIO(IOCell<Advice>),
}

impl GroupCell {
    /// Converts the cell into a query to it represented by an expression.
    pub fn to_expr<F: Field, E: ExprBuilder<F>>(self) -> E {
        match self {
            GroupCell::Assigned(cell) => cell.column.query_cell(Rotation::cur()),
            GroupCell::InstanceIO((column, _)) => column.query_cell(Rotation::cur()),
            GroupCell::AdviceIO((column, _)) => column.query_cell(Rotation::cur()),
        }
    }

    /// Returns the cell's row.
    pub fn row(&self) -> usize {
        match self {
            GroupCell::Assigned(cell) => cell.row_offset,
            GroupCell::InstanceIO(cell) => cell.1,
            GroupCell::AdviceIO(cell) => cell.1,
        }
    }

    /// Returns the region index of the cell if it's available.
    pub fn region_index(&self) -> Option<RegionIndex> {
        match self {
            GroupCell::Assigned(cell) => Some(cell.region_index),
            _ => None,
        }
    }

    /// Returns true if the cell is from a Fixed column.
    pub fn is_fixed(&self) -> bool {
        match self {
            GroupCell::Assigned(cell) => *cell.column.column_type() == Any::Fixed,
            GroupCell::InstanceIO(_) | GroupCell::AdviceIO(_) => false,
        }
    }
}

impl From<Cell> for GroupCell {
    fn from(value: Cell) -> Self {
        Self::Assigned(value)
    }
}

impl From<IOCell<Instance>> for GroupCell {
    fn from(value: IOCell<Instance>) -> Self {
        Self::InstanceIO(value)
    }
}

impl From<IOCell<Advice>> for GroupCell {
    fn from(value: IOCell<Advice>) -> Self {
        Self::AdviceIO(value)
    }
}

/// Shared implementation of a group.
#[derive(Debug)]
pub struct GroupBase {
    kind: GroupKind,
    name: Option<String>,
    inputs: Vec<GroupCell>,
    outputs: Vec<GroupCell>,
    regions: Regions,
}

impl GroupBase {
    /// Constructs an empty top-level group.
    fn top_level() -> Self {
        Self {
            kind: GroupKind::TopLevel,
            name: None,
            inputs: Default::default(),
            outputs: Default::default(),
            regions: Default::default(),
        }
    }

    /// Constructs an named empty group.
    fn empty(name: String, key: GroupKey) -> Self {
        Self {
            kind: GroupKind::Group(key),
            name: Some(name),
            inputs: Default::default(),
            outputs: Default::default(),
            regions: Default::default(),
        }
    }

    /// Returns a list of region data.
    pub fn regions(&self) -> Vec<RegionData<'_>> {
        self.regions.regions()
    }

    /// Returns the name of the group.
    pub fn name(&self) -> &str {
        if self.kind == GroupKind::TopLevel {
            return "Main";
        }
        self.name
            .as_deref()
            .and_then(|s| (!s.is_empty()).then_some(s))
            .unwrap_or("unnamed_group")
    }
}

/// A flat read-only representation of a group.
///
/// The parent-children relation is represented by indices on a vector instead.
#[derive(Debug)]
pub struct Group {
    base: GroupBase,
    children: Vec<usize>,
}

impl Group {
    fn with_children(base: GroupBase, children: Vec<usize>) -> Self {
        // Sanity check; if group is top level there cannot be any assigned cells.
        if base.kind == GroupKind::TopLevel {
            assert!(
                base.inputs
                    .iter()
                    .all(|i| !matches!(i, GroupCell::Assigned(_))),
                "Cannot assign input cells in the top level"
            );
            assert!(
                base.outputs
                    .iter()
                    .all(|i| !matches!(i, GroupCell::Assigned(_))),
                "Cannot assign output cells in the top level"
            );
        }
        Self { base, children }
    }

    ///// Returns the regions' rows
    //pub fn region_rows<'a, 'io, 'fq, F: Field>(
    //    &'a self,
    //    advice_io: &'io AdviceIO,
    //    instance_io: &'io InstanceIO,
    //    fqr: &'fq dyn FixedQueryResolver<F>,
    //) -> Vec<RegionRow<'a, 'io, 'fq, F>> {
    //    self.regions()
    //        .into_iter()
    //        .flat_map(move |r| {
    //            r.rows()
    //                .map(move |row| RegionRow::new(r, row, advice_io, instance_io, fqr))
    //        })
    //        .collect()
    //}

    /// Returns the inputs of the group.
    pub fn inputs(&self) -> &[GroupCell] {
        &self.inputs
    }

    /// Returns the outputs of the group.
    pub fn outputs(&self) -> &[GroupCell] {
        &self.outputs
    }

    /// Returns the group objects of the children
    pub fn children<'a>(&'a self, groups: &'a [Group]) -> Vec<(usize, &'a Group)> {
        self.children
            .iter()
            .copied()
            .map(|idx| (idx, groups.get(idx).unwrap()))
            .collect()
    }

    /// Returns the group key
    pub fn key(&self) -> Option<GroupKey> {
        match self.kind {
            GroupKind::TopLevel => None,
            GroupKind::Group(group_key_instance) => Some(group_key_instance),
        }
    }
}

impl Deref for Group {
    type Target = GroupBase;

    fn deref(&self) -> &Self::Target {
        &self.base
    }
}

impl DerefMut for Group {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.base
    }
}

/// A collection of groups.
///
/// It is represented with a newtype to be able to add methods to this type.
#[derive(Debug)]
pub struct Groups(Vec<Group>);

impl Groups {
    /// Returns a mapping between the region indices and their starting rows.
    pub fn region_starts(&self) -> HashMap<RegionIndex, usize> {
        self.0
            .iter()
            .flat_map(|g| g.regions())
            .map(|r| {
                let idx = r
                    .index()
                    .unwrap_or_else(|| panic!("Region {r:?} does not have an index"));

                (idx, r.start().unwrap_or_default())
            })
            .collect()
    }

    /// Returns information about the groups inputs and outputs.
    pub fn groups_io(&self) -> GroupsIO {
        /// Constructs a CircuitIO of advice cells.
        fn mk_advice_io(
            inputs: &[GroupCell],
            outputs: &[GroupCell],
            regions: &HashMap<RegionIndex, usize>,
        ) -> crate::io::AdviceIO {
            let filter_fn = |input: &GroupCell| -> Option<IOCell<Advice>> {
                match input {
                    GroupCell::Assigned(cell) => match cell.column.column_type() {
                        Any::Advice => {
                            let row = cell.row_offset + regions[&cell.region_index];
                            Some((cell.column.try_into().unwrap(), row))
                        }
                        Any::Instance => None,
                        Any::Fixed => unreachable!(),
                    },
                    GroupCell::InstanceIO(_) => None,
                    GroupCell::AdviceIO(cell) => Some(*cell),
                }
            };
            CircuitIO::new_from_iocells(
                inputs.iter().filter_map(filter_fn),
                outputs.iter().filter_map(filter_fn),
            )
        }

        /// Constructs a CircuitIO of instance cells.
        fn mk_instance_io(
            inputs: &[GroupCell],
            outputs: &[GroupCell],
            regions: &HashMap<RegionIndex, usize>,
        ) -> crate::io::InstanceIO {
            let filter_fn = |input: &GroupCell| -> Option<IOCell<Instance>> {
                match input {
                    GroupCell::Assigned(cell) => match cell.column.column_type() {
                        Any::Instance => {
                            let row = cell.row_offset + regions[&cell.region_index];
                            Some((cell.column.try_into().unwrap(), row))
                        }
                        Any::Advice => None,
                        Any::Fixed => unreachable!(),
                    },
                    GroupCell::InstanceIO(cell) => Some(*cell),
                    GroupCell::AdviceIO(_) => None,
                }
            };
            CircuitIO::new_from_iocells(
                inputs.iter().filter_map(filter_fn),
                outputs.iter().filter_map(filter_fn),
            )
        }

        let mut io = GroupsIO {
            advice_io: Default::default(),
            instance_io: Default::default(),
        };

        let regions = self.region_starts();
        for (idx, group) in self.iter().enumerate() {
            let advice_io = mk_advice_io(group.inputs(), group.outputs(), &regions);
            let instance_io = mk_instance_io(group.inputs(), group.outputs(), &regions);

            io.advice_io.insert(idx, advice_io);
            io.instance_io.insert(idx, instance_io);
        }

        io
    }
}

impl AsRef<[Group]> for Groups {
    fn as_ref(&self) -> &[Group] {
        self.0.as_ref()
    }
}

impl Borrow<[Group]> for Groups {
    fn borrow(&self) -> &[Group] {
        self.as_ref()
    }
}

impl Deref for Groups {
    type Target = Vec<Group>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Contains information about the groups input and output cells.
#[derive(Debug, Clone)]
pub struct GroupsIO {
    advice_io: HashMap<usize, AdviceIO>,
    instance_io: HashMap<usize, InstanceIO>,
}

impl GroupsIO {
    /// Returns the advice IO cells for the given group.
    ///
    /// # Panics
    ///
    /// If the group number is not in the mapping.
    pub fn advice_io(&self, group: usize) -> &AdviceIO {
        &self.advice_io[&group]
    }

    /// Returns the intsnace IO cells for the given group.
    ///
    /// # Panics
    ///
    /// If the group number is not in the mapping.
    pub fn instance_io(&self, group: usize) -> &InstanceIO {
        &self.instance_io[&group]
    }
}

/// Represents a piece of the circuit's constraint system.
///
/// Is meant to be used for constructing the call graph. For
/// lowering use [`Groups`] instead.
/// Has a set of regions of the circuit that represents what gates
/// are enabled in it.
///
/// Can have children blocks that represent subpieces of the logic.
/// The boundary between parent and children is determined by the groups
/// the circuit declares during synthesis.
#[derive(Debug)]
pub(crate) struct GroupTree {
    base: GroupBase,
    children: Vec<GroupTree>,
}

impl GroupTree {
    /// Constructs an empty top-level group.
    fn top_level() -> Self {
        Self {
            base: GroupBase::top_level(),
            children: Default::default(),
        }
    }

    /// Constructs an empty group
    fn new(name: String, key: GroupKey) -> Self {
        Self {
            base: GroupBase::empty(name, key),
            children: Default::default(),
        }
    }

    fn flatten_impl(self, groups: &mut Vec<Group>) {
        let mut child_indices = vec![];
        for child in self.children {
            child.flatten_impl(groups);
            child_indices.push(groups.len() - 1);
        }
        groups.push(Group::with_children(self.base, child_indices));
    }

    /// Transforms the tree into a read-only flat representation.
    pub fn flatten(self) -> Groups {
        let mut groups = vec![];
        self.flatten_impl(&mut groups);
        Groups(groups)
    }
}

impl Deref for GroupTree {
    type Target = GroupBase;

    fn deref(&self) -> &Self::Target {
        &self.base
    }
}

impl DerefMut for GroupTree {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.base
    }
}

/// Manages the creation of groups during synthesis.
///
/// Starts with a top level group and automatically handles parent-children relations during
/// construction. New children are pushed into a stack until they are completely built.
/// Once completed they get added to the list of children of the next group in the stack.
///
/// The root group owned by the builder is always a top-level block.
#[derive(Debug)]
pub(crate) struct GroupBuilder {
    root: GroupTree,
    stack: Vec<GroupTree>,
}

impl GroupBuilder {
    /// Creates a builder with a top-level group as the root block.
    pub fn new() -> Self {
        Self {
            root: GroupTree::top_level(),
            stack: vec![],
        }
    }

    /// Returns a mutable reference to the group that is currently being built.
    /// Private to ensure that only the builder can mutate the groups.
    #[inline]
    pub fn current(&self) -> &GroupTree {
        if self.stack.is_empty() {
            &self.root
        } else {
            self.stack.last().unwrap()
        }
    }

    /// Returns a mutable reference to the group that is currently being built.
    /// Private to ensure that only the builder can mutate the groups.
    #[inline]
    fn current_mut(&mut self) -> &mut GroupTree {
        if self.stack.is_empty() {
            &mut self.root
        } else {
            self.stack.last_mut().unwrap()
        }
    }

    /// Returns the root and consumes the builder.
    ///
    /// Panics if there are pending groups on the stack.
    pub fn into_root(self) -> GroupTree {
        assert!(self.stack.is_empty(), "Builder has pending groups");
        self.root
    }

    /// Pushes a new group group into the stack.
    pub fn push(&mut self, name: String, key: GroupKey) {
        self.stack.push(GroupTree::new(name, key))
    }

    /// Pops the top of the stack and moves it to the list of children of the parent element.
    ///
    /// Panics if the stack is empty.
    pub fn pop(&mut self) {
        assert!(!self.stack.is_empty(), "No pending groups");
        let g = self.stack.pop().unwrap();
        self.current_mut().children.push(g);
    }

    /// Adds a cell to the current group's list of inputs.
    ///
    /// If the cell is a fixed cell it is ignored.
    pub fn add_input(&mut self, cell: impl Into<GroupCell>) {
        let cell = cell.into();
        if !cell.is_fixed() {
            self.current_mut().inputs.push(cell)
        }
    }

    /// Adds a cell to the current group's list of outputs.
    ///
    /// If the cell is a fixed cell it is ignored.
    pub fn add_output(&mut self, cell: impl Into<GroupCell>) {
        let cell = cell.into();
        if !cell.is_fixed() {
            self.current_mut().outputs.push(cell)
        }
    }

    /// Adds to the list of input and output cells of the top-level block.
    pub fn add_root_io<C: ColumnType>(&mut self, io: &CircuitIO<C>)
    where
        IOCell<C>: Into<GroupCell>,
    {
        self.root
            .inputs
            .extend(io.inputs().iter().copied().map(Into::into));
        self.root
            .outputs
            .extend(io.outputs().iter().copied().map(Into::into));
    }

    /// Returns a mutable reference to the regions in the current group.
    pub fn regions_mut(&mut self) -> &mut Regions {
        &mut self.current_mut().regions
    }
}

impl Default for GroupBuilder {
    fn default() -> Self {
        Self::new()
    }
}
