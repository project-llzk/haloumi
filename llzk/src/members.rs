//! Types for working with struct members.

use std::{
    cell::RefCell,
    collections::{HashMap, hash_map},
    hash::{DefaultHasher, Hash as _, Hasher as _},
};

use llzk::{
    builder::OpBuilder,
    dialect::r#struct,
    error::Error as LlzkError,
    prelude::{MemberDefOpRef, StructDefOpLike as _, StructDefOpRefMut, StructType},
};
use melior::{
    Context,
    ir::{Location, Type},
};

use crate::{error::Error, factory::filename, state::LlzkCodegenState};

/// Hash version of [`MemberKind`] that avoids the lifetime of the callee name.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum MemberKindHash {
    /// Advice cells.
    Advice { col: usize, row: usize },
    /// Fixed cells.
    Fixed { col: usize, row: usize },
    /// Subcomponents called by the circuit.
    Callee { name: u64, id: usize },
    /// Output of the circuit
    Output { id: usize, public: bool },
    /// A temporary
    Temp { id: usize },
}

impl From<MemberKind<'_>> for MemberKindHash {
    fn from(value: MemberKind<'_>) -> Self {
        match value {
            MemberKind::Advice { col, row } => Self::Advice { col, row },
            MemberKind::Fixed { col, row } => Self::Fixed { col, row },
            MemberKind::Callee { name, id } => Self::Callee {
                name: {
                    let mut state = DefaultHasher::new();
                    name.hash(&mut state);
                    state.finish()
                },
                id,
            },
            MemberKind::Output { id, public } => Self::Output { id, public },
            MemberKind::Temp { id } => Self::Temp { id },
        }
    }
}

/// Types of members the circuit could have.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MemberKind<'s> {
    /// Advice cells.
    Advice { col: usize, row: usize },
    /// Fixed cells.
    Fixed { col: usize, row: usize },
    /// Subcomponents called by the circuit.
    Callee { name: &'s str, id: usize },
    /// Output of the circuit
    Output { id: usize, public: bool },
    /// A temporary
    Temp { id: usize },
}

impl MemberKind<'_> {
    /// String representation of the member's name.
    pub fn member_name(&self) -> String {
        match self {
            MemberKind::Advice { col, row } => format!("adv_{col}_{row}"),
            MemberKind::Fixed { col, row } => format!("fix_{col}_{row}"),
            MemberKind::Callee { name, id } => format!("subgrp_{name}_{id}"),
            MemberKind::Output { id, .. } => format!("out_{id}"),
            MemberKind::Temp { id } => format!("temp_{id}"),
        }
    }

    pub fn location<'c>(&self, context: &'c Context, struct_name: &str) -> Location<'c> {
        match self {
            MemberKind::Advice { col, row } => {
                let filename = filename(struct_name, Some("advice cell"));
                Location::new(context, &filename, *col, *row)
            }
            MemberKind::Fixed { col, row } => {
                let filename = filename(struct_name, Some("fixed cell"));
                Location::new(context, &filename, *col, *row)
            }
            MemberKind::Callee { name, id } => {
                let filename = filename(struct_name, Some(&format!("subgroup '{name}'")));
                Location::new(context, &filename, *id, 0)
            }
            MemberKind::Output { id, public } => {
                let section = if *public {
                    "public outputs"
                } else {
                    "private outputs"
                };
                let filename = filename(struct_name, Some(section));
                Location::new(context, &filename, *id, 0)
            }
            MemberKind::Temp { id } => {
                let filename = filename(struct_name, Some("Temporaries"));
                Location::new(context, &filename, *id, 0)
            }
        }
    }

    pub fn member_type<'c>(&self, state: &LlzkCodegenState<'c>) -> Type<'c> {
        match self {
            MemberKind::Advice { .. }
            | MemberKind::Fixed { .. }
            | MemberKind::Output { .. }
            | MemberKind::Temp { .. } => state.felt_type().into(),
            MemberKind::Callee { name, .. } => StructType::from_str(state.context(), name).into(),
        }
    }

    pub fn is_public(&self) -> bool {
        match self {
            MemberKind::Advice { .. }
            | MemberKind::Fixed { .. }
            | MemberKind::Callee { .. }
            | MemberKind::Temp { .. } => false,
            MemberKind::Output { public, .. } => *public,
        }
    }

    fn create_member_op<'c: 'v, 'v>(
        &self,
        builder: &OpBuilder<'c, '_>,
        state: &LlzkCodegenState<'c>,
        struct_name: &str,
    ) -> Result<MemberDefOpRef<'c, 'v>, LlzkError> {
        r#struct::member(
            builder,
            self.location(state.context(), struct_name),
            &self.member_name(),
            self.member_type(state),
            state.members_are_signals(),
            state.members_are_columns(),
            self.is_public(),
        )
    }

    /// Returns an iterator of outputs set to either public or private with ids in the given range.
    pub fn outputs(
        range: impl IntoIterator<Item = usize>,
        public: bool,
    ) -> impl Iterator<Item = Self> {
        range
            .into_iter()
            .map(move |id| MemberKind::Output { id, public })
    }
}

impl<'m> MemberKind<'m> {
    /// Returns an iterator of callees taken from the names list.
    pub fn callees<S: AsRef<str> + 'm>(
        callees: impl IntoIterator<Item = &'m S>,
    ) -> impl Iterator<Item = Self> {
        callees
            .into_iter()
            .map(AsRef::as_ref)
            .enumerate()
            .map(|(id, name)| MemberKind::Callee { name, id })
    }
}

#[derive(Debug)]
pub(crate) struct Members<'c, 's> {
    map: RefCell<HashMap<MemberKindHash, MemberDefOpRef<'c, 's>>>,
}

impl<'c, 's> Members<'c, 's> {
    pub fn new() -> Self {
        Self {
            map: Default::default(),
        }
    }

    pub fn get(
        &self,
        state: &'s LlzkCodegenState<'c>,
        struct_name: &str,
        builder: &OpBuilder<'c, '_>,
        kind: MemberKind<'_>,
    ) -> Result<MemberDefOpRef<'c, 's>, LlzkError> {
        let index = MemberKindHash::from(kind);
        let mut map = self.map.borrow_mut();
        match map.entry(index) {
            hash_map::Entry::Occupied(entry) => Ok(*entry.get()),
            hash_map::Entry::Vacant(entry) => {
                //let op = struct_op.find_or_create_member_def(&name, |builder| {
                //    log::debug!("Creating member named '@{name}'");
                //    kind.create_member_op(builder, state, struct_op.sym_name())
                //})?;
                Ok(*entry.insert(kind.create_member_op(builder, state, struct_name)?))
            }
        }
    }
}
