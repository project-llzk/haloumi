//! IR metadata

use haloumi_core::{
    constraints::CopyConstraint,
    query::Fixed,
    table::{Any, Column, RegionIndex},
};
use internment::Intern;

use crate::groups::GroupKey;

/// Implemented by IR objects that have metadata.
pub trait HasMeta {
    /// Returns a reference to the metadata.
    fn meta(&self) -> &Meta;

    /// Returns a mutable reference to the metadata.
    fn meta_mut(&mut self) -> &mut Meta;
}

/// Metadata associated with an IR object.
#[derive(Debug, Copy, Clone, Default)]
pub struct Meta(Intern<MetaImpl>);

impl Meta {
    fn edit_meta(&mut self, mut f: impl FnMut(&mut MetaImpl)) {
        let mut meta = (*self.0.as_ref()).clone();
        f(&mut meta);
        self.0 = Intern::new(meta)
    }

    /// Sets the location at a PLONK gate.
    pub fn at_gate(
        &mut self,
        name: impl ToString,
        region_name: impl ToString,
        region: Option<RegionIndex>,
        row: Option<usize>,
    ) {
        self.edit_meta(|meta| {
            meta.location = Location::Gate {
                name: name.to_string(),
                region_name: region_name.to_string(),
                region,
            };
            if let Some(row) = row {
                meta.row = Some(row);
            }
        });
    }

    /// Sets the location at a copy constraint.
    pub fn at_copy_constraint(&mut self, constraint: CopyConstraint) {
        self.edit_meta(|meta| meta.location = Location::CopyConstraint(constraint))
    }

    /// Sets the location at a lookup.
    pub fn at_lookup(&mut self, name: impl ToString, idx: usize, row: Option<usize>) {
        self.edit_meta(|meta| {
            meta.location = Location::Lookup {
                name: name.to_string(),
                idx,
            };
            if let Some(row) = row {
                meta.row = Some(row);
            }
        })
    }

    /// Sets the location at an injection index.
    pub fn at_inject(&mut self, region: RegionIndex, index: Option<usize>) {
        self.edit_meta(|meta| meta.location = Location::Injected { region, index })
    }

    /// Sets the group information.
    pub fn at_group(&mut self, name: impl ToString, key: Option<GroupKey>) {
        self.edit_meta(|meta| {
            meta.group_meta = Some(GroupMeta {
                name: name.to_string(),
                key,
            });
        });
    }

    /// Sets the row.
    pub fn at_row(&mut self, row: usize) {
        self.edit_meta(|meta| {
            meta.row = Some(row);
        });
    }

    /// Completes the metadata with information from the given instance.
    ///
    /// Does not overwrite anything that has already been written.
    pub fn complete_with(&mut self, other: Self) {
        self.edit_meta(|meta| {
            let other = other.0.as_ref();
            if let Some(group_meta) = other.group_meta.as_ref() {
                meta.group_meta.get_or_insert_with(|| group_meta.clone());
            }
            if matches!(&meta.location, Location::Unknown) {
                meta.location = other.location.clone();
            }
            if let Some(row) = other.row {
                meta.row.get_or_insert(row);
            }
        })
    }
}

fn fmt_cell(
    column: &Column<Any>,
    row: &usize,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    write!(
        f,
        "({}:{}, {row})",
        match column.column_type() {
            haloumi_core::table::Any::Fixed => "Fix",
            haloumi_core::table::Any::Advice => "Adv",
            haloumi_core::table::Any::Instance => "Ins",
        },
        column.index(),
    )
}

fn fmt_fixed_cell(
    column: &Column<Fixed>,
    row: &usize,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    write!(f, "(Fix:{}, {row})", column.index(),)
}

impl std::fmt::Display for Meta {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let meta = self.0.as_ref();
        if let Some(group_meta) = meta.group_meta.as_ref() {
            write!(f, "group({}", group_meta.name)?;
            if let Some(key) = group_meta.key {
                write!(f, ", {key}")?;
            }
            write!(f, "): ")?;
        }
        match &meta.location {
            Location::Unknown => write!(f, "unknown"),
            Location::Gate {
                name,
                region_name,
                region,
            } => {
                write!(f, "gate '{name}' @ region '{region_name}'")?;
                match region {
                    Some(index) => write!(f, "({})", **index),
                    None => write!(f, "(unk)"),
                }
            }
            Location::CopyConstraint(CopyConstraint::Cells(lhs_col, lhs_row, rhs_col, rhs_row)) => {
                write!(f, "copy ")?;
                fmt_cell(lhs_col, lhs_row, f)?;
                write!(f, " === ")?;
                fmt_cell(rhs_col, rhs_row, f)
            }
            Location::CopyConstraint(CopyConstraint::Fixed(col, row, value)) => {
                write!(f, "copy ")?;
                fmt_fixed_cell(col, row, f)?;
                write!(f, " === {value}")
            }
            Location::Lookup { name, idx } => {
                write!(f, "lookup '{name}'({idx})")
            }
            Location::Injected { region, index } => {
                write!(f, "injected")?;
                if let Some(index) = index {
                    write!(f, "({index})")?;
                }
                write!(f, " @ R{}", **region)
            }
        }?;
        if let Some(row) = meta.row {
            write!(f, " @ row {row}")?;
        }
        Ok(())
    }
}

#[derive(Debug, Default, Hash, PartialEq, Eq, Clone)]
struct GroupMeta {
    name: String,
    key: Option<GroupKey>,
}

#[derive(Debug, Default, Hash, PartialEq, Eq, Clone)]
enum Location {
    #[default]
    Unknown,
    Gate {
        name: String,
        region_name: String,
        region: Option<RegionIndex>,
    },
    CopyConstraint(CopyConstraint),
    Lookup {
        name: String,
        idx: usize,
    },
    Injected {
        region: RegionIndex,
        index: Option<usize>,
    },
}

#[derive(Debug, Default, Hash, PartialEq, Eq, Clone)]
struct MetaImpl {
    group_meta: Option<GroupMeta>,
    location: Location,
    row: Option<usize>,
}
