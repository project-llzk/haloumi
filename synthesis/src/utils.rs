//! Utility functions.

use std::{cmp::Ordering, fmt};

use haloumi_core::table::{Any, Column};

pub(crate) fn fmt_columns<'c>(
    columns: impl IntoIterator<Item = &'c Column<Any>>,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    let mut columns = Vec::from_iter(columns);
    columns.sort_by(|a, b| {
        match (a.column_type(), b.column_type()) {
            (Any::Instance, Any::Advice | Any::Fixed) | (Any::Advice, Any::Fixed) => {
                return Ordering::Less;
            }
            (Any::Fixed, Any::Instance | Any::Advice) | (Any::Advice, Any::Instance) => {
                return Ordering::Greater;
            }
            _ => {}
        }
        a.index().cmp(&b.index())
    });
    let columns = columns
        .into_iter()
        .map(|c| {
            format!(
                "{}:{}",
                match c.column_type() {
                    Any::Fixed => "Fix",
                    Any::Advice => "Adv",
                    Any::Instance => "Ins",
                },
                c.index()
            )
        })
        .collect::<Vec<_>>();

    write!(f, "{}", columns.join(", "))
}
