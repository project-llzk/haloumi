//! Macros for integrating types in the [`::core::table`] module.

/// Implements `From<RegionIndex>` for [`::core::table::RegionIndex`].
///
/// The macro needs to be injected in the same file where `RegionIndex` is defined.
#[macro_export]
macro_rules! __impl_from_region_index_for_haloumi_region_index {
    ($region_index:ty) => {
        impl From<$region_index> for $crate::core::table::RegionIndex {
            fn from(idx: $region_index) -> Self {
                Self::from(idx.0)
            }
        }
    };
}

/// Implements `From<Cell>` for [`::core::table::Cell`].
///
/// The macro needs to be injected in the same file where `Cell` is defined.
#[macro_export]
macro_rules! __impl_from_cell_for_haloumi_cell {
    ($cell:ty) => {
        impl From<$cell> for $crate::core::table::Cell {
            fn from(idx: $cell) -> Self {
                Self {
                    region_index: cell.region_index.into(),
                    row_offset: cell.row_offset,
                    column: cell.column.into(),
                }
            }
        }
    };
}

/// Implements the required traits for integrating with [`::core::table::Column`].
#[macro_export]
macro_rules! __impl_column_support {
    ($column_trait:path, $column:path, $any:ty, $instance:ty, $advice:ty,$fixed:ty) => {
        impl<F: $column_trait + Into<T>, T: $crate::core::table::ColumnType> From<$column<F>>
            for $crate::core::table::Column<T>
        {
            fn from(value: $column<F>) -> Self {
                Self::new(value.index, value.column_type.into())
            }
        }

        impl TryFrom<$column<$any>> for $crate::core::table::Column<$crate::core::table::Instance> {
            type Error = <$column<$instance> as TryFrom<$column<$any>>>::Error;

            fn try_from(value: $column<$any>) -> Result<Self, Self::Error> {
                $column::<$instance>::try_from(value).map(Into::into)
            }
        }

        impl TryFrom<$column<$any>> for $crate::core::table::Column<$crate::core::table::Advice> {
            type Error = <$column<$advice> as TryFrom<$column<$any>>>::Error;

            fn try_from(value: $column<$any>) -> Result<Self, Self::Error> {
                $column::<$advice>::try_from(value).map(Into::into)
            }
        }

        impl TryFrom<$column<$any>> for $crate::core::table::Column<$crate::core::table::Fixed> {
            type Error = <$column<$fixed> as TryFrom<$column<$any>>>::Error;

            fn try_from(value: $column<$any>) -> Result<Self, Self::Error> {
                $column::<$fixed>::try_from(value).map(Into::into)
            }
        }

        impl From<$any> for $crate::core::table::Any {
            fn from(value: $any) -> Self {
                match value {
                    $any::Advice(_) => Self::Advice,
                    $any::Fixed => Self::Fixed,
                    $any::Instance => Self::Instance,
                }
            }
        }

        impl From<$instance> for $crate::core::table::Instance {
            fn from(_: $instance) -> Self {
                Self
            }
        }

        impl From<$instance> for $crate::core::table::Any {
            fn from(_: $instance) -> Self {
                Self::Instance
            }
        }

        impl From<$advice> for $crate::core::table::Advice {
            fn from(_: $advice) -> Self {
                Self
            }
        }

        impl From<$advice> for $crate::core::table::Any {
            fn from(_: $advice) -> Self {
                Self::Advice
            }
        }

        impl From<$fixed> for $crate::core::table::Fixed {
            fn from(_: $fixed) -> Self {
                Self
            }
        }
        impl From<$fixed> for $crate::core::table::Any {
            fn from(_: $fixed) -> Self {
                Self::Fixed
            }
        }
    };
}
