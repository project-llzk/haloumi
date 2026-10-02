//! Macros for implementing info traits in a Halo2 implementation.

/// Implements the [`::core::info_traits::SelectorInfo`] for `Selector`.
#[macro_export]
macro_rules! __impl_selector_info_for_selector {
    ($selector:ty) => {
        impl $crate::core::info_traits::SelectorInfo for $selector {
            fn id(&self) -> usize {
                self.index()
            }
        }
    };
}

/// Implements the [`::core::info_traits::QueryInfo`] trait.
#[macro_export]
macro_rules! __impl_query_info {
    ($query:ty, $kind:ident) => {
        impl $crate::core::info_traits::QueryInfo for $query {
            type Kind = $crate::core::query::$kind;

            fn rotation(&self) -> $crate::core::table::Rotation {
                self.rotation.0
            }

            fn column_index(&self) -> usize {
                self.column_index
            }
        }
    };
}

/// Implements the [`::core::info_traits::CreateQuery`] trait.
#[macro_export]
macro_rules! __impl_create_query {
    ($query:ty, $field:path, $rotation:path, $new:expr, $($expr:ident)::+) => {
        impl<F: $field> $crate::core::info_traits::CreateQuery<$($expr)::+<F>> for $query {
            fn query_expr(index: usize, at: $crate::core::table::Rotation) -> $($expr)::+<F> {
                { $new }.query_cell(index, ($rotation)(at))
            }
        }
    };
}

/// Implements the [`::core::info_traits::ChallengeInfo`] trait.
#[macro_export]
macro_rules! __impl_challenge_info_for_challenge {
    ($challenge:ty) => {
        impl $crate::core::info_traits::ChallengeInfo for $challenge {
            fn index(&self) -> usize {
                self.index
            }

            fn phase(&self) -> u8 {
                self.phase()
            }
        }
    };
}

/// Implements the [`::core::info_traits::GateInfo`] trait.
#[macro_export]
macro_rules! __impl_gate_info_for_gate {
    ($($gate:ident)::+, $field:path, $($expr:ident)::+) => {
        impl<F: $field> $crate::core::info_traits::GateInfo<$($expr)::+<F>> for $($gate)::+<F> {
            fn name(&self) -> &str {
                &self.name
            }

            fn polynomials(&self) -> &[$($expr)::+<F>] {
                &self.polys
            }
        }
    };
}

/// Implements the [`::core::info_traits::ConstraintSystemInfo`] trait.
#[macro_export]
macro_rules! __impl_constraint_system_info_for_constraint_system {
    ($($cs:ident)::+, $field:path, $($expr:ident)::+) => {
        impl<F: $field> $crate::core::info_traits::ConstraintSystemInfo<F> for $($cs)::+<F> {
            type Polynomial = $($expr)::+<F>;

            fn gates(&self) -> Vec<&dyn $crate::core::info_traits::GateInfo<Self::Polynomial>> {
                self.gates
                    .iter()
                    .map(|g| g as &dyn $crate::core::info_traits::GateInfo<Self::Polynomial>)
                    .collect()
            }

            fn lookups<'cs>(
                &'cs self,
            ) -> Vec<$crate::core::lookups::LookupData<'cs, Self::Polynomial>> {
                self.lookups
                    .iter()
                    .map(|l| $crate::core::lookups::LookupData {
                        name: l.name(),
                        arguments: &l.input_expressions,
                        table: &l.table_expressions,
                    })
                    .collect()
            }
        }
    };
}
