//! Macros for integrating types related to groups with a Halo2 implementation.

/// Implements `Layouter<F>` for `GroupLayouter`.
///
/// This macro needs to be injected in the target halo2 crate.
#[macro_export]
macro_rules! __impl_layouter_for_group_layouter {
    ($field:path, $($layouter:ident)::+, $error:ty, $($region:ident)::+, $($table:ident)::+, $cell: ty, $instance_col:ty, $challenge:ty, $($value:ident)::+) => {
        impl<'l, F, L> $($layouter)::+<F> for $crate::core::groups::GroupLayouter<'l, F, L>
        where
            F: $field,
            L: $($layouter)::+<F> + $crate::core::groups::RegionsGroupHooks<F, $cell>,
        {
            type Root = <L as $($layouter)::+<F>>::Root;

            fn assign_region<A, AR, N, NR>(
                &mut self,
                name: N,
                mut assignment: A,
            ) -> Result<AR, $error>
            where
                A: FnMut($($region)::+<'_, F>) -> Result<AR, $error>,
                N: Fn() -> NR,
                NR: Into<String>,
            {
                let mut call_count = 0;
                let flag = self.flag();
                self.parent.assign_region(name, move |region| {
                    // Enable annotating only the first time we call the closure.
                    flag.set(call_count == 0);
                    let r = assignment(region);
                    flag.enable();
                    call_count += 1;
                    r
                })
            }

            fn assign_table<A, N, NR>(&mut self, name: N, mut assignment: A) -> Result<(), $error>
            where
                A: FnMut($($table)::+<'_, F>) -> Result<(), $error>,
                N: Fn() -> NR,
                NR: Into<String>,
            {
                let mut call_count = 0;
                let flag = self.flag();
                self.parent.assign_table(name, move |table| {
                    // Enable annotating only the first time we call the closure.
                    flag.set(call_count == 0);
                    let r = assignment(table);
                    flag.enable();
                    call_count += 1;
                    r
                })
            }

            fn constrain_instance(
                &mut self,
                cell: $cell,
                column: $instance_col,
                row: usize,
            ) -> Result<(), $error> {
                self.parent.constrain_instance(cell, column, row)
            }

            fn get_challenge(&self, challenge: $challenge) -> $($value)::+<F> {
                self.parent.get_challenge(challenge)
            }

            fn get_root(&mut self) -> &mut Self::Root {
                self.parent.get_root()
            }

            fn push_namespace<NR, N>(&mut self, name_fn: N)
            where
                NR: Into<String>,
                N: FnOnce() -> NR,
            {
                self.parent.push_namespace(name_fn)
            }

            fn pop_namespace(&mut self, gadget_name: Option<String>) {
                self.parent.pop_namespace(gadget_name)
            }
        }
    };
}

/// Opens a group using the given layouter that implements the hooks.
///
/// This version is only enabled during extraction. Outside of
/// extraction a different version of this function exists that
/// transparently forwards the layouter to the body as if nothing happened.
#[cfg(groups)]
#[doc(hidden)]
#[macro_export]
macro_rules! __group {
    ($layouter:ident, $name:expr, $key:expr, |$layouter_clo:ident, $groups:ident| $assignment:block) => {
        $layouter.group($name, $key, |$layouter_clo, $groups| $assignment)
    };
}

/// Forwards the layouter directly to the body of the function.
///
/// This version is enabled by default and is meant for transparently
/// building circuits outside of extraction mode.
#[cfg(not(groups))]
#[doc(hidden)]
#[macro_export]
macro_rules! __group {
    ($layouter:ident, $name:expr, $key:expr, |$layouter_clo:ident, $groups:ident| $assignment:block) => {{
        let $layouter_clo = $layouter;
        let $groups = ();
        $assignment
    }};
}

/// Annotates a collection of decomposable cells as inputs.
///
/// This version is only enabled during extraction. Outside of
/// extraction a different version of this function exists that
/// is a no-op.
#[cfg(groups)]
#[doc(hidden)]
#[macro_export]
macro_rules! __annotate_input_cells {
    ($scope:expr, $value:expr) => {
        $scope.annotate_as_input(&$value);
    };
}

/// No-op version of the input annotation function for using outside of
/// extraction mode.
#[cfg(not(groups))]
#[doc(hidden)]
#[macro_export]
macro_rules! __annotate_input_cells {
    ($scope:expr, $value:expr) => {};
}

/// Annotates a collection of decomposable cells as outputs.
///
/// This version is only enabled during extraction. Outside of
/// extraction a different version of this function exists that
/// is a no-op.
#[cfg(groups)]
#[doc(hidden)]
#[macro_export]
macro_rules! __annotate_output_cells {
    ($scope:expr, $value:expr) => {
        $scope.annotate_as_output(&$value)
    };
}

/// No-op version of the output annotation function for using outside of
/// extraction mode.
#[cfg(not(groups))]
#[doc(hidden)]
#[macro_export]
macro_rules! __annotate_output_cells {
    ($scope:expr, $value:expr) => {};
}
