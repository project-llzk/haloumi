//! Macros for integrating types related to groups with a Halo2 implementation.

/// Implements `Layouter<F>` for `GroupLayouter`.
///
/// This macro needs to be injected in the target halo2 crate.
#[macro_export]
macro_rules! __impl_layouter_for_group_layouter {
    ($field:path, $layouter:path, $error:ty, $region:path, $table:path, $cell: ty, $column:path, $instance:ty, $challenge:ty, $value:path) => {
        impl<'l, F, L> $layouter<F> for $crate::core::groups::GroupLayouter<'l, F, L>
        where
            F: $field,
            L: $layouter<F> + $crate::core::groups::RegionsGroupHooks<F, $cell>,
        {
            type Root = <L as $layouter<F>>::Root;

            fn assign_region<A, AR, N, NR>(
                &mut self,
                name: N,
                mut assignment: A,
            ) -> Result<AR, $error>
            where
                A: FnMut($region<'_, F>) -> Result<AR, $error>,
                N: Fn() -> NR,
                NR: Into<String>,
            {
                let mut call_count = 0;
                self.parent.assign_region(name, |region| {
                    // Enable annotating only the first time we call the closure.
                    self.set_enabled(call_count == 0);
                    let r = assignment(region);
                    self.enable();
                    call_count += 1;
                    r
                })
            }

            fn assign_table<A, N, NR>(&mut self, name: N, mut assignment: A) -> Result<(), $error>
            where
                A: FnMut($table<'_, F>) -> Result<(), $error>,
                N: Fn() -> NR,
                NR: Into<String>,
            {
                let mut call_count = 0;
                self.parent.assign_table(name, |table| {
                    // Enable annotating only the first time we call the closure.
                    self.set_enabled(call_count == 0);
                    let r = assignment(table);
                    self.enable();
                    call_count += 1;
                    r
                })
            }

            fn constrain_instance(
                &mut self,
                cell: $cell,
                column: $column<$instance>,
                row: usize,
            ) -> Result<(), $error> {
                self.parent.constrain_instance(cell, column, row)
            }

            fn get_challenge(&self, challenge: $challenge) -> $value<F> {
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
