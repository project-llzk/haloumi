//! Traits related to layouter integration.

/// Implements halo2's Layouter trait for an implementation of Haloumi's Layouter trait.
#[macro_export]
macro_rules! __impl_layouter_adaptor {
    ($($layouter:ident)::+, $($region_layouter:ident)::+, $($table_layouter:ident)::+, $field:path, $error:ty, $($region:ident)::+, $($table:ident)::+, $($value:ident)::+, $cell:ty, $instance_col:ty, $challenge:ty) => {
        impl<F, L> $($layouter)::+<F> for $crate::core::layouter::LayoutAdaptor<'_, L> where
            F: $field,
            L: $crate::core::layouter::Layouter<F, $error> + $crate::core::groups::RegionsGroupHooks<F, $cell, Error = $error> {
            type Root = Self;

            fn assign_region<A, AR, N, NR>(&mut self, name: N, mut assignment: A) -> Result<AR, $error>
            where
                A: FnMut($($region)::+<'_, F>) -> Result<AR, $error>,
                N: Fn() -> NR,
                NR: Into<String> {
                    self.0.assign_region(name, |mut region| {
                        let region = $($region)::+::from(&mut region as &mut dyn $($region_layouter)::+<F>);
                        assignment(region)
                    })
            }

            fn assign_table<A, N, NR>(&mut self, name: N, mut assignment: A) -> Result<(), $error>
            where
                A: FnMut($($table)::+<'_, F>) -> Result<(), $error>,
                N: Fn() -> NR,
                NR: Into<String> {
                    self.0.assign_table(name, |mut table| {
                        let table = $($table)::+::from(&mut table as &mut dyn $($table_layouter)::+<F>);
                        assignment(table)
                    })
                }

            fn constrain_instance(
                &mut self,
                cell: $cell,
                column: $instance_col,
                row: usize,
            ) -> Result<(), $error> {
                self.0.constrain_instance(cell, column, row)
            }

            fn get_challenge(&self, challenge: $challenge) -> $($value)::+<F> {
                match self.0.get_challenge(challenge) { Some(v) => $($value)::+::known(v), None => $($value)::+::unknown() }
            }

            fn get_root(&mut self) -> &mut Self::Root { self }

            fn push_namespace<NR, N>(&mut self, name_fn: N)
            where
                NR: Into<String>,
                N: FnOnce() -> NR {
                    self.0.push_namespace(name_fn);
            }

            fn pop_namespace(&mut self, gadget_name: Option<String>) {
                self.0.pop_namespace(gadget_name);
            }

        }
    };
}

/// Implements halo2's RegionLayouter trait for an implementation of Haloumi's RegionLayouter trait.
#[macro_export]
macro_rules! __impl_region_layouter_adaptor {
    ($($layouter:ident)::+,
     $field:path,
     $error:ty,
     $($value:ident)::+,
     $($rational:ident)::+,
     $cell:ty,
     $instance_col:ty,
     $advice_col:ty,
     $fixed_col:ty,
     $any_col:ty,
     $selector:ty
    ) => {
        impl<F: $field> $($layouter)::+<F> for $crate::core::layouter::RegionAdaptor<'_, F, $error> {
            fn enable_selector<'v>(
                &'v mut self,
                annotation: &'v (dyn Fn() -> String + 'v),
                selector: &$selector,
                offset: usize,
            ) -> Result<(), $error> {
                self.0.enable_selector(annotation, selector, offset)
            }

            fn name_column<'v>(
                &'v mut self,
                annotation: &'v (dyn Fn() -> String + 'v),
                column: $any_col,
            ) {
                self.0.name_column(annotation, column.into())
            }

            fn assign_advice<'v>(
                &'v mut self,
                annotation: &'v (dyn Fn() -> String + 'v),
                column: $advice_col,
                offset: usize,
                to: &'v mut (dyn FnMut() -> $($value)::+<$($rational)::+<F>> + 'v),
            ) -> Result<$cell, $error> {
                Ok(self.0.assign_advice(annotation, column.into(), offset, &mut || {
                    let value = to();
                    value.into_option().map(|r| r.evaluate())
                })?.into())
            }

            fn assign_advice_from_constant<'v>(
                &'v mut self,
                annotation: &'v (dyn Fn() -> String + 'v),
                column: $advice_col,
                offset: usize,
                constant: $($rational)::+<F>,
            ) -> Result<$cell, $error> {
                Ok(self.0.assign_advice_from_constant(annotation, column.into(), offset, constant.evaluate())?.into())
            }

            fn assign_advice_from_instance<'v>(
                &mut self,
                annotation: &'v (dyn Fn() -> String + 'v),
                instance: $instance_col,
                row: usize,
                advice: $advice_col,
                offset: usize,
            ) -> Result<($cell, $($value)::+<F>), $error> {
                let (cell, value) = self.0.assign_advice_from_instance(annotation, instance.into(), row, advice.into(), offset)?;
                Ok((cell.into(), match value { Some(v) => $($value)::+::known(v), None => $($value)::+::unknown() }))
            }

            fn instance_value(&mut self, instance: $instance_col, row: usize)
                -> Result<$($value)::+<F>, $error> {
                Ok(match self.0.instance_value(instance.into(), row)? { Some(v) => $($value)::+::known(v), None => $($value)::+::unknown() })
            }

            fn assign_fixed<'v>(
                &'v mut self,
                annotation: &'v (dyn Fn() -> String + 'v),
                column: $fixed_col,
                offset: usize,
                to: &'v mut (dyn FnMut() -> $($value)::+<$($rational)::+<F>> + 'v),
            ) -> Result<$cell, $error> {
                Ok(self.0.assign_fixed(annotation, column.into(), offset, &mut || {
                    let value = to();
                    value.into_option().map(|r| r.evaluate())
                })?.into())
            }

            fn constrain_constant(&mut self, cell: $cell, constant: $($rational)::+<F>) -> Result<(), $error> {
                self.0.constrain_constant(cell.into(), constant.evaluate())
            }

            fn constrain_equal(&mut self, left: $cell, right: $cell) -> Result<(), $error> {
                self.0.constrain_equal(left.into(), right.into())
            }
        }
    };
}

/// Implements halo2's TableLayouter trait for an implementation of Haloumi's TableLayouter trait.
#[macro_export]
macro_rules! __impl_table_layouter_adaptor {
    ($($layouter:ident)::+,
     $field:path,
     $error:ty,
     $($value:ident)::+,
     $($rational:ident)::+,
     $table_col:ty,
    ) => {
        impl <F: $field> $($layouter)::+<F> for $crate::core::layouter::TableAdaptor<'_, F, $error> {
            fn assign_cell<'v>(
                &'v mut self,
                annotation: &'v (dyn Fn() -> String + 'v),
                column: $table_col,
                offset: usize,
                to: &'v mut (dyn FnMut() -> $($value)::+<$($rational)::+<F>> + 'v),
            ) -> Result<(), $error> {
                self.0.assign_cell(annotation, column.inner().into(), offset, &mut || {
                    let value = to();
                    value.into_option().map(|r| r.evaluate())
                })
            }
        }
    };
}

/// Implements the `FromRegionAdaptor` trait.
#[macro_export]
macro_rules! __impl_from_region_adaptor {
    ($($region:ident)::+,
     $($region_layouter:ident)::+,
     $field:path,
     $error:ty
    ) => {
        impl<'a, F: $field> $crate::core::layouter::FromRegionAdaptor<'a, F, $error> for $($region)::+<'a, F> where
            $crate::core::layouter::RegionAdaptor<'_, F, $error>: $($region_layouter)::+<F>
        {
            fn from_region_adaptor(adaptor: &'a mut $crate::core::layouter::RegionAdaptor<'_, F, $error>) -> Self {
                Self::from(adaptor as &mut dyn $($region_layouter)::+<F>)
            }
        }
    };
}
