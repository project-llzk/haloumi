//! Helper types for working with the layouter during the IO steps.

use ff::Field;
use haloumi_core::{
    layouter::{LayoutAdaptor, Layouter},
    query::{Advice, Instance},
    table::{Cell, Column, FromCell},
};

use crate::{Types, circuit::io::ctx::LayoutHelper};

/// Wrapper over [`Layouter`] that implements
/// [`LayoutAdaptor`](extractor_support::cells::ctx::LayoutAdaptor).
#[derive(Debug)]
pub struct AdaptsLayouter<'a, 'l, L> {
    layouter: &'a mut LayoutAdaptor<'l, L>,
}

impl<'a, 'l, L> AdaptsLayouter<'a, 'l, L> {
    /// Constructs a new wrapper.
    pub fn new(layouter: &'a mut LayoutAdaptor<'l, L>) -> Self {
        Self { layouter }
    }
}

impl<F, T, L> LayoutHelper<F, T> for AdaptsLayouter<'_, '_, L>
where
    F: Field,
    T: Types<F>,
    L: Layouter<F, T::Error>,
{
    type Adaptee = L;

    fn adaptee_ref(&self) -> &L {
        self.layouter.0
    }

    fn adaptee_ref_mut(&mut self) -> &mut L {
        self.layouter.0
    }

    fn constrain_instance(
        &mut self,
        cell: T::Cell,
        instance_col: T::InstanceCol,
        instance_row: usize,
    ) -> Result<(), T::Error> {
        self.layouter
            .0
            .constrain_instance(cell.into(), instance_col, instance_row)
    }

    fn constrain_advice_constant(
        &mut self,
        advice_col: T::AdviceCol,
        advice_row: usize,
        constant: F,
    ) -> Result<T::Cell, T::Error> {
        let advice_col = Column::<Advice>::from(advice_col.into());
        Ok(self
            .layouter
            .0
            .assign_region(
                || format!("Adv[{}, {advice_row}] == 0", advice_col.index()),
                |region| {
                    region.0.assign_advice_from_constant(
                        &|| format!("Adv[{}, {advice_row}]", advice_col.index()),
                        advice_col,
                        advice_row,
                        constant,
                    )
                },
            )?
            .into())
    }

    fn assign_advice_from_instance<V>(
        &mut self,
        advice_col: T::AdviceCol,
        advice_row: usize,
        instance_col: T::InstanceCol,
        instance_row: usize,
    ) -> Result<T::AssignedCell<V>, T::Error>
    where
        V: Clone,
    {
        let advice_col = Column::<Advice>::from(advice_col.into());
        let instance_col = Column::<Instance>::from(instance_col.into());
        let c = self.layouter.0.assign_region(
            || "ins",
            |region| {
                region.0.assign_advice(
                    &|| {
                        format!(
                            "Adv[{}, +{advice_row}] == Ins[{}, {instance_row}]",
                            advice_col.index(),
                            instance_col.index()
                        )
                    },
                    advice_col,
                    advice_row,
                    &mut || None,
                )
            },
        )?;

        self.layouter
            .0
            .constrain_instance(c, instance_col, instance_row)?;
        Ok(from_cell_helper(c))
    }

    fn copy_advice<V>(
        &mut self,
        ac: &T::AssignedCell<V>,
        region: &mut T::Region<'_>,
        advice_col: T::AdviceCol,
        advice_row: usize,
    ) -> Result<T::AssignedCell<V>, T::Error>
    where
        V: Clone,
    {
        ac.copy_advice(region, advice_col, advice_row)
    }

    fn region<A, AR, N, NR>(&mut self, name: N, mut assignment: A) -> Result<AR, T::Error>
    where
        A: FnMut(T::Region<'_>) -> Result<AR, T::Error>,
        N: Fn() -> NR,
        NR: Into<String>,
    {
        self.layouter
            .0
            .assign_region(name, |adaptor| assignment(adaptor.into()))
    }
}

/// Supporting trait for implementing the [`LayoutHelper::copy_advice`].
pub trait AdviceCopy<V, F, T>: Sized
where
    F: ff::Field,
    T: Types<F, AssignedCell<V> = Self>,
{
    /// Performs the copy operation.
    fn copy_advice(
        &self,
        region: &mut T::Region<'_>,
        advice_col: T::AdviceCol,
        advice_row: usize,
    ) -> Result<Self, T::Error>;
}

/// Implements [`AdviceCopy`] for an assigned cell type.
#[macro_export]
macro_rules! __impl_advice_copy_for_assigned_cell {
    ($($assigned_cell:ident)::+, $field:path, $($types:ident)::+, $($region:ident)::+, $advice_col:ty, $error:ty) => {
        impl<F: $field, V> $crate::circuit::io::layouter<V, F, $($types)::+<F>> for $($assigned_cell)::+<V, F> {
            fn copy_advice(
                &self,
                region: &mut $($region)::+<'_, F>,
                advice_col: $advice_col,
                advice_row: usize,
            ) -> Result<Self, $error> {
                self.copy_advice(|| "", region, advice_col, advice_row)
            }
        }
    };
}

/// This helper is to keep the syntax of its users a bit more terse.
fn from_cell_helper<T>(cell: Cell) -> T
where
    T: FromCell,
{
    T::from_cell(cell)
}
