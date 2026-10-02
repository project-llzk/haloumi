//! Output context types.

use std::ops::{Deref, DerefMut};

use ff::Field;
use haloumi_core::{
    io::{ctx::BaseCtx, table::OutputDescr},
    layouter::{LayoutAdaptor, Layouter},
    table::DecomposeIn,
    types::Types,
};

/// Context type for the [`StoreIntoCells`](super::store::StoreIntoCells) trait.
#[derive(Debug)]
pub struct OCtx<'o, F: Field, H: Types<F>> {
    inner: BaseCtx<'o, OutputDescr<F, H>>,
}

impl<'o, F: Field, H: Types<F>> OCtx<'o, F, H> {
    /// Creates a new output context.
    pub fn new(input: impl Iterator<Item = OutputDescr<F, H>> + 'o) -> Self {
        Self {
            inner: BaseCtx::new(input),
        }
    }

    /// Sets the next output to zero.
    pub fn set_next_to_zero(
        &mut self,
        layouter: &mut LayoutAdaptor<'_, impl Layouter<F, H::Error>>,
    ) -> Result<(), H::Error> {
        self.next()?.set_to_zero(layouter)
    }

    /// Sets the next output to the given value.
    pub fn assign_next(
        &mut self,
        value: impl DecomposeIn<H::Cell>,
        layouter: &mut LayoutAdaptor<'_, impl Layouter<F, H::Error>>,
    ) -> Result<(), H::Error> {
        for cell in value.cells() {
            self.next()?.assign(cell, layouter)?;
        }
        Ok(())
    }
}

impl<'o, F: Field, H: Types<F>> Deref for OCtx<'o, F, H> {
    type Target = BaseCtx<'o, OutputDescr<F, H>>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<F: Field, H: Types<F>> DerefMut for OCtx<'_, F, H> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}
