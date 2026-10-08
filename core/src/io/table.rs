//! Types related to tables.

use std::marker::PhantomData;

use crate::{
    layouter::{LayoutAdaptor, Layouter},
    types::Types,
};
use ff::Field;

/// A cell in the table.
#[derive(Debug)]
pub struct Cell<C> {
    col: C,
    row: usize,
}

impl<C> Cell<C> {
    /// Creates a new cell.
    pub fn new(col: C, row: usize) -> Self {
        Self { col, row }
    }

    /// Creates a new cell in row 0.
    pub fn first_row(col: C) -> Self {
        Self::new(col, 0)
    }

    /// Returns the column of the cell.
    pub fn col(&self) -> C
    where
        C: Copy,
    {
        self.col
    }

    /// Returns the row of the cell.
    pub fn row(&self) -> usize {
        self.row
    }
}

impl<C> From<(C, usize)> for Cell<C> {
    fn from((col, row): (C, usize)) -> Self {
        Self::new(col, row)
    }
}

/// A description for an input. Comprises an instance cell that represents the
/// actual input and an advice cell that is used for integrating better with
/// regions.
#[derive(Debug)]
pub struct InputDescr<F: Field, H: Types<F>> {
    cell: Cell<H::InstanceCol>,
    temp: Cell<H::AdviceCol>,
    _marker: PhantomData<F>,
}

impl<F: Field, H: Types<F>> InputDescr<F, H> {
    /// Creates a new input description.
    pub fn new(cell: Cell<H::InstanceCol>, temp: H::AdviceCol) -> Self {
        Self {
            cell,
            temp: Cell::first_row(temp),
            _marker: Default::default(),
        }
    }

    /// Returns the column of the instance cell.
    pub fn col(&self) -> H::InstanceCol {
        self.cell.col()
    }

    /// Returns the row of the instance cell.
    pub fn row(&self) -> usize {
        self.cell.row()
    }

    /// Returns the column of the helper advice cell.
    pub fn temp(&self) -> H::AdviceCol {
        self.temp.col()
    }

    /// Returns the row of the helper advice cell.
    pub fn temp_offset(&self) -> usize {
        self.temp.row()
    }
}

impl<F: Field, Ts: Types<F>> From<OutputDescr<F, Ts>> for InputDescr<F, Ts> {
    fn from(descr: OutputDescr<F, Ts>) -> Self {
        InputDescr {
            cell: (descr.cell.col(), descr.cell.row).into(),
            temp: descr.helper,
            _marker: Default::default(),
        }
    }
}

/// A description for an output. Comprises an instance cell acting as the output
/// and a support advice cell.
#[derive(Debug)]
pub struct OutputDescr<F: Field, H: Types<F>> {
    cell: Cell<H::InstanceCol>,
    helper: Cell<H::AdviceCol>,
    _marker: PhantomData<F>,
}

impl<F: Field, Ts: Types<F>> OutputDescr<F, Ts> {
    /// Creates a new output description.
    pub fn new(cell: Cell<Ts::InstanceCol>, helper: Ts::AdviceCol) -> Self {
        Self {
            cell,
            helper: Cell {
                col: helper,
                row: 0,
            },
            _marker: Default::default(),
        }
    }

    /// Sets the output cell to be equal to 0.
    pub fn set_to_zero(
        &self,
        layouter: &mut LayoutAdaptor<'_, impl Layouter<F, Ts::Error>>,
    ) -> Result<(), Ts::Error> {
        let helper_cell = layouter.constrain_advice_constant::<F, Ts>(
            self.helper.col,
            self.helper.row,
            F::ZERO,
        )?;
        layouter.constrain_instance::<F, Ts>(helper_cell, self.cell.col, self.cell.row)?;
        Ok(())
    }

    /// Adds an equality constraint between the cell and the instance cell representing the output.
    pub fn assign(
        &self,
        cell: Ts::Cell,
        layouter: &mut LayoutAdaptor<'_, impl Layouter<F, Ts::Error>>,
    ) -> Result<(), Ts::Error> {
        layouter.constrain_instance::<F, Ts>(cell, self.cell.col(), self.cell.row())?;
        Ok(())
    }
}
