//! Input context types.

use std::{
    fmt,
    ops::{Deref, DerefMut},
    str::FromStr,
};

use ff::{Field, PrimeField};
use haloumi_core::{
    error::Error,
    io::{ctx::BaseCtx, error::IoError, table::InputDescr},
    layouter::{LayoutAdaptor, Layouter},
    types::Types,
};
use haloumi_ir::inject::InjectedIR;

use crate::io::load::LoadFromCells;

/// Context type for the [`LoadFromCells`](super::load::LoadFromCells) trait.
pub struct ICtx<'i, 's, F: Field, H: Types<F>> {
    inner: BaseCtx<'i, InputDescr<F, H>>,
    constants: Box<dyn Iterator<Item = &'s str> + 's>,
}

impl<'i, 's, F: Field, H: Types<F>> ICtx<'i, 's, F, H> {
    /// Creates a new input context.
    pub fn new(i: impl Iterator<Item = InputDescr<F, H>> + 'i, constants: &'s [String]) -> Self {
        Self {
            inner: BaseCtx::new(i),
            constants: Box::new(constants.iter().map(|s| s.as_str())),
        }
    }

    /// Returns the next constant.
    fn next_constant(&mut self) -> Result<&str, Error> {
        self.constants
            .next()
            .ok_or_else(|| IoError::NotEnoughConstants.into())
    }

    /// Tries to parse a constant as a field element.
    pub fn field_constant<O>(&mut self) -> Result<O, Error>
    where
        O: PrimeField,
    {
        self.next_constant().and_then(parse_field::<O>)
    }

    /// Tries to parse a primitive constant.
    pub fn primitive_constant<T, E>(&mut self) -> Result<T, Error>
    where
        T: FromStr<Err = E>,
        IoError: From<E>,
    {
        Ok(T::from_str(self.next_constant()?).map_err(IoError::from)?)
    }

    /// Assigns the next input to a cell.
    pub fn assign_next<V>(
        &mut self,
        layouter: &mut LayoutAdaptor<'_, impl Layouter<F, H::Error>>,
    ) -> Result<H::AssignedCell<V>, H::Error>
    where
        V: Clone,
        H::Rational: for<'v> From<&'v V>,
    {
        let i = self.next()?;
        layouter.assign_advice_from_instance::<F, H, V>(i.temp(), i.temp_offset(), i.col(), i.row())
    }

    /// Loads an instance from a set of cells.
    pub fn load<T, C>(
        &mut self,
        chip: &C,
        layouter: &mut LayoutAdaptor<'_, impl Layouter<F, H::Error>>,
        injected_ir: &mut InjectedIR<H::RegionIndex, H::Expression>,
    ) -> Result<T, H::Error>
    where
        T: LoadFromCells<F, C, H>,
    {
        T::load(self, chip, layouter, injected_ir)
    }
}

impl<'i, F: Field, H: Types<F>> Deref for ICtx<'i, '_, F, H> {
    type Target = BaseCtx<'i, InputDescr<F, H>>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<F: Field, H: Types<F>> DerefMut for ICtx<'_, '_, F, H> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<F: Field, H: Types<F>> fmt::Debug for ICtx<'_, '_, F, H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ICtx")
            .field("inner", &self.inner)
            .field("constants", &"<iterator>")
            .finish()
    }
}

/// Parses a value of F from the given string.
pub fn parse_field<F: PrimeField>(mut s: &str) -> Result<F, Error> {
    while s.len() > 1 && s.starts_with('0') {
        s = &s[1..];
    }
    if s.is_empty() {
        return Err(IoError::FieldParsingError.into());
    }
    F::from_str_vartime(s).ok_or(IoError::FieldParsingError.into())
}
