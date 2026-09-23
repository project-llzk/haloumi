//! Supporting types for loading and storing from cells.

use std::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
    str::FromStr,
};

use crate::{circuit::io::layouter::AdviceCopy, core::table::DecomposeIn};
use ff::{Field, PrimeField};

use crate::{
    Types, circuit::io::load::LoadFromCells, error::Error, ir::inject::InjectedIR, parse_field,
};
