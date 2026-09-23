//! Helper types for working with the layouter during the IO steps.

use ff::Field;
use haloumi_core::{
    layouter::{FromRegionAdaptor, LayoutAdaptor, Layouter, RegionAdaptor},
    query::{Advice, Instance},
    table::{Cell, Column, FromCell},
};

use crate::{Types, circuit::io::ctx::LayoutHelper};
