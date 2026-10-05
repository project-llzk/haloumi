use std::marker::PhantomData;

pub use haloumi_core::table::{Cell, RegionIndex};

pub struct AssignedCell<V, F> {
    cell: Cell,
    _data: PhantomData<(V, F)>,
}
