use llzk::prelude::{FuncDefOpRef, StructDefOpLike as _, StructDefOpRefMut};

use crate::{error::Error, members::Members};

/// Encapsulates pre-cached data generated during lowering.
#[derive(Debug)]
pub struct LoweringData<'c, 's> {
    pub constrain_func: FuncDefOpRef<'c, 's>,
    pub members: Members<'c, 's>,
}

impl<'c, 's> LoweringData<'c, 's> {
    pub fn new(
        struct_op: StructDefOpRefMut<'c, 's>,
        members: Members<'c, 's>,
    ) -> Result<Self, Error> {
        Ok(Self {
            constrain_func: struct_op
                .constrain_func()
                .ok_or(Error::MissingConstrainFunc)?,
            members,
        })
    }
}
