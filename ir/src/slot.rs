//! Trait implementations for [`Slot`].

use crate::{
    Slot,
    printer::{IRPrintable, IRPrinterCtx},
};
use std::fmt::Write;

impl IRPrintable for Slot {
    fn fmt(&self, ctx: &mut IRPrinterCtx<'_, '_>) -> crate::printer::Result {
        match self {
            Slot::Arg(arg_no) => write!(ctx, "(input {arg_no})"),
            Slot::Output(field_id) => write!(ctx, "(output {field_id})"),
            Slot::Advice(cell_ref) => {
                write!(ctx, "(advice {cell_ref})")
            }
            Slot::Fixed(cell_ref) => write!(ctx, "(fixed {cell_ref})"),
            Slot::TableLookup(id, col, row, idx, region) => {
                write!(ctx, "(lookup {id} {col} {row} {idx} {region})")
            }
            Slot::CallOutput(call, idx) => write!(ctx, "(call-result {call} {idx})"),
            Slot::Temp(temp) => write!(ctx, "(temp {})", *temp),
            Slot::Challenge(index, phase, _) => write!(ctx, "(challenge {index} {phase})"),
        }
    }
}
