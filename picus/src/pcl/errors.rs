use crate::pcl::note::Note;

#[derive(Debug, thiserror::Error)]
pub enum ExprArgsError {
    #[error("Idx {idx} is out of bounds for {place} (size = {size}){note}")]
    OutOfBounds {
        idx: usize,
        place: &'static str,
        size: usize,
        note: Note,
    },
    #[error("Was expecting {expected} expression{note}")]
    UnexpectedExprType { expected: &'static str, note: Note },
}
