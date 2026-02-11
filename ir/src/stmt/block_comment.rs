use haloumi_lowering::{Lowering, Result as LoweringResult, lowerable::LowerableStmt};

use crate::{
    error::Error,
    stmt::IRStmt,
    traits::{Canonicalize, ConstantFolding},
};

pub struct BlockComment<T> {
    comment: Option<String>,
    body: Box<IRStmt<T>>,
}

impl<T> BlockComment<T> {
    pub fn new(comment: Option<String>, body: IRStmt<T>) -> Self {
        Self {
            comment,
            body: Box::new(body),
        }
    }

    pub fn value(&self) -> Option<&str> {
        self.comment.as_deref()
    }

    pub fn body(&self) -> &IRStmt<T> {
        &self.body
    }

    pub fn take_body(self) -> IRStmt<T> {
        *self.body
    }

    pub fn body_mut(&mut self) -> &mut IRStmt<T> {
        &mut self.body
    }

    pub fn constant_fold(&mut self) -> Result<(), Error>
    where
        T: ConstantFolding + std::fmt::Debug + Clone,
        Error: From<T::Error>,
        T::T: Eq + Ord,
    {
        self.body.constant_fold()?;

        // Remove the comment if the body folded to nothing.
        if self.body.is_empty() {
            self.comment = None;
        }
        Ok(())
    }
}

impl<T> BlockComment<T>
where
    IRStmt<T>: Canonicalize,
{
    /// Matches the statements against a series of known patterns and applies rewrites if able to.
    pub fn canonicalize(&mut self) {
        self.body.canonicalize();
    }
}

impl<T> LowerableStmt for BlockComment<T>
where
    IRStmt<T>: LowerableStmt,
{
    fn lower<L>(self, l: &L) -> LoweringResult<()>
    where
        L: Lowering + ?Sized,
    {
        if let Some(comment) = self.comment {
            l.generate_comment(comment)?;
        }
        self.body.lower(l)
    }
}

impl<T: Clone> Clone for BlockComment<T> {
    fn clone(&self) -> Self {
        Self {
            comment: self.comment.clone(),
            body: self.body.clone(),
        }
    }
}

impl<T: PartialEq> PartialEq for BlockComment<T> {
    fn eq(&self, other: &Self) -> bool {
        self.comment == other.comment && self.body == other.body
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for BlockComment<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "block-comment '{}' {:?}",
            self.comment.as_deref().unwrap_or_default(),
            self.body
        )
    }
}
