use eqv::{EqvRelation, equiv};
use haloumi_core::eqv::SymbolicEqv;
use haloumi_lowering::{
    Lowering, Result as LoweringResult,
    lowerable::{LowerableExpr, LowerableStmt},
};

use crate::{
    error::Error,
    expr::IRBexpr,
    stmt::IRStmt,
    traits::{Canonicalize, ConstantFolding},
};

/// Block of IR that is emitted conditionally.
///
/// It's useful for emitting IR that can be optimized out but there's no
/// pattern that handles it.
#[derive(Clone, PartialEq)]
pub struct CondBlock<T> {
    cond: IRBexpr<T>,
    // Body of the block. Boxed for indirection.
    body: Box<IRStmt<T>>,
}

impl<T> CondBlock<T> {
    pub fn new(cond: IRBexpr<T>, body: IRStmt<T>) -> Self {
        Self {
            cond,
            body: Box::new(body),
        }
    }

    pub fn cond(&self) -> &IRBexpr<T> {
        &self.cond
    }

    pub fn cond_mut(&mut self) -> &mut IRBexpr<T> {
        &mut self.cond
    }

    pub fn body(&self) -> &IRStmt<T> {
        &self.body
    }

    pub fn body_mut(&mut self) -> &mut IRStmt<T> {
        &mut self.body
    }

    pub fn map<O>(self, f: &mut impl FnMut(T) -> O) -> CondBlock<O> {
        CondBlock {
            cond: IRBexpr::map(self.cond, f),
            body: Box::new(self.body.map(f)),
        }
    }

    pub fn map_into<O>(&self, f: &mut impl FnMut(&T) -> O) -> CondBlock<O> {
        CondBlock {
            cond: IRBexpr::map_into(&self.cond, f),
            body: Box::new(self.body.map_into(f)),
        }
    }

    pub fn try_map<O, E>(self, f: &mut impl FnMut(T) -> Result<O, E>) -> Result<CondBlock<O>, E> {
        Ok(CondBlock {
            cond: IRBexpr::try_map(self.cond, f)?,
            body: Box::new(self.body.try_map(f)?),
        })
    }

    pub fn map_inplace(&mut self, f: &mut impl FnMut(&mut T)) {
        IRBexpr::map_inplace(&mut self.cond, f);
        self.body.map_inplace(f);
    }

    pub fn try_map_inplace<E>(
        &mut self,
        f: &mut impl FnMut(&mut T) -> Result<(), E>,
    ) -> Result<(), E> {
        IRBexpr::try_map_inplace(&mut self.cond, f)?;
        self.body.try_map_inplace(f)
    }

    pub fn constant_fold(&mut self) -> Result<Option<IRStmt<T>>, Error>
    where
        IRBexpr<T>: ConstantFolding<T = bool>,
        IRStmt<T>: ConstantFolding<Error = Error>,
        Error: From<<IRBexpr<T> as ConstantFolding>::Error>,
    {
        self.body.constant_fold()?;
        self.cond.constant_fold()?;

        Ok(match self.cond.const_value() {
            Some(false) => Some(IRStmt::empty()),
            _ => None,
        })
    }

    pub fn canonicalize(&mut self)
    where
        IRBexpr<T>: Canonicalize,
        IRStmt<T>: Canonicalize,
    {
        self.cond.canonicalize();
        self.body.canonicalize();
    }
}

impl<L, R> EqvRelation<CondBlock<L>, CondBlock<R>> for SymbolicEqv
where
    SymbolicEqv: EqvRelation<L, R>,
{
    fn equivalent(lhs: &CondBlock<L>, rhs: &CondBlock<R>) -> bool {
        let cond = equiv! { SymbolicEqv | lhs.cond(), rhs.cond() };
        let body = equiv! { SymbolicEqv | lhs.body(), rhs.body() };
        cond && body
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for CondBlock<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "emit-if ")?;
        std::fmt::Debug::fmt(self.cond(), f)?;
        writeln!(f, " {{")?;
        std::fmt::Debug::fmt(self.body(), f)?;
        writeln!(f, " }}")
    }
}

impl<T: LowerableExpr> LowerableStmt for CondBlock<T>
where
    IRBexpr<T>: ConstantFolding<T = bool>,
{
    fn lower<L>(self, l: &L) -> LoweringResult<()>
    where
        L: Lowering + ?Sized,
    {
        match self.cond.const_value() {
            Some(false) => Ok(()),
            _ => self.body.lower(l),
        }
    }
}
