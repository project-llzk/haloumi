use eqv::{EqvRelation, equiv};
use haloumi_core::eqv::SymbolicEqv;

use crate::{
    diagnostics::Diagnostic,
    error::Error,
    expr::{IRBexpr, IRConstBexpr, NonConstIRBexprError},
    stmt::IRStmt,
    traits::{Canonicalize, ConstantFolding, Validatable},
};

/// Block of IR that is emitted conditionally.
///
/// It's useful for emitting IR that can be optimized out but there's no
/// pattern that handles it.
#[derive(Clone, PartialEq)]
pub struct CondBlock<T> {
    cond: IRConstBexpr<T>,
    // Body of the block. Boxed for indirection.
    body: Box<IRStmt<T>>,
}

impl<T> CondBlock<T> {
    pub fn new(cond: IRConstBexpr<T>, body: IRStmt<T>) -> Self {
        Self {
            cond,
            body: Box::new(body),
        }
    }

    pub fn cond(&self) -> &IRBexpr<T> {
        &self.cond
    }

    pub fn body(&self) -> &IRStmt<T> {
        &self.body
    }

    pub fn map<O>(self, f: &mut impl FnMut(T) -> O) -> CondBlock<O> {
        CondBlock {
            cond: IRConstBexpr::map(self.cond, f),
            body: Box::new(self.body.map(f)),
        }
    }

    pub fn map_into<O>(&self, f: &mut impl FnMut(&T) -> O) -> CondBlock<O> {
        CondBlock {
            cond: IRConstBexpr::map_into(&self.cond, f),
            body: Box::new(self.body.map_into(f)),
        }
    }

    pub fn try_map<O, E>(self, f: &mut impl FnMut(T) -> Result<O, E>) -> Result<CondBlock<O>, E> {
        Ok(CondBlock {
            cond: IRConstBexpr::try_map(self.cond, f)?,
            body: Box::new(self.body.try_map(f)?),
        })
    }

    pub fn map_inplace(&mut self, f: &mut impl FnMut(&mut T)) {
        IRConstBexpr::map_inplace(&mut self.cond, f);
        self.body.map_inplace(f);
    }

    pub fn try_map_inplace<E>(
        &mut self,
        f: &mut impl FnMut(&mut T) -> Result<(), E>,
    ) -> Result<(), E> {
        IRConstBexpr::try_map_inplace(&mut self.cond, f)?;
        self.body.try_map_inplace(f)
    }

    pub fn validate<D>(&self) -> Result<Vec<D>, Vec<D>>
    where
        IRConstBexpr<T>: Validatable<Diagnostic = D, Context = ()>,
        D: Diagnostic,
    {
        self.cond.validate()
    }

    pub fn constant_fold(&mut self) -> Result<Option<IRStmt<T>>, Error>
    where
        IRBexpr<T>: ConstantFolding<T = bool>,
        IRStmt<T>: ConstantFolding<Error = Error>,
        Error: From<<IRBexpr<T> as ConstantFolding>::Error>,
    {
        self.body.constant_fold()?;
        self.cond.constant_fold()?;

        let const_value = self.cond.const_value().ok_or(NonConstIRBexprError)?;
        Ok(Some(if const_value {
            std::mem::take(&mut self.body)
        } else {
            IRStmt::empty()
        }))
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

#[cfg(test)]
mod tests {
    use haloumi_core::{felt::Felt, slot::arg::ArgNo};
    use rstest::{fixture, rstest};

    use crate::expr::IRAexpr;

    use super::*;

    type Stmt = IRStmt<IRAexpr>;
    type Bexpr = IRBexpr<IRAexpr>;

    fn true_bexpr() -> Bexpr {
        true.into()
    }

    fn false_bexpr() -> Bexpr {
        false.into()
    }

    fn truthy_const_bexpr1() -> Bexpr {
        let one = IRAexpr::constant(Felt::new(BabyBear::from(1)));
        let ten = IRAexpr::constant(Felt::new(BabyBear::from(10)));
        let eleven = IRAexpr::constant(Felt::new(BabyBear::from(11)));
        Bexpr::eq(one + ten, eleven)
    }

    fn falshy_const_bexpr1() -> Bexpr {
        let one = IRAexpr::constant(Felt::new(BabyBear::from(1)));
        let ten = IRAexpr::constant(Felt::new(BabyBear::from(10)));
        let twelve = IRAexpr::constant(Felt::new(BabyBear::from(12)));
        Bexpr::eq(one + ten, twelve)
    }

    fn non_const_bexpr1() -> Bexpr {
        let one = IRAexpr::constant(Felt::new(BabyBear::from(1)));
        let arg0 = IRAexpr::slot(ArgNo::from(0));
        let eleven = IRAexpr::constant(Felt::new(BabyBear::from(11)));
        Bexpr::eq(one + arg0, eleven)
    }

    fn test_stmt() -> Stmt {
        Stmt::comment("There is an assertion below").then(Stmt::assert(truthy_const_bexpr1()))
    }

    #[fixture]
    fn stmt() -> Stmt {
        test_stmt()
    }

    #[rstest]
    #[case(true_bexpr())]
    #[case(false_bexpr())]
    #[case(truthy_const_bexpr1())]
    #[case(falshy_const_bexpr1())]
    #[should_panic(expected = "NonConstIRBexprError")]
    #[case(non_const_bexpr1())]
    fn const_block_validation(stmt: Stmt, #[case] cond: Bexpr) {
        let cb = CondBlock::new(cond.try_into().unwrap(), stmt);
        let _ = cb.validate().unwrap();
    }

    #[rstest]
    #[case(truthy_const_bexpr1())]
    #[case(falshy_const_bexpr1())]
    fn const_block_validation_after_map(stmt: Stmt, #[case] cond: Bexpr) {
        let mut cb = CondBlock::new(cond.try_into().unwrap(), stmt);
        let _ = cb.validate().unwrap();
        cb.map_inplace(&mut |e| {
            *e = IRAexpr::slot(ArgNo::from(1));
        });
        let res = cb.validate();
        assert!(res.is_err());
    }

    #[rstest]
    #[case(true_bexpr(), test_stmt())]
    #[case(false_bexpr(), Stmt::empty())]
    #[case(truthy_const_bexpr1(), test_stmt())]
    #[case(falshy_const_bexpr1(), Stmt::empty())]
    fn const_block_folding(stmt: Stmt, #[case] cond: Bexpr, #[case] expected: Stmt) {
        let mut cb = CondBlock::new(cond.try_into().unwrap(), stmt);
        let _ = cb.validate().unwrap();
        let folded = cb.constant_fold().unwrap().unwrap();
        assert_eq!(folded, expected);
    }

    use ff::PrimeField;

    /// Implementation of BabyBear used for testing the [`Felt`](super::Felt) type.
    #[derive(PrimeField)]
    #[PrimeFieldModulus = "2013265921"]
    #[PrimeFieldGenerator = "31"]
    #[PrimeFieldReprEndianness = "little"]
    pub struct BabyBear([u64; 1]);
}
