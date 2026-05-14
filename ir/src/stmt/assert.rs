use crate::{
    error::Error,
    expr::IRBexpr,
    meta::Meta,
    stmt::IRStmt,
    traits::{Canonicalize, ConstantFolding},
};
use eqv::{EqvRelation, equiv};
use haloumi_core::eqv::SymbolicEqv;
use haloumi_lowering::{
    Lowering,
    lowerable::{LowerableExpr, LowerableStmt},
};

pub struct Assert<T>(IRBexpr<T>);

impl<T> Assert<T> {
    pub fn new(cond: IRBexpr<T>) -> Self {
        Self(cond)
    }

    pub fn cond(&self) -> &IRBexpr<T> {
        &self.0
    }

    pub fn cond_mut(&mut self) -> &mut IRBexpr<T> {
        &mut self.0
    }

    pub fn map<O>(self, f: &mut impl FnMut(T) -> O) -> Assert<O> {
        Assert::new(self.0.map(f))
    }

    pub fn map_into<O>(&self, f: &mut impl FnMut(&T) -> O) -> Assert<O> {
        Assert::new(self.0.map_into(f))
    }

    pub fn try_map<O, E>(self, f: &mut impl FnMut(T) -> Result<O, E>) -> Result<Assert<O>, E> {
        self.0.try_map(f).map(Assert::new)
    }

    pub fn map_inplace(&mut self, f: &mut impl FnMut(&mut T)) {
        self.0.map_inplace(f)
    }

    pub fn try_map_inplace<E>(
        &mut self,
        f: &mut impl FnMut(&mut T) -> Result<(), E>,
    ) -> Result<(), E> {
        self.0.try_map_inplace(f)
    }

    /// Folds the statements if the expressions are constant.
    /// If a assert-like statement folds into a tautology (i.e. `(= 0 0 )`) gets removed. If it
    /// folds into a unsatisfiable proposition the method returns an error.
    pub fn constant_fold(&mut self, meta: Meta) -> Result<Option<IRStmt<T>>, Error>
    where
        T: ConstantFolding + std::fmt::Debug + Clone,
        T::T: Eq + Ord,
        Error: From<T::Error>,
    {
        self.0.constant_fold()?;
        if let Some(b) = self.0.const_value() {
            if b {
                return Ok(Some(IRStmt::empty()));
            } else {
                return Err(Error::FoldedFalseStmt(
                    "assert",
                    format!("{:#?}", self.0),
                    meta,
                ));
            }
        }
        Ok(None)
    }
}

impl<T> Canonicalize for Assert<T>
where
    IRBexpr<T>: Canonicalize,
{
    /// Matches the statements against a series of known patterns and applies rewrites if able to.
    fn canonicalize(&mut self) {
        self.0.canonicalize();
    }
}

impl<T: LowerableExpr> LowerableStmt for Assert<T> {
    fn lower<L>(self, l: &L) -> haloumi_lowering::Result<()>
    where
        L: Lowering + ?Sized,
    {
        l.generate_assert(&self.0.lower(l)?)
    }
}

impl<T: Clone> Clone for Assert<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T: PartialEq> PartialEq for Assert<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for Assert<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "assert ")?;
        if f.alternate() {
            write!(f, "{:#?}", self.0)
        } else {
            write!(f, "{:?}", self.0)
        }
    }
}

impl<L, R> EqvRelation<Assert<L>, Assert<R>> for SymbolicEqv
where
    SymbolicEqv: EqvRelation<L, R>,
{
    fn equivalent(lhs: &Assert<L>, rhs: &Assert<R>) -> bool {
        equiv! { SymbolicEqv | &lhs.0, &rhs.0 }
    }
}

#[cfg(test)]
mod tests {
    use haloumi_core::{
        constraints::CopyConstraint,
        table::{Any, Column},
    };

    use crate::meta::HasMeta as _;

    use super::*;

    type Stmt = IRStmt<()>;

    fn fold(stmt: &mut Stmt) {
        let _ = stmt
            .constant_fold()
            .map_err(|e| panic!("constant folding failed: {e}"));
    }

    #[should_panic(expected = "constant folding failed: unknown: detected ")]
    #[test]
    fn test_folded_to_false_meta_information_unknown() {
        let mut stmt = Stmt::assert(false.into());

        fold(&mut stmt);
    }

    #[should_panic(expected = "constant folding failed: group(group_1): unknown: detected ")]
    #[test]
    fn test_folded_to_false_meta_information_group_info() {
        let mut stmt = Stmt::assert(false.into());
        stmt.meta_mut().at_group("group_1", None);
        fold(&mut stmt);
    }

    #[should_panic(
        expected = "constant folding failed: group(group_1): gate 'gate name' @ region 'region name'(1): detected "
    )]
    #[test]
    fn test_folded_to_false_meta_information_group_info_at_gate() {
        let mut stmt = Stmt::assert(false.into());
        stmt.meta_mut().at_group("group_1", None);
        stmt.meta_mut()
            .at_gate("gate name", "region name", Some(1.into()), None);
        fold(&mut stmt);
    }

    #[should_panic(
        expected = "constant folding failed: group(group_1): gate 'gate name' @ region 'region name'(1) @ row 20: detected "
    )]
    #[test]
    fn test_folded_to_false_meta_information_group_info_at_gate_with_row1() {
        let mut stmt = Stmt::assert(false.into());
        stmt.meta_mut().at_group("group_1", None);
        stmt.meta_mut()
            .at_gate("gate name", "region name", Some(1.into()), Some(20));
        fold(&mut stmt);
    }

    #[should_panic(
        expected = "constant folding failed: group(group_1): gate 'gate name' @ region 'region name'(1) @ row 20: detected "
    )]
    #[test]
    fn test_folded_to_false_meta_information_group_info_at_gate_with_row2() {
        let mut stmt = Stmt::assert(false.into());
        stmt.meta_mut().at_group("group_1", None);
        stmt.meta_mut()
            .at_gate("gate name", "region name", Some(1.into()), None);
        stmt.meta_mut().at_row(20);
        fold(&mut stmt);
    }

    #[should_panic(
        expected = "constant folding failed: gate 'gate name' @ region 'region name'(1): detected "
    )]
    #[test]
    fn test_folded_to_false_meta_information_at_gate() {
        let mut stmt = Stmt::assert(false.into());
        stmt.meta_mut()
            .at_gate("gate name", "region name", Some(1.into()), None);
        fold(&mut stmt);
    }

    #[should_panic(
        expected = "constant folding failed: gate 'gate name' @ region 'region name'(1) @ row 20: detected "
    )]
    #[test]
    fn test_folded_to_false_meta_information_at_gate_with_row1() {
        let mut stmt = Stmt::assert(false.into());
        stmt.meta_mut()
            .at_gate("gate name", "region name", Some(1.into()), Some(20));
        fold(&mut stmt);
    }

    #[should_panic(
        expected = "constant folding failed: gate 'gate name' @ region 'region name'(1) @ row 20: detected "
    )]
    #[test]
    fn test_folded_to_false_meta_information_at_gate_with_row2() {
        let mut stmt = Stmt::assert(false.into());
        stmt.meta_mut()
            .at_gate("gate name", "region name", Some(1.into()), None);
        stmt.meta_mut().at_row(20);
        fold(&mut stmt);
    }

    #[should_panic(
        expected = "constant folding failed: copy (Adv:1, 10) === (Ins:3, 4): detected "
    )]
    #[test]
    fn test_folded_to_false_meta_information_at_copy_constraint() {
        let mut stmt = Stmt::assert(false.into());
        stmt.meta_mut().at_copy_constraint(CopyConstraint::Cells(
            Column::new(1, Any::Advice),
            10,
            Column::new(3, Any::Instance),
            4,
        ));
        fold(&mut stmt);
    }

    #[should_panic(
        expected = "constant folding failed: lookup 'lookup name'(1) @ row 20: detected "
    )]
    #[test]
    fn test_folded_to_false_meta_information_at_lookup_with_row() {
        let mut stmt = Stmt::assert(false.into());
        stmt.meta_mut().at_lookup("lookup name", 1, Some(20));
        fold(&mut stmt);
    }

    #[should_panic(expected = "constant folding failed: lookup 'lookup name'(1): detected ")]
    #[test]
    fn test_folded_to_false_meta_information_at_lookup() {
        let mut stmt = Stmt::assert(false.into());
        stmt.meta_mut().at_lookup("lookup name", 1, None);
        fold(&mut stmt);
    }
}
