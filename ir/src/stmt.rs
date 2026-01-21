//! Structs for representing statements of the circuit's logic.

use super::expr::IRBexpr;
use crate::{
    error::Error,
    expr::IRAexpr,
    printer::IRPrintable,
    traits::{Canonicalize, ConstantFolding},
};
use eqv::{EqvRelation, equiv};
use haloumi_core::{cmp::CmpOp, eqv::SymbolicEqv, slot::Slot};
use haloumi_lowering::{
    Lowering,
    lowerable::{LowerableExpr, LowerableStmt},
};
use std::fmt::Write;

mod assert;
mod assume_determ;
mod call;
mod comment;
mod constraint;
mod post_cond;
mod seq;

use assert::Assert;
use assume_determ::AssumeDeterministic;
use call::Call;
use comment::Comment;
use constraint::Constraint;
use post_cond::PostCond;
use seq::Seq;

/// IR for operations that occur in the main circuit.
pub struct IRStmt<T>(IRStmtImpl<T>);

enum IRStmtImpl<T> {
    /// A call to another module.
    ConstraintCall(Call<T>),
    /// A constraint between two expressions.
    Constraint(Constraint<T>),
    /// A text comment.
    Comment(Comment),
    /// Indicates that a [`Slot`] must be assumed deterministic by the backend.
    AssumeDeterministic(AssumeDeterministic),
    /// A constraint that a [`IRBexpr`] must be true.
    Assert(Assert<T>),
    /// A sequence of statements.
    Seq(Seq<T>),
    /// A post-condition expression.
    PostCond(PostCond<T>),
}

impl<T: PartialEq> PartialEq for IRStmt<T> {
    /// Equality is defined by the sequence of statements regardless of how they are structured
    /// inside.
    ///
    /// For example:
    ///     Seq([a, Seq([b, c])]) == Seq([a, b, c])
    ///     a == Seq([a])
    fn eq(&self, other: &Self) -> bool {
        std::iter::zip(self.iter(), other.iter()).all(|(lhs, rhs)| match (&lhs.0, &rhs.0) {
            (IRStmtImpl::ConstraintCall(lhs), IRStmtImpl::ConstraintCall(rhs)) => lhs.eq(rhs),
            (IRStmtImpl::Constraint(lhs), IRStmtImpl::Constraint(rhs)) => lhs.eq(rhs),
            (IRStmtImpl::Comment(lhs), IRStmtImpl::Comment(rhs)) => lhs.eq(rhs),
            (IRStmtImpl::AssumeDeterministic(lhs), IRStmtImpl::AssumeDeterministic(rhs)) => {
                lhs.eq(rhs)
            }
            (IRStmtImpl::Assert(lhs), IRStmtImpl::Assert(rhs)) => lhs.eq(rhs),
            (IRStmtImpl::PostCond(lhs), IRStmtImpl::PostCond(rhs)) => lhs.eq(rhs),
            (IRStmtImpl::Seq(_), _) | (_, IRStmtImpl::Seq(_)) => unreachable!(),
            _ => false,
        })
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for IRStmt<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            IRStmtImpl::ConstraintCall(call) => write!(f, "{call:?}"),
            IRStmtImpl::Constraint(constraint) => write!(f, "{constraint:?}"),
            IRStmtImpl::Comment(comment) => write!(f, "{comment:?}"),
            IRStmtImpl::AssumeDeterministic(assume_deterministic) => {
                write!(f, "{assume_deterministic:?}")
            }
            IRStmtImpl::Assert(assert) => write!(f, "{assert:?}"),
            IRStmtImpl::PostCond(pc) => write!(f, "{pc:?}"),
            IRStmtImpl::Seq(seq) => write!(f, "{seq:?}"),
        }
    }
}

impl<T> IRStmt<T> {
    /// Creates a call to another module.
    pub fn call(
        callee: impl AsRef<str>,
        inputs: impl IntoIterator<Item = T>,
        outputs: impl IntoIterator<Item = Slot>,
    ) -> Self {
        Call::new(callee, inputs, outputs).into()
    }

    /// Creates a post condition formula.
    pub fn post_cond(cond: IRBexpr<T>) -> Self {
        PostCond::new(cond).into()
    }

    /// Creates a constraint between two expressions.
    pub fn constraint(op: CmpOp, lhs: T, rhs: T) -> Self {
        Constraint::new(op, lhs, rhs).into()
    }

    #[inline]
    /// Creates a constraint with [`CmpOp::Eq`] between two expressions.
    pub fn eq(lhs: T, rhs: T) -> Self {
        Self::constraint(CmpOp::Eq, lhs, rhs)
    }

    #[inline]
    /// Creates a constraint with [`CmpOp::Lt`] between two expressions.
    pub fn lt(lhs: T, rhs: T) -> Self {
        Self::constraint(CmpOp::Lt, lhs, rhs)
    }

    #[inline]
    /// Creates a constraint with [`CmpOp::Le`] between two expressions.
    pub fn le(lhs: T, rhs: T) -> Self {
        Self::constraint(CmpOp::Le, lhs, rhs)
    }

    #[inline]
    /// Creates a constraint with [`CmpOp::Gt`] between two expressions.
    pub fn gt(lhs: T, rhs: T) -> Self {
        Self::constraint(CmpOp::Gt, lhs, rhs)
    }

    #[inline]
    /// Creates a constraint with [`CmpOp::Ge`] between two expressions.
    pub fn ge(lhs: T, rhs: T) -> Self {
        Self::constraint(CmpOp::Ge, lhs, rhs)
    }

    /// Creates a text comment.
    pub fn comment(s: impl AsRef<str>) -> Self {
        Comment::new(s).into()
    }

    /// Indicates that the [`Slot`] must be assumed deterministic by the backend.
    pub fn assume_deterministic(f: impl Into<Slot>) -> Self {
        AssumeDeterministic::new(f.into()).into()
    }

    /// Creates an assertion in the circuit.
    pub fn assert(cond: IRBexpr<T>) -> Self {
        Assert::new(cond).into()
    }

    /// Creates a statement that is a sequence of other statements.
    pub fn seq<I>(stmts: impl IntoIterator<Item = IRStmt<I>>) -> Self
    where
        I: Into<T>,
    {
        Seq::new(stmts).into()
    }

    /// Creates an empty statement.
    pub fn empty() -> Self {
        Seq::empty().into()
    }

    /// Returns true if the statement is empty.
    pub fn is_empty(&self) -> bool {
        match &self.0 {
            IRStmtImpl::Seq(s) => s.is_empty(),
            _ => false,
        }
    }

    /// Transforms the inner expression type into another.
    pub fn map<O>(self, f: &mut impl FnMut(T) -> O) -> IRStmt<O> {
        match self.0 {
            IRStmtImpl::ConstraintCall(call) => call.map(f).into(),
            IRStmtImpl::Constraint(constraint) => constraint.map(f).into(),
            IRStmtImpl::Comment(comment) => Comment::new(comment.value()).into(),
            IRStmtImpl::AssumeDeterministic(ad) => AssumeDeterministic::new(ad.value()).into(),
            IRStmtImpl::Assert(assert) => assert.map(f).into(),
            IRStmtImpl::PostCond(pc) => pc.map(f).into(),
            IRStmtImpl::Seq(seq) => Seq::new(seq.into_iter().map(|s| s.map(f))).into(),
        }
    }

    /// Maps the statement's inner type to a tuple with the passed value.
    pub fn with<O>(self, other: O) -> IRStmt<(O, T)>
    where
        O: Clone,
    {
        self.map(&mut |t| (other.clone(), t))
    }

    /// Maps the statement's inner type to a tuple with the result of the closure.
    pub fn with_fn<O>(self, other: impl Fn() -> O) -> IRStmt<(O, T)> {
        self.map(&mut |t| (other(), t))
    }

    /// Transforms the inner expression type using [`Into::into`].
    pub fn into<O>(self) -> IRStmt<O>
    where
        O: From<T>,
    {
        self.map(&mut Into::into)
    }

    /// Transforms the inner expression type using [`From::from`].
    pub fn from<O>(value: IRStmt<O>) -> Self
    where
        O: Into<T>,
    {
        value.map(&mut Into::into)
    }

    /// Appends the given statement to the current one.
    pub fn then(self, other: impl Into<Self>) -> Self {
        match self.0 {
            IRStmtImpl::Seq(mut seq) => {
                seq.push(other.into());
                seq.into()
            }
            this => Seq::new([Self(this), other.into()]).into(),
        }
    }

    /// Transforms the inner expression type into another, without moving.
    pub fn map_into<O>(&self, f: &mut impl FnMut(&T) -> O) -> IRStmt<O> {
        match &self.0 {
            IRStmtImpl::ConstraintCall(call) => call.map_into(f).into(),
            IRStmtImpl::Constraint(constraint) => constraint.map_into(f).into(),
            IRStmtImpl::Comment(comment) => Comment::new(comment.value()).into(),
            IRStmtImpl::AssumeDeterministic(ad) => AssumeDeterministic::new(ad.value()).into(),
            IRStmtImpl::Assert(assert) => assert.map_into(f).into(),
            IRStmtImpl::PostCond(pc) => pc.map_into(f).into(),
            IRStmtImpl::Seq(seq) => Seq::new(seq.iter().map(|s| s.map_into(f))).into(),
        }
    }

    /// Tries to transform the inner expression type into another.
    pub fn try_map<O, E>(self, f: &mut impl FnMut(T) -> Result<O, E>) -> Result<IRStmt<O>, E> {
        Ok(match self.0 {
            IRStmtImpl::ConstraintCall(call) => call.try_map(f)?.into(),
            IRStmtImpl::Constraint(constraint) => constraint.try_map(f)?.into(),
            IRStmtImpl::Comment(comment) => Comment::new(comment.value()).into(),
            IRStmtImpl::AssumeDeterministic(ad) => AssumeDeterministic::new(ad.value()).into(),
            IRStmtImpl::Assert(assert) => assert.try_map(f)?.into(),
            IRStmtImpl::PostCond(pc) => pc.try_map(f)?.into(),
            IRStmtImpl::Seq(seq) => Seq::new(
                seq.into_iter()
                    .map(|s| s.try_map(f))
                    .collect::<Result<Vec<_>, _>>()?,
            )
            .into(),
        })
    }

    /// Modifies the inner expression type in place.
    pub fn map_inplace(&mut self, f: &mut impl FnMut(&mut T)) {
        match &mut self.0 {
            IRStmtImpl::ConstraintCall(call) => call.map_inplace(f),
            IRStmtImpl::Constraint(constraint) => constraint.map_inplace(f),
            IRStmtImpl::Assert(assert) => assert.map_inplace(f),
            IRStmtImpl::PostCond(pc) => pc.map_inplace(f),
            IRStmtImpl::Seq(seq) => seq.iter_mut().for_each(|stmt| stmt.map_inplace(f)),
            _ => {}
        }
    }

    /// Tries to modify the inner expression type in place.
    pub fn try_map_inplace<E>(
        &mut self,
        f: &mut impl FnMut(&mut T) -> Result<(), E>,
    ) -> Result<(), E> {
        match &mut self.0 {
            IRStmtImpl::ConstraintCall(call) => call.try_map_inplace(f),
            IRStmtImpl::Constraint(constraint) => constraint.try_map_inplace(f),
            IRStmtImpl::Assert(assert) => assert.try_map_inplace(f),
            IRStmtImpl::PostCond(pc) => pc.try_map_inplace(f),
            IRStmtImpl::Seq(seq) => seq.iter_mut().try_for_each(|stmt| stmt.try_map_inplace(f)),
            _ => Ok(()),
        }
    }

    /// Modifies the inner slots in place.
    pub fn map_slot_inplace(&mut self, f: &mut impl FnMut(&mut Slot)) {
        match &mut self.0 {
            IRStmtImpl::ConstraintCall(call) => call.outputs_mut().iter_mut().for_each(f),
            IRStmtImpl::AssumeDeterministic(det) => f(det.value_mut()),
            IRStmtImpl::Seq(seq) => seq.iter_mut().for_each(|stmt| stmt.map_slot_inplace(f)),
            _ => {}
        }
    }

    /// Tries to modify the inner slots n place.
    pub fn try_map_slot_inplace<E>(
        &mut self,
        f: &mut impl FnMut(&mut Slot) -> Result<(), E>,
    ) -> Result<(), E> {
        match &mut self.0 {
            IRStmtImpl::ConstraintCall(call) => call.outputs_mut().iter_mut().try_for_each(f),
            IRStmtImpl::AssumeDeterministic(det) => f(det.value_mut()),
            IRStmtImpl::Seq(seq) => seq
                .iter_mut()
                .try_for_each(|stmt| stmt.try_map_slot_inplace(f)),
            _ => Ok(()),
        }
    }

    /// Returns an iterator of references to the statements.
    pub fn iter(&self) -> IRStmtRefIter<'_, T> {
        IRStmtRefIter { stack: vec![self] }
    }

    /// Returns an iterator of mutable references to the statements.
    pub fn iter_mut(&mut self) -> IRStmtRefMutIter<'_, T> {
        IRStmtRefMutIter { stack: vec![self] }
    }
}

impl<T> ConstantFolding for IRStmt<T>
where
    T: ConstantFolding + std::fmt::Debug + Clone,
    Error: From<T::Error>,
    T::T: Eq + Ord,
{
    type Error = Error;
    type T = ();

    /// Folds the statements if the expressions are constant.
    /// If a assert-like statement folds into a tautology (i.e. `(= 0 0 )`) gets removed. If it
    /// folds into a unsatisfiable proposition the method returns an error.
    fn constant_fold(&mut self) -> Result<(), Error> {
        match &mut self.0 {
            IRStmtImpl::ConstraintCall(call) => call.constant_fold()?,
            IRStmtImpl::Constraint(constraint) => {
                if let Some(replacement) = constraint.constant_fold()? {
                    *self = replacement;
                }
            }
            IRStmtImpl::Comment(_) => {}
            IRStmtImpl::AssumeDeterministic(_) => {}
            IRStmtImpl::Assert(assert) => {
                if let Some(replacement) = assert.constant_fold()? {
                    *self = replacement;
                }
            }
            IRStmtImpl::PostCond(pc) => {
                if let Some(replacement) = pc.constant_fold()? {
                    *self = replacement;
                }
            }
            IRStmtImpl::Seq(seq) => seq.constant_fold()?,
        }
        Ok(())
    }
}

impl Canonicalize for IRStmt<IRAexpr> {
    /// Matches the statements against a series of known patterns and applies rewrites if able to.
    fn canonicalize(&mut self) {
        match &mut self.0 {
            IRStmtImpl::ConstraintCall(call) => call.canonicalize(),
            IRStmtImpl::Constraint(constraint) => constraint.canonicalize(),
            IRStmtImpl::Comment(_) => {}
            IRStmtImpl::AssumeDeterministic(_) => {}
            IRStmtImpl::Assert(assert) => assert.canonicalize(),
            IRStmtImpl::PostCond(pc) => pc.canonicalize(),
            IRStmtImpl::Seq(seq) => seq.canonicalize(),
        }
    }
}

/// IRStmt transilitively inherits the [`SymbolicEqv`] equivalence relation.
impl<L, R> EqvRelation<IRStmt<L>, IRStmt<R>> for SymbolicEqv
where
    SymbolicEqv: EqvRelation<L, R> + EqvRelation<Slot, Slot>,
{
    /// Two statements are equivalent if they are structurally equal and their inner entities
    /// are equivalent.
    fn equivalent(lhs: &IRStmt<L>, rhs: &IRStmt<R>) -> bool {
        std::iter::zip(lhs.iter(), rhs.iter()).all(|(lhs, rhs)| match (&lhs.0, &rhs.0) {
            (IRStmtImpl::ConstraintCall(lhs), IRStmtImpl::ConstraintCall(rhs)) => {
                equiv! { SymbolicEqv | lhs, rhs }
            }
            (IRStmtImpl::Constraint(lhs), IRStmtImpl::Constraint(rhs)) => {
                equiv! { SymbolicEqv | lhs, rhs }
            }
            (IRStmtImpl::Comment(_), IRStmtImpl::Comment(_)) => true,
            (IRStmtImpl::AssumeDeterministic(lhs), IRStmtImpl::AssumeDeterministic(rhs)) => {
                equiv! { SymbolicEqv | lhs, rhs }
            }
            (IRStmtImpl::Assert(lhs), IRStmtImpl::Assert(rhs)) => {
                equiv! { SymbolicEqv | lhs, rhs }
            }
            (IRStmtImpl::PostCond(lhs), IRStmtImpl::PostCond(rhs)) => {
                equiv! { SymbolicEqv | lhs, rhs }
            }
            (IRStmtImpl::Seq(_), _) | (_, IRStmtImpl::Seq(_)) => unreachable!(),
            _ => false,
        })
    }
}

/// Iterator over references.
#[derive(Debug)]
pub struct IRStmtRefIter<'a, T> {
    stack: Vec<&'a IRStmt<T>>,
}

impl<'a, T> Iterator for IRStmtRefIter<'a, T> {
    type Item = &'a IRStmt<T>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.stack.pop() {
            match &node.0 {
                IRStmtImpl::Seq(children) => {
                    // Reverse to preserve left-to-right order
                    self.stack.extend(children.iter().rev());
                }
                _ => return Some(node),
            }
        }
        None
    }
}

/// Iterator over mutable references.
#[derive(Debug)]
pub struct IRStmtRefMutIter<'a, T> {
    stack: Vec<&'a mut IRStmt<T>>,
}

impl<'a, T> Iterator for IRStmtRefMutIter<'a, T> {
    type Item = &'a mut IRStmt<T>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.stack.pop() {
            if let IRStmt(IRStmtImpl::Seq(children)) = node {
                // Reverse to preserve left-to-right order
                self.stack.extend(children.iter_mut().rev());
            } else {
                return Some(node);
            }
        }
        None
    }
}

impl<T> Default for IRStmt<T> {
    fn default() -> Self {
        Self::empty()
    }
}

/// Iterator of statements.
#[derive(Debug)]
pub struct IRStmtIter<T> {
    stack: Vec<IRStmt<T>>,
}

impl<T> Iterator for IRStmtIter<T> {
    type Item = IRStmt<T>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.stack.pop() {
            match node {
                IRStmt(IRStmtImpl::Seq(children)) => {
                    // Reverse to preserve left-to-right order
                    self.stack.extend(children.into_iter().rev());
                }
                stmt => return Some(stmt),
            }
        }
        None
    }
}

impl<T> IntoIterator for IRStmt<T> {
    type Item = Self;

    type IntoIter = IRStmtIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IRStmtIter { stack: vec![self] }
    }
}

impl<'a, T> IntoIterator for &'a IRStmt<T> {
    type Item = Self;

    type IntoIter = IRStmtRefIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut IRStmt<T> {
    type Item = Self;

    type IntoIter = IRStmtRefMutIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<I> FromIterator<IRStmt<I>> for IRStmt<I> {
    fn from_iter<T: IntoIterator<Item = IRStmt<I>>>(iter: T) -> Self {
        Self::seq(iter)
    }
}

impl<T> From<Call<T>> for IRStmt<T> {
    fn from(value: Call<T>) -> Self {
        Self(IRStmtImpl::ConstraintCall(value))
    }
}
impl<T> From<Constraint<T>> for IRStmt<T> {
    fn from(value: Constraint<T>) -> Self {
        Self(IRStmtImpl::Constraint(value))
    }
}
impl<T> From<Comment> for IRStmt<T> {
    fn from(value: Comment) -> Self {
        Self(IRStmtImpl::Comment(value))
    }
}
impl<T> From<AssumeDeterministic> for IRStmt<T> {
    fn from(value: AssumeDeterministic) -> Self {
        Self(IRStmtImpl::AssumeDeterministic(value))
    }
}
impl<T> From<Assert<T>> for IRStmt<T> {
    fn from(value: Assert<T>) -> Self {
        Self(IRStmtImpl::Assert(value))
    }
}
impl<T> From<PostCond<T>> for IRStmt<T> {
    fn from(value: PostCond<T>) -> Self {
        Self(IRStmtImpl::PostCond(value))
    }
}
impl<T> From<Seq<T>> for IRStmt<T> {
    fn from(value: Seq<T>) -> Self {
        Self(IRStmtImpl::Seq(value))
    }
}

impl<T: LowerableExpr> LowerableStmt for IRStmt<T> {
    fn lower<L>(self, l: &L) -> haloumi_lowering::Result<()>
    where
        L: Lowering + ?Sized,
    {
        match self.0 {
            IRStmtImpl::ConstraintCall(call) => call.lower(l),
            IRStmtImpl::Constraint(constraint) => constraint.lower(l),
            IRStmtImpl::Comment(comment) => comment.lower(l),
            IRStmtImpl::AssumeDeterministic(ad) => ad.lower(l),
            IRStmtImpl::Assert(assert) => assert.lower(l),
            IRStmtImpl::PostCond(pc) => pc.lower(l),
            IRStmtImpl::Seq(seq) => seq.lower(l),
        }
    }
}

impl<T: Clone> Clone for IRStmt<T> {
    fn clone(&self) -> Self {
        match &self.0 {
            IRStmtImpl::ConstraintCall(call) => call.clone().into(),
            IRStmtImpl::Constraint(c) => c.clone().into(),
            IRStmtImpl::Comment(c) => c.clone().into(),
            IRStmtImpl::AssumeDeterministic(func_io) => func_io.clone().into(),
            IRStmtImpl::Assert(e) => e.clone().into(),
            IRStmtImpl::PostCond(e) => e.clone().into(),
            IRStmtImpl::Seq(stmts) => stmts.clone().into(),
        }
    }
}

impl<T: IRPrintable> IRPrintable for IRStmt<T> {
    fn fmt(&self, ctx: &mut crate::printer::IRPrinterCtx<'_, '_>) -> crate::printer::Result {
        match &self.0 {
            IRStmtImpl::ConstraintCall(call) => {
                ctx.fmt_call(call.callee(), call.inputs(), call.outputs(), None)
            }
            IRStmtImpl::Constraint(constraint) => {
                ctx.block(format!("assert/{}", constraint.op()).as_str(), |ctx| {
                    if constraint.lhs().depth() > 1 {
                        ctx.nl()?;
                    }
                    constraint.lhs().fmt(ctx)?;
                    if constraint.lhs().depth() > 1 || constraint.rhs().depth() > 1 {
                        ctx.nl()?;
                    }
                    constraint.rhs().fmt(ctx)
                })
            }
            IRStmtImpl::Comment(comment) => {
                ctx.nl()?;
                writeln!(ctx, "; {}", comment.value())
            }
            IRStmtImpl::AssumeDeterministic(assume_deterministic) => ctx
                .list_nl("assume-deterministic", |ctx| {
                    assume_deterministic.value().fmt(ctx)
                }),
            IRStmtImpl::Assert(assert) => ctx.block("assert", |ctx| assert.cond().fmt(ctx)),
            IRStmtImpl::Seq(seq) => {
                for stmt in seq.iter() {
                    stmt.fmt(ctx)?;
                }
                Ok(())
            }
            IRStmtImpl::PostCond(post_cond) => {
                ctx.block("post-cond", |ctx| post_cond.cond().fmt(ctx))
            }
        }
    }
}

#[cfg(test)]
mod test;
