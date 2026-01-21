//! Structs for handling boolean expressions.

use crate::error::Error;
use crate::printer::IRPrintable;
use crate::traits::{Canonicalize, ConstantFolding};
use crate::{canon::canonicalize_constraint, expr::IRAexpr};
use eqv::{EqvRelation, equiv};
use haloumi_core::cmp::CmpOp;
use haloumi_core::eqv::SymbolicEqv;
use haloumi_lowering::lowering_err;
use haloumi_lowering::{ExprLowering, lowerable::LowerableExpr};
use std::{
    convert::identity,
    fmt::Write,
    ops::{BitAnd, BitOr, Not},
};

/// Represents boolean expressions over some arithmetic expression type A.
#[derive(Debug)]
pub struct IRBexpr<A>(IRBexprImpl<A>);

enum IRBexprImpl<A> {
    /// Literal value for true.
    True,
    /// Literal value for false.
    False,
    /// Comparison operation of two inner arithmetic expressions.
    Cmp(CmpOp, A, A),
    /// Represents the conjunction of the inner expressions.
    And(Vec<IRBexpr<A>>),
    /// Represents the disjounction of the inner expressions.
    Or(Vec<IRBexpr<A>>),
    /// Represents the negation of the inner expression.
    Not(Box<IRBexpr<A>>),
    /// Declares that the inner arithmetic expression needs to be proven deterministic
    Det(A),
    /// Logical implication operator.
    Implies(Box<IRBexpr<A>>, Box<IRBexpr<A>>),
    /// Logical double-implication operator.
    Iff(Box<IRBexpr<A>>, Box<IRBexpr<A>>),
}

impl<T> IRBexpr<T> {
    /// Transforms the inner expression into a different type.
    pub fn map<O>(self, f: &mut impl FnMut(T) -> O) -> IRBexpr<O> {
        match self.0 {
            IRBexprImpl::Cmp(cmp_op, lhs, rhs) => IRBexpr(IRBexprImpl::Cmp(cmp_op, f(lhs), f(rhs))),
            IRBexprImpl::And(exprs) => IRBexpr(IRBexprImpl::And(
                exprs.into_iter().map(|e| e.map(f)).collect(),
            )),
            IRBexprImpl::Or(exprs) => IRBexpr(IRBexprImpl::Or(
                exprs.into_iter().map(|e| e.map(f)).collect(),
            )),
            IRBexprImpl::Not(expr) => IRBexpr(IRBexprImpl::Not(Box::new(expr.map(f)))),
            IRBexprImpl::True => IRBexpr(IRBexprImpl::True),
            IRBexprImpl::False => IRBexpr(IRBexprImpl::False),
            IRBexprImpl::Det(expr) => IRBexpr(IRBexprImpl::Det(f(expr))),
            IRBexprImpl::Implies(lhs, rhs) => IRBexpr(IRBexprImpl::Implies(
                Box::new(lhs.map(f)),
                Box::new(rhs.map(f)),
            )),
            IRBexprImpl::Iff(lhs, rhs) => {
                IRBexpr(IRBexprImpl::Iff(Box::new(lhs.map(f)), Box::new(rhs.map(f))))
            }
        }
    }

    /// Transforms the inner expression into a different type without moving the struct.
    pub fn map_into<O>(&self, f: &mut impl FnMut(&T) -> O) -> IRBexpr<O> {
        match &self.0 {
            IRBexprImpl::Cmp(cmp_op, lhs, rhs) => {
                IRBexpr(IRBexprImpl::Cmp(*cmp_op, f(lhs), f(rhs)))
            }
            IRBexprImpl::And(exprs) => IRBexpr(IRBexprImpl::And(
                exprs.iter().map(|e| e.map_into(f)).collect(),
            )),
            IRBexprImpl::Or(exprs) => IRBexpr(IRBexprImpl::Or(
                exprs.iter().map(|e| e.map_into(f)).collect(),
            )),
            IRBexprImpl::Not(expr) => IRBexpr(IRBexprImpl::Not(Box::new(expr.map_into(f)))),
            IRBexprImpl::True => IRBexpr(IRBexprImpl::True),
            IRBexprImpl::False => IRBexpr(IRBexprImpl::False),
            IRBexprImpl::Det(expr) => IRBexpr(IRBexprImpl::Det(f(expr))),
            IRBexprImpl::Implies(lhs, rhs) => IRBexpr(IRBexprImpl::Implies(
                Box::new(lhs.map_into(f)),
                Box::new(rhs.map_into(f)),
            )),
            IRBexprImpl::Iff(lhs, rhs) => IRBexpr(IRBexprImpl::Iff(
                Box::new(lhs.map_into(f)),
                Box::new(rhs.map_into(f)),
            )),
        }
    }

    /// Transforms the inner expression into a different type, potentially failing.
    pub fn try_map<O, E>(self, f: &mut impl FnMut(T) -> Result<O, E>) -> Result<IRBexpr<O>, E> {
        Ok(match self.0 {
            IRBexprImpl::Cmp(cmp_op, lhs, rhs) => {
                IRBexpr(IRBexprImpl::Cmp(cmp_op, f(lhs)?, f(rhs)?))
            }
            IRBexprImpl::And(exprs) => IRBexpr(IRBexprImpl::And(
                exprs
                    .into_iter()
                    .map(|e| e.try_map(f))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            IRBexprImpl::Or(exprs) => IRBexpr(IRBexprImpl::Or(
                exprs
                    .into_iter()
                    .map(|e| e.try_map(f))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            IRBexprImpl::Not(expr) => IRBexpr(IRBexprImpl::Not(Box::new(expr.try_map(f)?))),
            IRBexprImpl::True => IRBexpr(IRBexprImpl::True),
            IRBexprImpl::False => IRBexpr(IRBexprImpl::False),
            IRBexprImpl::Det(expr) => IRBexpr(IRBexprImpl::Det(f(expr)?)),
            IRBexprImpl::Implies(lhs, rhs) => IRBexpr(IRBexprImpl::Implies(
                Box::new(lhs.try_map(f)?),
                Box::new(rhs.try_map(f)?),
            )),
            IRBexprImpl::Iff(lhs, rhs) => IRBexpr(IRBexprImpl::Iff(
                Box::new(lhs.try_map(f)?),
                Box::new(rhs.try_map(f)?),
            )),
        })
    }

    /// Transforms the inner expression in place instead of returning a new expression.
    pub fn map_inplace(&mut self, f: &mut impl FnMut(&mut T)) {
        match &mut self.0 {
            IRBexprImpl::Cmp(_, lhs, rhs) => {
                f(lhs);
                f(rhs);
            }
            IRBexprImpl::And(exprs) => {
                for expr in exprs {
                    expr.map_inplace(f);
                }
            }
            IRBexprImpl::Or(exprs) => {
                for expr in exprs {
                    expr.map_inplace(f);
                }
            }
            IRBexprImpl::Not(expr) => expr.map_inplace(f),
            IRBexprImpl::True => {}
            IRBexprImpl::False => {}
            IRBexprImpl::Det(expr) => f(expr),
            IRBexprImpl::Implies(lhs, rhs) => {
                lhs.map_inplace(f);
                rhs.map_inplace(f);
            }
            IRBexprImpl::Iff(lhs, rhs) => {
                lhs.map_inplace(f);
                rhs.map_inplace(f);
            }
        }
    }

    /// Tries to transform the inner expression in place instead of returning a new expression.
    pub fn try_map_inplace<E>(
        &mut self,
        f: &mut impl FnMut(&mut T) -> Result<(), E>,
    ) -> Result<(), E> {
        match &mut self.0 {
            IRBexprImpl::Cmp(_, lhs, rhs) => {
                f(lhs)?;
                f(rhs)
            }
            IRBexprImpl::And(exprs) => {
                for expr in exprs {
                    expr.try_map_inplace(f)?;
                }
                Ok(())
            }
            IRBexprImpl::Or(exprs) => {
                for expr in exprs {
                    expr.try_map_inplace(f)?;
                }
                Ok(())
            }
            IRBexprImpl::Not(expr) => expr.try_map_inplace(f),
            IRBexprImpl::True => Ok(()),
            IRBexprImpl::False => Ok(()),
            IRBexprImpl::Det(expr) => f(expr),
            IRBexprImpl::Implies(lhs, rhs) => {
                lhs.try_map_inplace(f)?;
                rhs.try_map_inplace(f)
            }
            IRBexprImpl::Iff(lhs, rhs) => {
                lhs.try_map_inplace(f)?;
                rhs.try_map_inplace(f)
            }
        }
    }

    pub(crate) fn cmp(op: CmpOp, lhs: T, rhs: T) -> Self {
        Self(IRBexprImpl::Cmp(op, lhs, rhs))
    }

    /// Creates a expression that indicates the backend must prove deterministic.
    pub fn det(expr: T) -> Self {
        Self(IRBexprImpl::Det(expr))
    }

    #[inline]
    /// Creates a constraint with [`CmpOp::Eq`] between two expressions.
    pub fn eq(lhs: T, rhs: T) -> Self {
        Self(IRBexprImpl::Cmp(CmpOp::Eq, lhs, rhs))
    }

    #[inline]
    /// Creates a constraint with [`CmpOp::Lt`] between two expressions.
    pub fn lt(lhs: T, rhs: T) -> Self {
        Self(IRBexprImpl::Cmp(CmpOp::Lt, lhs, rhs))
    }

    #[inline]
    /// Creates a constraint with [`CmpOp::Le`] between two expressions.
    pub fn le(lhs: T, rhs: T) -> Self {
        Self(IRBexprImpl::Cmp(CmpOp::Le, lhs, rhs))
    }

    #[inline]
    /// Creates a constraint with [`CmpOp::Gt`] between two expressions.
    pub fn gt(lhs: T, rhs: T) -> Self {
        Self(IRBexprImpl::Cmp(CmpOp::Gt, lhs, rhs))
    }

    #[inline]
    /// Creates a constraint with [`CmpOp::Ge`] between two expressions.
    pub fn ge(lhs: T, rhs: T) -> Self {
        Self(IRBexprImpl::Cmp(CmpOp::Ge, lhs, rhs))
    }

    #[inline]
    /// Creates an implication expression.
    pub fn implies(self, rhs: Self) -> Self {
        Self(IRBexprImpl::Implies(Box::new(self), Box::new(rhs)))
    }

    #[inline]
    /// Creates a double implication expression.
    pub fn iff(self, rhs: Self) -> Self {
        Self(IRBexprImpl::Iff(Box::new(self), Box::new(rhs)))
    }

    /// Creates a logical AND.
    pub fn and(self, rhs: Self) -> Self {
        Self(match (self.0, rhs.0) {
            (IRBexprImpl::And(mut lhs), IRBexprImpl::And(rhs)) => {
                lhs.reserve(rhs.len());
                lhs.extend(rhs);
                IRBexprImpl::And(lhs)
            }
            // The order of the operators is irrelevant
            (exp, IRBexprImpl::And(mut lst)) | (IRBexprImpl::And(mut lst), exp) => {
                lst.push(Self(exp));
                IRBexprImpl::And(lst)
            }
            (lhs, rhs) => IRBexprImpl::And(vec![Self(lhs), Self(rhs)]),
        })
    }

    /// Creates a logical AND from a sequence of expressions.
    pub fn and_many(exprs: impl IntoIterator<Item = Self>) -> Self {
        Self(IRBexprImpl::And(exprs.into_iter().collect()))
    }

    /// Creates a logical OR.
    pub fn or(self, rhs: Self) -> Self {
        Self(match (self.0, rhs.0) {
            (IRBexprImpl::Or(mut lhs), IRBexprImpl::Or(rhs)) => {
                lhs.reserve(rhs.len());
                lhs.extend(rhs);
                IRBexprImpl::Or(lhs)
            }
            // The order of the operators is irrelevant
            (exp, IRBexprImpl::Or(mut lst)) | (IRBexprImpl::Or(mut lst), exp) => {
                lst.push(Self(exp));
                IRBexprImpl::Or(lst)
            }
            (lhs, rhs) => IRBexprImpl::Or(vec![Self(lhs), Self(rhs)]),
        })
    }

    /// Creates a logical OR from a sequence of expressions.
    pub fn or_many(exprs: impl IntoIterator<Item = Self>) -> Self {
        Self(IRBexprImpl::Or(exprs.into_iter().collect()))
    }

    /// Maps the statement's inner type to a tuple with the passed value.
    pub fn with<O>(self, other: O) -> IRBexpr<(O, T)>
    where
        O: Clone,
    {
        self.map(&mut |t| (other.clone(), t))
    }

    /// Maps the statement's inner type to a tuple with the result of the closure.
    pub fn with_fn<O>(self, other: impl Fn() -> O) -> IRBexpr<(O, T)> {
        self.map(&mut |t| (other(), t))
    }
}

struct LogLine {
    before: Option<String>,
    ident: usize,
}

impl LogLine {
    fn new<T: std::fmt::Debug>(expr: &IRBexprImpl<T>, ident: usize) -> Self {
        if matches!(
            expr,
            IRBexprImpl::True | IRBexprImpl::False | IRBexprImpl::Cmp(_, _, _)
        ) {
            Self {
                before: Some(format!("{expr:?}")),
                ident,
            }
        } else {
            log::debug!("[constant_fold] {:ident$} {expr:?} {{", "", ident = ident);
            Self {
                before: None,
                ident,
            }
        }
    }

    fn log<T: std::fmt::Debug>(self, expr: &mut IRBexprImpl<T>) {
        match self.before {
            Some(before) => {
                log::debug!(
                    "[constant_fold] {:ident$} {} -> {expr:?}",
                    "",
                    before,
                    ident = self.ident
                );
            }
            None => {
                log::debug!(
                    "[constant_fold] {:ident$} }} -> {expr:?}",
                    "",
                    ident = self.ident
                );
            }
        }
    }
}

impl Canonicalize for IRBexpr<IRAexpr> {
    /// Matches the expressions against a series of known patterns and applies rewrites if able to.
    fn canonicalize(&mut self) {
        match &mut self.0 {
            IRBexprImpl::True => {}
            IRBexprImpl::False => {}
            IRBexprImpl::Cmp(op, lhs, rhs) => {
                if let Some((op, lhs, rhs)) = canonicalize_constraint(*op, lhs, rhs) {
                    *self = Self(IRBexprImpl::Cmp(op, lhs, rhs));
                }
            }
            IRBexprImpl::And(exprs) => {
                for expr in exprs {
                    expr.canonicalize();
                }
            }
            IRBexprImpl::Or(exprs) => {
                for expr in exprs {
                    expr.canonicalize();
                }
            }
            IRBexprImpl::Not(expr) => {
                expr.canonicalize();
                match &expr.0 {
                    IRBexprImpl::True => {
                        *self = Self(IRBexprImpl::False);
                    }
                    IRBexprImpl::False => {
                        *self = Self(IRBexprImpl::True);
                    }
                    IRBexprImpl::Cmp(op, lhs, rhs) => {
                        *self = Self(IRBexprImpl::Cmp(
                            match op {
                                CmpOp::Eq => CmpOp::Ne,
                                CmpOp::Lt => CmpOp::Ge,
                                CmpOp::Le => CmpOp::Gt,
                                CmpOp::Gt => CmpOp::Le,
                                CmpOp::Ge => CmpOp::Lt,
                                CmpOp::Ne => CmpOp::Eq,
                            },
                            lhs.clone(),
                            rhs.clone(),
                        ));
                        self.canonicalize();
                    }
                    _ => {}
                }
            }
            IRBexprImpl::Det(_) => {}
            IRBexprImpl::Implies(lhs, rhs) => {
                lhs.canonicalize();
                rhs.canonicalize();
            }
            IRBexprImpl::Iff(lhs, rhs) => {
                lhs.canonicalize();
                rhs.canonicalize();
            }
        }
    }
}

impl<T> IRBexpr<T>
where
    T: ConstantFolding + std::fmt::Debug,
    T::T: Eq + Ord,
{
    /// Folds the expression if the values are constant.
    fn constant_fold_impl(&mut self, indent: usize) -> Result<(), T::Error> {
        let log = LogLine::new(&self.0, indent);
        match &mut self.0 {
            IRBexprImpl::True => {
                log.log(&mut self.0);
            }
            IRBexprImpl::False => {
                log.log(&mut self.0);
            }
            IRBexprImpl::Cmp(op, lhs, rhs) => {
                lhs.constant_fold()?;
                rhs.constant_fold()?;
                if let Some((lhs, rhs)) = lhs.const_value().zip(rhs.const_value()) {
                    *self = match op {
                        CmpOp::Eq => lhs == rhs,
                        CmpOp::Lt => lhs < rhs,
                        CmpOp::Le => lhs <= rhs,
                        CmpOp::Gt => lhs > rhs,
                        CmpOp::Ge => lhs >= rhs,
                        CmpOp::Ne => lhs != rhs,
                    }
                    .into()
                }
                log.log(&mut self.0);
            }
            IRBexprImpl::And(exprs) => {
                for expr in &mut *exprs {
                    expr.constant_fold_impl(indent + 2)?;
                }
                // If any value is a literal 'false' convert into IRBexprImpl::False
                if exprs.iter().any(|expr| {
                    expr.const_value()
                        // If the expr is false-y flip the boolean to return 'true'.
                        .map(|b| !b)
                        // Default to 'false' for non-literal expressions.
                        .unwrap_or_default()
                }) {
                    *self = Self(IRBexprImpl::False);
                    log.log(&mut self.0);
                    return Ok(());
                }
                // Remove any literal 'true' values.
                exprs.retain(|expr| {
                    expr.const_value()
                        // If the expr is IRBexprImpl::True we don't want to retain.
                        .map(|b| !b)
                        // Default to true to keep the non-literal values.
                        .unwrap_or(true)
                });
                if exprs.is_empty() {
                    *self = Self(IRBexprImpl::True);
                }
                log.log(&mut self.0);
            }
            IRBexprImpl::Or(exprs) => {
                for expr in &mut *exprs {
                    expr.constant_fold_impl(indent + 2)?;
                }
                // If any value is a literal 'true' convert into IRBexprImpl::True.
                if exprs
                    .iter()
                    .any(|expr| expr.const_value().unwrap_or_default())
                {
                    *self = Self(IRBexprImpl::True);
                    log.log(&mut self.0);
                    return Ok(());
                }
                // Remove any literal 'false' values.
                exprs.retain(|expr| {
                    expr.const_value()
                        // Default to true to keep the non-literal values.
                        .unwrap_or(true)
                });
                if exprs.is_empty() {
                    *self = Self(IRBexprImpl::False);
                }
                log.log(&mut self.0);
            }
            IRBexprImpl::Not(expr) => {
                expr.constant_fold_impl(indent + 2)?;
                if let Some(b) = expr.const_value() {
                    *self = (!b).into();
                }
                log.log(&mut self.0);
            }
            IRBexprImpl::Det(expr) => expr.constant_fold()?,
            IRBexprImpl::Implies(lhs, rhs) => {
                lhs.constant_fold_impl(indent + 2)?;
                rhs.constant_fold_impl(indent + 2)?;
                if let Some((lhs, rhs)) = lhs.const_value().zip(rhs.const_value()) {
                    *self = (!lhs || rhs).into();
                }
            }
            IRBexprImpl::Iff(lhs, rhs) => {
                lhs.constant_fold_impl(indent + 2)?;
                rhs.constant_fold_impl(indent + 2)?;
                if let Some((lhs, rhs)) = lhs.const_value().zip(rhs.const_value()) {
                    *self = (lhs == rhs).into();
                }
            }
        }
        Ok(())
    }
}

impl<T> ConstantFolding for IRBexpr<T>
where
    T: ConstantFolding + std::fmt::Debug,
    T::T: Eq + Ord,
{
    type T = bool;

    type Error = T::Error;

    fn constant_fold(&mut self) -> Result<(), Self::Error> {
        self.constant_fold_impl(0)
    }

    /// Returns `Some(true)` or `Some(false)` if the expression is constant, `None` otherwise.
    fn const_value(&self) -> Option<bool> {
        match &self.0 {
            IRBexprImpl::True => Some(true),
            IRBexprImpl::False => Some(false),
            _ => None,
        }
    }
}

impl<T> From<bool> for IRBexpr<T> {
    fn from(value: bool) -> Self {
        Self(if value {
            IRBexprImpl::True
        } else {
            IRBexprImpl::False
        })
    }
}

/// IRBexprImpl transitively inherits the symbolic equivalence relation.
impl<L, R> EqvRelation<IRBexpr<L>, IRBexpr<R>> for SymbolicEqv
where
    SymbolicEqv: EqvRelation<L, R>,
{
    /// Two boolean expressions are equivalent if they are structurally equal and their inner entities
    /// are equivalent.
    fn equivalent(lhs: &IRBexpr<L>, rhs: &IRBexpr<R>) -> bool {
        match (&lhs.0, &rhs.0) {
            (IRBexprImpl::True, IRBexprImpl::True) | (IRBexprImpl::False, IRBexprImpl::False) => {
                true
            }
            (IRBexprImpl::Cmp(op1, lhs1, rhs1), IRBexprImpl::Cmp(op2, lhs2, rhs2)) => {
                op1 == op2 && equiv!(Self | lhs1, lhs2) && equiv!(Self | rhs1, rhs2)
            }
            (IRBexprImpl::And(lhs), IRBexprImpl::And(rhs)) => {
                equiv!(Self | lhs, rhs)
            }
            (IRBexprImpl::Or(lhs), IRBexprImpl::Or(rhs)) => {
                equiv!(Self | lhs, rhs)
            }
            (IRBexprImpl::Not(lhs), IRBexprImpl::Not(rhs)) => {
                equiv!(Self | lhs, rhs)
            }
            (IRBexprImpl::Det(lhs), IRBexprImpl::Det(rhs)) => equiv!(Self | lhs, rhs),
            (IRBexprImpl::Implies(lhs1, rhs1), IRBexprImpl::Implies(lhs2, rhs2)) => {
                equiv!(Self | lhs1, lhs2) && equiv!(Self | rhs1, rhs2)
            }

            (IRBexprImpl::Iff(lhs1, rhs1), IRBexprImpl::Iff(lhs2, rhs2)) => {
                equiv!(Self | lhs1, lhs2) && equiv!(Self | rhs1, rhs2)
            }
            _ => false,
        }
    }
}

impl<T> BitAnd for IRBexpr<T> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.and(rhs)
    }
}

impl<T> BitOr for IRBexpr<T> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.or(rhs)
    }
}

impl<T> Not for IRBexpr<T> {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self.0 {
            IRBexprImpl::Not(e) => *e,
            e => Self(IRBexprImpl::Not(Box::new(Self(e)))),
        }
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for IRBexprImpl<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IRBexprImpl::Cmp(cmp_op, lhs, rhs) => write!(f, "({cmp_op} {lhs:?} {rhs:?})",),
            IRBexprImpl::And(exprs) => write!(f, "(&& {exprs:?})"),
            IRBexprImpl::Or(exprs) => write!(f, "(|| {exprs:?})"),
            IRBexprImpl::Not(expr) => write!(f, "(! {expr:?})"),
            IRBexprImpl::True => write!(f, "(true)"),
            IRBexprImpl::False => write!(f, "(false)"),
            IRBexprImpl::Det(expr) => write!(f, "(det {expr:?})"),
            IRBexprImpl::Implies(lhs, rhs) => write!(f, "(=> {lhs:?} {rhs:?})"),
            IRBexprImpl::Iff(lhs, rhs) => write!(f, "(<=> {lhs:?} {rhs:?})"),
        }
    }
}

impl<T: Clone> Clone for IRBexpr<T> {
    fn clone(&self) -> Self {
        Self(match &self.0 {
            IRBexprImpl::Cmp(cmp_op, lhs, rhs) => {
                IRBexprImpl::Cmp(*cmp_op, lhs.clone(), rhs.clone())
            }
            IRBexprImpl::And(exprs) => IRBexprImpl::And(exprs.clone()),
            IRBexprImpl::Or(exprs) => IRBexprImpl::Or(exprs.clone()),
            IRBexprImpl::Not(expr) => IRBexprImpl::Not(expr.clone()),
            IRBexprImpl::True => IRBexprImpl::True,
            IRBexprImpl::False => IRBexprImpl::False,
            IRBexprImpl::Det(expr) => IRBexprImpl::Det(expr.clone()),
            IRBexprImpl::Implies(lhs, rhs) => IRBexprImpl::Implies(lhs.clone(), rhs.clone()),
            IRBexprImpl::Iff(lhs, rhs) => IRBexprImpl::Iff(lhs.clone(), rhs.clone()),
        })
    }
}

impl<T: PartialEq> PartialEq for IRBexpr<T> {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (IRBexprImpl::Cmp(op1, lhs1, rhs1), IRBexprImpl::Cmp(op2, lhs2, rhs2)) => {
                op1 == op2 && lhs1 == lhs2 && rhs1 == rhs2
            }
            (IRBexprImpl::And(lhs), IRBexprImpl::And(rhs)) => lhs == rhs,
            (IRBexprImpl::Or(lhs), IRBexprImpl::Or(rhs)) => lhs == rhs,
            (IRBexprImpl::Not(lhs), IRBexprImpl::Not(rhs)) => lhs == rhs,
            (IRBexprImpl::True, IRBexprImpl::True) => true,
            (IRBexprImpl::False, IRBexprImpl::False) => true,
            (IRBexprImpl::Det(lhs), IRBexprImpl::Det(rhs)) => lhs == rhs,
            (IRBexprImpl::Implies(lhs1, rhs1), IRBexprImpl::Implies(lhs2, rhs2)) => {
                lhs1 == lhs2 && rhs1 == rhs2
            }
            (IRBexprImpl::Iff(lhs1, rhs1), IRBexprImpl::Iff(lhs2, rhs2)) => {
                lhs1 == lhs2 && rhs1 == rhs2
            }
            _ => false,
        }
    }
}

fn reduce_bool_expr<A, L>(
    exprs: impl IntoIterator<Item = IRBexpr<A>>,
    l: &L,
    cb: impl Fn(&L, &L::CellOutput, &L::CellOutput) -> haloumi_lowering::Result<L::CellOutput>,
) -> haloumi_lowering::Result<L::CellOutput>
where
    A: LowerableExpr,
    L: ExprLowering + ?Sized,
{
    exprs
        .into_iter()
        .map(|e| e.lower(l))
        .reduce(|lhs, rhs| lhs.and_then(|lhs| rhs.and_then(|rhs| cb(l, &lhs, &rhs))))
        .ok_or_else(|| lowering_err!(Error::EmptyBexpr))
        .and_then(identity)
}

impl<A: LowerableExpr> LowerableExpr for IRBexpr<A> {
    fn lower<L>(self, l: &L) -> haloumi_lowering::Result<L::CellOutput>
    where
        L: ExprLowering + ?Sized,
    {
        match self.0 {
            IRBexprImpl::Cmp(cmp_op, lhs, rhs) => {
                let lhs = lhs.lower(l)?;
                let rhs = rhs.lower(l)?;
                match cmp_op {
                    CmpOp::Eq => l.lower_eq(&lhs, &rhs),
                    CmpOp::Lt => l.lower_lt(&lhs, &rhs),
                    CmpOp::Le => l.lower_le(&lhs, &rhs),
                    CmpOp::Gt => l.lower_gt(&lhs, &rhs),
                    CmpOp::Ge => l.lower_ge(&lhs, &rhs),
                    CmpOp::Ne => l.lower_ne(&lhs, &rhs),
                }
            }
            IRBexprImpl::And(exprs) => reduce_bool_expr(exprs, l, L::lower_and),
            IRBexprImpl::Or(exprs) => reduce_bool_expr(exprs, l, L::lower_or),
            IRBexprImpl::Not(expr) => expr.lower(l).and_then(|e| l.lower_not(&e)),
            IRBexprImpl::True => l.lower_true(),
            IRBexprImpl::False => l.lower_false(),
            IRBexprImpl::Det(expr) => expr.lower(l).and_then(|e| l.lower_det(&e)),
            IRBexprImpl::Implies(lhs, rhs) => {
                let lhs = lhs.lower(l)?;
                let rhs = rhs.lower(l)?;
                l.lower_implies(&lhs, &rhs)
            }
            IRBexprImpl::Iff(lhs, rhs) => {
                let lhs = lhs.lower(l)?;
                let rhs = rhs.lower(l)?;
                l.lower_iff(&lhs, &rhs)
            }
        }
    }
}

impl<T: IRPrintable> IRPrintable for IRBexpr<T> {
    fn fmt(&self, ctx: &mut crate::printer::IRPrinterCtx<'_, '_>) -> crate::printer::Result {
        match &self.0 {
            IRBexprImpl::True => write!(ctx, "(true)"),
            IRBexprImpl::False => write!(ctx, "(false)"),
            IRBexprImpl::Cmp(cmp_op, lhs, rhs) => ctx.block(format!("{cmp_op}").as_str(), |ctx| {
                if lhs.depth() > 1 {
                    ctx.nl()?;
                }
                lhs.fmt(ctx)?;
                if lhs.depth() > 1 || rhs.depth() > 1 {
                    ctx.nl()?;
                }
                rhs.fmt(ctx)
            }),
            IRBexprImpl::And(exprs) => ctx.block("&&", |ctx| {
                let do_nl = exprs.iter().any(|expr| expr.depth() > 1);
                let mut is_first = true;
                for expr in exprs {
                    if do_nl && !is_first {
                        ctx.nl()?;
                    }
                    is_first = false;
                    expr.fmt(ctx)?;
                }
                Ok(())
            }),
            IRBexprImpl::Or(exprs) => ctx.block("||", |ctx| {
                let do_nl = exprs.iter().any(|expr| expr.depth() > 1);
                let mut is_first = true;
                for expr in exprs {
                    if do_nl && !is_first {
                        ctx.nl()?;
                    }
                    is_first = false;
                    expr.fmt(ctx)?;
                }
                Ok(())
            }),
            IRBexprImpl::Not(expr) => ctx.block("!", |ctx| expr.fmt(ctx)),
            IRBexprImpl::Det(expr) => ctx.block("det", |ctx| expr.fmt(ctx)),
            IRBexprImpl::Implies(lhs, rhs) => ctx.block("=>", |ctx| {
                if lhs.depth() > 1 {
                    ctx.nl()?;
                }
                lhs.fmt(ctx)?;
                if lhs.depth() > 1 || rhs.depth() > 1 {
                    ctx.nl()?;
                }
                rhs.fmt(ctx)
            }),
            IRBexprImpl::Iff(lhs, rhs) => ctx.block("<=>", |ctx| {
                if lhs.depth() > 1 {
                    ctx.nl()?;
                }
                lhs.fmt(ctx)?;
                if lhs.depth() > 1 || rhs.depth() > 1 {
                    ctx.nl()?;
                }
                rhs.fmt(ctx)
            }),
        }
    }

    fn depth(&self) -> usize {
        match &self.0 {
            IRBexprImpl::True | IRBexprImpl::False => 1,
            IRBexprImpl::Cmp(_, lhs, rhs) => 1 + std::cmp::max(lhs.depth(), rhs.depth()),
            IRBexprImpl::And(exprs) | IRBexprImpl::Or(exprs) => {
                1 + exprs
                    .iter()
                    .map(|expr| expr.depth())
                    .max()
                    .unwrap_or_default()
            }
            IRBexprImpl::Not(expr) => 1 + expr.depth(),
            IRBexprImpl::Det(expr) => 1 + expr.depth(),
            IRBexprImpl::Implies(lhs, rhs) | IRBexprImpl::Iff(lhs, rhs) => {
                1 + std::cmp::max(lhs.depth(), rhs.depth())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn t() -> IRBexpr<()> {
        true.into()
    }

    fn f() -> IRBexpr<()> {
        false.into()
    }

    #[test]
    fn constant_fold_not_true() {
        let mut expr = !t();
        expr.constant_fold().unwrap();
        assert_eq!(expr, f());
    }

    #[test]
    fn constant_fold_not_false() {
        let mut expr = !f();
        expr.constant_fold().unwrap();
        assert_eq!(expr, t());
    }

    impl ConstantFolding for () {
        type Error = std::convert::Infallible;

        type T = ();

        fn constant_fold(&mut self) -> Result<(), Self::Error> {
            Ok(())
        }
    }
}
