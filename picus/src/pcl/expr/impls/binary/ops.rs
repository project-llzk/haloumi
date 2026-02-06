use haloumi_ir::{Felt, Prime};

use crate::pcl::{
    display::TextRepresentable,
    expr::{Expr, Wrap, traits::ExprLike},
};

use super::BinaryExpr;

pub mod arith;
pub mod boolean;
pub mod constraint;

pub trait OpFolder: PartialEq + Clone {
    fn fold(&self, lhs: Expr, rhs: Expr, prime: Prime) -> Option<Expr>;

    fn commutative(&self) -> bool;

    fn flip(&self, lhs: &Expr, rhs: &Expr) -> Option<BinaryExpr<Self>>;
}

pub trait OpLike:
    Clone + PartialEq + OpFolder + TextRepresentable + std::fmt::Debug + std::hash::Hash + 'static
{
    fn extraible(&self) -> bool;
}

/// Tries to fold a newly created expression. If it didn't fold then returns the original
/// expression.
#[inline]
fn try_fold<E: ExprLike>(e: E, prime: Prime) -> Option<Expr> {
    e.fold(prime).or_else(|| Some(Wrap::new(e)))
}
