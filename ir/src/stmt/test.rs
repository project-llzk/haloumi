use helpers::{ConstraintFactory, IRStmtFactory, InnerConstraintFactory};

use super::*;

pub mod helpers;

type S = IRStmt<()>;

#[test]
fn iterator_nested_seqs() {
    let nested = S::seq([
        S::assert(IRBexpr::and_many(vec![])),
        S::seq([
            S::assert(IRBexpr::and_many(vec![])),
            S::assert(IRBexpr::and_many(vec![])),
        ]),
    ]);
    let expected = vec![S::assert(IRBexpr::and_many(vec![])); 3];
    let output = nested.into_iter().collect::<Vec<_>>();
    assert_eq!(expected, output);
}

#[test]
fn iterators_flatten_only_sequences() {
    let conditional =
        S::seq([S::assert(IRBexpr::and_many(vec![]))]).emit_unless_false(IRBexpr::and_many(vec![]));
    let commented = S::assert(IRBexpr::and_many(vec![])).with_comment("header".to_owned());
    let mut stmt = S::seq([conditional, commented]);

    // Composition sequences disappear, but structural wrappers remain roots.
    assert_eq!(stmt.iter().count(), 2);
    assert_eq!(stmt.iter_mut().count(), 2);
    assert_eq!(stmt.into_iter().count(), 2);
}

#[test]
fn semantic_equality_normalizes_sequences_but_not_wrappers() {
    use crate::meta::HasMeta as _;

    let assertion = S::assert(IRBexpr::and_many(vec![]));
    assert_eq!(
        assertion,
        S::seq([S::seq([S::assert(IRBexpr::and_many(vec![]))])])
    );
    assert_ne!(
        assertion,
        S::seq([S::assert(IRBexpr::and_many(vec![])), S::comment("extra")])
    );

    let mut with_metadata = S::assert(IRBexpr::and_many(vec![]));
    with_metadata.meta_mut().at_group("g", None);
    assert_eq!(assertion, with_metadata);

    let condition = IRBexpr::and_many(vec![]);
    let conditional = S::assert(IRBexpr::and_many(vec![])).emit_unless_false(condition.clone());
    assert_ne!(conditional, S::assert(IRBexpr::and_many(vec![])));
    assert_ne!(
        conditional,
        S::assert(IRBexpr::and_many(vec![])).emit_unless_false(IRBexpr::or_many(vec![]))
    );

    let commented = S::assert(IRBexpr::and_many(vec![])).with_comment("one".to_owned());
    assert_ne!(
        commented,
        S::assert(IRBexpr::and_many(vec![])).with_comment("two".to_owned())
    );
}

#[test]
fn exact_equality_preserves_nested_sequence_structure() {
    let leaf = || S::assert(IRBexpr::and_many(vec![]));
    let nested = || S::seq([leaf(), S::seq([leaf(), leaf()])]);
    let flat = || S::seq([leaf(), leaf(), leaf()]);

    let cases = [
        (nested(), flat()),
        (
            CondBlock::new(IRBexpr::and_many(vec![]), nested()).into(),
            CondBlock::new(IRBexpr::and_many(vec![]), flat()).into(),
        ),
        (
            nested().with_comment("header".to_owned()),
            flat().with_comment("header".to_owned()),
        ),
    ];

    for (lhs, rhs) in cases {
        assert_eq!(lhs, rhs);
        assert!(!lhs.exact_eq(&rhs));
    }
}

#[test]
fn symbolic_equivalence_preserves_wrappers_but_ignores_block_comment_text() {
    use eqv::EqvRelation;
    use haloumi_core::eqv::SymbolicEqv;

    type SymbolicStmt = IRStmt<crate::expr::IRAexpr>;
    let body = SymbolicStmt::assert(IRBexpr::and_many(vec![]));
    let lhs = body.clone().with_comment("one".to_owned());
    let rhs = body.with_comment("two".to_owned());
    assert!(SymbolicEqv::equivalent(&lhs, &rhs));
    assert!(!SymbolicEqv::equivalent(
        &lhs,
        &SymbolicStmt::assert(IRBexpr::and_many(vec![]))
    ));
}

pub struct TestHelper<T, O> {
    factory: Box<dyn ConstraintFactory<Inner = T, Out = O>>,
}

impl<T: 'static> TestHelper<T, Constraint<T>> {
    pub fn constraints() -> Self {
        Self {
            factory: Box::new(InnerConstraintFactory::default()),
        }
    }
}

impl<T: 'static> TestHelper<T, IRStmt<T>> {
    pub fn stmts() -> Self {
        Self {
            factory: Box::new(IRStmtFactory::default()),
        }
    }
}

impl<T, O> TestHelper<T, O>
where
    T: PartialEq + std::fmt::Debug + Clone,
    O: PartialEq + std::fmt::Debug,
{
    pub fn helper(&self, x: T, y: T, z: T, w: T) {
        let f = self.factory.as_ref();
        let a = f.eq(x.clone(), y.clone());
        let b = f.eq(x, y);
        let c = f.eq(z.clone(), w.clone());
        let d = f.lt(z, w);

        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_ne!(c, d);
    }

    pub fn helper_with(
        &self,
        x: impl Fn() -> T,
        y: impl Fn() -> T,
        z: impl Fn() -> T,
        w: impl Fn() -> T,
    ) {
        let f = self.factory.as_ref();
        let a = f.eq(x(), y());
        let b = f.eq(x(), y());
        let c = f.eq(z(), w());
        let d = f.lt(z(), w());

        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_ne!(c, d);
    }
}

impl<T> TestHelper<T, IRStmt<T>>
where
    T: PartialEq + std::fmt::Debug + Clone,
{
    pub fn helper_seqs_with(&self, x: impl Fn() -> T, y: impl Fn() -> T) {
        let f = self.factory.as_ref();
        let a = f.eq(x(), y());
        let b = IRStmt::from_iter([f.eq(x(), y())]);

        assert_eq!(a, b);
    }
}

#[test]
fn test_partial_eq_on_i32() {
    let h = TestHelper::<i32, IRStmt<i32>>::stmts();
    h.helper(1, 2, 3, 4);
}

pub mod ff {
    use std::ops::{Add, Mul};

    use crate::stmt::{IRStmt, test::TestHelper};
    use haloumi_core::table::{Rotation, RotationExt};

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub enum MockExpr {
        Constant(usize),
        Fixed(usize, i32),
        Advice(usize, i32),
        Instance(usize, i32),
        Add(Box<MockExpr>, Box<MockExpr>),
        Mul(Box<MockExpr>, Box<MockExpr>),
    }

    impl Mul for MockExpr {
        type Output = Self;

        fn mul(self, rhs: Self) -> Self::Output {
            MockExpr::Mul(Box::new(self), Box::new(rhs))
        }
    }

    impl Add for MockExpr {
        type Output = Self;

        fn add(self, rhs: Self) -> Self::Output {
            MockExpr::Add(Box::new(self), Box::new(rhs))
        }
    }

    pub fn c(n: usize) -> MockExpr {
        MockExpr::Constant(n)
    }

    pub fn f(col: usize, rot: Rotation) -> MockExpr {
        MockExpr::Fixed(col, rot)
    }

    pub fn a(col: usize, rot: Rotation) -> MockExpr {
        MockExpr::Advice(col, rot)
    }

    pub fn i(col: usize, rot: Rotation) -> MockExpr {
        MockExpr::Instance(col, rot)
    }

    #[test]
    fn test_partial_eq_on_expressions() {
        let h = TestHelper::<MockExpr, IRStmt<MockExpr>>::stmts();
        use Rotation as R;
        h.helper_with(|| c(1), || c(2), || c(3), || c(4));
        h.helper_with(|| f(1, R::cur()), || c(2), || c(3), || c(4));
        h.helper_with(|| a(1, R::cur()), || c(2), || c(3), || c(4));
        h.helper_with(|| i(1, R::cur()), || c(2), || c(3), || c(4));

        h.helper_seqs_with(|| c(1), || c(2));
        h.helper_seqs_with(|| f(1, R::cur()), || c(2));
        h.helper_seqs_with(|| a(1, R::cur()), || c(2));
        h.helper_seqs_with(|| i(1, R::cur()), || c(2));
    }
}

#[cfg(feature = "serde")]
mod serde {
    use quickcheck_macros::quickcheck;

    use crate::serde_tests_helpers::round_trip;

    use super::super::*;

    #[quickcheck]
    fn statement_round_trips(value: IRStmt<()>) {
        assert!(value.exact_eq(&round_trip(&value)));
    }
}
