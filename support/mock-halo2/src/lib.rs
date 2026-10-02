//! Minimal, deterministic circuit metadata used by Haloumi extractor tests.
//!
//! This crate deliberately models only the information Haloumi consumes while
//! extracting a circuit.  It is not a Halo2 implementation and performs no
//! proving or witness validation.

use std::marker::PhantomData;

use ff::Field;
use haloumi_core::{
    auto_conf::AutoConfigure,
    expressions::{EvalExpression, EvaluableExpr, ExprBuilder, ExpressionInfo, ExpressionTypes},
    info_traits::{ChallengeInfo, ConstraintSystemInfo, CreateQuery, GateInfo, QueryInfo, SelectorInfo},
    lookups::LookupData,
    query::{Advice, Fixed, Instance, QueryKind},
    table::{Any, Column, Rotation},
};

/// A selector allocated by [`ConstraintSystem`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Selector(usize);

impl SelectorInfo for Selector {
    fn id(&self) -> usize { self.0 }
}

/// A query to a mock column.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Query<K: QueryKind> {
    index: usize,
    rotation: Rotation,
    _kind: PhantomData<K>,
}

impl<K: QueryKind> Query<K> {
    /// Creates a query for a column and relative row.
    pub fn new(index: usize, rotation: Rotation) -> Self {
        Self { index, rotation, _kind: PhantomData }
    }
}

impl<K: QueryKind> QueryInfo for Query<K> {
    type Kind = K;
    fn rotation(&self) -> Rotation { self.rotation }
    fn column_index(&self) -> usize { self.index }
}

/// A challenge query.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Challenge { index: usize, phase: u8 }

impl ChallengeInfo for Challenge {
    fn index(&self) -> usize { self.index }
    fn phase(&self) -> u8 { self.phase }
}

/// The expression language retained by the mock constraint system.
#[derive(Clone, Debug)]
pub enum Expression<F: Field> {
    Constant(F),
    Selector(Selector),
    Fixed(Query<Fixed>),
    Advice(Query<Advice>),
    Instance(Query<Instance>),
    Challenge(Challenge),
    Negated(Box<Self>),
    Sum(Box<Self>, Box<Self>),
    Product(Box<Self>, Box<Self>),
    Scaled(Box<Self>, F),
}

impl<F: Field> ExpressionTypes for Expression<F> {
    type Selector = Selector;
    type FixedQuery = Query<Fixed>;
    type AdviceQuery = Query<Advice>;
    type InstanceQuery = Query<Instance>;
    type Challenge = Challenge;
}

impl<F: Field> ExpressionInfo for Expression<F> {
    fn as_negation(&self) -> Option<&Self> {
        match self { Self::Negated(value) => Some(value), _ => None }
    }
    fn as_fixed_query(&self) -> Option<&Query<Fixed>> {
        match self { Self::Fixed(query) => Some(query), _ => None }
    }
}

impl<F: Field> ExprBuilder<F> for Expression<F> {
    fn constant(value: F) -> Self { Self::Constant(value) }
    fn selector(value: Selector) -> Self { Self::Selector(value) }
    fn fixed(value: Query<Fixed>) -> Self { Self::Fixed(value) }
    fn advice(value: Query<Advice>) -> Self { Self::Advice(value) }
    fn instance(value: Query<Instance>) -> Self { Self::Instance(value) }
    fn challenge(value: Challenge) -> Self { Self::Challenge(value) }
    fn negated(value: Self) -> Self { Self::Negated(Box::new(value)) }
    fn sum(lhs: Self, rhs: Self) -> Self { Self::Sum(Box::new(lhs), Box::new(rhs)) }
    fn product(lhs: Self, rhs: Self) -> Self { Self::Product(Box::new(lhs), Box::new(rhs)) }
    fn scaled(value: Self, scalar: F) -> Self { Self::Scaled(Box::new(value), scalar) }
}

impl<F: Field> EvaluableExpr<F> for Expression<F> {
    fn evaluate<E: EvalExpression<F, Self>>(&self, evaluator: &E) -> E::Output {
        match self {
            Self::Constant(value) => evaluator.constant(value),
            Self::Selector(value) => evaluator.selector(value),
            Self::Fixed(value) => evaluator.fixed(value),
            Self::Advice(value) => evaluator.advice(value),
            Self::Instance(value) => evaluator.instance(value),
            Self::Challenge(value) => evaluator.challenge(value),
            Self::Negated(value) => evaluator.negated(value.evaluate(evaluator)),
            Self::Sum(lhs, rhs) => evaluator.sum(lhs.evaluate(evaluator), rhs.evaluate(evaluator)),
            Self::Product(lhs, rhs) => evaluator.product(lhs.evaluate(evaluator), rhs.evaluate(evaluator)),
            Self::Scaled(value, scalar) => evaluator.scaled(value.evaluate(evaluator), scalar),
        }
    }
}

impl<F: Field> CreateQuery<Expression<F>> for Query<Advice> {
    fn query_expr(index: usize, at: Rotation) -> Expression<F> { Expression::Advice(Self::new(index, at)) }
}
impl<F: Field> CreateQuery<Expression<F>> for Query<Fixed> {
    fn query_expr(index: usize, at: Rotation) -> Expression<F> { Expression::Fixed(Self::new(index, at)) }
}
impl<F: Field> CreateQuery<Expression<F>> for Query<Instance> {
    fn query_expr(index: usize, at: Rotation) -> Expression<F> { Expression::Instance(Self::new(index, at)) }
}

/// A gate recorded during mock circuit configuration.
#[derive(Clone, Debug)]
pub struct Gate<F: Field> { name: String, polynomials: Vec<Expression<F>> }

impl<F: Field> GateInfo<Expression<F>> for Gate<F> {
    fn name(&self) -> &str { &self.name }
    fn polynomials(&self) -> &[Expression<F>] { &self.polynomials }
}

#[derive(Clone, Debug)]
struct Lookup<F: Field> { name: String, arguments: Vec<Expression<F>>, table: Vec<Expression<F>> }

/// Metadata-only constraint system for mock circuits.
#[derive(Clone, Debug)]
pub struct ConstraintSystem<F: Field> {
    advice: usize,
    fixed: usize,
    instance: usize,
    selectors: usize,
    gates: Vec<Gate<F>>,
    lookups: Vec<Lookup<F>>,
    constants: Vec<Column<Fixed>>,
}

impl<F: Field> Default for ConstraintSystem<F> {
    fn default() -> Self {
        Self { advice: 0, fixed: 0, instance: 0, selectors: 0, gates: vec![], lookups: vec![], constants: vec![] }
    }
}

impl<F: Field> AutoConfigure<ConstraintSystem<F>> for Column<Advice> {
    fn configure(cs: &mut ConstraintSystem<F>) -> Self { Column::new(cs.advice_column(), Advice) }
}

impl<F: Field> AutoConfigure<ConstraintSystem<F>> for Column<Fixed> {
    fn configure(cs: &mut ConstraintSystem<F>) -> Self { Column::new(cs.fixed_column(), Fixed) }
}

impl<F: Field> AutoConfigure<ConstraintSystem<F>> for Column<Instance> {
    fn configure(cs: &mut ConstraintSystem<F>) -> Self { Column::new(cs.instance_column(), Instance) }
}

impl<F: Field> ConstraintSystem<F> {
    /// Allocates an advice column index.
    pub fn advice_column(&mut self) -> usize { let index = self.advice; self.advice += 1; index }
    /// Allocates a fixed column index.
    pub fn fixed_column(&mut self) -> usize { let index = self.fixed; self.fixed += 1; index }
    /// Allocates an instance column index.
    pub fn instance_column(&mut self) -> usize { let index = self.instance; self.instance += 1; index }
    /// Allocates a selector.
    pub fn selector(&mut self) -> Selector { let index = self.selectors; self.selectors += 1; Selector(index) }
    /// Records a gate and its constraint expressions.
    pub fn create_gate(&mut self, name: impl Into<String>, polynomials: Vec<Expression<F>>) {
        self.gates.push(Gate { name: name.into(), polynomials });
    }
    /// Records a lookup declaration.
    pub fn lookup(&mut self, name: impl Into<String>, arguments: Vec<Expression<F>>, table: Vec<Expression<F>>) {
        self.lookups.push(Lookup { name: name.into(), arguments, table });
    }
}

impl<F: Field> ConstraintSystemInfo<F> for ConstraintSystem<F> {
    type Polynomial = Expression<F>;
    type InstanceCol = Column<Instance>;
    type AdviceCol = Column<Advice>;
    type FixedCol = Column<Fixed>;
    type AnyCol = Column<Any>;
    fn gates(&self) -> Vec<&dyn GateInfo<Self::Polynomial>> {
        self.gates.iter().map(|gate| gate as &dyn GateInfo<_>).collect()
    }
    fn lookups(&self) -> Vec<LookupData<'_, Self::Polynomial>> {
        self.lookups.iter().map(|lookup| LookupData {
            name: &lookup.name,
            arguments: &lookup.arguments,
            table: &lookup.table,
        }).collect()
    }
    fn constants(&self) -> &[Self::FixedCol] { &self.constants }
    fn enable_constant(&mut self, column: Self::FixedCol) {
        if !self.constants.contains(&column) { self.constants.push(column); }
    }
    fn enable_equality(&mut self, _: impl Into<Self::AnyCol>) {}
}

#[cfg(test)]
mod tests {
    use super::*;
    use haloumi_core::{
        expressions::ExprBuilder,
        info_traits::ConstraintSystemInfo,
        table::RotationExt,
    };
    use halo2curves::bn256::Fr;

    #[test]
    fn records_gate_and_lookup_metadata() {
        let mut cs = ConstraintSystem::<Fr>::default();
        let advice = cs.advice_column();
        let fixed = cs.fixed_column();
        let _selector = cs.selector();
        let advice = Expression::advice(Query::new(advice, Rotation::cur()));
        let fixed = Expression::fixed(Query::new(fixed, Rotation::cur()));

        cs.create_gate("product", vec![Expression::product(advice.clone(), fixed.clone())]);
        cs.lookup("table", vec![advice], vec![fixed]);

        assert_eq!(cs.gates().len(), 1);
        assert_eq!(cs.gates()[0].name(), "product");
        assert_eq!(cs.lookups().len(), 1);
        assert_eq!(cs.lookups()[0].name, "table");
    }
}
