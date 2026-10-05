use std::{
    iter::{Product, Sum},
    marker::PhantomData,
    ops::{Add, Mul, Neg, Sub},
    sync::Arc,
};

use ff::Field;
use haloumi_core::{
    auto_conf::AutoConfigure,
    expressions::{EvalExpression, EvaluableExpr, ExprBuilder, ExpressionInfo, ExpressionTypes},
    info_traits::{
        ChallengeInfo, ConstraintSystemInfo, CreateQuery, GateInfo, QueryInfo, SelectorInfo,
    },
    lookups::LookupData,
    query::QueryKind,
    table::{Any, Rotation},
};

#[derive(Debug)]
pub enum Error {
    Synthesis(String),
    Other(Arc<dyn std::error::Error + Send + Sync + 'static>),
}

haloumi_integration::__impl_into_and_from_error!(Error, |value| Self::Other(Arc::new(value)));

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Synthesis(err) => write!(f, "Synthesis: {err}"),
            Error::Other(error) => write!(f, "Error: {error}"),
        }
    }
}

impl std::error::Error for Error {}

/// A selector allocated by [`ConstraintSystem`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Selector(pub(crate) usize);

impl SelectorInfo for Selector {
    fn id(&self) -> usize {
        self.0
    }
}

impl Selector {
    /// Enable this selector at the given offset within the given region.
    pub fn enable<F: Field>(&self, region: &mut Region<F>, offset: usize) -> Result<(), Error> {
        region.enable_selector(|| "", self, offset)
    }

    /// Is this selector "simple"? Simple selectors can only be multiplied
    /// by expressions that contain no other simple selectors.
    pub fn is_simple(&self) -> bool {
        true
    }

    /// Returns index of this selector
    pub fn index(&self) -> usize {
        self.0
    }

    /// Return expression from selector
    pub fn expr<F: Field>(&self) -> Expression<F> {
        Expression::Selector(*self)
    }
}

pub use haloumi_core::query::{Advice, Fixed, Instance};
pub use haloumi_core::table::Column;

use crate::circuit::Region;

/// The expression language retained by the mock constraint system.
#[derive(Clone, Debug, PartialEq, Eq)]
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

impl<F: Field> Expression<F> {
    /// Returns whether or not this expression contains a simple `Selector`.
    fn contains_simple_selector(&self) -> bool {
        match self {
            Expression::Constant(_)
            | Expression::Fixed(_)
            | Expression::Advice(_)
            | Expression::Instance(_)
            | Expression::Challenge(_) => false,
            Expression::Selector(selector) => selector.is_simple(),
            Expression::Negated(expression) | Expression::Scaled(expression, _) => {
                expression.contains_simple_selector()
            }
            Expression::Sum(lhs, rhs) | Expression::Product(lhs, rhs) => {
                lhs.contains_simple_selector() || rhs.contains_simple_selector()
            }
        }
    }
}

impl<F: Field + From<u64>> From<u64> for Expression<F> {
    fn from(value: u64) -> Self {
        Expression::Constant(F::from(value))
    }
}

impl<F: Field> Neg for Expression<F> {
    type Output = Expression<F>;
    fn neg(self) -> Self::Output {
        Expression::Negated(Box::new(self))
    }
}

impl<F: Field> Neg for &Expression<F> {
    type Output = Expression<F>;
    fn neg(self) -> Self::Output {
        -self.clone()
    }
}

impl<F: Field> Add for Expression<F> {
    type Output = Expression<F>;
    fn add(self, rhs: Expression<F>) -> Expression<F> {
        if self.contains_simple_selector() || rhs.contains_simple_selector() {
            panic!("attempted to use a simple selector in an addition");
        }
        if self == Expression::Constant(F::ZERO) {
            return rhs;
        }
        if rhs == Expression::Constant(F::ZERO) {
            return self;
        }
        Expression::Sum(Box::new(self), Box::new(rhs))
    }
}

impl<'a, F: Field> Add for &'a Expression<F> {
    type Output = Expression<F>;
    fn add(self, rhs: &'a Expression<F>) -> Expression<F> {
        self.clone() + rhs.clone()
    }
}

impl<F: Field> Add<Expression<F>> for &Expression<F> {
    type Output = Expression<F>;
    fn add(self, rhs: Expression<F>) -> Expression<F> {
        self.clone() + rhs
    }
}

impl<'a, F: Field> Add<&'a Expression<F>> for Expression<F> {
    type Output = Expression<F>;
    fn add(self, rhs: &'a Expression<F>) -> Expression<F> {
        self + rhs.clone()
    }
}

impl<F: Field> Sub for Expression<F> {
    type Output = Expression<F>;
    fn sub(self, rhs: Expression<F>) -> Expression<F> {
        if self.contains_simple_selector() || rhs.contains_simple_selector() {
            panic!("attempted to use a simple selector in a subtraction");
        }
        if self == Expression::Constant(F::ZERO) {
            return -rhs;
        }
        if rhs == Expression::Constant(F::ZERO) {
            return self;
        }
        Expression::Sum(Box::new(self), Box::new(-rhs))
    }
}

impl<'a, F: Field> Sub for &'a Expression<F> {
    type Output = Expression<F>;
    fn sub(self, rhs: &'a Expression<F>) -> Expression<F> {
        self.clone() - rhs.clone()
    }
}

impl<F: Field> Sub<Expression<F>> for &Expression<F> {
    type Output = Expression<F>;
    fn sub(self, rhs: Expression<F>) -> Expression<F> {
        self.clone() - rhs
    }
}

impl<'a, F: Field> Sub<&'a Expression<F>> for Expression<F> {
    type Output = Expression<F>;
    fn sub(self, rhs: &'a Expression<F>) -> Expression<F> {
        self - rhs.clone()
    }
}

impl<F: Field> Mul for Expression<F> {
    type Output = Expression<F>;
    fn mul(self, rhs: Expression<F>) -> Expression<F> {
        if self.contains_simple_selector() && rhs.contains_simple_selector() {
            panic!("attempted to multiply two expressions containing simple selectors");
        }
        if self == Expression::Constant(F::ZERO) || rhs == Expression::Constant(F::ZERO) {
            return Expression::Constant(F::ZERO);
        }
        if self == Expression::Constant(F::ONE) {
            return rhs;
        }
        if rhs == Expression::Constant(F::ONE) {
            return self;
        }
        Expression::Product(Box::new(self), Box::new(rhs))
    }
}

impl<'a, F: Field> Mul for &'a Expression<F> {
    type Output = Expression<F>;
    fn mul(self, rhs: &'a Expression<F>) -> Expression<F> {
        self.clone() * rhs.clone()
    }
}

impl<F: Field> Mul<Expression<F>> for &Expression<F> {
    type Output = Expression<F>;
    fn mul(self, rhs: Expression<F>) -> Expression<F> {
        self.clone() * rhs
    }
}

impl<'a, F: Field> Mul<&'a Expression<F>> for Expression<F> {
    type Output = Expression<F>;
    fn mul(self, rhs: &'a Expression<F>) -> Expression<F> {
        self * rhs.clone()
    }
}

impl<F: Field> Mul<F> for Expression<F> {
    type Output = Expression<F>;
    fn mul(self, rhs: F) -> Expression<F> {
        Expression::Scaled(Box::new(self), rhs)
    }
}

impl<F: Field> Mul<F> for &Expression<F> {
    type Output = Expression<F>;
    fn mul(self, rhs: F) -> Expression<F> {
        self.clone() * rhs
    }
}

impl<F: Field> Sum<Self> for Expression<F> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, x| acc + x)
            .unwrap_or(Expression::Constant(F::ZERO))
    }
}

impl<F: Field> Product<Self> for Expression<F> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, x| acc * x)
            .unwrap_or(Expression::Constant(F::ONE))
    }
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
        match self {
            Self::Negated(value) => Some(value),
            _ => None,
        }
    }
    fn as_fixed_query(&self) -> Option<&Query<Fixed>> {
        match self {
            Self::Fixed(query) => Some(query),
            _ => None,
        }
    }
}

impl<F: Field> ExprBuilder<F> for Expression<F> {
    fn constant(value: F) -> Self {
        Self::Constant(value)
    }
    fn selector(value: Selector) -> Self {
        Self::Selector(value)
    }
    fn fixed(value: Query<Fixed>) -> Self {
        Self::Fixed(value)
    }
    fn advice(value: Query<Advice>) -> Self {
        Self::Advice(value)
    }
    fn instance(value: Query<Instance>) -> Self {
        Self::Instance(value)
    }
    fn challenge(value: Challenge) -> Self {
        Self::Challenge(value)
    }
    fn negated(value: Self) -> Self {
        Self::Negated(Box::new(value))
    }
    fn sum(lhs: Self, rhs: Self) -> Self {
        Self::Sum(Box::new(lhs), Box::new(rhs))
    }
    fn product(lhs: Self, rhs: Self) -> Self {
        Self::Product(Box::new(lhs), Box::new(rhs))
    }
    fn scaled(value: Self, scalar: F) -> Self {
        Self::Scaled(Box::new(value), scalar)
    }
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
            Self::Product(lhs, rhs) => {
                evaluator.product(lhs.evaluate(evaluator), rhs.evaluate(evaluator))
            }
            Self::Scaled(value, scalar) => evaluator.scaled(value.evaluate(evaluator), scalar),
        }
    }
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
    fn new(index: usize, rotation: Rotation) -> Self {
        Self {
            index,
            rotation,
            _kind: PhantomData,
        }
    }
}

impl<K: QueryKind> QueryInfo for Query<K> {
    type Kind = K;
    fn rotation(&self) -> Rotation {
        self.rotation
    }
    fn column_index(&self) -> usize {
        self.index
    }
}

/// A challenge query.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Challenge {
    index: usize,
    phase: u8,
}

impl ChallengeInfo for Challenge {
    fn index(&self) -> usize {
        self.index
    }
    fn phase(&self) -> u8 {
        self.phase
    }
}

impl<F: Field> CreateQuery<Expression<F>> for Query<Advice> {
    fn query_expr(index: usize, at: Rotation) -> Expression<F> {
        Expression::Advice(Self::new(index, at))
    }
}
impl<F: Field> CreateQuery<Expression<F>> for Query<Fixed> {
    fn query_expr(index: usize, at: Rotation) -> Expression<F> {
        Expression::Fixed(Self::new(index, at))
    }
}
impl<F: Field> CreateQuery<Expression<F>> for Query<Instance> {
    fn query_expr(index: usize, at: Rotation) -> Expression<F> {
        Expression::Instance(Self::new(index, at))
    }
}

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
        Self {
            advice: 0,
            fixed: 0,
            instance: 0,
            selectors: 0,
            gates: vec![],
            lookups: vec![],
            constants: vec![],
        }
    }
}

impl<F: Field> ConstraintSystem<F> {
    /// Allocates an advice column index.
    pub fn advice_column(&mut self) -> Column<Advice> {
        let index = self.advice;
        self.advice += 1;
        Column::new(index, Advice)
    }
    /// Allocates a fixed column index.
    pub fn fixed_column(&mut self) -> Column<Fixed> {
        let index = self.fixed;
        self.fixed += 1;
        Column::new(index, Fixed)
    }
    /// Allocates an instance column index.
    pub fn instance_column(&mut self) -> Column<Instance> {
        let index = self.instance;
        self.instance += 1;
        Column::new(index, Instance)
    }
    /// Allocates a selector.
    pub fn selector(&mut self) -> Selector {
        let index = self.selectors;
        self.selectors += 1;
        Selector(index)
    }
    /// Allocates a selector that may be used in lookup expressions.
    pub fn complex_selector(&mut self) -> Selector {
        self.selector()
    }
    /// Allocates a fixed column for use as a lookup table column.
    pub fn lookup_table_column(&mut self) -> TableColumn {
        TableColumn {
            inner: self.fixed_column(),
        }
    }
    /// Records a gate and its constraint expressions.
    pub fn create_gate(
        &mut self,
        name: impl Into<String>,
        mut polynomials: impl FnMut(&mut VirtualCells<F>) -> Vec<Expression<F>>,
    ) {
        let polynomials = polynomials(&mut VirtualCells::new());
        self.gates.push(Gate {
            name: name.into(),
            polynomials,
        });
    }
    /// Records a lookup declaration.
    pub fn lookup(
        &mut self,
        name: impl Into<String>,
        mut lookup: impl FnMut(&mut VirtualCells<F>) -> Vec<(Expression<F>, TableColumn)>,
    ) {
        let (arguments, table): (Vec<_>, Vec<_>) = lookup(&mut VirtualCells::new())
            .into_iter()
            .map(|(argument, table)| {
                (
                    argument,
                    Expression::Fixed(Query::new(table.inner().index(), 0)),
                )
            })
            .unzip();
        self.lookups.push(Lookup {
            name: name.into(),
            arguments,
            table,
        });
    }

    pub fn enable_equality(&mut self, _: impl Into<Column<Any>>) {}
}

#[derive(Debug)]
pub struct VirtualCells<F>(PhantomData<F>);

impl<F: Field> VirtualCells<F> {
    fn new() -> Self {
        VirtualCells(PhantomData)
    }

    pub fn query_selector(&mut self, selector: Selector) -> Expression<F> {
        Expression::Selector(selector)
    }

    pub fn query_fixed(&mut self, column: Column<Fixed>, at: Rotation) -> Expression<F> {
        Expression::Fixed(Query::new(column.index(), at))
    }

    pub fn query_advice(&mut self, column: Column<Advice>, at: Rotation) -> Expression<F> {
        Expression::Advice(Query::new(column.index(), at))
    }

    pub fn query_instance(&mut self, column: Column<Instance>, at: Rotation) -> Expression<F> {
        Expression::Instance(Query::new(column.index(), at))
    }

    pub fn query_any<C: Into<Column<Any>>>(&mut self, column: C, at: Rotation) -> Expression<F> {
        let column = column.into();
        match column.column_type() {
            Any::Advice => self.query_advice(Column::<Advice>::try_from(column).unwrap(), at),
            Any::Fixed => self.query_fixed(Column::<Fixed>::try_from(column).unwrap(), at),
            Any::Instance => self.query_instance(Column::<Instance>::try_from(column).unwrap(), at),
        }
    }

    pub fn query_challenge(&mut self, challenge: Challenge) -> Expression<F> {
        Expression::Challenge(challenge)
    }
}

impl<F: Field> ConstraintSystemInfo<F> for ConstraintSystem<F> {
    type Polynomial = Expression<F>;
    type InstanceCol = Column<Instance>;
    type AdviceCol = Column<Advice>;
    type FixedCol = Column<Fixed>;
    type AnyCol = Column<Any>;
    fn gates(&self) -> Vec<&dyn GateInfo<Self::Polynomial>> {
        self.gates
            .iter()
            .map(|gate| gate as &dyn GateInfo<_>)
            .collect()
    }
    fn lookups(&self) -> Vec<LookupData<'_, Self::Polynomial>> {
        self.lookups
            .iter()
            .map(|lookup| LookupData {
                name: &lookup.name,
                arguments: &lookup.arguments,
                table: &lookup.table,
            })
            .collect()
    }
    fn constants(&self) -> &[Self::FixedCol] {
        &self.constants
    }
    fn enable_constant(&mut self, column: Self::FixedCol) {
        if !self.constants.contains(&column) {
            self.constants.push(column);
        }
    }
    fn enable_equality(&mut self, _: impl Into<Self::AnyCol>) {}
}

impl<F: Field> AutoConfigure<ConstraintSystem<F>> for Column<Advice> {
    fn configure(cs: &mut ConstraintSystem<F>) -> Self {
        cs.advice_column()
    }
}

impl<F: Field> AutoConfigure<ConstraintSystem<F>> for Column<Fixed> {
    fn configure(cs: &mut ConstraintSystem<F>) -> Self {
        cs.fixed_column()
    }
}

impl<F: Field> AutoConfigure<ConstraintSystem<F>> for Column<Instance> {
    fn configure(cs: &mut ConstraintSystem<F>) -> Self {
        cs.instance_column()
    }
}

/// A gate recorded during mock circuit configuration.
#[derive(Clone, Debug)]
pub struct Gate<F: Field> {
    name: String,
    polynomials: Vec<Expression<F>>,
}

impl<F: Field> GateInfo<Expression<F>> for Gate<F> {
    fn name(&self) -> &str {
        &self.name
    }
    fn polynomials(&self) -> &[Expression<F>] {
        &self.polynomials
    }
}

#[derive(Clone, Debug)]
struct Lookup<F: Field> {
    name: String,
    arguments: Vec<Expression<F>>,
    table: Vec<Expression<F>>,
}

pub struct Constraints;

impl Constraints {
    pub fn with_selector<F: Field>(
        selector: Selector,
        exprs: Vec<Expression<F>>,
    ) -> Vec<Expression<F>> {
        exprs
            .into_iter()
            .map(|e| Expression::Product(Box::new(Expression::Selector(selector)), Box::new(e)))
            .collect()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct TableColumn {
    inner: Column<Fixed>,
}

impl TableColumn {
    /// Returns inner column
    pub fn inner(&self) -> Column<Fixed> {
        self.inner
    }
}
