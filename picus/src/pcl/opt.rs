use std::{marker::PhantomData, sync::Arc};

use anyhow::Result;

use crate::pcl::{
    Module, Program,
    errors::ExprArgsError,
    expr::{Expr, traits::ExprLike},
    stmt::traits::StmtLike,
    vars::VarKind,
};

pub mod passes;

/// Optimizer pass error.
#[derive(Debug)]
pub struct PassError(Arc<dyn std::error::Error + Send + Sync + 'static>);

impl std::fmt::Display for PassError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.0.as_ref(), f)
    }
}

impl PassError {
    pub(crate) fn new<E>(error: E) -> Self
    where
        E: std::error::Error + Send + Sync + 'static,
    {
        Self(Arc::new(error))
    }
}

impl From<ExprArgsError> for PassError {
    fn from(value: ExprArgsError) -> Self {
        Self::new(value)
    }
}

pub type OptResult<O> = Result<O, PassError>;
pub type MutOptResult = OptResult<()>;

pub trait Optimizer<I: ?Sized, O>: std::fmt::Debug {
    fn optimize(&mut self, i: &I) -> OptResult<O>;
}

pub trait MutOptimizer<T: ?Sized>: std::fmt::Debug {
    fn optimize(&mut self, t: &mut T) -> MutOptResult;
}

#[derive(Debug)]
pub struct OptimizerPipelineBuilder<K: VarKind>(OptimizerPipeline<K>);

impl<K: VarKind + 'static> OptimizerPipelineBuilder<K> {
    pub fn new() -> Self {
        Self(OptimizerPipeline {
            passes: Default::default(),
        })
    }

    pub fn add_pass_with_params<P: ProgramOptimizer<K> + 'static>(
        self,
        params: impl Into<P>,
    ) -> Self {
        let mut b = self;
        b.0.passes.push(P::create(params));
        b
    }

    pub fn add_pass<P: ProgramOptimizer<K> + Default + 'static>(self) -> Self {
        let mut b = self;
        b.0.passes.push(P::create(P::default()));
        b
    }

    pub fn add_module_scope_expr_pass_fn<FN, FN2>(self, f: FN) -> Self
    where
        FN: FnMut(&str) -> FN2 + 'static,
        FN2: FnMut(&dyn ExprLike) -> OptResult<Expr> + 'static,
    {
        self.add_pass_with_params::<AnonModuleScopedExprPass<K, FN, FN2>>(f)
    }
}

impl<K: VarKind + 'static> Default for OptimizerPipelineBuilder<K> {
    fn default() -> Self {
        Self::new()
    }
}

struct AnonModuleScopedExprPass<K, FN, FN2>(FN, PhantomData<(K, FN2)>)
where
    K: VarKind,
    FN: FnMut(&str) -> FN2,
    FN2: FnMut(&dyn ExprLike) -> OptResult<Expr>;

impl<K, FN, FN2> std::fmt::Debug for AnonModuleScopedExprPass<K, FN, FN2>
where
    K: VarKind,
    FN: FnMut(&str) -> FN2,
    FN2: FnMut(&dyn ExprLike) -> OptResult<Expr>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AnonModuleScopedExprPass").finish()
    }
}

impl<K, FN, FN2> From<FN> for AnonModuleScopedExprPass<K, FN, FN2>
where
    K: VarKind,
    FN: FnMut(&str) -> FN2,
    FN2: FnMut(&dyn ExprLike) -> OptResult<Expr>,
{
    fn from(value: FN) -> Self {
        Self(value, Default::default())
    }
}

impl<K, FN, FN2> MutOptimizer<Module<K>> for AnonModuleScopedExprPass<K, FN, FN2>
where
    K: VarKind,
    FN: FnMut(&str) -> FN2,
    FN2: FnMut(&dyn ExprLike) -> OptResult<Expr>,
{
    fn optimize(&mut self, module: &mut Module<K>) -> MutOptResult {
        let name = module.name();
        let mut f = self.0(name);
        for stmt in module.stmts_mut() {
            apply_to_args(stmt, &mut f)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct OptimizerPipeline<K: VarKind> {
    passes: Vec<Box<dyn MutOptimizer<Program<K>>>>,
}

impl<K: VarKind> From<OptimizerPipelineBuilder<K>> for OptimizerPipeline<K> {
    fn from(value: OptimizerPipelineBuilder<K>) -> Self {
        value.0
    }
}

impl<K: VarKind> MutOptimizer<Program<K>> for OptimizerPipeline<K> {
    fn optimize(&mut self, program: &mut Program<K>) -> Result<(), PassError> {
        self.passes.as_mut_slice().optimize(program)
    }
}

#[allow(dead_code)]
pub trait ExprOptimizer: Optimizer<dyn ExprLike, Expr> {
    fn create<I>(i: I) -> Box<dyn Optimizer<dyn ExprLike, Expr>>
    where
        I: Into<Self>,
        Self: Sized + 'static,
    {
        Box::new(i.into())
    }
}

#[allow(dead_code)]
pub trait StmtOptimizer: MutOptimizer<dyn StmtLike> {
    fn create<I>(i: I) -> Box<dyn MutOptimizer<dyn StmtLike>>
    where
        I: Into<Self>,
        Self: Sized + 'static,
    {
        Box::new(i.into())
    }
}

#[allow(dead_code)]
pub trait ModuleOptimizer<K: VarKind>: MutOptimizer<Module<K>> {
    fn create<I>(i: I) -> Box<dyn MutOptimizer<Module<K>>>
    where
        I: Into<Self>,
        Self: Sized + 'static,
    {
        Box::new(i.into())
    }
}

pub trait ProgramOptimizer<K: VarKind>: MutOptimizer<Program<K>> {
    fn create<I>(i: I) -> Box<dyn MutOptimizer<Program<K>>>
    where
        I: Into<Self>,
        Self: Sized + 'static,
    {
        Box::new(i.into())
    }
}

fn apply_to_args<F>(stmt: &mut dyn StmtLike, f: &mut F) -> MutOptResult
where
    F: FnMut(&dyn ExprLike) -> OptResult<Expr>,
{
    for (idx, expr) in stmt.args().iter().enumerate() {
        let new_expr = f(expr)?;
        stmt.replace_arg(idx, new_expr).map_err(PassError::new)?;
    }
    Ok(())
}

impl<T> ExprOptimizer for T where T: Optimizer<dyn ExprLike, Expr> {}

impl<T> MutOptimizer<dyn StmtLike> for T
where
    T: Optimizer<dyn ExprLike + 'static, Expr>,
{
    fn optimize(&mut self, stmt: &mut (dyn StmtLike + 'static)) -> MutOptResult {
        for (idx, expr) in stmt.args().iter().enumerate() {
            let new_expr = self.optimize(expr)?;
            stmt.replace_arg(idx, new_expr).map_err(PassError::new)?;
        }
        Ok(())
    }
}
impl<T> StmtOptimizer for T where T: MutOptimizer<dyn StmtLike> {}

impl<T, K> MutOptimizer<Module<K>> for T
where
    T: MutOptimizer<dyn StmtLike>,
    K: VarKind,
{
    fn optimize(&mut self, module: &mut Module<K>) -> MutOptResult {
        for stmt in module.stmts_mut() {
            self.optimize(stmt)?;
        }
        Ok(())
    }
}
impl<T, K> ModuleOptimizer<K> for T
where
    T: MutOptimizer<Module<K>>,
    K: VarKind,
{
}

impl<T, K: VarKind> MutOptimizer<Program<K>> for T
where
    T: MutOptimizer<Module<K>>,
{
    fn optimize(&mut self, program: &mut Program<K>) -> MutOptResult {
        for module in program.modules_mut() {
            self.optimize(module)?;
        }
        Ok(())
    }
}

impl<T, K> ProgramOptimizer<K> for T
where
    T: MutOptimizer<Program<K>>,
    K: VarKind,
{
}

impl<T> MutOptimizer<T> for &mut [Box<dyn MutOptimizer<T>>] {
    fn optimize(&mut self, t: &mut T) -> MutOptResult {
        for pass in self.iter_mut() {
            pass.optimize(t)?;
        }
        Ok(())
    }
}
