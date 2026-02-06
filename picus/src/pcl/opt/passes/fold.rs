use haloumi_ir::Prime;

use crate::pcl::{
    Program,
    expr::{Expr, traits::ExprLike},
    opt::{MutOptResult, MutOptimizer, OptResult, Optimizer},
    vars::VarKind,
};

#[derive(Default, Debug)]
pub struct FoldExprsPass;

impl<K: VarKind + Copy> MutOptimizer<Program<K>> for FoldExprsPass {
    fn optimize(&mut self, t: &mut Program<K>) -> MutOptResult {
        let prime = t.prime().clone();
        let mut inner = FoldExprsPassImpl(prime);
        let opt: &mut dyn MutOptimizer<Program<K>> = &mut inner;
        opt.optimize(t)
    }
}

#[derive(Debug)]
struct FoldExprsPassImpl(Prime);

impl Optimizer<dyn ExprLike, Expr> for FoldExprsPassImpl {
    fn optimize(&mut self, i: &dyn ExprLike) -> OptResult<Expr> {
        Ok(i.fold(self.0).unwrap_or_else(|| i.wrap()))
    }
}
