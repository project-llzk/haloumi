use std::sync::Arc;

use super::vars::{NamingConvention, VarKey, VarKeySeed};
use crate::pcl::{ModuleLike as _, expr, stmt};
use haloumi_backend::lowering::CallTracker;
use haloumi_core::{
    cmp::CmpOp,
    felt::Felt,
    slot::{Slot as FuncIO, arg::ArgNo, output::OutputId as FieldId},
};
use haloumi_ir::Prime;
use haloumi_lowering::{ExprLowering, Lowering, Result};

pub type PicusModuleRef = crate::pcl::ModuleRef<VarKey>;
pub(super) type PicusExpr = crate::pcl::expr::Expr;

#[derive(Clone, Debug)]
pub struct PicusModuleLowering {
    module: PicusModuleRef,
    naming_convention: NamingConvention,
    prime: Prime,
    calls: CallTracker,
}

impl PicusModuleLowering {
    pub(crate) fn new(
        module: PicusModuleRef,
        naming_convention: NamingConvention,
        prime: Prime,
    ) -> Self {
        Self {
            module,
            naming_convention,
            prime,
            calls: Default::default(),
        }
    }
}

impl PicusModuleLowering {
    pub(crate) fn lower_func_io(&self, func_io: FuncIO) -> PicusExpr {
        let seed = VarKeySeed::io(func_io, self.naming_convention);
        expr::var(&self.module, seed)
    }
}

fn err(e: anyhow::Error) -> haloumi_lowering::error::Error {
    let b: Box<dyn std::error::Error> = e.into();
    let a: Arc<dyn std::error::Error> = b.into();
    haloumi_lowering::error::Error::Backend(a)
}

impl Lowering for PicusModuleLowering {
    fn generate_constraint<'l: 'o, 'o>(
        &'l self,
        op: CmpOp,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<()> {
        self.module.borrow_mut().add_constraint(match op {
            CmpOp::Eq => expr::eq(lhs, rhs),
            CmpOp::Lt => expr::lt(lhs, rhs),
            CmpOp::Le => expr::le(lhs, rhs),
            CmpOp::Gt => expr::gt(lhs, rhs),
            CmpOp::Ge => expr::ge(lhs, rhs),
            CmpOp::Ne => unimplemented!(),
        });
        Ok(())
    }

    fn num_constraints(&self) -> usize {
        self.module.constraints_len()
    }

    fn generate_comment(&self, s: String) -> Result<()> {
        self.module.borrow_mut().add_stmt(stmt::comment(s));
        Ok(())
    }

    fn generate_call<'l: 'o, 'o>(
        &'l self,
        name: &str,
        inputs: &[Self::CellOutput<'o>],
        output_count: usize,
    ) -> Result<Vec<FuncIO>> {
        let slots = FuncIO::call_outputs(self.calls.next(), output_count);
        let stmt = stmt::call(
            name.to_owned(),
            inputs.to_vec(),
            slots.iter().map(|o| self.lower_func_io(*o)).collect(),
        )
        .map_err(err)?;
        self.module.borrow_mut().add_stmt(stmt);
        Ok(slots)
    }

    fn generate_assume_deterministic(&self, func_io: FuncIO) -> Result<()> {
        let stmt = stmt::assume_deterministic(self.lower_func_io(func_io)).map_err(err)?;
        self.module.borrow_mut().add_stmt(stmt);
        Ok(())
    }

    fn generate_assert<'l: 'o, 'o>(&'l self, expr: &Self::CellOutput<'o>) -> Result<()> {
        let stmt = stmt::constrain(expr.clone());
        self.module.borrow_mut().add_stmt(stmt);
        Ok(())
    }

    fn generate_post_condition<'l: 'o, 'o>(&'l self, expr: &Self::CellOutput<'o>) -> Result<()> {
        let stmt = stmt::post_condition(expr.clone());
        self.module.borrow_mut().add_stmt(stmt);
        Ok(())
    }
}

impl ExprLowering for PicusModuleLowering {
    type CellOutput<'o> = PicusExpr;

    fn lower_sum<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>> {
        Ok(expr::add(lhs, rhs))
    }

    fn lower_product<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>> {
        Ok(expr::mul(lhs, rhs))
    }

    fn lower_neg<'l: 'o, 'o>(
        &'l self,
        expr: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>> {
        Ok(expr::neg(expr))
    }

    fn lower_constant<'l: 'o, 'o>(&'l self, f: Felt) -> Result<Self::CellOutput<'o>> {
        let expr = expr::r#const(f);
        log::debug!(
            "[PicusBackend::lower_constant] Constant value {f:?} becomes expression {expr:?}"
        );
        Ok(expr)
    }

    fn lower_eq<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>> {
        Ok(expr::eq(lhs, rhs))
    }

    fn lower_and<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>> {
        Ok(expr::and(lhs, rhs))
    }

    fn lower_or<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>> {
        Ok(expr::or(lhs, rhs))
    }

    fn lower_function_input(&self, i: usize) -> FuncIO {
        ArgNo::from(i).into()
    }

    fn lower_function_output(&self, o: usize) -> FuncIO {
        FieldId::from(o).into()
    }

    fn lower_funcio<'l: 'o, 'o, IO>(&'l self, io: IO) -> Result<Self::CellOutput<'o>>
    where
        IO: Into<FuncIO>,
    {
        Ok(self.lower_func_io(io.into()))
    }

    fn lower_lt<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>> {
        Ok(expr::lt(lhs, rhs))
    }

    fn lower_le<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>> {
        Ok(expr::le(lhs, rhs))
    }

    fn lower_gt<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>> {
        Ok(expr::gt(lhs, rhs))
    }

    fn lower_ge<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>> {
        Ok(expr::ge(lhs, rhs))
    }

    fn lower_ne<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>> {
        Ok(expr::ne(lhs, rhs))
    }

    fn lower_not<'l: 'o, 'o>(
        &'l self,
        value: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>> {
        Ok(expr::not(value))
    }

    fn lower_true<'l: 'o, 'o>(&'l self) -> Result<Self::CellOutput<'o>> {
        Ok(expr::eq(
            &expr::r#const(self.prime.zero()),
            &expr::r#const(self.prime.zero()),
        ))
    }

    fn lower_false<'l: 'o, 'o>(&'l self) -> Result<Self::CellOutput<'o>> {
        Ok(expr::eq(
            &expr::r#const(self.prime.zero()),
            &expr::r#const(self.prime.one()),
        ))
    }

    fn lower_det<'l: 'o, 'o>(
        &'l self,
        expr: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>> {
        Ok(expr::det(expr))
    }

    fn lower_implies<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>> {
        Ok(expr::implies(lhs, rhs))
    }

    fn lower_iff<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>> {
        Ok(expr::iff(lhs, rhs))
    }
}
