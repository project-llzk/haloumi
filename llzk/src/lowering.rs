use crate::error::{Error, UnexpectedTypeError};
use crate::factory::{MemberKind, StructIO, filename};
use crate::state::LlzkCodegenState;
use haloumi_backend::lowering::CallTracker;
//use backend_err::{Result, backend_err};
use haloumi_lowering::{ExprLowering, Lowering, Result as LoweringResult, bail_backend};
use llzk::builder::OpBuilder;
use llzk::dialect::function;
use llzk::prelude::*;
use melior::dialect::arith;
use melior::ir::ValueLike;
use melior::ir::attribute::IntegerAttribute;
use melior::ir::r#type::IntegerType;
use melior::{
    Context,
    ir::{Location, Operation, OperationRef, Type, Value},
};
use mlir_sys::MlirValue;
use num_bigint::BigUint;
use std::rc::Rc;

use super::counter::Counter;
use super::extras::{block_list, operations_list};
use haloumi_core::{
    cmp::CmpOp,
    felt::Felt,
    slot::{Slot, arg::ArgNo, output::OutputId as FieldId},
};

#[derive(Debug)]
pub struct LlzkStructLowering<'c, 's> {
    state: &'s LlzkCodegenState<'c>,
    builder: OpBuilder<'c, 'c>,
    struct_op: StructDefOpRefMut<'c, 's>,
    constraints_counter: Rc<Counter>,
    callees_counter: CallTracker,
    io: StructIO,
}

impl<'c, 's> LlzkStructLowering<'c, 's> {
    pub fn new(
        state: &'s LlzkCodegenState<'c>,
        struct_op: StructDefOpRefMut<'c, 's>,
        io: StructIO,
    ) -> Result<Self, Error> {
        let builder = OpBuilder::at_block_end(
            state.context(),
            struct_op
                .constrain_func()
                .ok_or(Error::MissingConstrainFunc)?
                .region(0)?
                .first_block()
                .ok_or(Error::MissingBlock)?,
        );
        Ok(Self {
            state,
            struct_op,
            builder,
            constraints_counter: Rc::new(Default::default()),
            callees_counter: Default::default(),
            io,
        })
    }

    fn context(&self) -> &'c Context {
        self.state.context()
    }

    fn builder(&self) -> &OpBuilder<'c, 'c> {
        &self.builder
    }

    fn struct_name(&self) -> &str {
        self.struct_op.sym_name()
    }

    fn get_cell_member(&self, kind: MemberKind<'_>) -> Result<MemberDefOpRef<'c, '_>, Error> {
        let name = kind.member_name();
        Ok(self.struct_op.find_or_create_member_def(&name, || {
            log::debug!("Creating member named '@{name}'");
            kind.create_member_op(self.state, self.struct_name())
        })?)
    }

    /// Tries to fetch an advice cell field, if it doesn't exist creates a field that represents
    /// it.
    #[inline]
    fn get_adv_cell(&self, col: usize, row: usize) -> Result<MemberDefOpRef<'c, '_>, Error> {
        self.get_cell_member(MemberKind::Advice { col, row })
    }

    /// Tries to fetch a fixed cell field, if it doesn't exist creates a field that represents
    /// it.
    #[inline]
    fn get_fix_cell(&self, col: usize, row: usize) -> Result<MemberDefOpRef<'c, '_>, Error> {
        self.get_cell_member(MemberKind::Fixed { col, row })
    }

    fn get_output(&self, field: FieldId) -> Result<MemberDefOpRef<'c, '_>, Error> {
        self.struct_op
            .find_member_def(format!("out_{field}").as_str())
            .ok_or(Error::MissingOutput(field))
    }

    fn get_constrain_func(&self) -> Result<FuncDefOpRef<'c, '_>, Error> {
        self.struct_op
            .constrain_func()
            .ok_or(Error::MissingConstrainFunc)
    }

    /// Adds an operation at the end of the constrain function.
    fn append_op<O>(&self, op: O) -> Result<OperationRef<'c, '_>, Error>
    where
        O: Into<Operation<'c>>,
    {
        let block = self
            .get_constrain_func()?
            .region(0)?
            .first_block()
            .ok_or(Error::MissingBlock)?;
        let op_ref = block.insert_operation_before(
            block.terminator().ok_or(Error::MissingTerminator)?,
            op.into(),
        );
        log::debug!("Inserted operation {op_ref}");
        Ok(op_ref)
    }

    /// Adds an operation at the end of the constrain function and returns the first resulf of the
    /// operation.
    fn append_expr<O>(&self, op: O) -> Result<Value<'c, '_>, Error>
    where
        O: Into<Operation<'c>>,
    {
        Ok(self.append_op(op)?.result(0)?.into())
    }

    fn get_arg_impl(&self, idx: usize) -> Result<Value<'c, '_>, Error> {
        Ok(self.get_constrain_func()?.argument(idx)?.into())
    }

    /// Returns the (n+1)-th argument of the constrain function. The index is offset by one because
    /// in the constrain function the first argument is always an instance of the struct.
    fn get_arg(&self, arg_no: ArgNo) -> Result<Value<'c, '_>, Error> {
        self.get_arg_impl(*arg_no + 1)
    }

    fn get_component(&self) -> Result<Value<'c, '_>, Error> {
        self.get_arg_impl(0)
    }

    fn read_field(&self, field: MemberDefOpRef<'c, '_>) -> Result<Value<'c, '_>, Error> {
        self.append_expr(dialect::r#struct::readm(
            self.builder(),
            Location::unknown(self.context()),
            field.member_type(),
            self.get_component()?,
            field.member_name(),
        )?)
    }

    fn read_callee_output(
        &self,
        field: MemberDefOpRef<'c, '_>,
        callee: Value<'c, '_>,
    ) -> Result<Value<'c, '_>, Error> {
        self.append_expr(dialect::r#struct::readm(
            self.builder(),
            Location::unknown(self.context()),
            field.member_type(),
            callee,
            field.member_name(),
        )?)
    }

    fn lower_constant_impl(&self, f: &BigUint) -> Result<Value<'c, '_>, Error> {
        let const_attr =
            FeltConstAttribute::from_biguint(self.context(), f, self.state.field_name());
        self.append_expr(dialect::felt::constant(
            Location::unknown(self.context()),
            const_attr,
        )?)
    }

    /// Generate an assertion as a constraint to 0.
    ///
    /// The type of `expr` must be `i1`. That expression is then
    /// negated and converted into a felt. Then emit a constraint that
    /// that felt is equal to 0.
    fn create_assert_op(&self, expr: Value<'c, '_>) -> LoweringResult<Operation<'c>> {
        let location = Location::unknown(self.context());
        let i1 = Type::from(IntegerType::new(self.context(), 1));
        if expr.r#type() != i1 {
            bail_backend!(
                UnexpectedTypeError::new(i1, expr.r#type())
                    .with_context("Failed to assert expression")
            );
        }
        let not_expr =
            self.append_expr(dialect::bool::not(location, expr).map_err(Error::Llzk)?)?;
        let as_felt = self.append_expr(dialect::cast::tofelt(
            location,
            not_expr,
            Some(self.state.felt_type()),
        ))?;
        let zero = self.lower_constant_impl(&BigUint::ZERO)?;
        Ok(dialect::constrain::eq(location, as_felt, zero))
    }

    fn create_bin_op<E>(
        &self,
        op: impl Fn(Location<'c>, Value<'c, '_>, Value<'c, '_>) -> Result<Operation<'c>, E>,
        lhs: Value<'c, '_>,
        rhs: Value<'c, '_>,
    ) -> Result<Operation<'c>, Error>
    where
        Error: From<E>,
    {
        Ok(op(Location::unknown(self.context()), lhs, rhs)?)
    }

    fn create_un_op<E>(
        &self,
        op: impl Fn(Location<'c>, Value<'c, '_>) -> Result<Operation<'c>, E>,
        value: Value<'c, '_>,
    ) -> Result<Operation<'c>, Error>
    where
        Error: From<E>,
    {
        Ok(op(Location::unknown(self.context()), value)?)
    }
}

/// Value wrapper used as lowering output for circumventing lifetime restrictions.
#[derive(Copy, Clone, Debug)]
pub struct ValueWrap(MlirValue);

impl From<ValueWrap> for Value<'_, '_> {
    fn from(value: ValueWrap) -> Self {
        unsafe { Self::from_raw(value.0) }
    }
}

impl From<&ValueWrap> for Value<'_, '_> {
    fn from(value: &ValueWrap) -> Self {
        unsafe { Self::from_raw(value.0) }
    }
}

macro_rules! wrap {
    ($r:expr) => {
        Ok(($r).map(|v| ValueWrap(v.to_raw()))?)
    };
}

impl Lowering for LlzkStructLowering<'_, '_> {
    fn generate_constraint(
        &self,
        op: CmpOp,
        lhs: &Self::CellOutput,
        rhs: &Self::CellOutput,
    ) -> LoweringResult<()> {
        let loc = Location::new(
            self.context(),
            filename(self.struct_name(), Some("constraints")).as_str(),
            self.constraints_counter.next(),
            0,
        );
        let cond = match op {
            CmpOp::Eq => {
                self.append_op(dialect::constrain::eq(loc, lhs.into(), rhs.into()))?;
                return Ok(());
            }
            CmpOp::Lt => self.lower_lt(lhs, rhs),
            CmpOp::Le => self.lower_le(lhs, rhs),
            CmpOp::Gt => self.lower_gt(lhs, rhs),
            CmpOp::Ge => self.lower_ge(lhs, rhs),
            CmpOp::Ne => self.lower_ne(lhs, rhs),
        }?;
        self.generate_assert(&cond)
    }

    fn num_constraints(&self) -> usize {
        self.get_constrain_func()
            .map(|op| {
                op.regions()
                    .flat_map(block_list)
                    .flat_map(operations_list)
                    .filter(|o| {
                        o.name()
                            .as_string_ref()
                            .as_str()
                            .map(|op_name| matches!(op_name, "constrain.eq"))
                            .unwrap_or_default()
                    })
                    .count()
            })
            .unwrap_or_default()
    }

    fn generate_comment(&self, s: String) -> LoweringResult<()> {
        // If the final target is picus generate a 'picus.comment' op. Otherwise do nothing.
        log::warn!("Comment {s:?} was not generated");
        Ok(())
    }

    fn generate_call(
        &self,
        name: &str,
        inputs: &[Self::CellOutput],
        output_count: usize,
    ) -> LoweringResult<Vec<Slot>> {
        let id = self.callees_counter.next();
        let kind = MemberKind::Callee { name, id };
        let subcmp = self.read_field(self.get_cell_member(kind)?)?;
        let args = std::iter::once(subcmp)
            .chain(inputs.iter().map(|i| i.into()))
            .collect::<Vec<_>>();
        let ret: [Type; 0] = [];

        self.append_op(
            function::call(
                self.builder(),
                Location::unknown(self.context()),
                SymbolRefAttribute::new_from_str(self.context(), name, &[&FUNC_NAME_CONSTRAIN]),
                &args,
                &ret,
            )
            .map_err(Error::Llzk)?,
        )?;

        Ok(Slot::call_outputs(id, output_count))
    }

    fn generate_assume_deterministic(&self, _func_io: Slot) -> LoweringResult<()> {
        // If the final target is picus generate a 'picus.assume_deterministic' op. Otherwise do nothing.
        todo!(
            "There isn't yet a construct in LLZK that supports the 'assume_deterministic' statement"
        )
    }

    fn generate_assert(&self, expr: &Self::CellOutput) -> LoweringResult<()> {
        self.append_op(self.create_assert_op(expr.into())?)?;
        Ok(())
    }

    fn generate_post_condition(&self, _expr: &Self::CellOutput) -> LoweringResult<()> {
        todo!()
    }
}

impl ExprLowering for LlzkStructLowering<'_, '_> {
    type CellOutput = ValueWrap;

    fn lower_sum(
        &self,
        lhs: &Self::CellOutput,
        rhs: &Self::CellOutput,
    ) -> LoweringResult<Self::CellOutput> {
        wrap! {
            self.append_expr(self.create_bin_op(dialect::felt::add,
                lhs.into(),
                rhs.into(),
            )?)
        }
    }

    fn lower_product(
        &self,
        lhs: &Self::CellOutput,
        rhs: &Self::CellOutput,
    ) -> LoweringResult<Self::CellOutput> {
        wrap! {
            self.append_expr(self.create_bin_op(dialect::felt::mul,
                lhs.into(),
                rhs.into(),
            )?)
        }
    }

    fn lower_neg(&self, expr: &Self::CellOutput) -> LoweringResult<Self::CellOutput> {
        wrap! { self.append_expr(self.create_un_op(dialect::felt::neg, expr.into())?) }
    }

    fn lower_constant(&self, f: Felt) -> LoweringResult<Self::CellOutput> {
        wrap! {self.lower_constant_impl(&f)}
    }

    fn lower_eq(
        &self,
        lhs: &Self::CellOutput,
        rhs: &Self::CellOutput,
    ) -> LoweringResult<Self::CellOutput> {
        wrap!(self.append_expr(self.create_bin_op(dialect::bool::eq, lhs.into(), rhs.into())?))
    }

    fn lower_and(
        &self,
        lhs: &Self::CellOutput,
        rhs: &Self::CellOutput,
    ) -> LoweringResult<Self::CellOutput> {
        wrap!(self.append_expr(self.create_bin_op(dialect::bool::and, lhs.into(), rhs.into())?))
    }

    fn lower_or(
        &self,
        lhs: &Self::CellOutput,
        rhs: &Self::CellOutput,
    ) -> LoweringResult<Self::CellOutput> {
        wrap!(self.append_expr(self.create_bin_op(dialect::bool::or, lhs.into(), rhs.into())?))
    }

    fn lower_function_input(&self, i: usize) -> Slot {
        ArgNo::from(i).into()
    }

    fn lower_function_output(&self, o: usize) -> Slot {
        FieldId::from(o).into()
    }

    fn lower_funcio<IO>(&self, io: IO) -> LoweringResult<Self::CellOutput>
    where
        IO: Into<Slot>,
    {
        match io.into() {
            Slot::Arg(arg_no) => wrap!(self.get_arg(arg_no)),
            Slot::Output(field_id) => wrap!(self.read_field(self.get_output(field_id)?)),
            Slot::Advice(cell) => {
                wrap!(self.read_field(self.get_adv_cell(cell.col(), cell.row())?))
            }
            Slot::Fixed(cell) => {
                wrap!(self.read_field(self.get_fix_cell(cell.col(), cell.row())?))
            }
            Slot::TableLookup(_, _, _, _, _) => todo!(),
            Slot::CallOutput(callee, output_idx) => {
                let member = self.get_cell_member(self.io.callee(callee)?)?;
                let member_type =
                    StructType::try_from(member.member_type()).map_err(Error::Mlir)?;
                let parent = self.struct_op.parent_operation().ok_or_else(|| {
                    Error::Other("expected struct op to have a parent operation".to_owned())
                })?;
                let lookup = member_type
                    .lookup_definition(&parent)
                    .map_err(Error::Llzk)?;
                let member_impl: StructDefOpRef = lookup
                    .operation()
                    .ok_or_else(|| Error::MissingStruct(format!("{member_type}")))?
                    .try_into()
                    .map_err(Error::Llzk)?;

                let member_output = *member_impl
                    .member_defs()
                    .get(output_idx)
                    .ok_or(Error::MissingCalleeMemberOutput(callee, output_idx))?;
                let member_value = self.read_field(member)?;
                wrap!(self.read_callee_output(member_output, member_value))
            }
            Slot::Temp(_) => todo!(),
            Slot::Challenge(_, _, _) => todo!(),
        }
    }

    fn lower_lt(
        &self,
        lhs: &Self::CellOutput,
        rhs: &Self::CellOutput,
    ) -> LoweringResult<Self::CellOutput> {
        wrap!(self.append_expr(self.create_bin_op(dialect::bool::lt, lhs.into(), rhs.into())?))
    }

    fn lower_le(
        &self,
        lhs: &Self::CellOutput,
        rhs: &Self::CellOutput,
    ) -> LoweringResult<Self::CellOutput> {
        wrap!(self.append_expr(self.create_bin_op(dialect::bool::le, lhs.into(), rhs.into())?))
    }

    fn lower_gt(
        &self,
        lhs: &Self::CellOutput,
        rhs: &Self::CellOutput,
    ) -> LoweringResult<Self::CellOutput> {
        wrap!(self.append_expr(self.create_bin_op(dialect::bool::gt, lhs.into(), rhs.into())?))
    }

    fn lower_ge(
        &self,
        lhs: &Self::CellOutput,
        rhs: &Self::CellOutput,
    ) -> LoweringResult<Self::CellOutput> {
        wrap!(self.append_expr(self.create_bin_op(dialect::bool::ge, lhs.into(), rhs.into())?))
    }

    fn lower_ne(
        &self,
        lhs: &Self::CellOutput,
        rhs: &Self::CellOutput,
    ) -> LoweringResult<Self::CellOutput> {
        wrap!(self.append_expr(self.create_bin_op(dialect::bool::ne, lhs.into(), rhs.into())?))
    }

    fn lower_not(&self, value: &Self::CellOutput) -> LoweringResult<Self::CellOutput> {
        wrap!(self.append_expr(self.create_un_op(dialect::bool::not, value.into(),)?))
    }

    fn lower_true(&self) -> LoweringResult<Self::CellOutput> {
        wrap!(self.append_expr(arith::constant(
            self.context(),
            IntegerAttribute::new(IntegerType::new(self.context(), 1).into(), 1).into(),
            Location::unknown(self.context())
        )))
    }

    fn lower_false(&self) -> LoweringResult<Self::CellOutput> {
        wrap!(self.append_expr(arith::constant(
            self.context(),
            IntegerAttribute::new(IntegerType::new(self.context(), 1).into(), 0).into(),
            Location::unknown(self.context())
        )))
    }

    fn lower_det(&self, _expr: &Self::CellOutput) -> LoweringResult<Self::CellOutput> {
        unimplemented!("the determinism predicate is not supported by the LLZK backend")
    }

    fn lower_implies(
        &self,
        lhs: &Self::CellOutput,
        rhs: &Self::CellOutput,
    ) -> LoweringResult<Self::CellOutput> {
        let i1: Type = IntegerType::new(self.context(), 1).into();
        let lhs: Value = lhs.into();
        let rhs: Value = rhs.into();
        if lhs.r#type() != i1 {
            bail_backend!(
                UnexpectedTypeError::new(i1, lhs.r#type())
                    .with_context("Failed to lower lhs of implies expression")
            );
        }
        if rhs.r#type() != i1 {
            bail_backend!(
                UnexpectedTypeError::new(i1, rhs.r#type())
                    .with_context("Failed to lower rhs of implies expression")
            );
        }
        let lhs = self.append_expr(self.create_un_op(dialect::bool::not, lhs)?)?;
        wrap!(self.append_expr(self.create_bin_op(dialect::bool::or, lhs, rhs)?))
    }

    fn lower_iff(
        &self,
        lhs: &Self::CellOutput,
        rhs: &Self::CellOutput,
    ) -> LoweringResult<Self::CellOutput> {
        let i1: Type = IntegerType::new(self.context(), 1).into();
        let lhs: Value = lhs.into();
        let rhs: Value = rhs.into();
        if lhs.r#type() != i1 {
            bail_backend!(
                UnexpectedTypeError::new(i1, lhs.r#type())
                    .with_context("Failed to lower lhs of iff expression")
            );
        }
        if rhs.r#type() != i1 {
            bail_backend!(
                UnexpectedTypeError::new(i1, rhs.r#type())
                    .with_context("Failed to lower rhs of iff expression")
            );
        }

        wrap!(self.append_expr(arith::cmpi(
            self.context(),
            arith::CmpiPredicate::Eq,
            lhs,
            rhs,
            Location::unknown(self.context())
        )))
    }
}

#[cfg(test)]
mod tests {
    use haloumi_core::{
        query::{Advice, Instance},
        table::Column,
    };
    use log::LevelFilter;
    use simplelog::{Config, TestLogger};
    use std::fmt::Write as _;

    use crate::{LlzkCodegen, LlzkCodegenState, params::LlzkParams};
    use haloumi_backend::codegen::Codegen as _;
    use haloumi_synthesis::io::{AdviceIO, InstanceIO};

    use super::*;
    use ff::Field as _;

    use rstest::{fixture, rstest};

    #[fixture]
    fn fragment_main() -> FragmentCfg {
        FragmentCfg {
            struct_name: "Main",
            n_inputs: 2,
            n_public_inputs: 1,
            n_outputs: 2,
            n_public_outputs: 1,
            self_name: "self",
            advice_cells: vec![],
            fixed_cells: vec![],
            is_main: true,
        }
    }

    #[fixture]
    fn fragment_main_with_cells() -> FragmentCfg {
        FragmentCfg {
            struct_name: "Main",
            n_inputs: 2,
            n_public_inputs: 1,
            n_outputs: 2,
            n_public_outputs: 1,
            self_name: "self",
            advice_cells: vec![(1, 5)],
            fixed_cells: vec![(2, 3)],
            is_main: true,
        }
    }

    #[rstest]
    fn lower_reading_cells(fragment_main_with_cells: FragmentCfg) {
        fragment_test(
            fragment_main_with_cells,
            r"%0 = struct.readm %self[@adv_1_5] : <@Main<[]>>, !felt.type
              %1 = struct.readm %self[@fix_2_3] : <@Main<[]>>, !felt.type",
            |l| {
                l.lower_funcio(Slot::advice_abs(1, 5))?;
                l.lower_funcio(Slot::fixed_abs(2, 3))?;
                Ok(())
            },
        )
    }

    #[rstest]
    fn lower_sum(fragment_main: FragmentCfg) {
        fragment_test(fragment_main, r"%1 = felt.add %arg1, %arg1", |l| {
            let arg = l.lower_funcio(l.lower_function_input(0))?;
            l.lower_sum(&arg, &arg)?;
            Ok(())
        })
    }

    #[rstest]
    fn lower_sum_with_io(fragment_main: FragmentCfg) {
        fragment_test(
            fragment_main,
            r"%2 = struct.readm %self[@out_0] : <@Main<[]>>, !felt.type
              %3 = struct.readm %self[@out_1] : <@Main<[]>>, !felt.type
              %4 = felt.add %arg1, %2
              %5 = felt.add %arg2, %3",
            |l| {
                let arg0 = l.lower_funcio(l.lower_function_input(0))?;
                let arg1 = l.lower_funcio(l.lower_function_input(1))?;
                let out0 = l.lower_funcio(l.lower_function_output(0))?;
                let out1 = l.lower_funcio(l.lower_function_output(1))?;
                l.lower_sum(&arg0, &out0)?;
                l.lower_sum(&arg1, &out1)?;
                Ok(())
            },
        )
    }

    #[rstest]
    fn lower_product(fragment_main: FragmentCfg) {
        fragment_test(fragment_main, r"%1 = felt.mul %arg1, %arg1", |l| {
            let arg = l.lower_funcio(l.lower_function_input(0))?;
            l.lower_product(&arg, &arg)?;
            Ok(())
        })
    }

    #[rstest]
    fn lower_neg(fragment_main: FragmentCfg) {
        fragment_test(fragment_main, r"%1 = felt.neg %arg1", |l| {
            let arg = l.lower_funcio(l.lower_function_input(0))?;
            l.lower_neg(&arg)?;
            Ok(())
        })
    }

    #[rstest]
    fn lower_eq(fragment_main: FragmentCfg) {
        fragment_test(fragment_main, r"%1 = bool.cmp eq(%arg1, %arg1)", |l| {
            let arg = l.lower_funcio(l.lower_function_input(0))?;
            l.lower_eq(&arg, &arg)?;
            Ok(())
        })
    }

    #[rstest]
    fn lower_lt(fragment_main: FragmentCfg) {
        fragment_test(fragment_main, r"%1 = bool.cmp lt(%arg1, %arg1)", |l| {
            let arg = l.lower_funcio(l.lower_function_input(0))?;
            l.lower_lt(&arg, &arg)?;
            Ok(())
        })
    }

    #[rstest]
    fn lower_le(fragment_main: FragmentCfg) {
        fragment_test(fragment_main, r"%1 = bool.cmp le(%arg1, %arg1)", |l| {
            let arg = l.lower_funcio(l.lower_function_input(0))?;
            l.lower_le(&arg, &arg)?;
            Ok(())
        })
    }

    #[rstest]
    fn lower_gt(fragment_main: FragmentCfg) {
        fragment_test(fragment_main, r"%1 = bool.cmp gt(%arg1, %arg1)", |l| {
            let arg = l.lower_funcio(l.lower_function_input(0))?;
            l.lower_gt(&arg, &arg)?;
            Ok(())
        })
    }

    #[rstest]
    fn lower_ge(fragment_main: FragmentCfg) {
        fragment_test(fragment_main, r"%1 = bool.cmp ge(%arg1, %arg1)", |l| {
            let arg = l.lower_funcio(l.lower_function_input(0))?;
            l.lower_ge(&arg, &arg)?;
            Ok(())
        })
    }

    #[rstest]
    fn lower_ne(fragment_main: FragmentCfg) {
        fragment_test(fragment_main, r"%1 = bool.cmp ne(%arg1, %arg1)", |l| {
            let arg = l.lower_funcio(l.lower_function_input(0))?;
            l.lower_ne(&arg, &arg)?;
            Ok(())
        })
    }

    #[rstest]
    fn lower_and(fragment_main: FragmentCfg) {
        fragment_test(
            fragment_main,
            r"%true = arith.constant true
              %1 = bool.and %true, %true",
            |l| {
                let t = l.lower_true()?;
                l.lower_and(&t, &t)?;
                Ok(())
            },
        )
    }

    #[rstest]
    fn lower_or(fragment_main: FragmentCfg) {
        fragment_test(
            fragment_main,
            r"%true = arith.constant true
              %1 = bool.or %true, %true",
            |l| {
                let t = l.lower_true()?;
                l.lower_or(&t, &t)?;
                Ok(())
            },
        )
    }

    #[rstest]
    fn lower_implies(fragment_main: FragmentCfg) {
        fragment_test(
            fragment_main,
            r"%true = arith.constant true
              %0 = bool.not %true
              %1 = bool.or %0, %true",
            |l| {
                let t = l.lower_true()?;
                l.lower_implies(&t, &t)?;
                Ok(())
            },
        )
    }

    #[rstest]
    #[should_panic(expected = "Failed to lower lhs of implies expression")]
    fn lower_implies_wrong_lhs(fragment_main: FragmentCfg) {
        fragment_test(fragment_main, r"", |l| {
            let arg = l.lower_funcio(l.lower_function_input(0))?;
            let t = l.lower_true()?;
            l.lower_implies(&arg, &t)?;
            Ok(())
        })
    }

    #[rstest]
    #[should_panic(expected = "Failed to lower rhs of implies expression")]
    fn lower_implies_wrong_rhs(fragment_main: FragmentCfg) {
        fragment_test(fragment_main, r"", |l| {
            let arg = l.lower_funcio(l.lower_function_input(0))?;
            let t = l.lower_true()?;
            l.lower_implies(&t, &arg)?;
            Ok(())
        })
    }

    #[rstest]
    fn lower_iff(fragment_main: FragmentCfg) {
        fragment_test(
            fragment_main,
            r"%true = arith.constant true
              %0 = arith.cmpi eq, %true, %true : i1",
            |l| {
                let t = l.lower_true()?;
                l.lower_iff(&t, &t)?;
                Ok(())
            },
        )
    }

    #[rstest]
    #[should_panic(expected = "Failed to lower lhs of iff expression")]
    fn lower_iff_wrong_lhs(fragment_main: FragmentCfg) {
        fragment_test(fragment_main, r"", |l| {
            let arg = l.lower_funcio(l.lower_function_input(0))?;
            let t = l.lower_true()?;
            l.lower_iff(&arg, &t)?;
            Ok(())
        })
    }

    #[rstest]
    #[should_panic(expected = "Failed to lower rhs of iff expression")]
    fn lower_iff_wrong_rhs(fragment_main: FragmentCfg) {
        fragment_test(fragment_main, r"", |l| {
            let arg = l.lower_funcio(l.lower_function_input(0))?;
            let t = l.lower_true()?;
            l.lower_iff(&t, &arg)?;
            Ok(())
        })
    }

    #[rstest]
    fn lower_true(fragment_main: FragmentCfg) {
        fragment_test(fragment_main, "%true = arith.constant true", |l| {
            l.lower_true()?;
            Ok(())
        })
    }

    #[rstest]
    fn lower_false(fragment_main: FragmentCfg) {
        fragment_test(fragment_main, "%false = arith.constant false", |l| {
            l.lower_false()?;
            Ok(())
        })
    }

    #[rstest]
    fn lower_not(fragment_main: FragmentCfg) {
        fragment_test(
            fragment_main,
            "%true = arith.constant true\n%0 = bool.not %true",
            |l| {
                let t = l.lower_true()?;
                l.lower_not(&t)?;
                Ok(())
            },
        )
    }

    #[rstest]
    #[should_panic(expected = "the determinism predicate is not supported by the LLZK backend")]
    fn lower_det(fragment_main: FragmentCfg) {
        fragment_test(fragment_main, "", |l| {
            let t = l.lower_true()?;
            l.lower_det(&t)?;
            Ok(())
        })
    }

    #[rstest]
    fn lower_constant(fragment_main: FragmentCfg) {
        fragment_test(fragment_main, "%felt_const_1 = felt.const 1", |l| {
            l.lower_constant(Felt::new(halo2curves::bn256::Fq::ONE))?;
            Ok(())
        })
    }

    /// Empty test to make sure the basic structure works as intended.
    #[rstest]
    fn empty_fragment(fragment_main: FragmentCfg) {
        fragment_test(fragment_main, "", |_| Ok(()))
    }

    /// Test infrastructure for testing the lowering module inside the correct context.
    ///
    /// Creates a codegen module and instantiates the lowering component inside a struct.
    /// The test is defined inside the closure, making calls to [`LlzkStructLowering`].
    /// The structs is then lowered whole into MLIR IR.
    ///
    /// The expected behavior is defined in textual MLIR IR as the fragment. This fragment is
    /// injected into a textual representation of the final module and compared against the emitted
    /// module. To avoid whitespacing issues or other formatting issues the textual IR is parsed
    /// into a [`melior::ir::Module`] and then reprinted to standardize the syntax.
    fn fragment_test(
        cfg: FragmentCfg,
        frag: &str,
        test: impl FnOnce(&LlzkStructLowering) -> haloumi_lowering::Result<()>,
    ) {
        let _ = TestLogger::init(LevelFilter::Debug, Config::default());
        let context = LlzkContext::new();
        let state: LlzkCodegenState = LlzkParams::new(&context)
            .with_top_level(cfg.struct_name)
            .no_optimize()
            .into();
        let codegen = LlzkCodegen::initialize(&state);
        let advice_io = cfg.advice_io();
        let instance_io = cfg.instance_io();
        let s = if cfg.is_main {
            codegen.define_main_function(&advice_io, &instance_io, [])
        } else {
            assert_eq!(cfg.n_public_inputs, 0);
            assert_eq!(cfg.n_public_outputs, 0);
            codegen.define_function(cfg.struct_name, cfg.n_inputs, cfg.n_outputs, [])
        }
        .unwrap();
        test(&s).unwrap();
        codegen.on_scope_end(s).unwrap();

        let out = codegen.generate_output().unwrap();
        verify_operation_with_diags(&out.module().as_operation()).unwrap();

        let fragment = expected_fragment(&cfg, frag);
        mlir_testutils::assert_module_eq(out.module(), &fragment);
    }

    struct FragmentCfg {
        struct_name: &'static str,
        n_inputs: usize,
        n_public_inputs: usize,
        n_outputs: usize,
        n_public_outputs: usize,
        self_name: &'static str,
        advice_cells: Vec<(usize, usize)>,
        fixed_cells: Vec<(usize, usize)>,
        is_main: bool,
    }

    impl FragmentCfg {
        fn advice_io(&self) -> AdviceIO {
            let inputs = Vec::from_iter(self.n_public_inputs..self.n_inputs);
            let outputs = Vec::from_iter(self.n_public_outputs..self.n_outputs);
            AdviceIO::new(
                &[(Column::new(0, Advice), &inputs)],
                &[(Column::new(1, Advice), &outputs)],
            )
            .unwrap()
        }

        fn instance_io(&self) -> InstanceIO {
            let inputs = Vec::from_iter(0..self.n_public_inputs);
            let outputs = Vec::from_iter(0..self.n_public_outputs);
            InstanceIO::new(
                &[(Column::new(0, Instance), &inputs)],
                &[(Column::new(1, Instance), &outputs)],
            )
            .unwrap()
        }

        fn inputs(&self) -> String {
            (1..=self.n_inputs).fold(String::new(), |mut acc, n| {
                write!(
                    acc,
                    "{} %arg{n}: {}{}",
                    if n == 1 { "" } else { "," },
                    self.input_type_str(),
                    if n <= self.n_public_inputs {
                        " {llzk.pub = #llzk.pub}"
                    } else {
                        ""
                    }
                )
                .unwrap();
                acc
            })
        }

        fn input_type_str(&self) -> &'static str {
            "!felt.type"
        }

        fn cells(&self) -> String {
            self.advice_cells
                .iter()
                .map(|(col, row)| format!("struct.member @adv_{col}_{row} : !felt.type\n"))
                .chain(
                    self.fixed_cells
                        .iter()
                        .map(|(col, row)| format!("struct.member @fix_{col}_{row} : !felt.type\n")),
                )
                .collect()
        }

        fn fields(&self) -> String {
            (0..self.n_outputs).fold(String::new(), |mut acc, n| {
                writeln!(
                    acc,
                    "struct.member @out_{n} : !felt.type{}",
                    if n < self.n_public_outputs {
                        " {llzk.pub}"
                    } else {
                        ""
                    }
                )
                .unwrap();
                acc
            })
        }
    }

    fn expected_fragment(cfg: &FragmentCfg, frag: &str) -> String {
        format!(
            r#"module attributes {{llzk.lang = "halo2", llzk.main = !struct.type<@{name}<[]>>}} {{
  struct.def @{name} {{
    {fields}
    function.def @compute({inputs}) -> !struct.type<@{name}<[]>> attributes {{function.allow_non_native_field_ops, function.allow_witness}} {{
      %{self_name} = struct.new : <@{name}<[]>>
      function.return %{self_name} : !struct.type<@{name}<[]>>
    }}
    function.def @constrain(%{self_name}: !struct.type<@{name}<[]>>, {inputs}) attributes {{function.allow_constraint, function.allow_non_native_field_ops}} {{
      {frag}
      function.return
    }}
    {cells}
  }}
}}"#,
            name = cfg.struct_name,
            inputs = cfg.inputs(),
            fields = cfg.fields(),
            self_name = cfg.self_name,
            cells = cfg.cells()
        )
    }
}
