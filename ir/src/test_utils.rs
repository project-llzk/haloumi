use haloumi_core::{felt::Felt, slot::Slot};
use haloumi_lowering::ExprLowering;

use ff::PrimeField;

/// Implementation of BabyBear used for testing.
#[derive(PrimeField)]
#[PrimeFieldModulus = "2013265921"]
#[PrimeFieldGenerator = "31"]
#[PrimeFieldReprEndianness = "little"]
pub struct BabyBear([u64; 1]);

pub const BABYBEAR: u64 = 2013265921;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MockCellOutput {
    Const(usize, Felt),
    Slot(usize, Slot),
    Neg(usize, usize),
    Sum(usize, usize, usize),
    Product(usize, usize, usize),
}

impl MockCellOutput {
    pub fn id(&self) -> usize {
        match self {
            MockCellOutput::Const(id, _)
            | MockCellOutput::Slot(id, _)
            | MockCellOutput::Neg(id, _)
            | MockCellOutput::Sum(id, _, _)
            | MockCellOutput::Product(id, _, _) => *id,
        }
    }
}

pub type MockLoweringResult = Result<MockCellOutput, haloumi_lowering::error::Error>;

mockall::mock! {
    pub TestExprLowering {}

    impl ExprLowering for TestExprLowering {
        type CellOutput = MockCellOutput;


fn lower_sum(&self, lhs: &MockCellOutput, rhs: &MockCellOutput)
-> MockLoweringResult;

fn lower_product(
    &self,
    lhs: &MockCellOutput,
    rhs: &MockCellOutput,
) -> MockLoweringResult;

fn lower_neg(&self, expr: &MockCellOutput) -> MockLoweringResult;

fn lower_constant(&self, f: Felt) ->MockLoweringResult;

fn lower_eq(&self, lhs: &MockCellOutput, rhs: &MockCellOutput) -> MockLoweringResult;

fn lower_lt(&self, lhs: &MockCellOutput, rhs: &MockCellOutput) -> MockLoweringResult;

fn lower_le(&self, lhs: &MockCellOutput, rhs: &MockCellOutput) -> MockLoweringResult;

fn lower_gt(&self, lhs: &MockCellOutput, rhs: &MockCellOutput) -> MockLoweringResult;

fn lower_ge(&self, lhs: &MockCellOutput, rhs: &MockCellOutput) -> MockLoweringResult;

fn lower_ne(&self, lhs: &MockCellOutput, rhs: &MockCellOutput) -> MockLoweringResult;

fn lower_and(&self, lhs: &MockCellOutput, rhs: &MockCellOutput)
-> MockLoweringResult;

fn lower_or(&self, lhs: &MockCellOutput, rhs: &MockCellOutput) -> MockLoweringResult;

fn lower_not(&self, value: &MockCellOutput) -> MockLoweringResult;

fn lower_true(&self) -> MockLoweringResult;

fn lower_false(&self) -> MockLoweringResult;

fn lower_det(&self, expr: &MockCellOutput) -> MockLoweringResult;

fn lower_implies(
    &self,
    lhs: &MockCellOutput,
    rhs: &MockCellOutput,
) -> MockLoweringResult;

fn lower_iff(&self, lhs: &MockCellOutput, rhs: &MockCellOutput)
-> MockLoweringResult;

fn lower_function_input(&self, i: usize) -> Slot;

fn lower_function_output(&self, o: usize) -> Slot;



fn lower_funcio<IO>(&self, io: IO) -> MockLoweringResult
where
    IO: Into<Slot> + 'static;
    }
}
