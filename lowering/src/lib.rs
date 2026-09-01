#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

use haloumi_core::{cmp::CmpOp, felt::Felt, slot::Slot};

pub mod error;
pub mod lowerable;

/// Result type for lowering related operations.
pub type Result<T> = std::result::Result<T, error::Error>;

/// Defines the interface code generators expose for generating code in their corresponding IR.
pub trait Lowering: ExprLowering {
    /// Generates a constraint.
    fn generate_constraint<'l: 'o, 'o>(
        &'l self,
        op: CmpOp,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<()>;

    /// Returns the number of generated constraints.
    fn num_constraints(&self) -> usize;

    /// Attempts to generate a constraint and fails if it couldn't be generated.
    fn checked_generate_constraint<'l: 'o, 'o>(
        &'l self,
        op: CmpOp,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<()> {
        let before = self.num_constraints();
        self.generate_constraint(op, lhs, rhs)?;
        let after = self.num_constraints();
        if before >= after {
            return Err(error::Error::LastConstraintNotGenerated);
        }
        Ok(())
    }

    /// Generates IR representing a comment with the given text.
    fn generate_comment(&self, s: String) -> Result<()>;

    /// Generates an statement that hints that the given [`Slot`] must be assumed to be
    /// deterministic.
    fn generate_assume_deterministic(&self, slot: Slot) -> Result<()>;

    /// Generates a call to another group.
    ///
    /// Returns a list of slots referencing the output result of calling the group.
    fn generate_call<'l: 'o, 'o>(
        &'l self,
        name: &str,
        selectors: &[Self::CellOutput<'o>],
        output_count: usize,
    ) -> Result<Vec<Slot>>;

    /// Generates an assertion using the given expression.
    ///
    /// How exactly this assertion is represented is backend dependant.
    fn generate_assert<'l: 'o, 'o>(&'l self, expr: &Self::CellOutput<'o>) -> Result<()>;

    /// Generates an assertion using the given expression that is treated as a post-condition.
    ///
    /// How exactly this assertion is represented is backend dependant.
    fn generate_post_condition<'l: 'o, 'o>(&'l self, expr: &Self::CellOutput<'o>) -> Result<()>;
}

/// Defines the interface code generators expose for generating expressions in their corresponding IR.
pub trait ExprLowering {
    /// The type representing a generated expression.
    type CellOutput<'o>
    where
        Self: 'o;

    /// Emits an expression representing addition.
    fn lower_sum<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>>;

    /// Emits an expression representing multiplication.
    fn lower_product<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>>;

    /// Emits an expression representing negation.
    fn lower_neg<'l: 'o, 'o>(&'l self, expr: &Self::CellOutput<'o>)
    -> Result<Self::CellOutput<'o>>;

    /// Emits a constant value.
    fn lower_constant<'l: 'o, 'o>(&'l self, f: Felt) -> Result<Self::CellOutput<'o>>;

    /// Emits a boolean expression representing equality between the operands.
    fn lower_eq<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>>;

    /// Emits a boolean expression representing a less-than relation between the operands.
    fn lower_lt<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>>;

    /// Emits a boolean expression representing a less-than or equal relation between the operands.
    fn lower_le<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>>;

    /// Emits a boolean expression representing a greater-than relation between the operands.
    fn lower_gt<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>>;

    /// Emits a boolean expression representing a greater-than or equal relation between the operands.
    fn lower_ge<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>>;

    /// Emits a boolean expression representing the negation of equality between the operands.
    fn lower_ne<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>>;

    /// Emits a logical AND between the two operands.
    fn lower_and<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>>;

    /// Emits a logical OR between the two operands.
    fn lower_or<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>>;

    /// Emits a logical NOT between the two operands.
    fn lower_not<'l: 'o, 'o>(
        &'l self,
        value: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>>;

    /// Emits a literal `true` value.
    fn lower_true<'l: 'o, 'o>(&'l self) -> Result<Self::CellOutput<'o>>;

    /// Emits a literal `false` value.
    fn lower_false<'l: 'o, 'o>(&'l self) -> Result<Self::CellOutput<'o>>;

    /// Emits an expression that hints that the given expression must be proven deterministic.
    ///
    /// The concrete semantics of this expression are backend dependant but it must return an
    /// expression of boolean type.
    fn lower_det<'l: 'o, 'o>(&'l self, expr: &Self::CellOutput<'o>)
    -> Result<Self::CellOutput<'o>>;

    /// Emits a logical implication between the two operands.
    fn lower_implies<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>>;

    /// Emits a logical double-implication between the two operands.
    fn lower_iff<'l: 'o, 'o>(
        &'l self,
        lhs: &Self::CellOutput<'o>,
        rhs: &Self::CellOutput<'o>,
    ) -> Result<Self::CellOutput<'o>>;

    /// Returns a [`Slot`] representing the `i`-th input.
    fn lower_function_input(&self, i: usize) -> Slot;

    /// Returns a [`Slot`] representing the `o`-th output.
    fn lower_function_output(&self, o: usize) -> Slot;

    /// Returns a list of [`Slot`] representing the input indices in the iterator.
    fn lower_function_inputs(&self, ins: impl IntoIterator<Item = usize>) -> Vec<Slot> {
        ins.into_iter()
            .map(|i| self.lower_function_input(i))
            .collect()
    }

    /// Returns a list of [`Slot`] representing the output indices in the iterator.
    fn lower_function_outputs(&self, outs: impl IntoIterator<Item = usize>) -> Vec<Slot> {
        outs.into_iter()
            .map(|o| self.lower_function_output(o))
            .collect()
    }

    /// Emits an expression representing the given IO.
    fn lower_funcio<'l: 'o, 'o, IO>(&'l self, io: IO) -> Result<Self::CellOutput<'o>>
    where
        IO: Into<Slot>;
}
