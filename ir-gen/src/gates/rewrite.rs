//! Types and traits for defining custom IR generation for PLONK gates.

use std::{borrow::Cow, sync::Arc};

use ff::Field;
use haloumi_ir::stmt::IRStmt;

use crate::gates::GateScope;

/// Indicates if the pattern matched the gate or not.
#[derive(Debug)]
pub enum Match {
    /// The pattern matched.
    Match,
    /// The pattern didn't match.
    NoMatch,
}

/// Error type for rewrites.
#[derive(Debug, Clone)]
pub struct RewriteError(Arc<dyn std::error::Error + Send + Sync + 'static>);

impl<E: std::error::Error + Send + Sync + 'static> From<E> for RewriteError {
    fn from(value: E) -> Self {
        RewriteError(Arc::new(value))
    }
}

impl std::fmt::Display for RewriteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.0.as_ref(), f)
    }
}

/// The type used for rewriting the gates. Each expression has an associated row that is used as
/// the base offset on the queries.
pub type RewriteOutput<'syn, E> = IRStmt<(usize, Cow<'syn, E>)>;

/// Result type for [`GateRewritePattern::match_gate`].
pub type MatchResult = Result<Match, RewriteError>;

/// Result type for  [`GateRewritePattern::rewrite_gate`].
pub type RewriteResult<'syn, E> = Result<RewriteOutput<'syn, E>, RewriteError>;

/// Result type for [`GateRewritePattern::match_and_rewrite`].
pub type MatchAndRewriteResult<'syn, E> = Result<Option<RewriteOutput<'syn, E>>, RewriteError>;

/// Implementations of this trait can selectively rewrite a gate when lowering the circuit.
///
/// The rewrites performed by these patterns should be semantics preserving.
pub trait GateRewritePattern<F, E> {
    /// Checks if the gate matches the pattern.
    ///
    /// Returns Ok(()) if the pattern matched.
    #[allow(unused_variables)]
    fn match_gate(&self, gate: GateScope<F, E>) -> MatchResult
    where
        F: Field,
    {
        panic!("Implement match_gate and rewrite_gate OR match_and_rewrite")
    }

    /// Performs the rewriting of the gate.
    #[allow(unused_variables)]
    fn rewrite_gate<'syn>(&self, gate: GateScope<'syn, '_, F, E>) -> RewriteResult<'syn, E>
    where
        F: Field,
        E: Clone,
    {
        panic!("Implement match_gate and rewrite_gate OR match_and_rewrite")
    }

    /// Checks if the gate matches the pattern and then performs the rewriting.
    fn match_and_rewrite<'syn>(
        &self,
        gate: GateScope<'syn, '_, F, E>,
    ) -> MatchAndRewriteResult<'syn, E>
    where
        F: Field,
        E: Clone,
    {
        matches!(self.match_gate(gate)?, Match::Match)
            .then(|| self.rewrite_gate(gate))
            .transpose()
    }
}

/// A set of rewrite patterns.
pub(crate) struct RewritePatternSet<F, E>(Vec<Box<dyn GateRewritePattern<F, E>>>);

impl<F, E> RewritePatternSet<F, E> {
    /// Adds a pattern to the set.
    pub fn add(&mut self, p: impl GateRewritePattern<F, E> + 'static) {
        self.0.push(Box::new(p))
    }
}

impl<F, E> Default for RewritePatternSet<F, E> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<F, E> Extend<Box<dyn GateRewritePattern<F, E>>> for RewritePatternSet<F, E> {
    fn extend<T: IntoIterator<Item = Box<dyn GateRewritePattern<F, E>>>>(&mut self, iter: T) {
        self.0.extend(iter)
    }
}

impl<F, E> GateRewritePattern<F, E> for RewritePatternSet<F, E> {
    fn match_and_rewrite<'syn>(
        &self,
        gate: GateScope<'syn, '_, F, E>,
    ) -> MatchAndRewriteResult<'syn, E>
    where
        F: Field,
        E: Clone,
    {
        log::debug!(
            "Starting match for gate '{}' on region '{}'",
            gate.gate_name(),
            gate.region_name()
        );

        for pattern in self.0.iter() {
            log::debug!("Starting pattern");
            match pattern.match_and_rewrite(gate)? {
                Some(r) => {
                    log::debug!("Returning a value from the pattern");
                    return Ok(Some(r));
                }
                None => {
                    log::debug!("Pattern did not match");
                }
            }
        }

        Ok(None)
    }
}
