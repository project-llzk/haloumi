//! Types related to sets of selectors.

use bit_set::BitSet;

/// Set of selectors.
///
/// What the selectors in the set represent depends on the context. For example, the set of
/// selectors obtained from the polynomials of a gate represent what selectors enable it.
pub type SelectorSet = BitSet;
