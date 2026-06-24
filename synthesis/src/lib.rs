#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

use std::sync::Arc;

use ff::{Field, PrimeField};
use haloumi_core::info_traits::ConstraintSystemInfo;

use crate::{
    eq_constraint::EqConstraintGraph,
    error::Error,
    gates::Gate,
    groups::Groups,
    io::{AdviceIO, InstanceIO},
    lookups::Lookup,
    regions::{FixedData, TableData},
    synthesizer::Synthesizer,
};

pub mod eq_constraint;
pub mod error;
pub mod gates;
pub mod groups;
pub mod io;
pub mod lookups;
pub mod regions;
pub mod selector;
pub mod synthesizer;
mod utils;

/// Entry point of the synthesis step in the lowering pipeline.
#[derive(Debug, Default)]
pub struct SynthesisUser {
    id_count: usize,
}

impl SynthesisUser {
    /// Creates a new synthesis user.
    pub fn new() -> Self {
        Self { id_count: 0 }
    }

    /// Synthesizes a circuit .
    pub fn synthesize<F, C>(
        &mut self,
        circuit: &C,
    ) -> Result<SynthesizedCircuit<F, <C::CS as ConstraintSystemInfo<F>>::Polynomial>, Error>
    where
        C: CircuitSynthesis<F>,
        F: PrimeField,
    {
        let mut cs = C::CS::default();
        let mut syn = Synthesizer::new(self.next_id());
        let config = C::configure(&mut cs);

        log::debug!("Validating io hints");
        let advice_io: AdviceIO = C::advice_io(&config)?;
        let instance_io: InstanceIO = C::instance_io(&config)?;

        syn.configure_io(advice_io, instance_io);
        log::debug!("Starting synthesis");
        C::synthesize(circuit.circuit(), config, &mut syn, &cs)
            .map_err(|e| Error::Synthesis(Arc::new(e)))?;
        cs.synthesis_completed();
        let synthesized = syn.build(cs)?;
        log::debug!("Synthesis completed successfuly");
        Ok(synthesized)
    }

    fn next_id(&mut self) -> usize {
        let id = self.id_count;
        self.id_count += 1;
        id
    }
}

/// Implementations of this trait define how a circuit is synthesized.
///
/// Serves as a bridge to the Halo2 circuit synthesis process that allows disconnecting the types
/// defined in this crate with the types defined by Halo2. Since many Halo2 based projects fork the
/// library this trait allows for swapping the concrete implementation of Halo2 without having to
/// change the codebase of this crate.
pub trait CircuitSynthesis<F: Field> {
    /// The type of the circuit.
    type Circuit;
    /// Should be the same type as the circuit config.
    type Config;
    /// Type of the constraint system.
    type CS: ConstraintSystemInfo<F> + Default + 'static;
    /// Error type for synthesis.
    type Error: std::error::Error + Sync + Send + 'static;

    /// Returns a reference to the circuit.
    fn circuit(&self) -> &Self::Circuit;

    /// Creates the configuration of the circuit.
    fn configure(cs: &mut Self::CS) -> Self::Config;

    /// Returns the advice cells that are part of the inputs and outputs of the circuit.
    fn advice_io(config: &Self::Config) -> Result<AdviceIO, Error>;

    /// Returns the instance cells that are part of the inputs and outputs of the circuit.
    fn instance_io(config: &Self::Config) -> Result<InstanceIO, Error>;

    /// This callback requests the client to fill out the [`Synthesizer`] with the synthesis
    /// information about the circuit.
    fn synthesize(
        circuit: &Self::Circuit,
        config: Self::Config,
        synthesizer: &mut Synthesizer<F>,
        cs: &Self::CS,
    ) -> Result<(), Self::Error>;
}

/// Result of synthesizing a circuit.
#[derive(Debug)]
pub struct SynthesizedCircuit<F, E>
where
    F: Field,
{
    id: usize,
    lookups: Vec<Lookup<E>>,
    gates: Vec<Gate<E>>,
    eq_constraints: EqConstraintGraph<F>,
    fixed: FixedData<F>,
    tables: Vec<TableData<F>>,
    groups: Groups,
}

impl<F, E> SynthesizedCircuit<F, E>
where
    F: Field,
{
    /// Returns the list of gates in the constraint system.
    pub fn gates(&self) -> &[Gate<E>] {
        &self.gates
    }

    /// Returns the lookups declared during synthesis.
    pub fn lookups(&self) -> &[Lookup<E>] {
        &self.lookups
    }

    /// Returns the list of tables in the circuit.
    pub fn tables(&self) -> &[TableData<F>] {
        &self.tables
    }

    ///// Finds the table that corresponds to the query set.
    //fn find_table(&self, q: &[E::FixedQuery]) -> Result<Vec<Vec<F>>>
    //where
    //    E: ExpressionTypes,
    //{
    //    self.tables
    //        .iter()
    //        .find_map(|table| table.get_rows(q))
    //        .ok_or_else(|| anyhow!("Could not get values from table"))
    //        .and_then(identity)
    //}

    ///// Returns the list of tables the lookup refers to.
    //pub(crate) fn tables_for_lookup(&self, l: &Lookup<E>) -> Result<Vec<LookupTableRow<F>>>
    //where
    //    E: ExpressionInfo,
    //{
    //    fn transpose<T>(v: Vec<Vec<T>>) -> Vec<Vec<T>> {
    //        assert!(!v.is_empty());
    //        let len = v[0].len();
    //        let mut iters: Vec<_> = v.into_iter().map(|n| n.into_iter()).collect();
    //        (0..len)
    //            .map(|_| {
    //                iters
    //                    .iter_mut()
    //                    .map(|n| n.next().unwrap())
    //                    .collect::<Vec<T>>()
    //            })
    //            .collect()
    //    }
    //
    //    l.table_queries().and_then(|q| {
    //        // For each table region look if they have the columns we are looking for and
    //        // collect all the fixed values
    //        let columns = q.iter().map(|q| q.column_index()).collect::<Vec<_>>();
    //        let table = self.find_table(&q)?;
    //        if q.len() != table.len() {
    //            anyhow::bail!(
    //                "Inconsistency check failed: Lookup has {} columns but table yielded {}",
    //                q.len(),
    //                table.len()
    //            )
    //        }
    //
    //        // The table needs to be transposed from [row,col] to [col,row].
    //        Ok(transpose(table)
    //            .into_iter()
    //            .map(|row| LookupTableRow::new(&columns, row))
    //            .collect())
    //    })
    //}

    /// Returns the groups in the circuit.
    pub fn groups(&self) -> &Groups {
        &self.groups
    }

    /// Returns the equality constraints.
    pub fn constraints(&self) -> &EqConstraintGraph<F> {
        &self.eq_constraints
    }

    /// Returns a reference to the fixed values data.
    pub fn fixed_data(&self) -> &FixedData<F> {
        &self.fixed
    }

    /// Returns the identifier of the circuit.
    pub fn id(&self) -> usize {
        self.id
    }
}
