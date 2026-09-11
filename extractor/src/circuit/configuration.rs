//! Traits related to circuit configuration.

use ff::{Field, PrimeField};
use haloumi_core::{
    auto_conf::AutoConfigure,
    info_traits::ConstraintSystemInfo,
    query::{Advice, Fixed, Instance},
    table::{Column, ColumnType},
};
use haloumi_integration::{
    Types,
    circuit::{
        AbstractCircuitIO, ExtraibleChip,
        io::ctx::{Cell, InputDescr, OutputDescr},
    },
};

/// Configuration for a chip type that implements [`AbstractCircuitIO`].
#[derive(Debug, Clone)]
pub struct ChipConfig<C: AbstractCircuitIO> {
    pub cfg: C::ConfigCols,
    pub inner: C::Config,
}

impl<C: AbstractCircuitIO> ChipConfig<C> {
    fn configure<CS, L, F>(meta: &mut CS) -> Self
    where
        C::Chip: ExtraibleChip<L, Config = C::Config, ConfigCols = C::ConfigCols, CS = CS>,
        F: PrimeField,
        CS: ConstraintSystemInfo<F>,
        C::ConfigCols: AutoConfigure<CS>,
    {
        let cfg = C::ConfigCols::configure(meta);
        let inner = C::Chip::configure_circuit(meta, &cfg);
        Self { cfg, inner }
    }
}

/// Configuration for a IO instance column.
///
/// Each IO instance column has an associated advice column that can be used for writting
/// intermediate values if required by the circuit.
#[derive(Clone, Copy, Debug)]
pub struct IOColumn {
    pub instance: Column<Instance>,
    pub helper: Column<Advice>,
}

impl IOColumn {
    fn configure<F: Field, CS: ConstraintSystemInfo<F>>(meta: &mut CS) -> Self
    where
        CS::InstanceCol: Into<Column<Instance>>,
        CS::AdviceCol: Into<Column<Advice>>,
    {
        let instance = meta.instance_col();
        let helper = meta.advice_col();

        meta.enable_equality(helper);
        meta.enable_equality(instance);
        Self {
            instance: instance.into(),
            helper: helper.into(),
        }
    }

    fn to_cell<C: ColumnType>(self, row: usize) -> Cell<Column<C>>
    where
        Column<C>: From<Column<Instance>>,
    {
        (self.instance.into(), row).into()
    }

    fn descrs<C: ColumnType, D>(
        &self,
        ctor: impl Fn(Cell<Column<C>>, Column<Advice>) -> D,
    ) -> impl Iterator<Item = D>
    where
        Column<C>: From<Column<Instance>>,
    {
        (0..).map(move |row| ctor(self.to_cell(row), self.helper))
    }
}

/// Configuration for the circuit IO used by the circuit scaffold.
#[derive(Clone, Copy, Debug)]
pub struct IOConfig {
    pub input: IOColumn,
    pub output: IOColumn,
}

impl IOConfig {
    fn configure<F: Field, CS: ConstraintSystemInfo<F>>(meta: &mut CS) -> Self
    where
        CS::InstanceCol: Into<Column<Instance>>,
        CS::AdviceCol: Into<Column<Advice>>,
    {
        Self {
            input: IOColumn::configure(meta),
            output: IOColumn::configure(meta),
        }
    }

    fn inputs<F, E>(&self) -> impl Iterator<Item = InputDescr<F, E>>
    where
        F: PrimeField,
        E: Types<F>,
        E::AdviceCol: From<Column<Advice>>,
        E::InstanceCol: From<Cell<Column<Instance>>>,
    {
        self.input
            .descrs(|cell, col| InputDescr::new(cell.into(), col.into()))
    }

    fn outputs<F: PrimeField, E: Types<F>>(&self) -> impl Iterator<Item = OutputDescr<F, E>> {
        self.output.descrs(OutputDescr::new)
    }
}

/// Helper struct that defines a fixed column designed for constants if the constraint system has
/// not defined one already.
#[derive(Clone, Copy, Debug)]
pub struct Constants {
    _helper: Option<Column<Fixed>>,
}

impl Constants {
    fn configure<F: Field, CS: ConstraintSystemInfo<F>>(meta: &mut CS) -> Self
    where
        CS::FixedCol: Into<Column<Fixed>>,
    {
        let helper = if meta.constants().is_empty() {
            let fixed_helper = meta.fixed_col();
            meta.enable_constant(fixed_helper);
            Some(fixed_helper)
        } else {
            None
        };
        Self {
            _helper: helper.map(Into::into),
        }
    }
}

/// Configuration for a circuit.
#[derive(Clone)]
pub struct Config<C: AbstractCircuitIO> {
    pub io: IOConfig,
    pub chip: ChipConfig<C>,
    pub constants: Constants,
}

impl<C: AbstractCircuitIO> Config<C> {
    pub fn configure<L, F: Field, CS: ConstraintSystemInfo<F>>(meta: &mut CS) -> Self
    where
        F: PrimeField,
        C::Chip: ExtraibleChip<L, Config = C::Config, ConfigCols = C::ConfigCols, CS = CS>,
        C::ConfigCols: AutoConfigure<CS>,
        CS::InstanceCol: Into<Column<Instance>>,
        CS::AdviceCol: Into<Column<Advice>>,
        CS::FixedCol: Into<Column<Fixed>>,
    {
        log::info!(
            "Circuit has {} inputs and {} outputs",
            C::Input::SIZE,
            C::Output::SIZE
        );
        Self {
            io: IOConfig::configure(meta),
            chip: ChipConfig::configure::<CS, L, F>(meta),
            constants: Constants::configure(meta),
        }
    }
}
