use crate::pcl::vars::Temp;
pub use crate::pcl::vars::{VarKind, VarStr};

use haloumi_core::slot::Slot;

/// Inner value of [`VarKeySeed`].
#[derive(Clone, Hash, Eq, PartialEq, Debug)]
pub enum VarKeySeedInner {
    Slot(Slot),
    Temp,
    Lifted(usize),
}

impl VarKeySeed {
    pub fn arg(arg_no: usize, conv: NamingConvention) -> Self {
        Self(VarKeySeedInner::Slot(Slot::Arg(arg_no.into())), conv)
    }

    pub fn field(field_no: usize, conv: NamingConvention) -> Self {
        Self(VarKeySeedInner::Slot(Slot::Output(field_no.into())), conv)
    }
}

#[derive(Clone, Copy, Hash, Eq, PartialEq, Debug)]
pub enum VarKey {
    Slot(Slot),
    Temp,
    Lifted(usize),
}

impl Default for VarKeySeedInner {
    fn default() -> Self {
        Self::Temp
    }
}

impl Default for VarKey {
    fn default() -> Self {
        Self::Temp
    }
}

impl Temp<'_> for VarKey {
    type Ctx = NamingConvention;
    type Output = VarKeySeed;

    fn temp(conv: Self::Ctx) -> Self::Output {
        VarKeySeed(VarKeySeedInner::Temp, conv)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum NamingConvention {
    Short,
}

impl NamingConvention {
    fn format_io(&self, slot: Slot) -> String {
        match self {
            NamingConvention::Short => match slot {
                Slot::Arg(arg_no) => format!("in_{arg_no}"),
                Slot::Output(out_no) => format!("out_{out_no}"),
                Slot::Advice(adv) => format!("adv_{}_{}", adv.col(), adv.row()),
                Slot::Fixed(fix) => format!("fix_{}_{}", fix.col(), fix.row()),
                Slot::TableLookup(id, col, row, idx, ridx) => {
                    format!("lkp{id}_{col}_{row}_{idx}_{ridx}")
                }
                Slot::CallOutput(module, out) => format!("cout_{module}_{out}"),
                Slot::Temp(temp) => format!("t{temp}"),
                Slot::Challenge(index, phase, _) => format!("chall_{index}_{phase}"),
            },
        }
    }

    fn format_temp(&self) -> String {
        match self {
            // These temps are exclusive from the Picus backend so we use 'pt' for 'Picus temp'.
            NamingConvention::Short => "pt",
        }
        .to_owned()
    }

    fn format_lifted(&self, id: usize) -> String {
        match self {
            NamingConvention::Short => format!("l{id}"),
        }
    }
}

/// Struct containing the metadata necessary to create a [`VarStr`].
#[derive(Clone, Debug)]
pub struct VarKeySeed(VarKeySeedInner, NamingConvention);

impl VarKeySeed {
    pub fn new(inner: VarKeySeedInner, conv: NamingConvention) -> Self {
        Self(inner, conv)
    }

    pub fn io<I: Into<Slot>>(i: I, conv: NamingConvention) -> Self {
        Self(VarKeySeedInner::Slot(i.into()), conv)
    }

    pub fn lifted(id: usize, conv: NamingConvention) -> Self {
        Self(VarKeySeedInner::Lifted(id), conv)
    }
}

impl From<VarKeySeed> for VarKey {
    fn from(seed: VarKeySeed) -> VarKey {
        match seed.0 {
            VarKeySeedInner::Slot(slot) => VarKey::Slot(slot),
            VarKeySeedInner::Temp => VarKey::Temp,
            VarKeySeedInner::Lifted(idx) => VarKey::Lifted(idx),
        }
    }
}

impl From<VarKeySeed> for VarStr {
    fn from(seed: VarKeySeed) -> VarStr {
        match seed.0 {
            VarKeySeedInner::Slot(slot) => seed.1.format_io(slot),
            VarKeySeedInner::Temp => seed.1.format_temp(),
            VarKeySeedInner::Lifted(id) => seed.1.format_lifted(id),
        }
        .try_into()
        .unwrap()
    }
}

impl VarKind for VarKey {
    fn is_input(&self) -> bool {
        match self {
            VarKey::Slot(func_io) => matches!(func_io, Slot::Arg(_) | Slot::Challenge(_, _, _)),
            VarKey::Lifted(_) => true,
            _ => false,
        }
    }

    fn is_output(&self) -> bool {
        match self {
            VarKey::Slot(func_io) => matches!(func_io, Slot::Output(_)),
            _ => false,
        }
    }

    fn is_temp(&self) -> bool {
        match self {
            VarKey::Slot(func_io) => matches!(
                func_io,
                Slot::Advice(_) | Slot::CallOutput(_, _) | Slot::Temp(_)
            ),
            VarKey::Temp => true,
            _ => false,
        }
    }

    fn get_input_no(&self) -> Option<usize> {
        match self {
            VarKey::Slot(Slot::Arg(n)) => Some(**n),
            VarKey::Slot(Slot::Challenge(_, _, n)) => Some(**n),
            _ => None,
        }
    }

    fn get_output_no(&self) -> Option<usize> {
        match self {
            VarKey::Slot(Slot::Output(n)) => Some(**n),
            _ => None,
        }
    }
}

impl<T: Into<Slot>> From<T> for VarKeySeedInner {
    fn from(value: T) -> Self {
        Self::Slot(value.into())
    }
}
