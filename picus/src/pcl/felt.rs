use haloumi_core::felt::Felt;
use haloumi_ir::Prime;

use crate::pcl::display::{TextRepresentable, TextRepresentation};

impl TextRepresentable for Felt {
    fn to_repr(&self) -> TextRepresentation<'_> {
        TextRepresentation::owned_atom(self.to_string())
    }

    fn width_hint(&self) -> usize {
        self.to_string().len()
    }
}

impl TextRepresentable for Prime {
    fn to_repr(&self) -> TextRepresentation<'_> {
        TextRepresentation::owned_atom(self.to_string())
    }

    fn width_hint(&self) -> usize {
        self.to_string().len()
    }
}
