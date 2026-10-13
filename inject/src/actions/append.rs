use crate::{actions::InjectAction, crate_info::CrateMut, error::Error, spec::Append};

/// Applies an append patch.
pub struct AppendAction<'a> {
    append: &'a Append,
}

impl<'a> AppendAction<'a> {
    /// Creates a new action.
    pub fn boxed(append: &'a Append) -> Box<dyn InjectAction + 'a> {
        Box::new(Self::from(append))
    }
}

impl<'a> From<&'a Append> for AppendAction<'a> {
    fn from(append: &'a Append) -> Self {
        Self { append }
    }
}

impl InjectAction for AppendAction<'_> {
    fn apply(&self, dest_crate: &mut CrateMut) -> Result<(), Error> {
        let file = dest_crate.open_rust_file(self.append.path())?;
        let contents = self.append.content()?;
        file.items.extend(contents);
        Ok(())
    }
}
