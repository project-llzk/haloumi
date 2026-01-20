//! Common traits used in IR objects.

/// Represents a constant-foldable object.
pub trait ConstantFolding {
    /// Error type.
    type Error;
    /// Object's type for constants.
    type T;

    /// Folds the object in-place.
    fn constant_fold(&mut self) -> Result<(), Self::Error>;

    /// Moves the object after folding it.
    fn constant_folded(mut self) -> Result<Self, Self::Error>
    where
        Self: Sized,
    {
        self.constant_fold()?;
        Ok(self)
    }

    /// May return the object as a constant value.
    fn const_value(&self) -> Option<Self::T> {
        None
    }
}

/// Represents an object that has a canonical form.
pub trait Canonicalize {
    /// Canonicalizes the object in-place.
    fn canonicalize(&mut self);

    /// Transforms the object into its canonical version.
    fn canonicalized(mut self) -> Self
    where
        Self: Sized,
    {
        self.canonicalize();
        self
    }
}
