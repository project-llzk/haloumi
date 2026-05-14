//! Common traits used in IR objects.

use std::iter::Sum;

use crate::diagnostics::Diagnostic;

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

impl<T: ConstantFolding> ConstantFolding for Box<T> {
    type Error = T::Error;

    type T = T::T;

    fn constant_fold(&mut self) -> Result<(), Self::Error> {
        self.as_mut().constant_fold()
    }

    fn constant_folded(self) -> Result<Self, Self::Error>
    where
        Self: Sized,
    {
        (*self).constant_folded().map(Box::new)
    }

    fn const_value(&self) -> Option<Self::T> {
        self.as_ref().const_value()
    }
}

impl<E: ConstantFolding> ConstantFolding for Vec<E> {
    type Error = E::Error;

    type T = Vec<E::T>;

    fn constant_fold(&mut self) -> Result<(), Self::Error> {
        self.iter_mut().try_for_each(|e| e.constant_fold())
    }

    fn const_value(&self) -> Option<Self::T> {
        self.iter().map(|e| e.const_value()).collect()
    }
}

impl<E: ConstantFolding> ConstantFolding for [E] {
    type Error = E::Error;

    type T = Vec<E::T>;

    fn constant_fold(&mut self) -> Result<(), Self::Error> {
        self.iter_mut().try_for_each(|e| e.constant_fold())
    }

    fn const_value(&self) -> Option<Self::T> {
        self.iter().map(|e| e.const_value()).collect()
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

impl<E: Canonicalize> Canonicalize for Vec<E> {
    fn canonicalize(&mut self) {
        for e in self {
            e.canonicalize();
        }
    }
}

impl<E: Canonicalize> Canonicalize for [E] {
    fn canonicalize(&mut self) {
        for e in self {
            e.canonicalize();
        }
    }
}

impl<T: Canonicalize> Canonicalize for Box<T> {
    fn canonicalize(&mut self) {
        self.as_mut().canonicalize()
    }
}

/// Trait for evaluating IR objects.
pub trait Evaluate<Output> {
    /// Evaluate the IR object and return a result.
    fn evaluate(&self) -> Output;
}

impl<O, T: Evaluate<O>> Evaluate<O> for Box<T> {
    fn evaluate(&self) -> O {
        self.as_ref().evaluate()
    }
}

impl<O, T: Evaluate<O>> Evaluate<Option<O>> for Option<T> {
    fn evaluate(&self) -> Option<O> {
        self.as_ref().map(Evaluate::<O>::evaluate)
    }
}

impl<O: Sum, T: Evaluate<O>> Evaluate<O> for [T] {
    fn evaluate(&self) -> O {
        self.iter().map(Evaluate::<O>::evaluate).sum()
    }
}

impl<O: Sum, T: Evaluate<O>> Evaluate<O> for Vec<T> {
    fn evaluate(&self) -> O {
        self.iter().map(Evaluate::<O>::evaluate).sum()
    }
}

/// Trait for performing validation on the IR.
pub trait Validatable {
    /// The type used to represent diagnostics.
    type Diagnostic: Diagnostic;

    /// Context necessary for validating the IR.
    type Context: ?Sized;

    /// Performs validation checks, returning either
    /// `Ok` with a list of non-error diagnostics or `Err` with a list of all the diagnostics.
    fn validate_with_context(
        &self,
        context: &Self::Context,
    ) -> Result<Vec<Self::Diagnostic>, Vec<Self::Diagnostic>>;

    /// Performs validation checks, returning either
    /// `Ok` with a list of non-error diagnostics or `Err` with a list of all the diagnostics.
    fn validate(&self) -> Result<Vec<Self::Diagnostic>, Vec<Self::Diagnostic>>
    where
        Self::Context: Default,
    {
        self.validate_with_context(&Default::default())
    }
}
