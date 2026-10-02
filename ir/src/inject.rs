//! Types for creating IR on the fly during synthesis.

use std::{
    collections::HashMap,
    ops::{Deref, DerefMut},
};

use crate::stmt::IRStmt;

/// Records additional IR that gets added after synthesis.
pub struct InjectedIR<R, E>(HashMap<R, Vec<IRStmt<(usize, E)>>>);

impl<R, E> InjectedIR<R, E> {
    /// Adds the IR of the other into self.
    pub fn combine_ir(&mut self, other: Self)
    where
        R: std::hash::Hash + Copy + Eq,
    {
        for (region, ir) in other {
            self.entry(region).or_default().extend(ir);
        }
    }
}

impl<R, E> Deref for InjectedIR<R, E> {
    type Target = HashMap<R, Vec<IRStmt<(usize, E)>>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<R, E> DerefMut for InjectedIR<R, E> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<R, E> Default for InjectedIR<R, E> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<R: std::fmt::Debug, E: std::fmt::Debug> std::fmt::Debug for InjectedIR<R, E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl<R, E> IntoIterator for InjectedIR<R, E> {
    type Item = (R, Vec<IRStmt<(usize, E)>>);

    type IntoIter = <HashMap<R, Vec<IRStmt<(usize, E)>>> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, R, E> IntoIterator for &'a InjectedIR<R, E> {
    type Item = (&'a R, &'a Vec<IRStmt<(usize, E)>>);

    type IntoIter = <&'a HashMap<R, Vec<IRStmt<(usize, E)>>> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        (&self.0).into_iter()
    }
}

impl<'a, R, E> IntoIterator for &'a mut InjectedIR<R, E> {
    type Item = (&'a R, &'a mut Vec<IRStmt<(usize, E)>>);

    type IntoIter = <&'a mut HashMap<R, Vec<IRStmt<(usize, E)>>> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        (&mut self.0).into_iter()
    }
}
