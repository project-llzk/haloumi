//! Serde testing helpers.

use serde::{Serialize, de::DeserializeOwned};
use serde_json::{from_slice, to_vec};

pub fn round_trip<T>(value: &T) -> T
where
    T: Serialize + DeserializeOwned,
{
    from_slice(&to_vec(value).unwrap()).unwrap()
}

use quickcheck_macros::quickcheck;

use crate::{
    IRCircuit,
    expr::{IRAexpr, IRBexpr},
    groups::{IRGroup, callsite::CallSite},
    meta::Meta,
    stmt::IRStmt,
};

#[quickcheck]
fn circuit_round_trips(value: IRCircuit<(), ()>) {
    assert_stable(value);
}
