//! Serde testing helpers.

use serde::{Serialize, de::DeserializeOwned};
use serde_json::{from_slice, to_vec};

pub fn round_trip<T>(value: T) -> T
where
    T: Serialize + DeserializeOwned,
{
    from_slice(&to_vec(&value).unwrap()).unwrap()
}
