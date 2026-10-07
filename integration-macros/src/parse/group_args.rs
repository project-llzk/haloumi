//! Arguments accepted by the `group` attribute macro.

use syn::parse::{Parse, ParseStream};

/// Empty arguments for the [`group`](crate::group) attribute macro.
#[derive(Debug)]
pub struct GroupArgs;

impl Parse for GroupArgs {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.is_empty() {
            Ok(Self)
        } else {
            Err(input.error("the #[group] attribute does not accept arguments"))
        }
    }
}
