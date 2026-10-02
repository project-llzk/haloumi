//! Error type for the support crate.

pub use haloumi_core::error::Error;

/// This macro implements the conversion between the error types in Halo2 and Haloumi.
#[macro_export]
macro_rules! __impl_into_and_from_error {
    ($error:ty, $factory:expr) => {
        impl From<$error> for $crate::error::Error {
            fn from(value: $error) -> Self {
                Self::Plonk(std::sync::Arc::new(value))
            }
        }

        impl From<$crate::error::Error> for $error {
            fn from(value: $crate::error::Error) -> Self {
                ($factory)(value)
            }
        }
    };
}

/// Macro for creating [`Error::UnexpectedElements`] errors.
///
/// The macro accepts a comparison expression between two values (expected and actual) and an
/// optional message. The message itself can accept formatting arguments.
/// It will return an [`Err`] with an [`Error::UnexpectedElements`] error so the
/// caller of the macro should have a return type of `Result<_, E>` s.t. `E` implements [`From`] for the [`Error`] type.
///
/// Because of how the macro is implemented, when passign a custom message is necessary to surround the comparison with parenthesis.
///
/// # Examples
///
/// ```no_run
/// use haloumi_integration::error::Error;
/// use haloumi_integration::expect_elements;
///
/// fn foo(c: usize) -> Result<(), Error> {
///     let a = 6;
///     let b = 7;
///     // Default message
///     expect_elements!(a == b);
///     // With a custom message
///     expect_elements!((a <= b), "During call to foo()");
///     // With a custom formatted message
///     expect_elements!((a > c), "During call to foo({c})");
///     Ok(())
/// }
/// ```
#[macro_export]
macro_rules! expect_elements {
    // With custom message
    (($($tokens:tt)+) , $($fmt:tt)+) => {
        $crate::__expect_elements_parse! { [] [$($tokens)+] format!($($fmt)+) }
    };

    // Without message → default
    ($($tokens:tt)+) => {
        $crate::__expect_elements_parse! { [] [$($tokens)+] String::new() }
    };
}

//
// TT MUNCHER: split into lhs / op / rhs
//
#[macro_export]
#[doc(hidden)]
macro_rules! __expect_elements_parse {
    // ==
    ([$($lhs:tt)+] [== $($rhs:tt)+] $msg:expr) => {
        $crate::__expect_elements_finish! {
            ($($lhs)*)
            (==)
            ($($rhs)*)
            ($msg)
        }
    };

    // !=
    ([$($lhs:tt)+] [!= $($rhs:tt)+] $msg:expr) => {
        $crate::__expect_elements_finish! {
            ($($lhs)*)
            (!=)
            ($($rhs)*)
            ($msg)
        }
    };

    // <
    ([$($lhs:tt)+] [< $($rhs:tt)+] $msg:expr) => {
        $crate::__expect_elements_finish! {
            ($($lhs)*)
            (<)
            ($($rhs)*)
            ($msg)
        }
    };

    // <=
    ([$($lhs:tt)+] [<= $($rhs:tt)+] $msg:expr) => {
        $crate::__expect_elements_finish! {
            ($($lhs)*)
            (<=)
            ($($rhs)*)
            ($msg)
        }
    };

    // >
    ([$($lhs:tt)+] [> $($rhs:tt)+] $msg:expr) => {
        $crate::__expect_elements_finish! {
            ($($lhs)*)
            (>)
            ($($rhs)*)
            ($msg)
        }
    };

    // >=
    ([$($lhs:tt)+] [>= $($rhs:tt)+] $msg:expr) => {
        $crate::__expect_elements_finish! {
            ($($lhs)*)
            (>=)
            ($($rhs)*)
            ($msg)
        }
    };

    // Keep munching
    ([$($lhs:tt)*] [$next:tt $($rest:tt)*] $msg:expr) => {
        $crate::__expect_elements_parse! { [$($lhs)* $next] [$($rest)*] $msg }
    };

    // No operator -> error
    ([$($lhs:tt)*] [] $msg:expr) => {
        compile_error!("expected a comparison expression such as `lhs == rhs`");
    };
}

//
// Final step: evaluate lhs, rhs, and return Err(A::B)
//
#[doc(hidden)]
#[macro_export]
macro_rules! __expect_elements_finish {
    // ==
    (($($lhs:tt)+) (==) ($($rhs:tt)+) ($msg:expr)) => {{
        let lhs_val: usize = $($lhs)*;
        let rhs_val: usize = $($rhs)*;
        $crate::error::__expect_elements_impl($msg, lhs_val, rhs_val, lhs_val == rhs_val)?;
    }};

    // !=
    (($($lhs:tt)+) (!=) ($($rhs:tt)+) ($msg:expr)) => {{
        let lhs_val: usize = $($lhs)*;
        let rhs_val: usize = $($rhs)*;
        $crate::error::__expect_elements_impl($msg, lhs_val, rhs_val, lhs_val != rhs_val)?;
    }};

    // <
    (($($lhs:tt)+) (<) ($($rhs:tt)+) ($msg:expr)) => {{
        let lhs_val: usize = $($lhs)*;
        let rhs_val: usize = $($rhs)*;
        $crate::error::__expect_elements_impl($msg, lhs_val, rhs_val, lhs_val < rhs_val)?;
    }};

    // <=
    (($($lhs:tt)+) (<=) ($($rhs:tt)+) ($msg:expr)) => {{
        let lhs_val: usize = $($lhs)*;
        let rhs_val: usize = $($rhs)*;
        $crate::error::__expect_elements_impl($msg, lhs_val, rhs_val, lhs_val <= rhs_val)?;
    }};

    // >
    (($($lhs:tt)+) (>) ($($rhs:tt)+) ($msg:expr)) => {{
        let lhs_val: usize = $($lhs)*;
        let rhs_val: usize = $($rhs)*;
        $crate::error::__expect_elements_impl($msg, lhs_val, rhs_val, lhs_val > rhs_val)?;
    }};

    // >=
    (($($lhs:tt)+) (>=) ($($rhs:tt)+) ($msg:expr)) => {{
        let lhs_val: usize = $($lhs)*;
        let rhs_val: usize = $($rhs)*;
        $crate::error::__expect_elements_impl($msg, lhs_val, rhs_val, lhs_val >= rhs_val)?;
    }};
}

#[doc(hidden)]
#[inline]
pub fn __expect_elements_impl(
    header: String,
    expected: usize,
    actual: usize,
    passed: bool,
) -> Result<(), Error> {
    if passed {
        Ok(())
    } else {
        Err(Error::UnexpectedElements {
            header,
            expected,
            actual,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[derive(Debug)]
    enum Cmp {
        Eq,
        Ne,
        Lt,
        Le,
        Gt,
        Ge,
    }

    #[rstest]
    #[case(Cmp::Eq, 1, 1)]
    #[case(Cmp::Ne, 1, 2)]
    #[case(Cmp::Lt, 1, 2)]
    #[case(Cmp::Le, 1, 1)]
    #[case(Cmp::Gt, 2, 1)]
    #[case(Cmp::Ge, 1, 1)]
    #[should_panic(expected = "unexpected elements error")]
    #[case(Cmp::Eq, 1, 2)]
    #[should_panic(expected = "unexpected elements error")]
    #[case(Cmp::Ne, 1, 1)]
    #[should_panic(expected = "unexpected elements error")]
    #[case(Cmp::Lt, 1, 0)]
    #[should_panic(expected = "unexpected elements error")]
    #[case(Cmp::Le, 1, 0)]
    #[should_panic(expected = "unexpected elements error")]
    #[case(Cmp::Gt, 2, 3)]
    #[should_panic(expected = "unexpected elements error")]
    #[case(Cmp::Ge, 1, 3)]
    fn expect_elements_test(#[case] cmp: Cmp, #[case] expected: usize, #[case] actual: usize) {
        fn do_test(cmp: Cmp, expected: usize, actual: usize) -> Result<(), Error> {
            match cmp {
                Cmp::Eq => expect_elements!((expected == actual), "unexpected elements error"),
                Cmp::Ne => expect_elements!((expected != actual), "unexpected elements error"),
                Cmp::Lt => expect_elements!((expected < actual), "unexpected elements error"),
                Cmp::Le => expect_elements!((expected <= actual), "unexpected elements error"),
                Cmp::Gt => expect_elements!((expected > actual), "unexpected elements error"),
                Cmp::Ge => expect_elements!((expected >= actual), "unexpected elements error"),
            }
            Ok(())
        }
        eprintln!("cmp = {cmp:?}, expected = {expected}, actual = {actual}");
        do_test(cmp, expected, actual).unwrap();
    }

    #[rstest]
    #[should_panic(expected = "unexpected elements error")]
    #[case(Cmp::Eq)]
    #[should_panic(expected = "unexpected elements error")]
    #[case(Cmp::Ne)]
    #[should_panic(expected = "unexpected elements error")]
    #[case(Cmp::Lt)]
    #[should_panic(expected = "unexpected elements error")]
    #[case(Cmp::Le)]
    #[should_panic(expected = "unexpected elements error")]
    #[case(Cmp::Gt)]
    #[should_panic(expected = "unexpected elements error")]
    #[case(Cmp::Ge)]
    fn expect_elements_complex_expr_rhs(#[case] cmp: Cmp) {
        fn do_test(cmp: Cmp) -> Result<(), Error> {
            let v = vec![1, 2, 3];
            match cmp {
                Cmp::Eq => expect_elements!((2 == v.len()), "unexpected elements error"),
                Cmp::Ne => expect_elements!((3 != v.len()), "unexpected elements error"),
                Cmp::Lt => expect_elements!((4 < v.len()), "unexpected elements error"),
                Cmp::Le => expect_elements!((4 <= v.len()), "unexpected elements error"),
                Cmp::Gt => expect_elements!((2 > v.len()), "unexpected elements error"),
                Cmp::Ge => expect_elements!((2 >= v.len()), "unexpected elements error"),
            };
            Ok(())
        }
        do_test(cmp).unwrap();
    }

    #[rstest]
    #[should_panic(expected = "unexpected elements error")]
    #[case(Cmp::Eq)]
    #[should_panic(expected = "unexpected elements error")]
    #[case(Cmp::Ne)]
    #[should_panic(expected = "unexpected elements error")]
    #[case(Cmp::Lt)]
    #[should_panic(expected = "unexpected elements error")]
    #[case(Cmp::Le)]
    #[should_panic(expected = "unexpected elements error")]
    #[case(Cmp::Gt)]
    #[should_panic(expected = "unexpected elements error")]
    #[case(Cmp::Ge)]
    fn expect_elements_complex_expr_lhs(#[case] cmp: Cmp) {
        fn do_test(cmp: Cmp) -> Result<(), Error> {
            let v = vec![1, 2, 3];
            match cmp {
                Cmp::Eq => expect_elements!((v.len() == 2), "unexpected elements error"),
                Cmp::Ne => expect_elements!((v.len() != 3), "unexpected elements error"),
                Cmp::Lt => expect_elements!((v.len() < 2), "unexpected elements error"),
                Cmp::Le => expect_elements!((v.len() <= 2), "unexpected elements error"),
                Cmp::Gt => expect_elements!((v.len() > 4), "unexpected elements error"),
                Cmp::Ge => expect_elements!((v.len() >= 4), "unexpected elements error"),
            };
            Ok(())
        }
        do_test(cmp).unwrap();
    }
}
