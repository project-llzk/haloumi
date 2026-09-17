//! Utilities for parsing a constants file.

use std::io::{self, BufRead};

pub fn parse_constants_file(reader: impl BufRead) -> Result<Vec<String>, io::Error> {
    Ok(reader
        .lines()
        .map(|l| {
            Ok(l?
                .split(",")
                .flat_map(|s| s.split_whitespace())
                .map(|s| s.trim())
                .filter(|s| !s.is_empty())
                .map(|s| s.to_owned())
                .collect::<Vec<_>>())
        })
        .collect::<Result<Vec<_>, io::Error>>()?
        .into_iter()
        .flatten()
        .collect())
}

#[cfg(test)]
mod tests {
    use ff::PrimeField;
    use halo2curves::bn256::Fr;
    use haloumi_integration::parse_field;

    use super::parse_constants_file;

    fn helper<F: PrimeField>(input: &str, expected: F) {
        let parsed = parse_field::<F>(input);
        assert_eq!(parsed.unwrap(), expected);
    }

    #[test]
    #[should_panic]
    fn test_empty() {
        parse_field::<Fr>("").unwrap();
    }

    #[test]
    fn test0() {
        helper("0", Fr::zero());
    }

    #[test]
    fn test00() {
        helper("00", Fr::zero());
    }

    #[test]
    fn test1() {
        helper("1", Fr::one());
    }

    #[test]
    fn test10() {
        helper("10", Fr::from(10));
    }

    #[test]
    fn test010() {
        helper("010", Fr::from(10));
    }

    #[test]
    fn parse_constants_file_test() {
        let content = r#"
        1,2,3
        4,5 6 
        7
        8
    "#;
        let expected = [1, 2, 3, 4, 5, 6, 7, 8]
            .iter()
            .map(|i| format!("{}", i))
            .collect::<Vec<_>>();

        let output = parse_constants_file(content.as_bytes()).unwrap();
        assert_eq!(output, expected);
    }
}
