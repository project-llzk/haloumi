use std::{
    collections::{HashMap, HashSet},
    fmt,
    hash::{DefaultHasher, Hash as _, Hasher as _},
};

use anyhow::{Result, anyhow, bail};
use haloumi_ir::{Felt, Prime};

use crate::pcl::{
    display::{TextRepresentable, TextRepresentation},
    errors::ExprArgsError,
    note::Note,
    stmt::traits::ConstraintLike,
    vars::VarStr,
};

use super::{
    Expr, ExprHash, Wrap,
    traits::{
        ConstantFolding, ConstraintExpr, ExprLike, ExprSize, GetExprHash, MaybeVarLike, WrappedExpr,
    },
};

macro_rules! hash {
    ($($elt:expr),* $(,)?) => { {
        let mut hasher = DefaultHasher::new();
        '('.hash(&mut hasher);

        $( $elt.hash(&mut hasher); )*

        ')'.hash(&mut hasher);

        hasher.finish().into()
    } };
}

mod binary;

pub use binary::{BinaryExpr, BinaryOp, Boolean, ConstraintKind};

//===----------------------------------------------------------------------===//
// ConstExpr
//===----------------------------------------------------------------------===//

#[derive(Clone, Debug, PartialEq)]
pub struct ConstExpr(Felt);

impl ConstExpr {
    pub fn new(f: Felt) -> Self {
        Self(f)
    }
}

impl WrappedExpr for ConstExpr {
    fn wrap(&self) -> Expr {
        Wrap::new(self.clone())
    }
}

impl ExprSize for ConstExpr {
    fn size(&self) -> usize {
        1
    }

    fn extraible(&self) -> bool {
        false
    }

    fn args(&self) -> Vec<Expr> {
        vec![]
    }

    fn replace_args(&self, args: &[Option<Expr>]) -> Result<Option<Expr>, ExprArgsError> {
        if args.is_empty() {
            return Ok(None);
        }

        Err(ExprArgsError::OutOfBounds {
            idx: args.len(),
            place: "const expression",
            size: 0,
            note: Note::NoNote,
        })
    }
}

impl fmt::Display for ConstExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl ConstantFolding for ConstExpr {
    fn as_const(&self) -> Option<Felt> {
        Some(self.0.clone())
    }

    fn fold(&self, _: Prime) -> Option<Expr> {
        None
    }

    fn replaced_by_const(&self, _: &HashMap<VarStr, Felt>) -> Option<Expr> {
        None
    }
}

impl TextRepresentable for ConstExpr {
    fn to_repr(&self) -> TextRepresentation<'_> {
        self.0.to_repr()
    }

    fn width_hint(&self) -> usize {
        self.0.width_hint()
    }
}

impl MaybeVarLike for ConstExpr {
    fn var_name(&self) -> Option<&VarStr> {
        None
    }

    fn renamed(&self, _: &HashMap<VarStr, VarStr>) -> Option<Expr> {
        None
    }

    fn free_vars(&self) -> HashSet<&VarStr> {
        Default::default()
    }
}

impl ConstraintLike for ConstExpr {
    fn is_constraint(&self) -> bool {
        false
    }

    fn constraint_expr(&self) -> Option<&dyn ConstraintExpr> {
        None
    }
}

impl GetExprHash for ConstExpr {
    fn hash(&self) -> ExprHash {
        hash!(self.0)
    }
}

impl ExprLike for ConstExpr {}

//===----------------------------------------------------------------------===//
// VarExpr
//===----------------------------------------------------------------------===//

#[derive(Clone, Debug, PartialEq)]
pub struct VarExpr(VarStr);

impl WrappedExpr for VarExpr {
    fn wrap(&self) -> Expr {
        Wrap::new(self.clone())
    }
}

impl VarExpr {
    pub fn new(s: VarStr) -> Self {
        Self(s)
    }
}

impl ExprSize for VarExpr {
    fn size(&self) -> usize {
        1
    }

    fn extraible(&self) -> bool {
        false
    }

    fn args(&self) -> Vec<Expr> {
        vec![]
    }

    fn replace_args(&self, args: &[Option<Expr>]) -> Result<Option<Expr>, ExprArgsError> {
        if args.is_empty() {
            return Ok(None);
        }

        Err(ExprArgsError::OutOfBounds {
            idx: args.len(),
            place: "var expression",
            size: 0,
            note: Note::NoNote,
        })
        //Err(anyhow!("VarExpr does not have arguments"))
    }
}

impl ConstantFolding for VarExpr {
    fn as_const(&self) -> Option<Felt> {
        None
    }

    fn fold(&self, _: Prime) -> Option<Expr> {
        None
    }

    fn replaced_by_const(&self, map: &HashMap<VarStr, Felt>) -> Option<Expr> {
        map.get(&self.0).cloned().map(super::r#const)
    }
}

impl TextRepresentable for VarExpr {
    fn to_repr(&self) -> TextRepresentation<'_> {
        self.0.to_repr()
    }

    fn width_hint(&self) -> usize {
        self.0.width_hint()
    }
}

impl MaybeVarLike for VarExpr {
    fn var_name(&self) -> Option<&VarStr> {
        Some(&self.0)
    }

    fn renamed(&self, map: &HashMap<VarStr, VarStr>) -> Option<Expr> {
        if let Some(new_name) = map.get(&self.0).cloned() {
            return Some(Wrap::new(VarExpr(new_name)));
        }
        None
    }

    fn free_vars(&self) -> HashSet<&VarStr> {
        HashSet::from([&self.0])
    }
}

impl ConstraintLike for VarExpr {
    fn is_constraint(&self) -> bool {
        false
    }

    fn constraint_expr(&self) -> Option<&dyn ConstraintExpr> {
        None
    }
}

impl GetExprHash for VarExpr {
    fn hash(&self) -> ExprHash {
        hash!(self.0)
    }
}

impl ExprLike for VarExpr {}

//===----------------------------------------------------------------------===//
// NegExpr
//===----------------------------------------------------------------------===//

#[derive(Clone, Debug)]
pub struct NegExpr(Expr);

impl NegExpr {
    pub fn new(e: Expr) -> Self {
        Self(e)
    }
}

impl WrappedExpr for NegExpr {
    fn wrap(&self) -> Expr {
        Wrap::new(self.clone())
    }
}

impl ExprSize for NegExpr {
    fn size(&self) -> usize {
        self.0.size() + 1
    }

    fn extraible(&self) -> bool {
        true
    }

    fn args(&self) -> Vec<Expr> {
        vec![self.0.clone()]
    }

    fn replace_args(&self, args: &[Option<Expr>]) -> Result<Option<Expr>, ExprArgsError> {
        Ok(match args {
            [None] => None,
            [Some(expr)] => Some(expr),
            _ => {
                return Err(ExprArgsError::OutOfBounds {
                    idx: args.len(),
                    place: "neg expression",
                    size: 1,
                    note: Note::NoNote,
                });
            } //_ => bail!("NegExpr expects 1 argument"),
        }
        .map(|expr| -> Expr { Wrap::new(Self(expr.clone())) }))
    }
}

impl ConstantFolding for NegExpr {
    fn as_const(&self) -> Option<Felt> {
        None
    }

    fn fold(&self, prime: Prime) -> Option<Expr> {
        let inner = self.0.fold(prime).unwrap_or_else(|| self.0.clone());

        inner
            .as_const()
            .map(|e| {
                -e
                //let prime = prime.clone();
                //assert!(e < prime);
                //(prime.clone() - e) % prime
            })
            .map(ConstExpr)
            .map(|e| -> Expr { Wrap::new(e) })
            .or_else(|| -> Option<Expr> { Some(Wrap::new(Self(inner))) })
    }

    fn replaced_by_const(&self, map: &HashMap<VarStr, Felt>) -> Option<Expr> {
        self.0
            .replaced_by_const(map)
            .map(|inner| -> Expr { Wrap::new(Self(inner)) })
    }
}

impl TextRepresentable for NegExpr {
    fn to_repr(&self) -> TextRepresentation<'_> {
        owned_list!("-", &self.0)
    }

    fn width_hint(&self) -> usize {
        3 + self.0.width_hint()
    }
}

impl MaybeVarLike for NegExpr {
    fn var_name(&self) -> Option<&VarStr> {
        None
    }

    fn renamed(&self, map: &HashMap<VarStr, VarStr>) -> Option<Expr> {
        self.0.renamed(map).map(|e| -> Expr { Wrap::new(Self(e)) })
    }

    fn free_vars(&self) -> HashSet<&VarStr> {
        self.0.free_vars()
    }
}

impl ConstraintLike for NegExpr {
    fn is_constraint(&self) -> bool {
        false
    }

    fn constraint_expr(&self) -> Option<&dyn ConstraintExpr> {
        None
    }
}

impl PartialEq for NegExpr {
    fn eq(&self, other: &Self) -> bool {
        self.0 == *other.0
    }
}

impl GetExprHash for NegExpr {
    fn hash(&self) -> ExprHash {
        hash!('-', self.0.hash())
    }
}

impl ExprLike for NegExpr {}

#[cfg(test)]
mod test_neg_expr {
    use haloumi_ir::Felt;

    use crate::pcl::expr::{Wrap, traits::ConstantFolding as _};

    use super::{ConstExpr, NegExpr};

    use ff::PrimeField;

    /// Implementation of BabyBear used for testing.
    #[derive(PrimeField)]
    #[PrimeFieldModulus = "2013265921"]
    #[PrimeFieldGenerator = "31"]
    #[PrimeFieldReprEndianness = "little"]
    pub struct BabyBear([u64; 1]);

    #[test]
    fn test_const_folding() {
        let original_value = Felt::from(BabyBear::from(2));
        let inner = ConstExpr(original_value);
        let e = NegExpr(Wrap::new(inner));

        let folded = e.fold(original_value.prime()).unwrap();
        let value = folded.as_const().unwrap();
        assert_eq!(value, -original_value);
    }

    #[test]
    fn test_const_folding_0() {
        let original_value = Felt::from(BabyBear::from(0));
        let inner = ConstExpr(original_value);
        let e = NegExpr(Wrap::new(inner));

        let folded = e.fold(original_value.prime()).unwrap();
        let value = folded.as_const().unwrap();
        assert_eq!(value, original_value);
    }
}

//===----------------------------------------------------------------------===//
// NotExpr
//===----------------------------------------------------------------------===//

#[derive(Clone, Debug)]
pub struct NotExpr(Expr);

impl NotExpr {
    pub fn new(e: Expr) -> Self {
        Self(e)
    }
}

impl WrappedExpr for NotExpr {
    fn wrap(&self) -> Expr {
        Wrap::new(self.clone())
    }
}

impl ExprSize for NotExpr {
    fn size(&self) -> usize {
        self.0.size() + 1
    }

    fn extraible(&self) -> bool {
        true
    }

    fn args(&self) -> Vec<Expr> {
        vec![self.0.clone()]
    }

    fn replace_args(&self, args: &[Option<Expr>]) -> Result<Option<Expr>, ExprArgsError> {
        Ok(match args {
            [None] => None,
            [Some(expr)] => Some(expr),
            _ => {
                return Err(ExprArgsError::OutOfBounds {
                    idx: args.len(),
                    place: "not expression",
                    size: 1,
                    note: Note::NoNote,
                });
            }
        }
        .map(|expr| -> Expr { Wrap::new(Self(expr.clone())) }))
    }
}

impl ConstantFolding for NotExpr {
    fn as_const(&self) -> Option<Felt> {
        None
    }

    fn fold(&self, prime: Prime) -> Option<Expr> {
        self.0
            .fold(prime)
            .map(|inner| -> Expr { Wrap::new(Self(inner)) })
    }

    fn replaced_by_const(&self, map: &HashMap<VarStr, Felt>) -> Option<Expr> {
        self.0
            .replaced_by_const(map)
            .map(|inner| -> Expr { Wrap::new(Self(inner)) })
    }
}

impl TextRepresentable for NotExpr {
    fn to_repr(&self) -> TextRepresentation<'_> {
        owned_list!("!", &self.0)
    }

    fn width_hint(&self) -> usize {
        3 + self.0.width_hint()
    }
}

impl MaybeVarLike for NotExpr {
    fn var_name(&self) -> Option<&VarStr> {
        None
    }

    fn renamed(&self, map: &HashMap<VarStr, VarStr>) -> Option<Expr> {
        self.0.renamed(map).map(|e| -> Expr { Wrap::new(Self(e)) })
    }

    fn free_vars(&self) -> HashSet<&VarStr> {
        self.0.free_vars()
    }
}

impl ConstraintLike for NotExpr {
    fn is_constraint(&self) -> bool {
        false
    }

    fn constraint_expr(&self) -> Option<&dyn ConstraintExpr> {
        None
    }
}

impl PartialEq for NotExpr {
    fn eq(&self, other: &Self) -> bool {
        self.0 == *other.0
    }
}

impl GetExprHash for NotExpr {
    fn hash(&self) -> ExprHash {
        hash!('!', self.0.hash())
    }
}

impl ExprLike for NotExpr {}

//===----------------------------------------------------------------------===//
// DetExpr
//===----------------------------------------------------------------------===//

#[derive(Clone, Debug)]
/// `DetExpr` is the logical predicate `(det e)` in the Picus constraint language and
/// it denotes that the value of `e` is a deterministic. This is useful for specifying
/// axioms to Picus when there are built-in assumptions to ZK constructs that are infeasible to encode
/// as constraints i.e, lookups.
pub struct DetExpr(Expr);

impl DetExpr {
    pub fn new(e: Expr) -> Self {
        Self(e)
    }
}

impl WrappedExpr for DetExpr {
    fn wrap(&self) -> Expr {
        Wrap::new(self.clone())
    }
}

impl ExprSize for DetExpr {
    fn size(&self) -> usize {
        self.0.size() + 1
    }

    fn extraible(&self) -> bool {
        true
    }

    fn args(&self) -> Vec<Expr> {
        vec![self.0.clone()]
    }

    fn replace_args(&self, args: &[Option<Expr>]) -> Result<Option<Expr>, ExprArgsError> {
        Ok(match args {
            [None] => None,
            [Some(expr)] => Some(expr),
            _ => {
                return Err(ExprArgsError::OutOfBounds {
                    idx: args.len(),
                    place: "det expression",
                    size: 1,
                    note: Note::NoNote,
                });
            }
        }
        .map(|expr| -> Expr { Wrap::new(Self(expr.clone())) }))
    }
}

impl ConstantFolding for DetExpr {
    fn as_const(&self) -> Option<Felt> {
        None
    }

    fn fold(&self, prime: Prime) -> Option<Expr> {
        self.0
            .fold(prime)
            .map(|inner| -> Expr { Wrap::new(Self(inner)) })
    }

    fn replaced_by_const(&self, map: &HashMap<VarStr, Felt>) -> Option<Expr> {
        self.0
            .replaced_by_const(map)
            .map(|inner| -> Expr { Wrap::new(Self(inner)) })
    }
}

impl TextRepresentable for DetExpr {
    fn to_repr(&self) -> TextRepresentation<'_> {
        owned_list!("det", &self.0)
    }

    fn width_hint(&self) -> usize {
        6 + self.0.width_hint()
    }
}

impl MaybeVarLike for DetExpr {
    fn var_name(&self) -> Option<&VarStr> {
        None
    }

    fn renamed(&self, map: &HashMap<VarStr, VarStr>) -> Option<Expr> {
        self.0.renamed(map).map(|e| -> Expr { Wrap::new(Self(e)) })
    }

    fn free_vars(&self) -> HashSet<&VarStr> {
        self.0.free_vars()
    }
}

impl ConstraintLike for DetExpr {
    fn is_constraint(&self) -> bool {
        false
    }

    fn constraint_expr(&self) -> Option<&dyn ConstraintExpr> {
        None
    }
}

impl PartialEq for DetExpr {
    fn eq(&self, other: &Self) -> bool {
        self.0 == *other.0
    }
}

impl GetExprHash for DetExpr {
    fn hash(&self) -> ExprHash {
        hash!("det", self.0.hash())
    }
}

impl ExprLike for DetExpr {}

//===----------------------------------------------------------------------===//
// BoolExpr
//===----------------------------------------------------------------------===//

//#[derive(Copy, Clone, Debug, PartialEq)]
//pub struct BoolExpr(bool);
//
//impl From<bool> for BoolExpr {
//    fn from(value: bool) -> Self {
//        Self(value)
//    }
//}
//
//impl ExprSize for BoolExpr {
//    fn size(&self) -> usize {
//        1
//    }
//
//    fn extraible(&self) -> bool {
//        false
//    }
//
//    fn args(&self) -> Vec<Expr> {
//        vec![]
//    }
//
//    fn replace_args(&self, args: &[Option<Expr>]) -> Result<Option<Expr>, ExprArgsError> {
//        if args.is_empty() {
//            return Ok(None);
//        }
//
//        Err(ExprArgsError::OutOfBounds {
//            idx: args.len(),
//            place: "bool expression",
//            size: 0,
//            note: Note::NoNote,
//        })
//    }
//}
//
//impl ConstantFolding for BoolExpr {
//    fn as_const(&self) -> Option<Felt> {
//        None
//    }
//
//    fn fold(&self) -> Option<Expr> {
//        None
//    }
//
//    fn replaced_by_const(&self, _map: &HashMap<VarStr, Felt>) -> Option<Expr> {
//        None
//    }
//}
//
//impl TextRepresentable for BoolExpr {
//    fn to_repr(&self) -> TextRepresentation<'_> {
//        let rhs = if self.0 { "0" } else { "1" };
//        owned_list!("=", "0", rhs)
//    }
//
//    fn width_hint(&self) -> usize {
//        "(= 0 0)".len()
//    }
//}
//
//impl WrappedExpr for BoolExpr {
//    fn wrap(&self) -> Expr {
//        Expr::new(*self)
//    }
//}
//
//impl MaybeVarLike for BoolExpr {
//    fn var_name(&self) -> Option<&VarStr> {
//        None
//    }
//
//    fn renamed(&self, _map: &HashMap<VarStr, VarStr>) -> Option<Expr> {
//        None
//    }
//
//    fn free_vars(&self) -> HashSet<&VarStr> {
//        Default::default()
//    }
//}
//
//impl ConstraintLike for BoolExpr {
//    fn is_constraint(&self) -> bool {
//        true
//    }
//
//    fn constraint_expr(&self) -> Option<&dyn ConstraintExpr> {
//        Some(self)
//    }
//}
//
//impl ConstraintExpr for BoolExpr {
//    fn is_eq(&self) -> bool {
//        true
//    }
//
//    fn lhs(&self) -> Expr {
//        todo!()
//    }
//
//    fn rhs(&self) -> Expr {
//        todo!()
//    }
//}
//
//impl ExprLike for BoolExpr {}
