// trust-types/formula/smtlib: SMT-LIB2 text serialization for Formula
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::Formula;

impl Formula {
    /// Convert this Formula to its SMT-LIB2 text representation.
    ///
    /// This is the canonical serializer used by all crates (trust-router,
    /// trust-vcgen, trust-cegar). Covers every Formula variant.
    #[must_use]
    pub fn to_smtlib(&self) -> String {
        match self {
            // Literals
            Formula::Bool(true) => "true".to_string(),
            Formula::Bool(false) => "false".to_string(),
            Formula::UInt(n) => n.to_string(),
            Formula::Int(n) => {
                if *n < 0 {
                    let abs = n.unsigned_abs();
                    format!("(- {abs})")
                } else {
                    n.to_string()
                }
            }
            Formula::BitVec { value, width } => {
                if *value >= 0 {
                    format!("(_ bv{value} {width})")
                } else {
                    // tRust #752: Use u128 for two's complement to handle width=128 correctly.
                    // i128 mask overflows at width=128; u128::MAX is the correct all-ones mask.
                    let mask: u128 = if *width < 128 { (1u128 << width) - 1 } else { u128::MAX };
                    let twos_comp = (*value as u128) & mask;
                    format!("(_ bv{twos_comp} {width})")
                }
            }

            // Variables
            Formula::Var(name, _sort) => name.clone(),
            Formula::SymVar(sym, _sort) => sym.as_str().to_string(),

            // Boolean connectives
            Formula::Not(inner) => format!("(not {})", inner.to_smtlib()),
            Formula::And(terms) => {
                if terms.is_empty() {
                    "true".to_string()
                } else if terms.len() == 1 {
                    terms[0].to_smtlib()
                } else {
                    let parts: Vec<String> = terms.iter().map(|t| t.to_smtlib()).collect();
                    format!("(and {})", parts.join(" "))
                }
            }
            Formula::Or(terms) => {
                if terms.is_empty() {
                    "false".to_string()
                } else if terms.len() == 1 {
                    terms[0].to_smtlib()
                } else {
                    let parts: Vec<String> = terms.iter().map(|t| t.to_smtlib()).collect();
                    format!("(or {})", parts.join(" "))
                }
            }
            Formula::Implies(a, b) => {
                format!("(=> {} {})", a.to_smtlib(), b.to_smtlib())
            }

            // Comparisons
            Formula::Eq(a, b) => format!("(= {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::Lt(a, b) => format!("(< {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::Le(a, b) => format!("(<= {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::Gt(a, b) => format!("(> {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::Ge(a, b) => format!("(>= {} {})", a.to_smtlib(), b.to_smtlib()),

            // Integer arithmetic
            Formula::Add(a, b) => format!("(+ {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::Sub(a, b) => format!("(- {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::Mul(a, b) => format!("(* {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::Div(a, b) => format!("(div {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::Rem(a, b) => format!("(mod {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::Neg(inner) => format!("(- {})", inner.to_smtlib()),

            // Bitvector arithmetic
            Formula::BvAdd(a, b, _) => format!("(bvadd {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvSub(a, b, _) => format!("(bvsub {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvMul(a, b, _) => format!("(bvmul {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvUDiv(a, b, _) => format!("(bvudiv {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvSDiv(a, b, _) => format!("(bvsdiv {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvURem(a, b, _) => format!("(bvurem {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvSRem(a, b, _) => format!("(bvsrem {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvAnd(a, b, _) => format!("(bvand {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvOr(a, b, _) => format!("(bvor {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvXor(a, b, _) => format!("(bvxor {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvNot(inner, _) => format!("(bvnot {})", inner.to_smtlib()),
            Formula::BvShl(a, b, _) => format!("(bvshl {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvLShr(a, b, _) => format!("(bvlshr {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvAShr(a, b, _) => format!("(bvashr {} {})", a.to_smtlib(), b.to_smtlib()),

            // Bitvector comparisons
            Formula::BvULt(a, b, _) => format!("(bvult {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvULe(a, b, _) => format!("(bvule {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvSLt(a, b, _) => format!("(bvslt {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvSLe(a, b, _) => format!("(bvsle {} {})", a.to_smtlib(), b.to_smtlib()),

            // Bitvector conversions
            Formula::BvToInt(inner, width, signed) => {
                let inner_smt = inner.to_smtlib();
                if *signed {
                    let two_to_width = 1u128 << width;
                    format!(
                        "(ite (bvsge {inner_smt} (_ bv0 {width})) \
                         (bv2int {inner_smt}) \
                         (- (bv2int {inner_smt}) {two_to_width}))"
                    )
                } else {
                    format!("(bv2int {inner_smt})")
                }
            }
            Formula::IntToBv(inner, width) => {
                format!("((_ int2bv {width}) {})", inner.to_smtlib())
            }
            Formula::BvExtract { inner, high, low } => {
                format!("((_ extract {high} {low}) {})", inner.to_smtlib())
            }
            Formula::BvConcat(a, b) => format!("(concat {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvZeroExt(inner, bits) => {
                format!("((_ zero_extend {bits}) {})", inner.to_smtlib())
            }
            Formula::BvSignExt(inner, bits) => {
                format!("((_ sign_extend {bits}) {})", inner.to_smtlib())
            }

            // Conditional
            Formula::Ite(cond, then, els) => {
                format!("(ite {} {} {})", cond.to_smtlib(), then.to_smtlib(), els.to_smtlib())
            }

            // Quantifiers
            Formula::Forall(bindings, body) => {
                let params: Vec<String> = bindings
                    .iter()
                    .map(|(name, sort)| format!("({name} {})", sort.to_smtlib()))
                    .collect();
                format!("(forall ({}) {})", params.join(" "), body.to_smtlib())
            }
            Formula::Exists(bindings, body) => {
                let params: Vec<String> = bindings
                    .iter()
                    .map(|(name, sort)| format!("({name} {})", sort.to_smtlib()))
                    .collect();
                format!("(exists ({}) {})", params.join(" "), body.to_smtlib())
            }

            // Arrays
            Formula::Select(arr, idx) => {
                format!("(select {} {})", arr.to_smtlib(), idx.to_smtlib())
            }
            Formula::Store(arr, idx, val) => {
                format!("(store {} {} {})", arr.to_smtlib(), idx.to_smtlib(), val.to_smtlib())
            }
        }
    }
}
