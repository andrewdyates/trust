// tRust #477: VC deduplication to avoid redundant solver calls.
//
// Many VCs for the same function or across functions may be structurally
// identical (up to variable renaming). This module provides:
// - Structural hashing of Formula and VerificationCondition
// - Alpha-equivalence normalization (rename bound variables canonically)
// - VcDeduplicator cache that maps fingerprints to prior solver results
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::hash::{Hash, Hasher};
use trust_types::fx::FxHashMap;

use trust_types::{Formula, Sort, VerificationCondition, VerificationResult};

// tRust #477: Discriminant tags for Formula variants used in structural hashing.
// These ensure different formula constructors produce different hashes even when
// their children hash the same.
const TAG_BOOL: u8 = 0;
const TAG_INT: u8 = 1;
const TAG_UINT: u8 = 2;
const TAG_BITVEC: u8 = 3;
const TAG_VAR: u8 = 4;
const TAG_NOT: u8 = 5;
const TAG_AND: u8 = 6;
const TAG_OR: u8 = 7;
const TAG_IMPLIES: u8 = 8;
const TAG_EQ: u8 = 9;
const TAG_LT: u8 = 10;
const TAG_LE: u8 = 11;
const TAG_GT: u8 = 12;
const TAG_GE: u8 = 13;
const TAG_ADD: u8 = 14;
const TAG_SUB: u8 = 15;
const TAG_MUL: u8 = 16;
const TAG_DIV: u8 = 17;
const TAG_REM: u8 = 18;
const TAG_NEG: u8 = 19;
const TAG_BV_ADD: u8 = 20;
const TAG_BV_SUB: u8 = 21;
const TAG_BV_MUL: u8 = 22;
const TAG_BV_UDIV: u8 = 23;
const TAG_BV_SDIV: u8 = 24;
const TAG_BV_UREM: u8 = 25;
const TAG_BV_SREM: u8 = 26;
const TAG_BV_AND: u8 = 27;
const TAG_BV_OR: u8 = 28;
const TAG_BV_XOR: u8 = 29;
const TAG_BV_NOT: u8 = 30;
const TAG_BV_SHL: u8 = 31;
const TAG_BV_LSHR: u8 = 32;
const TAG_BV_ASHR: u8 = 33;
const TAG_BV_ULT: u8 = 34;
const TAG_BV_ULE: u8 = 35;
const TAG_BV_SLT: u8 = 36;
const TAG_BV_SLE: u8 = 37;
const TAG_BV_TO_INT: u8 = 38;
const TAG_INT_TO_BV: u8 = 39;
const TAG_BV_EXTRACT: u8 = 40;
const TAG_BV_CONCAT: u8 = 41;
const TAG_BV_ZERO_EXT: u8 = 42;
const TAG_BV_SIGN_EXT: u8 = 43;
const TAG_ITE: u8 = 44;
const TAG_FORALL: u8 = 45;
const TAG_EXISTS: u8 = 46;
const TAG_SELECT: u8 = 47;
const TAG_STORE: u8 = 48;

/// tRust #477: Compute a structural fingerprint of a `Formula`.
///
/// Performs alpha-equivalence normalization before hashing: quantifier-bound
/// variables are renamed to canonical de Bruijn-style names (`__alpha_0`,
/// `__alpha_1`, ...) so that structurally identical formulas that differ only
/// in bound variable names produce the same fingerprint.
///
/// Free variables are hashed by their original names since they represent
/// semantically distinct program values.
#[must_use]
pub fn formula_fingerprint(f: &Formula) -> u64 {
    // tRust #477: Normalize bound variables for alpha-equivalence, then hash.
    let normalized = normalize_alpha(f);
    let mut hasher = std::hash::DefaultHasher::new();
    hash_formula(&normalized, &mut hasher);
    hasher.finish()
}

/// tRust #477: Compute a structural fingerprint of a `VerificationCondition`.
///
/// Combines the VcKind description (which encodes the kind, operation, and
/// types) with the formula fingerprint. Two VCs with the same kind and
/// structurally equivalent formulas will have the same fingerprint.
#[must_use]
pub fn vc_fingerprint(vc: &VerificationCondition) -> u64 {
    let mut hasher = std::hash::DefaultHasher::new();
    // tRust #477: Hash the kind description as a stable string representation.
    vc.kind.description().hash(&mut hasher);
    // tRust #477: Hash the formula structurally (with alpha-normalization).
    let normalized = normalize_alpha(&vc.formula);
    hash_formula(&normalized, &mut hasher);
    hasher.finish()
}

/// tRust #477: Cache for deduplicating VCs across solver calls.
///
/// Maps structural fingerprints to prior solver results so that identical
/// VCs are not sent to the solver multiple times.
#[derive(Debug, Default)]
pub struct VcDeduplicator {
    // tRust #477: Map from VC fingerprint to cached solver result.
    cache: FxHashMap<u64, VerificationResult>,
}

impl VcDeduplicator {
    /// Create a new empty deduplicator.
    #[must_use]
    pub fn new() -> Self {
        Self { cache: FxHashMap::default() }
    }

    /// Look up a cached result for a VC.
    ///
    /// Returns `Some(&VerificationResult)` if a structurally identical VC
    /// was previously recorded, `None` otherwise.
    #[must_use]
    pub fn check(&self, vc: &VerificationCondition) -> Option<&VerificationResult> {
        let fp = vc_fingerprint(vc);
        self.cache.get(&fp)
    }

    /// Record a solver result for a VC.
    ///
    /// Future calls to `check` with structurally identical VCs will return
    /// a reference to this result.
    pub fn record(&mut self, vc: &VerificationCondition, result: VerificationResult) {
        let fp = vc_fingerprint(vc);
        self.cache.insert(fp, result);
    }

    /// Number of cached entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.cache.len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.cache.is_empty()
    }

    /// Clear all cached entries.
    pub fn clear(&mut self) {
        self.cache.clear();
    }
}

// ---------------------------------------------------------------------------
// tRust #477: Alpha-equivalence normalization
// ---------------------------------------------------------------------------

/// tRust #477: Normalize bound variables to canonical names for alpha-equivalence.
///
/// Quantifier-bound variables are renamed to `__alpha_0`, `__alpha_1`, etc.
/// in order of first binding encounter. Free variables are left unchanged.
#[must_use]
pub(crate) fn normalize_alpha(f: &Formula) -> Formula {
    let mut counter = 0usize;
    let mut env: FxHashMap<String, String> = FxHashMap::default();
    normalize_inner(f, &mut env, &mut counter)
}

/// Recursive alpha-normalization with scoped environment.
fn normalize_inner(
    f: &Formula,
    env: &mut FxHashMap<String, String>,
    counter: &mut usize,
) -> Formula {
    match f {
        Formula::Var(name, sort) => {
            // tRust #477: Look up in environment for bound vars, else keep free name.
            let resolved = env.get(name).cloned().unwrap_or_else(|| name.clone());
            Formula::Var(resolved, sort.clone())
        }
        Formula::Forall(bindings, body) => normalize_quantifier(bindings, body, true, env, counter),
        Formula::Exists(bindings, body) => {
            normalize_quantifier(bindings, body, false, env, counter)
        }
        // tRust #477: For all other nodes, recursively normalize children.
        _ => normalize_structural(f, env, counter),
    }
}

/// Normalize a quantifier node (Forall or Exists).
fn normalize_quantifier(
    bindings: &[(trust_types::Symbol, Sort)],
    body: &Formula,
    is_forall: bool,
    env: &mut FxHashMap<String, String>,
    counter: &mut usize,
) -> Formula {
    // tRust #477: Save old bindings so we can restore after scope exit.
    let mut saved: Vec<(String, Option<String>)> = Vec::new();
    let mut new_bindings = Vec::new();

    for (name, sort) in bindings {
        let canonical = format!("__alpha_{counter}");
        *counter += 1;
        let name_str = name.to_string();
        saved.push((name_str.clone(), env.get(&name_str).cloned()));
        env.insert(name_str, canonical.clone());
        new_bindings.push((trust_types::Symbol::intern(&canonical), sort.clone()));
    }

    let new_body = normalize_inner(body, env, counter);

    // tRust #477: Restore previous bindings (important for nested quantifiers).
    for (name, old_val) in saved {
        match old_val {
            Some(v) => {
                env.insert(name, v);
            }
            None => {
                env.remove(&name);
            }
        }
    }

    if is_forall {
        Formula::Forall(new_bindings, Box::new(new_body))
    } else {
        Formula::Exists(new_bindings, Box::new(new_body))
    }
}

/// Normalize non-quantifier, non-variable nodes by rebuilding with normalized children.
fn normalize_structural(
    f: &Formula,
    env: &mut FxHashMap<String, String>,
    counter: &mut usize,
) -> Formula {
    match f {
        // Leaves with no sub-formulas.
        Formula::Bool(_)
        | Formula::Int(_)
        | Formula::UInt(_)
        | Formula::BitVec { .. }
        | Formula::Var(..) => f.clone(),

        Formula::Not(a) => Formula::Not(Box::new(normalize_inner(a, env, counter))),
        Formula::Neg(a) => Formula::Neg(Box::new(normalize_inner(a, env, counter))),

        Formula::And(terms) => {
            Formula::And(terms.iter().map(|t| normalize_inner(t, env, counter)).collect())
        }
        Formula::Or(terms) => {
            Formula::Or(terms.iter().map(|t| normalize_inner(t, env, counter)).collect())
        }

        Formula::Implies(a, b) => Formula::Implies(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Eq(a, b) => Formula::Eq(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Lt(a, b) => Formula::Lt(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Le(a, b) => Formula::Le(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Gt(a, b) => Formula::Gt(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Ge(a, b) => Formula::Ge(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Add(a, b) => Formula::Add(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Sub(a, b) => Formula::Sub(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Mul(a, b) => Formula::Mul(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Div(a, b) => Formula::Div(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Rem(a, b) => Formula::Rem(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),

        // Bitvector binary ops with width.
        Formula::BvAdd(a, b, w) => Formula::BvAdd(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvSub(a, b, w) => Formula::BvSub(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvMul(a, b, w) => Formula::BvMul(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvUDiv(a, b, w) => Formula::BvUDiv(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvSDiv(a, b, w) => Formula::BvSDiv(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvURem(a, b, w) => Formula::BvURem(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvSRem(a, b, w) => Formula::BvSRem(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvAnd(a, b, w) => Formula::BvAnd(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvOr(a, b, w) => Formula::BvOr(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvXor(a, b, w) => Formula::BvXor(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvShl(a, b, w) => Formula::BvShl(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvLShr(a, b, w) => Formula::BvLShr(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvAShr(a, b, w) => Formula::BvAShr(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),

        // Bitvector comparisons with width.
        Formula::BvULt(a, b, w) => Formula::BvULt(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvULe(a, b, w) => Formula::BvULe(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvSLt(a, b, w) => Formula::BvSLt(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvSLe(a, b, w) => Formula::BvSLe(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),

        // Bitvector unary / conversions.
        Formula::BvNot(a, w) => Formula::BvNot(Box::new(normalize_inner(a, env, counter)), *w),
        Formula::BvToInt(a, w, s) => {
            Formula::BvToInt(Box::new(normalize_inner(a, env, counter)), *w, *s)
        }
        Formula::IntToBv(a, w) => Formula::IntToBv(Box::new(normalize_inner(a, env, counter)), *w),
        Formula::BvExtract { inner, high, low } => Formula::BvExtract {
            inner: Box::new(normalize_inner(inner, env, counter)),
            high: *high,
            low: *low,
        },
        Formula::BvConcat(a, b) => Formula::BvConcat(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::BvZeroExt(a, bits) => {
            Formula::BvZeroExt(Box::new(normalize_inner(a, env, counter)), *bits)
        }
        Formula::BvSignExt(a, bits) => {
            Formula::BvSignExt(Box::new(normalize_inner(a, env, counter)), *bits)
        }

        // Ternary.
        Formula::Ite(cond, then_f, else_f) => Formula::Ite(
            Box::new(normalize_inner(cond, env, counter)),
            Box::new(normalize_inner(then_f, env, counter)),
            Box::new(normalize_inner(else_f, env, counter)),
        ),
        Formula::Store(arr, idx, val) => Formula::Store(
            Box::new(normalize_inner(arr, env, counter)),
            Box::new(normalize_inner(idx, env, counter)),
            Box::new(normalize_inner(val, env, counter)),
        ),

        // Arrays.
        Formula::Select(arr, idx) => Formula::Select(
            Box::new(normalize_inner(arr, env, counter)),
            Box::new(normalize_inner(idx, env, counter)),
        ),

        // Quantifiers handled in normalize_inner; unreachable here but safe.
        Formula::Forall(..) | Formula::Exists(..) => f.clone(),

        // tRust #477: Wildcard for #[non_exhaustive] — unknown variants are
        // cloned unchanged. This is sound: new variants will simply not be
        // alpha-normalized, which means they might not benefit from
        // deduplication but won't produce incorrect fingerprints.
        _ => f.clone(),
    }
}

// ---------------------------------------------------------------------------
// tRust #477: Structural hashing for Formula
// ---------------------------------------------------------------------------

/// tRust #477: Recursively hash a Formula into the given Hasher.
///
/// This produces a structural hash: two formulas that are syntactically
/// identical (after alpha-normalization) will hash to the same value.
/// The hashing uses discriminant tags to distinguish formula constructors.
fn hash_formula(f: &Formula, h: &mut impl Hasher) {
    match f {
        Formula::Bool(b) => {
            TAG_BOOL.hash(h);
            b.hash(h);
        }
        Formula::Int(n) => {
            TAG_INT.hash(h);
            n.hash(h);
        }
        Formula::UInt(n) => {
            TAG_UINT.hash(h);
            n.hash(h);
        }
        Formula::BitVec { value, width } => {
            TAG_BITVEC.hash(h);
            value.hash(h);
            width.hash(h);
        }
        Formula::Var(name, sort) => {
            TAG_VAR.hash(h);
            name.hash(h);
            sort.hash(h);
        }
        Formula::Not(a) => {
            TAG_NOT.hash(h);
            hash_formula(a, h);
        }
        Formula::And(terms) => {
            TAG_AND.hash(h);
            terms.len().hash(h);
            for t in terms {
                hash_formula(t, h);
            }
        }
        Formula::Or(terms) => {
            TAG_OR.hash(h);
            terms.len().hash(h);
            for t in terms {
                hash_formula(t, h);
            }
        }
        Formula::Implies(a, b) => {
            TAG_IMPLIES.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Eq(a, b) => {
            TAG_EQ.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Lt(a, b) => {
            TAG_LT.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Le(a, b) => {
            TAG_LE.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Gt(a, b) => {
            TAG_GT.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Ge(a, b) => {
            TAG_GE.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Add(a, b) => {
            TAG_ADD.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Sub(a, b) => {
            TAG_SUB.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Mul(a, b) => {
            TAG_MUL.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Div(a, b) => {
            TAG_DIV.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Rem(a, b) => {
            TAG_REM.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Neg(a) => {
            TAG_NEG.hash(h);
            hash_formula(a, h);
        }
        // Bitvector binary ops.
        Formula::BvAdd(a, b, w) => {
            TAG_BV_ADD.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvSub(a, b, w) => {
            TAG_BV_SUB.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvMul(a, b, w) => {
            TAG_BV_MUL.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvUDiv(a, b, w) => {
            TAG_BV_UDIV.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvSDiv(a, b, w) => {
            TAG_BV_SDIV.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvURem(a, b, w) => {
            TAG_BV_UREM.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvSRem(a, b, w) => {
            TAG_BV_SREM.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvAnd(a, b, w) => {
            TAG_BV_AND.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvOr(a, b, w) => {
            TAG_BV_OR.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvXor(a, b, w) => {
            TAG_BV_XOR.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvShl(a, b, w) => {
            TAG_BV_SHL.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvLShr(a, b, w) => {
            TAG_BV_LSHR.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvAShr(a, b, w) => {
            TAG_BV_ASHR.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        // Bitvector comparisons.
        Formula::BvULt(a, b, w) => {
            TAG_BV_ULT.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvULe(a, b, w) => {
            TAG_BV_ULE.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvSLt(a, b, w) => {
            TAG_BV_SLT.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvSLe(a, b, w) => {
            TAG_BV_SLE.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        // Bitvector unary / conversions.
        Formula::BvNot(a, w) => {
            TAG_BV_NOT.hash(h);
            w.hash(h);
            hash_formula(a, h);
        }
        Formula::BvToInt(a, w, signed) => {
            TAG_BV_TO_INT.hash(h);
            w.hash(h);
            signed.hash(h);
            hash_formula(a, h);
        }
        Formula::IntToBv(a, w) => {
            TAG_INT_TO_BV.hash(h);
            w.hash(h);
            hash_formula(a, h);
        }
        Formula::BvExtract { inner, high, low } => {
            TAG_BV_EXTRACT.hash(h);
            high.hash(h);
            low.hash(h);
            hash_formula(inner, h);
        }
        Formula::BvConcat(a, b) => {
            TAG_BV_CONCAT.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::BvZeroExt(a, bits) => {
            TAG_BV_ZERO_EXT.hash(h);
            bits.hash(h);
            hash_formula(a, h);
        }
        Formula::BvSignExt(a, bits) => {
            TAG_BV_SIGN_EXT.hash(h);
            bits.hash(h);
            hash_formula(a, h);
        }
        // Ternary.
        Formula::Ite(cond, then_f, else_f) => {
            TAG_ITE.hash(h);
            hash_formula(cond, h);
            hash_formula(then_f, h);
            hash_formula(else_f, h);
        }
        Formula::Store(arr, idx, val) => {
            TAG_STORE.hash(h);
            hash_formula(arr, h);
            hash_formula(idx, h);
            hash_formula(val, h);
        }
        // Arrays.
        Formula::Select(arr, idx) => {
            TAG_SELECT.hash(h);
            hash_formula(arr, h);
            hash_formula(idx, h);
        }
        // Quantifiers.
        Formula::Forall(bindings, body) => {
            TAG_FORALL.hash(h);
            hash_bindings(bindings, h);
            hash_formula(body, h);
        }
        Formula::Exists(bindings, body) => {
            TAG_EXISTS.hash(h);
            hash_bindings(bindings, h);
            hash_formula(body, h);
        }
        // tRust #477: Wildcard for #[non_exhaustive] — unknown variants are
        // hashed by their Debug representation as a fallback. This ensures
        // they still produce deterministic fingerprints even if new Formula
        // variants are added without updating this match.
        other => {
            255u8.hash(h);
            format!("{other:?}").hash(h);
        }
    }
}

/// Hash a bitvector binary operation (two sub-formulas + width).
fn hash_bv_binary(a: &Formula, b: &Formula, w: u32, h: &mut impl Hasher) {
    w.hash(h);
    hash_formula(a, h);
    hash_formula(b, h);
}

/// Hash quantifier bindings (name, sort pairs).
fn hash_bindings(bindings: &[(trust_types::Symbol, Sort)], h: &mut impl Hasher) {
    bindings.len().hash(h);
    for (name, sort) in bindings {
        name.hash(h);
        sort.hash(h);
    }
}

// ---------------------------------------------------------------------------
// tRust #477: Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{Formula, ProofStrength, Sort, SourceSpan, VcKind, VerificationResult};

    /// Helper: build a variable formula.
    fn var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    /// Helper: build a basic VC with the given kind and formula.
    fn make_vc(kind: VcKind, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    /// Helper: build a Proved result.
    fn proved() -> VerificationResult {
        VerificationResult::Proved {
            solver: "z4".into(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        }
    }

    #[test]
    fn test_formula_fingerprint_identical_formulas_same_hash() {
        let f1 = Formula::Add(Box::new(var("x")), Box::new(Formula::Int(1)));
        let f2 = Formula::Add(Box::new(var("x")), Box::new(Formula::Int(1)));
        assert_eq!(formula_fingerprint(&f1), formula_fingerprint(&f2));
    }

    #[test]
    fn test_formula_fingerprint_different_formulas_different_hash() {
        let f1 = Formula::Add(Box::new(var("x")), Box::new(Formula::Int(1)));
        let f2 = Formula::Sub(Box::new(var("x")), Box::new(Formula::Int(1)));
        assert_ne!(formula_fingerprint(&f1), formula_fingerprint(&f2));
    }

    #[test]
    fn test_formula_fingerprint_different_vars_different_hash() {
        let f1 = Formula::Add(Box::new(var("x")), Box::new(Formula::Int(1)));
        let f2 = Formula::Add(Box::new(var("y")), Box::new(Formula::Int(1)));
        // Free variables have different names, so fingerprints differ.
        assert_ne!(formula_fingerprint(&f1), formula_fingerprint(&f2));
    }

    #[test]
    fn test_formula_fingerprint_alpha_equivalence_forall() {
        // forall x: Int. x > 0  vs  forall y: Int. y > 0
        let f1 = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)))),
        );
        let f2 = Formula::Forall(
            vec![("y".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(0)))),
        );
        assert_eq!(
            formula_fingerprint(&f1),
            formula_fingerprint(&f2),
            "alpha-equivalent formulas must have the same fingerprint"
        );
    }

    #[test]
    fn test_formula_fingerprint_alpha_equivalence_exists() {
        // exists a: Int. a = 42  vs  exists b: Int. b = 42
        let f1 = Formula::Exists(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(42)))),
        );
        let f2 = Formula::Exists(
            vec![("b".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("b")), Box::new(Formula::Int(42)))),
        );
        assert_eq!(
            formula_fingerprint(&f1),
            formula_fingerprint(&f2),
            "alpha-equivalent exists formulas must have the same fingerprint"
        );
    }

    #[test]
    fn test_formula_fingerprint_nested_quantifiers_alpha() {
        // forall x. exists y. x < y  vs  forall a. exists b. a < b
        let f1 = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Exists(
                vec![("y".into(), Sort::Int)],
                Box::new(Formula::Lt(Box::new(var("x")), Box::new(var("y")))),
            )),
        );
        let f2 = Formula::Forall(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Exists(
                vec![("b".into(), Sort::Int)],
                Box::new(Formula::Lt(Box::new(var("a")), Box::new(var("b")))),
            )),
        );
        assert_eq!(
            formula_fingerprint(&f1),
            formula_fingerprint(&f2),
            "nested quantifiers with alpha-renamed bound vars must match"
        );
    }

    #[test]
    fn test_formula_fingerprint_leaf_types_distinguished() {
        // Bool(true) vs Int(1) -- different tags.
        let f1 = Formula::Bool(true);
        let f2 = Formula::Int(1);
        assert_ne!(formula_fingerprint(&f1), formula_fingerprint(&f2));
    }

    #[test]
    fn test_vc_fingerprint_same_kind_same_formula() {
        let vc1 = make_vc(
            VcKind::DivisionByZero,
            Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0))),
        );
        let vc2 = make_vc(
            VcKind::DivisionByZero,
            Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0))),
        );
        assert_eq!(vc_fingerprint(&vc1), vc_fingerprint(&vc2));
    }

    #[test]
    fn test_vc_fingerprint_different_kind_same_formula() {
        let formula = Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0)));
        let vc1 = make_vc(VcKind::DivisionByZero, formula.clone());
        let vc2 = make_vc(VcKind::RemainderByZero, formula);
        assert_ne!(
            vc_fingerprint(&vc1),
            vc_fingerprint(&vc2),
            "different VcKind must produce different fingerprints"
        );
    }

    #[test]
    fn test_deduplicator_check_miss_returns_none() {
        let dedup = VcDeduplicator::new();
        let vc = make_vc(VcKind::DivisionByZero, Formula::Bool(true));
        assert!(dedup.check(&vc).is_none());
    }

    #[test]
    fn test_deduplicator_record_then_check_hit() {
        let mut dedup = VcDeduplicator::new();
        let vc = make_vc(VcKind::DivisionByZero, Formula::Bool(true));
        let result = proved();
        dedup.record(&vc, result);

        // Same VC should hit.
        let hit = dedup.check(&vc);
        assert!(hit.is_some());
        assert!(hit.unwrap().is_proved());
    }

    #[test]
    fn test_deduplicator_structurally_identical_vc_hits() {
        let mut dedup = VcDeduplicator::new();
        let vc1 = make_vc(
            VcKind::DivisionByZero,
            Formula::Eq(Box::new(var("b")), Box::new(Formula::Int(0))),
        );
        dedup.record(&vc1, proved());

        // Build an identical VC separately.
        let vc2 = make_vc(
            VcKind::DivisionByZero,
            Formula::Eq(Box::new(var("b")), Box::new(Formula::Int(0))),
        );
        assert!(dedup.check(&vc2).is_some(), "structurally identical VC must hit cache");
    }

    #[test]
    fn test_deduplicator_different_formula_misses() {
        let mut dedup = VcDeduplicator::new();
        let vc1 = make_vc(
            VcKind::DivisionByZero,
            Formula::Eq(Box::new(var("b")), Box::new(Formula::Int(0))),
        );
        dedup.record(&vc1, proved());

        let vc2 = make_vc(
            VcKind::DivisionByZero,
            Formula::Eq(Box::new(var("c")), Box::new(Formula::Int(0))),
        );
        assert!(dedup.check(&vc2).is_none(), "different free var name must miss");
    }

    #[test]
    fn test_deduplicator_len_and_clear() {
        let mut dedup = VcDeduplicator::new();
        assert_eq!(dedup.len(), 0);
        assert!(dedup.is_empty());

        dedup.record(&make_vc(VcKind::DivisionByZero, Formula::Bool(true)), proved());
        assert_eq!(dedup.len(), 1);
        assert!(!dedup.is_empty());

        dedup.clear();
        assert_eq!(dedup.len(), 0);
        assert!(dedup.is_empty());
    }

    #[test]
    fn test_normalize_alpha_free_vars_unchanged() {
        let f = Formula::Add(Box::new(var("x")), Box::new(var("y")));
        let normalized = normalize_alpha(&f);
        // Free vars should remain unchanged.
        assert_eq!(normalized, f);
    }

    #[test]
    fn test_normalize_alpha_bound_vars_renamed() {
        let f = Formula::Forall(
            vec![("my_var".into(), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Var("my_var".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        let normalized = normalize_alpha(&f);
        match &normalized {
            Formula::Forall(bindings, body) => {
                assert_eq!(bindings[0].0, "__alpha_0");
                match body.as_ref() {
                    Formula::Gt(lhs, _) => {
                        assert_eq!(**lhs, Formula::Var("__alpha_0".into(), Sort::Int));
                    }
                    other => panic!("expected Gt, got: {other:?}"),
                }
            }
            other => panic!("expected Forall, got: {other:?}"),
        }
    }

    #[test]
    fn test_normalize_alpha_preserves_sorts() {
        let bv_sort = Sort::BitVec(32);
        let f = Formula::Forall(
            vec![("v".into(), bv_sort.clone())],
            Box::new(Formula::Var("v".into(), bv_sort.clone())),
        );
        let normalized = normalize_alpha(&f);
        match &normalized {
            Formula::Forall(bindings, body) => {
                assert_eq!(bindings[0].1, bv_sort);
                match body.as_ref() {
                    Formula::Var(_, sort) => assert_eq!(*sort, bv_sort),
                    other => panic!("expected Var, got: {other:?}"),
                }
            }
            other => panic!("expected Forall, got: {other:?}"),
        }
    }

    #[test]
    fn test_formula_fingerprint_bitvec_ops_distinguished() {
        let a = Formula::Var("a".into(), Sort::BitVec(32));
        let b = Formula::Var("b".into(), Sort::BitVec(32));
        let f_add = Formula::BvAdd(Box::new(a.clone()), Box::new(b.clone()), 32);
        let f_sub = Formula::BvSub(Box::new(a), Box::new(b), 32);
        assert_ne!(
            formula_fingerprint(&f_add),
            formula_fingerprint(&f_sub),
            "BvAdd and BvSub must produce different fingerprints"
        );
    }

    #[test]
    fn test_formula_fingerprint_ite() {
        let f = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(0)),
        );
        // Just check it does not panic and produces a deterministic value.
        let fp1 = formula_fingerprint(&f);
        let fp2 = formula_fingerprint(&f);
        assert_eq!(fp1, fp2);
    }

    #[test]
    fn test_formula_fingerprint_array_ops() {
        let arr = Formula::Var("arr".into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
        let sel = Formula::Select(Box::new(arr.clone()), Box::new(Formula::Int(0)));
        let sto =
            Formula::Store(Box::new(arr), Box::new(Formula::Int(0)), Box::new(Formula::Int(42)));
        assert_ne!(
            formula_fingerprint(&sel),
            formula_fingerprint(&sto),
            "Select and Store must produce different fingerprints"
        );
    }
}
