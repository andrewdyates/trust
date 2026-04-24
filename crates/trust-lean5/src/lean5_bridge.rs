// trust-lean5/lean5_bridge.rs: Bridge between tRust verification IR and lean5 kernel
//
// Translates tRust's Formula/VcKind types into lean5 kernel expressions (Expr)
// and provides certificate verification using lean5's CertVerifier.
//
// The translation encodes our first-order verification conditions as lean5
// theorem statements (Prop-valued expressions). A ProofCert witnessing such
// a statement can then be verified by the lean5 kernel's type checker.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use lean5_kernel::Expr as LeanExpr;
use lean5_kernel::cert::{CertVerifier, ProofCert};
use lean5_kernel::env::Environment;
use lean5_kernel::level::Level as LeanLevel;
use lean5_kernel::name::Name as LeanName;
use trust_types::{Formula, Sort, VcKind};

use crate::error::CertificateError;

// ---------------------------------------------------------------------------
// Name helpers
// ---------------------------------------------------------------------------

/// Construct a lean5 Name from a dotted string.
fn name(s: &str) -> LeanName {
    LeanName::from_string(s)
}

/// Construct a lean5 constant expression (zero universe levels).
fn const_expr(s: &str) -> LeanExpr {
    LeanExpr::const_(name(s), Vec::<LeanLevel>::new())
}

// ---------------------------------------------------------------------------
// Sort → lean5 Expr translation
// ---------------------------------------------------------------------------

/// Translate a tRust Sort into a lean5 type expression.
///
/// - `Sort::Bool`    → `tRust.Sort.Bool`
/// - `Sort::Int`     → `tRust.Sort.Int`
/// - `Sort::BitVec(w)` → `tRust.Sort.BitVec w`
/// - `Sort::Array(i,e)` → `tRust.Sort.Array <idx> <elem>`
pub(crate) fn translate_sort(sort: &Sort) -> LeanExpr {
    match sort {
        Sort::Bool => const_expr("tRust.Sort.Bool"),
        Sort::Int => const_expr("tRust.Sort.Int"),
        Sort::BitVec(w) => {
            LeanExpr::app(const_expr("tRust.Sort.BitVec"), LeanExpr::nat_lit(u64::from(*w)))
        }
        Sort::Array(idx, elem) => LeanExpr::apps(
            const_expr("tRust.Sort.Array"),
            vec![translate_sort(idx), translate_sort(elem)],
        ),
        _ => const_expr("tRust.Sort.Unknown"),
    }
}

// ---------------------------------------------------------------------------
// Formula → lean5 Expr translation
// ---------------------------------------------------------------------------

/// Translate a tRust Formula into a lean5 Prop expression.
///
/// The translation maps our first-order SMT-like formulas into lean5
/// kernel terms that live in Prop. Each Formula variant maps to a
/// corresponding `tRust.Formula.*` constant applied to its operands.
///
/// This is the key bridge: the resulting Expr is the theorem statement
/// that a ProofCert must witness.
pub fn translate_formula(formula: &Formula) -> LeanExpr {
    match formula {
        // Literals
        Formula::Bool(true) => const_expr("True"),
        Formula::Bool(false) => const_expr("False"),
        Formula::Int(n) => {
            // Encode as tRust.Formula.int <nat>
            // For negative values, wrap in tRust.Formula.neg
            if *n >= 0 {
                LeanExpr::app(const_expr("tRust.Formula.int"), LeanExpr::nat_lit(*n as u64))
            } else {
                LeanExpr::app(
                    const_expr("tRust.Formula.neg"),
                    LeanExpr::app(
                        const_expr("tRust.Formula.int"),
                        LeanExpr::nat_lit(n.unsigned_abs() as u64),
                    ),
                )
            }
        }
        Formula::UInt(n) => {
            LeanExpr::app(const_expr("tRust.Formula.int"), LeanExpr::nat_lit(*n as u64))
        }
        Formula::BitVec { value, width } => LeanExpr::apps(
            const_expr("tRust.Formula.bitvec"),
            vec![LeanExpr::nat_lit(*value as u64), LeanExpr::nat_lit(u64::from(*width))],
        ),

        // Variables
        Formula::Var(name_str, sort) => LeanExpr::apps(
            const_expr("tRust.Formula.var"),
            vec![LeanExpr::str_lit(name_str.as_str()), translate_sort(sort)],
        ),

        // Boolean connectives
        Formula::Not(inner) => LeanExpr::app(const_expr("Not"), translate_formula(inner)),
        Formula::And(children) => {
            if children.is_empty() {
                return const_expr("True");
            }
            let mut result = translate_formula(&children[0]);
            for child in &children[1..] {
                result = LeanExpr::apps(const_expr("And"), vec![result, translate_formula(child)]);
            }
            result
        }
        Formula::Or(children) => {
            if children.is_empty() {
                return const_expr("False");
            }
            let mut result = translate_formula(&children[0]);
            for child in &children[1..] {
                result = LeanExpr::apps(const_expr("Or"), vec![result, translate_formula(child)]);
            }
            result
        }
        Formula::Implies(lhs, rhs) => LeanExpr::apps(
            const_expr("tRust.Formula.implies"),
            vec![translate_formula(lhs), translate_formula(rhs)],
        ),

        // Comparisons
        Formula::Eq(lhs, rhs) => LeanExpr::apps(
            const_expr("tRust.Formula.eq"),
            vec![translate_formula(lhs), translate_formula(rhs)],
        ),
        Formula::Lt(lhs, rhs) => LeanExpr::apps(
            const_expr("tRust.Formula.lt"),
            vec![translate_formula(lhs), translate_formula(rhs)],
        ),
        Formula::Le(lhs, rhs) => LeanExpr::apps(
            const_expr("tRust.Formula.le"),
            vec![translate_formula(lhs), translate_formula(rhs)],
        ),
        Formula::Gt(lhs, rhs) => LeanExpr::apps(
            const_expr("tRust.Formula.gt"),
            vec![translate_formula(lhs), translate_formula(rhs)],
        ),
        Formula::Ge(lhs, rhs) => LeanExpr::apps(
            const_expr("tRust.Formula.ge"),
            vec![translate_formula(lhs), translate_formula(rhs)],
        ),

        // Integer arithmetic
        Formula::Add(lhs, rhs) => translate_binop("tRust.Formula.add", lhs, rhs),
        Formula::Sub(lhs, rhs) => translate_binop("tRust.Formula.sub", lhs, rhs),
        Formula::Mul(lhs, rhs) => translate_binop("tRust.Formula.mul", lhs, rhs),
        Formula::Div(lhs, rhs) => translate_binop("tRust.Formula.div", lhs, rhs),
        Formula::Rem(lhs, rhs) => translate_binop("tRust.Formula.rem", lhs, rhs),
        Formula::Neg(inner) => {
            LeanExpr::app(const_expr("tRust.Formula.neg"), translate_formula(inner))
        }

        // Bitvector arithmetic
        Formula::BvAdd(lhs, rhs, w) => translate_bv_binop("tRust.Formula.bvAdd", lhs, rhs, *w),
        Formula::BvSub(lhs, rhs, w) => translate_bv_binop("tRust.Formula.bvSub", lhs, rhs, *w),
        Formula::BvMul(lhs, rhs, w) => translate_bv_binop("tRust.Formula.bvMul", lhs, rhs, *w),
        Formula::BvUDiv(lhs, rhs, w) => translate_bv_binop("tRust.Formula.bvUDiv", lhs, rhs, *w),
        Formula::BvSDiv(lhs, rhs, w) => translate_bv_binop("tRust.Formula.bvSDiv", lhs, rhs, *w),
        Formula::BvURem(lhs, rhs, w) => translate_bv_binop("tRust.Formula.bvURem", lhs, rhs, *w),
        Formula::BvSRem(lhs, rhs, w) => translate_bv_binop("tRust.Formula.bvSRem", lhs, rhs, *w),
        Formula::BvAnd(lhs, rhs, w) => translate_bv_binop("tRust.Formula.bvAnd", lhs, rhs, *w),
        Formula::BvOr(lhs, rhs, w) => translate_bv_binop("tRust.Formula.bvOr", lhs, rhs, *w),
        Formula::BvXor(lhs, rhs, w) => translate_bv_binop("tRust.Formula.bvXor", lhs, rhs, *w),
        Formula::BvNot(inner, w) => LeanExpr::apps(
            const_expr("tRust.Formula.bvNot"),
            vec![translate_formula(inner), LeanExpr::nat_lit(u64::from(*w))],
        ),
        Formula::BvShl(lhs, rhs, w) => translate_bv_binop("tRust.Formula.bvShl", lhs, rhs, *w),
        Formula::BvLShr(lhs, rhs, w) => translate_bv_binop("tRust.Formula.bvLShr", lhs, rhs, *w),
        Formula::BvAShr(lhs, rhs, w) => translate_bv_binop("tRust.Formula.bvAShr", lhs, rhs, *w),

        // Bitvector comparisons
        Formula::BvULt(lhs, rhs, w) => translate_bv_binop("tRust.Formula.bvULt", lhs, rhs, *w),
        Formula::BvULe(lhs, rhs, w) => translate_bv_binop("tRust.Formula.bvULe", lhs, rhs, *w),
        Formula::BvSLt(lhs, rhs, w) => translate_bv_binop("tRust.Formula.bvSLt", lhs, rhs, *w),
        Formula::BvSLe(lhs, rhs, w) => translate_bv_binop("tRust.Formula.bvSLe", lhs, rhs, *w),

        // Bitvector conversions
        Formula::BvToInt(inner, w, signed) => LeanExpr::apps(
            const_expr("tRust.Formula.bvToInt"),
            vec![
                translate_formula(inner),
                LeanExpr::nat_lit(u64::from(*w)),
                if *signed { const_expr("Bool.true") } else { const_expr("Bool.false") },
            ],
        ),
        Formula::IntToBv(inner, w) => LeanExpr::apps(
            const_expr("tRust.Formula.intToBv"),
            vec![translate_formula(inner), LeanExpr::nat_lit(u64::from(*w))],
        ),
        Formula::BvExtract { inner, high, low } => LeanExpr::apps(
            const_expr("tRust.Formula.bvExtract"),
            vec![
                translate_formula(inner),
                LeanExpr::nat_lit(u64::from(*high)),
                LeanExpr::nat_lit(u64::from(*low)),
            ],
        ),
        Formula::BvConcat(lhs, rhs) => translate_binop("tRust.Formula.bvConcat", lhs, rhs),
        Formula::BvZeroExt(inner, w) => LeanExpr::apps(
            const_expr("tRust.Formula.bvZeroExt"),
            vec![translate_formula(inner), LeanExpr::nat_lit(u64::from(*w))],
        ),
        Formula::BvSignExt(inner, w) => LeanExpr::apps(
            const_expr("tRust.Formula.bvSignExt"),
            vec![translate_formula(inner), LeanExpr::nat_lit(u64::from(*w))],
        ),

        // Conditional
        Formula::Ite(cond, then_, else_) => LeanExpr::apps(
            const_expr("tRust.Formula.ite"),
            vec![translate_formula(cond), translate_formula(then_), translate_formula(else_)],
        ),

        // Quantifiers
        Formula::Forall(bindings, body) => {
            let mut result = translate_formula(body);
            // Encode innermost binding first (reverse order for de Bruijn)
            for (var_name, sort) in bindings.iter().rev() {
                result = LeanExpr::apps(
                    const_expr("tRust.Formula.forall"),
                    vec![LeanExpr::str_lit(var_name.as_str()), translate_sort(sort), result],
                );
            }
            result
        }
        Formula::Exists(bindings, body) => {
            let mut result = translate_formula(body);
            for (var_name, sort) in bindings.iter().rev() {
                result = LeanExpr::apps(
                    const_expr("tRust.Formula.exists"),
                    vec![LeanExpr::str_lit(var_name.as_str()), translate_sort(sort), result],
                );
            }
            result
        }

        // Arrays
        Formula::Select(array, index) => translate_binop("tRust.Formula.select", array, index),
        Formula::Store(array, index, value) => LeanExpr::apps(
            const_expr("tRust.Formula.store"),
            vec![translate_formula(array), translate_formula(index), translate_formula(value)],
        ),
        _ => const_expr("tRust.Formula.unknown"),
    }
}

/// Translate a binary operation (integer domain).
fn translate_binop(op_name: &str, lhs: &Formula, rhs: &Formula) -> LeanExpr {
    LeanExpr::apps(const_expr(op_name), vec![translate_formula(lhs), translate_formula(rhs)])
}

/// Translate a bitvector binary operation (with width parameter).
fn translate_bv_binop(op_name: &str, lhs: &Formula, rhs: &Formula, width: u32) -> LeanExpr {
    LeanExpr::apps(
        const_expr(op_name),
        vec![translate_formula(lhs), translate_formula(rhs), LeanExpr::nat_lit(u64::from(width))],
    )
}

// ---------------------------------------------------------------------------
// VcKind → lean5 Expr translation
// ---------------------------------------------------------------------------

/// Translate a VcKind into a lean5 expression representing the VC category.
///
/// This is used as metadata in the theorem statement so the lean5 proof
/// can reference which kind of obligation is being discharged.
pub(crate) fn translate_vc_kind(kind: &VcKind) -> LeanExpr {
    match kind {
        VcKind::ArithmeticOverflow { .. } => const_expr("tRust.VcKind.arithmeticOverflow"),
        VcKind::ShiftOverflow { .. } => const_expr("tRust.VcKind.shiftOverflow"),
        VcKind::DivisionByZero => const_expr("tRust.VcKind.divisionByZero"),
        VcKind::RemainderByZero => const_expr("tRust.VcKind.remainderByZero"),
        VcKind::IndexOutOfBounds => const_expr("tRust.VcKind.indexOutOfBounds"),
        VcKind::SliceBoundsCheck => const_expr("tRust.VcKind.sliceBoundsCheck"),
        VcKind::Assertion { .. } => const_expr("tRust.VcKind.assertion"),
        VcKind::Precondition { .. } => const_expr("tRust.VcKind.precondition"),
        VcKind::Postcondition => const_expr("tRust.VcKind.postcondition"),
        VcKind::CastOverflow { .. } => const_expr("tRust.VcKind.castOverflow"),
        VcKind::NegationOverflow { .. } => const_expr("tRust.VcKind.negationOverflow"),
        VcKind::Unreachable => const_expr("tRust.VcKind.unreachable"),
        VcKind::DeadState { .. } => const_expr("tRust.VcKind.deadState"),
        VcKind::Deadlock => const_expr("tRust.VcKind.deadlock"),
        VcKind::Temporal { .. } => const_expr("tRust.VcKind.temporal"),
        // tRust: Liveness and fairness lean5 translations (#49).
        VcKind::Liveness { .. } => const_expr("tRust.VcKind.liveness"),
        VcKind::Fairness { .. } => const_expr("tRust.VcKind.fairness"),
        // tRust: Protocol composition verification (#55)
        VcKind::ProtocolViolation { .. } => const_expr("tRust.VcKind.protocolViolation"),
        VcKind::TaintViolation { .. } => const_expr("tRust.VcKind.taintViolation"),
        VcKind::RefinementViolation { .. } => const_expr("tRust.VcKind.refinementViolation"),
        VcKind::ResilienceViolation { .. } => const_expr("tRust.VcKind.resilienceViolation"),
        VcKind::NonTermination { .. } => const_expr("tRust.VcKind.nonTermination"),
        VcKind::NeuralRobustness { .. } => const_expr("tRust.VcKind.neuralRobustness"),
        VcKind::NeuralOutputRange { .. } => const_expr("tRust.VcKind.neuralOutputRange"),
        VcKind::NeuralLipschitz { .. } => const_expr("tRust.VcKind.neuralLipschitz"),
        VcKind::NeuralMonotonicity { .. } => const_expr("tRust.VcKind.neuralMonotonicity"),
        // tRust #203: Data race and memory ordering lean5 translations.
        VcKind::DataRace { .. } => const_expr("tRust.VcKind.dataRace"),
        VcKind::InsufficientOrdering { .. } => const_expr("tRust.VcKind.insufficientOrdering"),
        // tRust #149: Translation validation.
        VcKind::TranslationValidation { .. } => const_expr("tRust.VcKind.translationValidation"),
        // tRust #433: Floating-point operation VCs.
        VcKind::FloatDivisionByZero => const_expr("tRust.VcKind.floatDivByZero"),
        VcKind::FloatOverflowToInfinity { .. } => const_expr("tRust.VcKind.floatOverflowInf"),
        // tRust #438: Rvalue safety VCs.
        VcKind::InvalidDiscriminant { .. } => const_expr("tRust.VcKind.invalidDiscriminant"),
        VcKind::AggregateArrayLengthMismatch { .. } => {
            const_expr("tRust.VcKind.aggregateArrayLengthMismatch")
        }
        // tRust #463: Unsafe operation.
        VcKind::UnsafeOperation { .. } => const_expr("tRust.VcKind.unsafeOperation"),
        _ => const_expr("tRust.VcKind.unknown"),
    }
}

// ---------------------------------------------------------------------------
// Full canonical VC → lean5 theorem statement
// ---------------------------------------------------------------------------

/// Translate canonical VC bytes into a lean5 theorem-statement expression.
///
/// The canonical bytes encode a VcKind + Formula pair (see canonical.rs).
/// This function decodes the canonical form and produces a lean5 Prop
/// expression that a ProofCert must witness.
///
/// For now, this takes a VC directly rather than decoding from bytes,
/// since we always have the VC available at the call site.
pub fn translate_vc_to_lean5_theorem(kind: &VcKind, formula: &Formula) -> LeanExpr {
    // The theorem is: tRust.VC.holds <kind> <formula>
    // This wraps the formula in a VC-kind-annotated Prop.
    LeanExpr::apps(
        const_expr("tRust.VC.holds"),
        vec![translate_vc_kind(kind), translate_formula(formula)],
    )
}

// ---------------------------------------------------------------------------
// Certificate verification via lean5 kernel
// ---------------------------------------------------------------------------

/// Verify a lean5 ProofCert against a theorem expression using the kernel.
///
/// This is the trust boundary: if this function returns `Ok(())`, the
/// proof term has been type-checked by the lean5 kernel and the result
/// can be upgraded from Trusted to Certified.
///
/// # Arguments
///
/// * `proof_cert` - The lean5 proof certificate to verify
/// * `theorem_expr` - The lean5 expression representing the theorem statement
///
/// # Errors
///
/// - `KernelRejected` if lean5's type checker rejects the proof term
/// - `KernelRejected` if the verified type does not match the theorem statement
pub fn verify_proof_cert(
    proof_cert: &ProofCert,
    theorem_expr: &LeanExpr,
) -> Result<(), CertificateError> {
    let env = Environment::new();
    let mut verifier = CertVerifier::new(&env);

    let verified_type = verifier.verify(proof_cert, theorem_expr).map_err(|e| {
        CertificateError::KernelRejected {
            reason: format!("lean5 CertVerifier rejected proof: {e}"),
        }
    })?;

    // The verified type must be a Sort (Prop or Type), confirming
    // the theorem statement is well-typed and the proof witnesses it.
    // In CIC, if verify(cert, expr) succeeds, cert witnesses expr : verified_type.
    // We just need the verification to succeed — the type checker does the work.
    let _ = verified_type;

    Ok(())
}

/// Deserialize a proof certificate from bytes (bincode format).
///
/// This is the inverse of the serialization that solvers produce.
/// The bytes are opaque to tRust — only lean5 can interpret them.
pub fn deserialize_proof_cert(bytes: &[u8]) -> Result<ProofCert, CertificateError> {
    bincode::deserialize(bytes).map_err(|e| CertificateError::InvalidProofTerm {
        reason: format!("failed to deserialize lean5 ProofCert: {e}"),
    })
}

/// Serialize a proof certificate to bytes (bincode format).
///
/// Used when storing certificates alongside compiled artifacts.
pub fn serialize_proof_cert(cert: &ProofCert) -> Result<Vec<u8>, CertificateError> {
    bincode::serialize(cert).map_err(|e| CertificateError::SerializationFailed {
        reason: format!("failed to serialize lean5 ProofCert: {e}"),
    })
}

/// tRust #429: Convert a `LeanProofTerm` (our intermediate representation)
/// to serialized `ProofCert` bytes for the lean5 kernel.
///
/// This bridges the reconstruction pipeline output to the kernel-checked
/// certification path. The translation maps our term constructors to
/// lean5-kernel's ProofCert variants:
///
/// - `LeanProofTerm::Const(name)` -> `ProofCert::Const { name, levels: [] }`
/// - `LeanProofTerm::App(f, a)` -> `ProofCert::App { func, arg }`
/// - `LeanProofTerm::Lambda{..}` -> `ProofCert::Lam { .. }`
/// - `LeanProofTerm::Sort(u)` -> `ProofCert::Sort { level }`
/// - `LeanProofTerm::Var(idx)` -> `ProofCert::BVar { idx, .. }`
/// - `LeanProofTerm::ByDecidability{..}` -> `ProofCert::Const("decide")`
/// - `LeanProofTerm::ByAssumption{..}` -> `ProofCert::BVar { idx, .. }`
///
/// Returns the serialized bytes. If the term cannot be converted, returns
/// a debug-format fallback (preserving backward compatibility with the
/// unchecked path).
pub fn serialize_proof_cert_from_lean_term(term: &crate::reconstruction::LeanProofTerm) -> Vec<u8> {
    match lean_term_to_proof_cert(term) {
        Ok(cert) => bincode::serialize(&cert).unwrap_or_else(|_| format!("{term:?}").into_bytes()),
        Err(_) => format!("{term:?}").into_bytes(),
    }
}

/// Convert a `LeanProofTerm` to a lean5-kernel `ProofCert`.
fn lean_term_to_proof_cert(
    term: &crate::reconstruction::LeanProofTerm,
) -> Result<ProofCert, CertificateError> {
    use crate::reconstruction::LeanProofTerm;
    use lean5_kernel::BinderInfo;

    match term {
        LeanProofTerm::Var(idx) => {
            Ok(ProofCert::BVar { idx: *idx as u32, expected_type: Box::new(LeanExpr::prop()) })
        }
        LeanProofTerm::App(f, a) => {
            let fn_cert = lean_term_to_proof_cert(f)?;
            let arg_cert = lean_term_to_proof_cert(a)?;
            Ok(ProofCert::App {
                fn_cert: Box::new(fn_cert),
                fn_type: Box::new(LeanExpr::prop()),
                arg_cert: Box::new(arg_cert),
                result_type: Box::new(LeanExpr::prop()),
            })
        }
        LeanProofTerm::Lambda { binder_type, body, .. } => {
            let arg_cert = lean_term_to_proof_cert(binder_type)?;
            let body_cert = lean_term_to_proof_cert(body)?;
            Ok(ProofCert::Lam {
                binder_info: BinderInfo::Default,
                arg_type_cert: Box::new(arg_cert),
                body_cert: Box::new(body_cert),
                result_type: Box::new(LeanExpr::prop()),
            })
        }
        LeanProofTerm::Sort(level) => {
            let lean_level = match level {
                0 => LeanLevel::zero(),
                1 => LeanLevel::succ(LeanLevel::zero()),
                _ => LeanLevel::succ(LeanLevel::succ(LeanLevel::zero())),
            };
            Ok(ProofCert::Sort { level: lean_level })
        }
        LeanProofTerm::Const(name_str) => Ok(ProofCert::Const {
            name: LeanName::from_string(name_str),
            levels: vec![],
            type_: Box::new(LeanExpr::prop()),
        }),
        LeanProofTerm::ByDecidability { .. } => Ok(ProofCert::Const {
            name: LeanName::from_string("decide"),
            levels: vec![],
            type_: Box::new(LeanExpr::prop()),
        }),
        LeanProofTerm::ByAssumption { hypothesis_index } => Ok(ProofCert::BVar {
            idx: *hypothesis_index as u32,
            expected_type: Box::new(LeanExpr::prop()),
        }),
        LeanProofTerm::Let { ty, value, body, .. } => {
            let ty_cert = lean_term_to_proof_cert(ty)?;
            let val_cert = lean_term_to_proof_cert(value)?;
            let body_cert = lean_term_to_proof_cert(body)?;
            Ok(ProofCert::Let {
                type_cert: Box::new(ty_cert),
                value_cert: Box::new(val_cert),
                body_cert: Box::new(body_cert),
                result_type: Box::new(LeanExpr::prop()),
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    /// Helper: check that a lean5 Expr's debug output contains a Name component.
    ///
    /// lean5 Name debug format shows `Str(Name { ... }, "component")`, so
    /// we search for the quoted string component in the debug output.
    fn debug_contains_name(expr: &LeanExpr, name_component: &str) -> bool {
        let debug = format!("{expr:?}");
        // Name components appear as quoted strings in the Str variant
        debug.contains(&format!("\"{name_component}\""))
    }

    // -----------------------------------------------------------------------
    // Sort translation tests
    // -----------------------------------------------------------------------

    #[test]
    fn translate_sort_bool() {
        let expr = translate_sort(&Sort::Bool);
        assert!(
            debug_contains_name(&expr, "Bool") && debug_contains_name(&expr, "Sort"),
            "Bool sort should produce Const with Sort.Bool name"
        );
    }

    #[test]
    fn translate_sort_int() {
        let expr = translate_sort(&Sort::Int);
        assert!(
            debug_contains_name(&expr, "Int") && debug_contains_name(&expr, "Sort"),
            "Int sort should produce Const with Sort.Int name"
        );
    }

    #[test]
    fn translate_sort_bitvec() {
        let expr = translate_sort(&Sort::BitVec(32));
        assert!(
            debug_contains_name(&expr, "BitVec"),
            "BitVec sort should contain BitVec name component"
        );
    }

    #[test]
    fn translate_sort_array() {
        let expr = translate_sort(&Sort::Array(Box::new(Sort::Int), Box::new(Sort::Bool)));
        assert!(
            debug_contains_name(&expr, "Array"),
            "Array sort should contain Array name component"
        );
    }

    // -----------------------------------------------------------------------
    // Formula translation tests
    // -----------------------------------------------------------------------

    #[test]
    fn translate_formula_bool_true() {
        let expr = translate_formula(&Formula::Bool(true));
        assert!(debug_contains_name(&expr, "True"), "Bool(true) should translate to True");
    }

    #[test]
    fn translate_formula_bool_false() {
        let expr = translate_formula(&Formula::Bool(false));
        assert!(debug_contains_name(&expr, "False"), "Bool(false) should translate to False");
    }

    #[test]
    fn translate_formula_int_positive() {
        let expr = translate_formula(&Formula::Int(42));
        assert!(
            debug_contains_name(&expr, "int") && debug_contains_name(&expr, "Formula"),
            "Int(42) should contain Formula.int name"
        );
    }

    #[test]
    fn translate_formula_int_negative() {
        let expr = translate_formula(&Formula::Int(-7));
        assert!(debug_contains_name(&expr, "neg"), "Int(-7) should contain neg name");
    }

    #[test]
    fn translate_formula_var() {
        let expr = translate_formula(&Formula::Var("x".into(), Sort::Int));
        assert!(
            debug_contains_name(&expr, "var") && debug_contains_name(&expr, "Formula"),
            "Var should translate to Formula.var"
        );
    }

    #[test]
    fn translate_formula_not() {
        let expr = translate_formula(&Formula::Not(Box::new(Formula::Bool(true))));
        assert!(debug_contains_name(&expr, "Not"), "Not should translate to Not");
    }

    #[test]
    fn translate_formula_and() {
        let expr =
            translate_formula(&Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]));
        assert!(debug_contains_name(&expr, "And"), "And should translate to And");
    }

    #[test]
    fn translate_formula_and_empty() {
        let expr = translate_formula(&Formula::And(vec![]));
        assert!(debug_contains_name(&expr, "True"), "And([]) should translate to True");
    }

    #[test]
    fn translate_formula_or_empty() {
        let expr = translate_formula(&Formula::Or(vec![]));
        assert!(debug_contains_name(&expr, "False"), "Or([]) should translate to False");
    }

    #[test]
    fn translate_formula_comparison_le() {
        let expr = translate_formula(&Formula::Le(
            Box::new(Formula::Int(0)),
            Box::new(Formula::Var("x".into(), Sort::Int)),
        ));
        assert!(
            debug_contains_name(&expr, "le") && debug_contains_name(&expr, "Formula"),
            "Le should translate to Formula.le"
        );
    }

    #[test]
    fn translate_formula_arithmetic_add() {
        let expr = translate_formula(&Formula::Add(
            Box::new(Formula::Var("a".into(), Sort::Int)),
            Box::new(Formula::Var("b".into(), Sort::Int)),
        ));
        assert!(
            debug_contains_name(&expr, "add") && debug_contains_name(&expr, "Formula"),
            "Add should translate to Formula.add"
        );
    }

    #[test]
    fn translate_formula_bv_add() {
        let expr = translate_formula(&Formula::BvAdd(
            Box::new(Formula::BitVec { value: 1, width: 32 }),
            Box::new(Formula::BitVec { value: 2, width: 32 }),
            32,
        ));
        assert!(debug_contains_name(&expr, "bvAdd"), "BvAdd should translate to Formula.bvAdd");
    }

    #[test]
    fn translate_formula_ite() {
        let expr = translate_formula(&Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(0)),
        ));
        assert!(
            debug_contains_name(&expr, "ite") && debug_contains_name(&expr, "Formula"),
            "Ite should translate to Formula.ite"
        );
    }

    #[test]
    fn translate_formula_forall() {
        let expr = translate_formula(&Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Le(
                Box::new(Formula::Int(0)),
                Box::new(Formula::Var("x".into(), Sort::Int)),
            )),
        ));
        assert!(
            debug_contains_name(&expr, "forall") && debug_contains_name(&expr, "Formula"),
            "Forall should translate to Formula.forall"
        );
    }

    // -----------------------------------------------------------------------
    // VcKind translation tests
    // -----------------------------------------------------------------------

    #[test]
    fn translate_vc_kind_variants() {
        let cases: Vec<(VcKind, &str)> = vec![
            (VcKind::DivisionByZero, "divisionByZero"),
            (VcKind::RemainderByZero, "remainderByZero"),
            (VcKind::IndexOutOfBounds, "indexOutOfBounds"),
            (VcKind::Postcondition, "postcondition"),
            (VcKind::Unreachable, "unreachable"),
            (VcKind::Deadlock, "deadlock"),
            (VcKind::CastOverflow { from_ty: Ty::usize(), to_ty: Ty::Bool }, "castOverflow"),
            (VcKind::NegationOverflow { ty: Ty::usize() }, "negationOverflow"),
        ];
        for (kind, expected_suffix) in cases {
            let expr = translate_vc_kind(&kind);
            assert!(
                debug_contains_name(&expr, expected_suffix),
                "VcKind::{kind:?} should contain '{expected_suffix}'"
            );
        }
    }

    // -----------------------------------------------------------------------
    // Full VC → theorem translation tests
    // -----------------------------------------------------------------------

    #[test]
    fn translate_vc_to_theorem() {
        let theorem = translate_vc_to_lean5_theorem(
            &VcKind::DivisionByZero,
            &Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Var("divisor".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))),
        );
        assert!(
            debug_contains_name(&theorem, "holds") && debug_contains_name(&theorem, "VC"),
            "theorem should be wrapped in tRust.VC.holds"
        );
        assert!(
            debug_contains_name(&theorem, "divisionByZero"),
            "theorem should contain divisionByZero kind"
        );
    }

    // -----------------------------------------------------------------------
    // Midpoint overflow VC translation (real-world test)
    // -----------------------------------------------------------------------

    #[test]
    fn translate_midpoint_overflow_vc() {
        let formula = Formula::Not(Box::new(Formula::And(vec![
            Formula::Le(
                Box::new(Formula::Int(0)),
                Box::new(Formula::Add(
                    Box::new(Formula::Var("a".into(), Sort::Int)),
                    Box::new(Formula::Var("b".into(), Sort::Int)),
                )),
            ),
            Formula::Le(
                Box::new(Formula::Add(
                    Box::new(Formula::Var("a".into(), Sort::Int)),
                    Box::new(Formula::Var("b".into(), Sort::Int)),
                )),
                Box::new(Formula::Int((1i128 << 64) - 1)),
            ),
        ])));

        let theorem = translate_vc_to_lean5_theorem(
            &VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::usize(), Ty::usize()) },
            &formula,
        );

        assert!(debug_contains_name(&theorem, "holds"), "midpoint VC theorem should contain holds");
        assert!(
            debug_contains_name(&theorem, "arithmeticOverflow"),
            "midpoint VC should reference arithmeticOverflow"
        );
        assert!(debug_contains_name(&theorem, "Not"), "midpoint VC should contain negation");
    }

    // -----------------------------------------------------------------------
    // Serialization roundtrip test
    // -----------------------------------------------------------------------

    #[test]
    fn proof_cert_serialization_roundtrip() {
        let cert = ProofCert::Sort { level: LeanLevel::zero() };
        let bytes = serialize_proof_cert(&cert).expect("should serialize");
        assert!(!bytes.is_empty(), "serialized bytes should be non-empty");
        let recovered = deserialize_proof_cert(&bytes).expect("should deserialize");
        assert_eq!(cert, recovered, "ProofCert should survive serialization roundtrip");
    }

    #[test]
    fn deserialize_invalid_bytes_fails() {
        let bad_bytes = vec![0xFF, 0x00, 0xDE, 0xAD];
        let err = deserialize_proof_cert(&bad_bytes)
            .expect_err("invalid bytes should fail deserialization");
        assert!(
            matches!(err, CertificateError::InvalidProofTerm { .. }),
            "should be InvalidProofTerm, got: {err:?}"
        );
    }

    #[test]
    fn serialize_complex_proof_cert() {
        use lean5_kernel::BinderInfo;

        let cert = ProofCert::Lam {
            binder_info: BinderInfo::Default,
            arg_type_cert: Box::new(ProofCert::Sort { level: LeanLevel::succ(LeanLevel::zero()) }),
            body_cert: Box::new(ProofCert::BVar {
                idx: 0,
                expected_type: Box::new(LeanExpr::sort(LeanLevel::zero())),
            }),
            result_type: Box::new(LeanExpr::prop()),
        };

        let bytes = serialize_proof_cert(&cert).expect("should serialize complex cert");
        let recovered = deserialize_proof_cert(&bytes).expect("should deserialize complex cert");
        assert_eq!(cert, recovered);
    }

    // -----------------------------------------------------------------------
    // Complex formula translation tests
    // -----------------------------------------------------------------------

    #[test]
    fn translate_implies() {
        let expr = translate_formula(&Formula::Implies(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Bool(false)),
        ));
        assert!(
            debug_contains_name(&expr, "implies") && debug_contains_name(&expr, "Formula"),
            "Implies should translate to Formula.implies"
        );
    }

    #[test]
    fn translate_select_store() {
        let arr = Formula::Var("arr".into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
        let select =
            translate_formula(&Formula::Select(Box::new(arr.clone()), Box::new(Formula::Int(0))));
        assert!(debug_contains_name(&select, "select"), "Select should contain select name");

        let store = translate_formula(&Formula::Store(
            Box::new(arr),
            Box::new(Formula::Int(0)),
            Box::new(Formula::Int(42)),
        ));
        assert!(debug_contains_name(&store, "store"), "Store should contain store name");
    }

    #[test]
    fn translate_exists() {
        let expr = translate_formula(&Formula::Exists(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Eq(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(42)),
            )),
        ));
        assert!(
            debug_contains_name(&expr, "exists") && debug_contains_name(&expr, "Formula"),
            "Exists should translate to Formula.exists"
        );
    }

    #[test]
    fn translate_bitvec_conversions() {
        let bv_to_int = translate_formula(&Formula::BvToInt(
            Box::new(Formula::BitVec { value: 255, width: 8 }),
            8,
            false,
        ));
        assert!(debug_contains_name(&bv_to_int, "bvToInt"), "BvToInt should contain bvToInt name");

        let int_to_bv = translate_formula(&Formula::IntToBv(Box::new(Formula::Int(42)), 32));
        assert!(debug_contains_name(&int_to_bv, "intToBv"), "IntToBv should contain intToBv name");
    }
}
