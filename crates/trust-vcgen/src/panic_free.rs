// trust-vcgen/panic_free.rs: Panic-free verification for Rust functions
//
// Enumerates all potential panic sites in a VerifiableFunction's MIR and
// generates Unreachable VCs for each. If all VCs are proved, the function
// is panic-free.
//
// Panic sources detected:
//   - Unwrap / Expect calls on Option/Result
//   - Index out-of-bounds (array/slice subscript)
//   - Assert terminator failures (rustc-inserted safety checks)
//   - Unreachable terminators (exhaustive match fallthrough)
//   - Division by zero (via assert on divisor)
//   - Arithmetic overflow (via checked ops + assert)
//   - Explicit panic!() / unimplemented!() / todo!() calls
//
// Part of #83: Panic-free verification
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    AssertMessage, BlockId, Formula, SourceSpan, Terminator, VcKind,
    VerifiableFunction, VerificationCondition, strip_generics,
};

#[cfg(test)]
use trust_types::{
    BasicBlock, BinOp, LocalDecl, Operand, Place, ProofLevel, Rvalue,
    Statement, Ty, VerifiableBody,
};

/// Classification of how a function might panic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PanicKind {
    /// `.unwrap()` on Option or Result.
    Unwrap,
    /// `.expect("msg")` on Option or Result.
    Expect,
    /// Array or slice index without bounds check.
    IndexBounds,
    /// `assert!`, `assert_eq!`, `debug_assert!`, or rustc-inserted Assert.
    Assert,
    /// `unreachable!()` or MIR Unreachable terminator.
    Unreachable,
    /// Division or remainder by zero.
    DivByZero,
    /// Arithmetic overflow on checked operations.
    Overflow,
    /// Explicit `panic!()`, `todo!()`, `unimplemented!()`.
    ExplicitPanic,
}

impl PanicKind {
    /// Human-readable label for diagnostic output.
    pub fn label(&self) -> &str {
        match self {
            PanicKind::Unwrap => "unwrap on None/Err",
            PanicKind::Expect => "expect on None/Err",
            PanicKind::IndexBounds => "index out of bounds",
            PanicKind::Assert => "assertion failure",
            PanicKind::Unreachable => "unreachable code",
            PanicKind::DivByZero => "division by zero",
            PanicKind::Overflow => "arithmetic overflow",
            PanicKind::ExplicitPanic => "explicit panic",
        }
    }
}

/// A potential panic site in a function's MIR.
#[derive(Debug, Clone)]
pub struct PanicSite {
    /// What kind of panic this site represents.
    pub kind: PanicKind,
    /// Source location of the panic site.
    pub span: SourceSpan,
    /// Human-readable description of the panic site.
    pub message: String,
    /// Block where the panic originates.
    pub block: BlockId,
}

/// Enumerate all potential panic paths in a function's MIR.
///
/// Walks every block and its terminator/statements to find sites that can
/// panic at runtime. Returns one `PanicSite` per distinct panic source.
#[must_use]
pub fn enumerate_panic_sites(func: &VerifiableFunction) -> Vec<PanicSite> {
    let mut sites = Vec::new();

    for block in &func.body.blocks {
        // Check terminator for panic-producing patterns.
        match &block.terminator {
            Terminator::Assert { msg, span, .. } => {
                let (kind, message) = classify_assert_message(msg);
                sites.push(PanicSite {
                    kind,
                    span: span.clone(),
                    message,
                    block: block.id,
                });
            }
            Terminator::Unreachable => {
                sites.push(PanicSite {
                    kind: PanicKind::Unreachable,
                    span: SourceSpan::default(),
                    message: "unreachable code reached".to_string(),
                    block: block.id,
                });
            }
            Terminator::Call { func: func_name, span, .. } => {
                if let Some(kind) = classify_panic_call(func_name) {
                    sites.push(PanicSite {
                        kind,
                        span: span.clone(),
                        message: format!("call to `{func_name}`"),
                        block: block.id,
                    });
                }
            }
            Terminator::Goto(_)
            | Terminator::SwitchInt { .. }
            | Terminator::Return
            | Terminator::Drop { .. } => {}
            _ => {},
        }
    }

    sites
}

/// Generate Unreachable VCs for each panic site.
///
/// Each panic site becomes a VC asserting that the panic location is
/// unreachable. If the solver proves UNSAT, the panic cannot happen.
/// If SAT, the solver's model is a counterexample triggering the panic.
#[must_use]
pub fn generate_panic_free_vcs(
    func: &VerifiableFunction,
    sites: &[PanicSite],
) -> Vec<VerificationCondition> {
    sites
        .iter()
        .map(|site| {
            VerificationCondition {
                kind: VcKind::Unreachable,
                function: func.name.clone(),
                location: site.span.clone(),
                // Convention: formula is satisfiable iff the panic is reachable.
                // Bool(true) = always reachable (conservative).
                // In practice, the path condition from guards refines this.
                formula: Formula::Bool(true),
                contract_metadata: None,
            }
        })
        .collect()
}

/// Result of panic-free analysis for a single panic site.
#[derive(Debug, Clone)]
pub struct PanicSiteResult {
    /// The panic site that was checked.
    pub site: PanicSite,
    /// Whether this panic site was proved unreachable.
    pub proved_unreachable: bool,
}

/// Summary report for panic-free verification of a function.
#[derive(Debug, Clone)]
pub struct PanicFreeReport {
    /// Name of the function that was analyzed.
    pub function: String,
    /// Whether the function is completely panic-free.
    pub panic_free: bool,
    /// Per-site verification results.
    pub sites: Vec<PanicSiteResult>,
}

impl PanicFreeReport {
    /// Build a report from panic sites and their verification outcomes.
    ///
    /// `proved` is a parallel slice: `proved[i]` is true if `sites[i]` was
    /// proved unreachable by the solver.
    #[must_use]
    pub fn from_results(function: &str, sites: Vec<PanicSite>, proved: &[bool]) -> Self {
        let site_results: Vec<PanicSiteResult> = sites
            .into_iter()
            .zip(proved.iter().copied())
            .map(|(site, proved_unreachable)| PanicSiteResult { site, proved_unreachable })
            .collect();

        let panic_free = site_results.iter().all(|r| r.proved_unreachable);

        PanicFreeReport {
            function: function.to_string(),
            panic_free,
            sites: site_results,
        }
    }

    /// Number of panic sites that could not be proved unreachable.
    #[must_use]
    pub fn unproved_count(&self) -> usize {
        self.sites.iter().filter(|r| !r.proved_unreachable).count()
    }

    /// Number of panic sites total.
    #[must_use]
    pub fn total_sites(&self) -> usize {
        self.sites.len()
    }
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Classify an `AssertMessage` into a `PanicKind` and description.
fn classify_assert_message(msg: &AssertMessage) -> (PanicKind, String) {
    match msg {
        AssertMessage::BoundsCheck => {
            (PanicKind::IndexBounds, "index out of bounds".to_string())
        }
        AssertMessage::Overflow(op) => {
            (PanicKind::Overflow, format!("arithmetic overflow ({op:?})"))
        }
        AssertMessage::OverflowNeg => {
            (PanicKind::Overflow, "negation overflow".to_string())
        }
        AssertMessage::DivisionByZero => {
            (PanicKind::DivByZero, "division by zero".to_string())
        }
        AssertMessage::RemainderByZero => {
            (PanicKind::DivByZero, "remainder by zero".to_string())
        }
        AssertMessage::ResumedAfterReturn => {
            (PanicKind::Unreachable, "resumed after return".to_string())
        }
        AssertMessage::ResumedAfterPanic => {
            (PanicKind::Unreachable, "resumed after panic".to_string())
        }
        AssertMessage::MisalignedPointerDereference => {
            (PanicKind::Assert, "misaligned pointer dereference".to_string())
        }
        AssertMessage::ResumedAfterDrop => {
            (PanicKind::Unreachable, "resumed after drop".to_string())
        }
        AssertMessage::NullPointerDereference => {
            (PanicKind::Assert, "null pointer dereference".to_string())
        }
        AssertMessage::InvalidEnumConstruction => {
            (PanicKind::Assert, "invalid enum construction".to_string())
        }
        AssertMessage::Custom(msg) => {
            (PanicKind::Assert, format!("assertion: {msg}"))
        }
        _ => (PanicKind::Assert, "unknown assertion".to_string()),
    }
}


/// Classify a Call terminator's target function as a panic-producing call.
/// Returns `None` if the call is not panic-related.
fn classify_panic_call(func_name: &str) -> Option<PanicKind> {
    let normalized = strip_generics(func_name);

    // Unwrap / Expect
    const UNWRAP_PATTERNS: &[&str] = &[
        "Result::unwrap",
        "Option::unwrap",
    ];
    if UNWRAP_PATTERNS.iter().any(|p| normalized.contains(p)) {
        return Some(PanicKind::Unwrap);
    }

    const EXPECT_PATTERNS: &[&str] = &[
        "Result::expect",
        "Option::expect",
    ];
    if EXPECT_PATTERNS.iter().any(|p| normalized.contains(p)) {
        return Some(PanicKind::Expect);
    }

    // Explicit panic calls
    const PANIC_PATTERNS: &[&str] = &[
        "core::panicking::panic",
        "std::panicking::begin_panic",
        "core::panicking::panic_fmt",
        "core::panicking::panic_nounwind",
        "std::rt::begin_panic",
    ];
    if PANIC_PATTERNS.iter().any(|p| normalized.contains(p)) {
        return Some(PanicKind::ExplicitPanic);
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A function that never panics: just returns its input.
    fn panic_free_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "identity".to_string(),
            def_path: "test::identity".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// A function with an unwrap call.
    fn unwrap_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "risky_unwrap".to_string(),
            def_path: "test::risky_unwrap".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::Unit, name: Some("opt".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "core::option::Option::<u32>::unwrap".to_string(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(2),
                            target: Some(BlockId(1)),
                            span: SourceSpan {
                                file: "test.rs".into(),
                                line_start: 5,
                                col_start: 4,
                                line_end: 5,
                                col_end: 20,
                            },
                            atomic: None,
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// A function with a checked add (overflow assert) and division.
    fn overflow_and_div_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "add_and_div".to_string(),
            def_path: "test::add_and_div".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                    LocalDecl {
                        index: 3,
                        ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                        name: None,
                    },
                ],
                blocks: vec![
                    // bb0: checked add -> assert no overflow
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            cond: Operand::Copy(Place::field(3, 1)),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(1),
                            span: SourceSpan {
                                file: "test.rs".into(),
                                line_start: 3,
                                col_start: 4,
                                line_end: 3,
                                col_end: 9,
                            },
                        },
                    },
                    // bb1: assert divisor != 0
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Assert {
                            cond: Operand::Copy(Place::local(2)),
                            expected: true,
                            msg: AssertMessage::DivisionByZero,
                            target: BlockId(2),
                            span: SourceSpan {
                                file: "test.rs".into(),
                                line_start: 4,
                                col_start: 4,
                                line_end: 4,
                                col_end: 9,
                            },
                        },
                    },
                    // bb2: return
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 2,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// A function with an explicit panic!() call.
    fn explicit_panic_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "explicit_panic".to_string(),
            def_path: "test::explicit_panic".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(1)),
                            targets: vec![(1, BlockId(1))],
                            otherwise: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb1: return
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    },
                    // bb2: panic!()
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "core::panicking::panic_fmt".to_string(),
                            args: vec![],
                            dest: Place::local(0),
                            target: None,
                            span: SourceSpan {
                                file: "test.rs".into(),
                                line_start: 10,
                                col_start: 8,
                                line_end: 10,
                                col_end: 30,
                            },
                            atomic: None,
                        },
                    },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// A function with an Unreachable terminator (exhaustive match fallthrough).
    fn unreachable_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "match_exhaustive".to_string(),
            def_path: "test::match_exhaustive".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(1)),
                            targets: vec![(0, BlockId(1)), (1, BlockId(2))],
                            otherwise: BlockId(3),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    },
                    // bb3: unreachable fallthrough
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![],
                        terminator: Terminator::Unreachable,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    // -----------------------------------------------------------------------
    // Tests for enumerate_panic_sites
    // -----------------------------------------------------------------------

    #[test]
    fn test_enumerate_panic_free_function_no_sites() {
        let func = panic_free_function();
        let sites = enumerate_panic_sites(&func);
        assert!(sites.is_empty(), "panic-free function should have no panic sites");
    }

    #[test]
    fn test_enumerate_unwrap_site() {
        let func = unwrap_function();
        let sites = enumerate_panic_sites(&func);
        assert_eq!(sites.len(), 1, "unwrap function should have 1 panic site");
        assert_eq!(sites[0].kind, PanicKind::Unwrap);
        assert!(sites[0].message.contains("unwrap"));
        assert_eq!(sites[0].span.line_start, 5);
    }

    #[test]
    fn test_enumerate_overflow_and_div_sites() {
        let func = overflow_and_div_function();
        let sites = enumerate_panic_sites(&func);
        assert_eq!(sites.len(), 2, "should find overflow assert + div-by-zero assert");

        let kinds: Vec<&PanicKind> = sites.iter().map(|s| &s.kind).collect();
        assert!(kinds.contains(&&PanicKind::Overflow));
        assert!(kinds.contains(&&PanicKind::DivByZero));
    }

    #[test]
    fn test_enumerate_explicit_panic_site() {
        let func = explicit_panic_function();
        let sites = enumerate_panic_sites(&func);
        assert_eq!(sites.len(), 1);
        assert_eq!(sites[0].kind, PanicKind::ExplicitPanic);
        assert_eq!(sites[0].block, BlockId(2));
    }

    #[test]
    fn test_enumerate_unreachable_site() {
        let func = unreachable_function();
        let sites = enumerate_panic_sites(&func);
        assert_eq!(sites.len(), 1);
        assert_eq!(sites[0].kind, PanicKind::Unreachable);
        assert_eq!(sites[0].block, BlockId(3));
    }

    // -----------------------------------------------------------------------
    // Tests for generate_panic_free_vcs
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_vcs_empty_sites() {
        let func = panic_free_function();
        let vcs = generate_panic_free_vcs(&func, &[]);
        assert!(vcs.is_empty());
    }

    #[test]
    fn test_generate_vcs_one_per_site() {
        let func = unwrap_function();
        let sites = enumerate_panic_sites(&func);
        let vcs = generate_panic_free_vcs(&func, &sites);
        assert_eq!(vcs.len(), sites.len());
        assert!(matches!(vcs[0].kind, VcKind::Unreachable));
        assert_eq!(vcs[0].function, "risky_unwrap");
    }

    #[test]
    fn test_generate_vcs_preserves_spans() {
        let func = unwrap_function();
        let sites = enumerate_panic_sites(&func);
        let vcs = generate_panic_free_vcs(&func, &sites);
        assert_eq!(vcs[0].location.line_start, 5);
        assert_eq!(vcs[0].location.file, "test.rs");
    }

    #[test]
    fn test_generate_vcs_multiple_sites() {
        let func = overflow_and_div_function();
        let sites = enumerate_panic_sites(&func);
        let vcs = generate_panic_free_vcs(&func, &sites);
        assert_eq!(vcs.len(), 2);
        assert!(vcs.iter().all(|vc| matches!(vc.kind, VcKind::Unreachable)));
    }

    // -----------------------------------------------------------------------
    // Tests for PanicFreeReport
    // -----------------------------------------------------------------------

    #[test]
    fn test_report_panic_free_when_all_proved() {
        let func = overflow_and_div_function();
        let sites = enumerate_panic_sites(&func);
        let proved = vec![true, true];
        let report = PanicFreeReport::from_results(&func.name, sites, &proved);

        assert!(report.panic_free);
        assert_eq!(report.unproved_count(), 0);
        assert_eq!(report.total_sites(), 2);
        assert_eq!(report.function, "add_and_div");
    }

    #[test]
    fn test_report_not_panic_free_when_some_unproved() {
        let func = overflow_and_div_function();
        let sites = enumerate_panic_sites(&func);
        let proved = vec![true, false];
        let report = PanicFreeReport::from_results(&func.name, sites, &proved);

        assert!(!report.panic_free);
        assert_eq!(report.unproved_count(), 1);
        assert_eq!(report.total_sites(), 2);
    }

    #[test]
    fn test_report_empty_sites_is_panic_free() {
        let report = PanicFreeReport::from_results("trivial", vec![], &[]);
        assert!(report.panic_free);
        assert_eq!(report.unproved_count(), 0);
        assert_eq!(report.total_sites(), 0);
    }

    #[test]
    fn test_report_all_unproved() {
        let func = overflow_and_div_function();
        let sites = enumerate_panic_sites(&func);
        let proved = vec![false, false];
        let report = PanicFreeReport::from_results(&func.name, sites, &proved);

        assert!(!report.panic_free);
        assert_eq!(report.unproved_count(), 2);
    }

    // -----------------------------------------------------------------------
    // Tests for classify_panic_call
    // -----------------------------------------------------------------------

    #[test]
    fn test_classify_unwrap_calls() {
        assert_eq!(
            classify_panic_call("core::option::Option::<u32>::unwrap"),
            Some(PanicKind::Unwrap)
        );
        assert_eq!(
            classify_panic_call("core::result::Result::<T, E>::unwrap"),
            Some(PanicKind::Unwrap)
        );
    }

    #[test]
    fn test_classify_expect_calls() {
        assert_eq!(
            classify_panic_call("core::option::Option::<u32>::expect"),
            Some(PanicKind::Expect)
        );
        assert_eq!(
            classify_panic_call("core::result::Result::<T, E>::expect"),
            Some(PanicKind::Expect)
        );
    }

    #[test]
    fn test_classify_explicit_panic_calls() {
        assert_eq!(
            classify_panic_call("core::panicking::panic"),
            Some(PanicKind::ExplicitPanic)
        );
        assert_eq!(
            classify_panic_call("core::panicking::panic_fmt"),
            Some(PanicKind::ExplicitPanic)
        );
        assert_eq!(
            classify_panic_call("std::panicking::begin_panic"),
            Some(PanicKind::ExplicitPanic)
        );
    }

    #[test]
    fn test_classify_non_panic_calls() {
        assert_eq!(classify_panic_call("std::vec::Vec::push"), None);
        assert_eq!(classify_panic_call("redis::Commands::get"), None);
        assert_eq!(classify_panic_call("std::io::Write::write"), None);
    }

    // -----------------------------------------------------------------------
    // Tests for classify_assert_message
    // -----------------------------------------------------------------------

    #[test]
    fn test_classify_assert_bounds_check() {
        let (kind, msg) = classify_assert_message(&AssertMessage::BoundsCheck);
        assert_eq!(kind, PanicKind::IndexBounds);
        assert!(msg.contains("bounds"));
    }

    #[test]
    fn test_classify_assert_overflow() {
        let (kind, msg) = classify_assert_message(&AssertMessage::Overflow(BinOp::Add));
        assert_eq!(kind, PanicKind::Overflow);
        assert!(msg.contains("overflow"));
    }

    #[test]
    fn test_classify_assert_div_zero() {
        let (kind, _) = classify_assert_message(&AssertMessage::DivisionByZero);
        assert_eq!(kind, PanicKind::DivByZero);
    }

    #[test]
    fn test_classify_assert_custom() {
        let (kind, msg) = classify_assert_message(&AssertMessage::Custom("invariant".into()));
        assert_eq!(kind, PanicKind::Assert);
        assert!(msg.contains("invariant"));
    }

    // -----------------------------------------------------------------------
    // Tests for PanicKind::label
    // -----------------------------------------------------------------------

    #[test]
    fn test_panic_kind_labels() {
        assert_eq!(PanicKind::Unwrap.label(), "unwrap on None/Err");
        assert_eq!(PanicKind::Expect.label(), "expect on None/Err");
        assert_eq!(PanicKind::IndexBounds.label(), "index out of bounds");
        assert_eq!(PanicKind::Assert.label(), "assertion failure");
        assert_eq!(PanicKind::Unreachable.label(), "unreachable code");
        assert_eq!(PanicKind::DivByZero.label(), "division by zero");
        assert_eq!(PanicKind::Overflow.label(), "arithmetic overflow");
        assert_eq!(PanicKind::ExplicitPanic.label(), "explicit panic");
    }

    // -----------------------------------------------------------------------
    // Integration: end-to-end panic-free analysis
    // -----------------------------------------------------------------------

    #[test]
    fn test_end_to_end_panic_free_function() {
        let func = panic_free_function();
        let sites = enumerate_panic_sites(&func);
        let vcs = generate_panic_free_vcs(&func, &sites);

        // No panic sites -> no VCs -> function is trivially panic-free.
        assert!(sites.is_empty());
        assert!(vcs.is_empty());

        let report = PanicFreeReport::from_results(&func.name, sites, &[]);
        assert!(report.panic_free);
    }

    #[test]
    fn test_end_to_end_function_with_multiple_panic_kinds() {
        // Build a function with expect + unreachable.
        let func = VerifiableFunction {
            name: "multi_panic".to_string(),
            def_path: "test::multi_panic".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::Unit, name: Some("opt".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: None },
                ],
                blocks: vec![
                    // bb0: call expect
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "core::option::Option::<u32>::expect".to_string(),
                            args: vec![],
                            dest: Place::local(2),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    // bb1: switch
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(2)),
                            targets: vec![(0, BlockId(2))],
                            otherwise: BlockId(3),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb2: return
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    },
                    // bb3: unreachable
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![],
                        terminator: Terminator::Unreachable,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let sites = enumerate_panic_sites(&func);
        assert_eq!(sites.len(), 2);

        let kinds: Vec<&PanicKind> = sites.iter().map(|s| &s.kind).collect();
        assert!(kinds.contains(&&PanicKind::Expect));
        assert!(kinds.contains(&&PanicKind::Unreachable));

        let vcs = generate_panic_free_vcs(&func, &sites);
        assert_eq!(vcs.len(), 2);
        assert!(vcs.iter().all(|vc| vc.kind.proof_level() == ProofLevel::L0Safety));
    }
}
