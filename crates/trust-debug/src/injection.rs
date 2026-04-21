// trust-debug/injection.rs: Injection pattern detection
//
// Detects conditions where attacker-controlled data can influence:
// - Function pointers / indirect calls (code injection / RCE)
// - System calls (command injection)
// - Format strings (format string attacks)
// - Memory operations (arbitrary read/write)
//
// This is what makes trust-debug security-aware rather than just safety-aware.
// We don't just find bugs — we find exploitable bugs and the paths to them.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use crate::{SecurityViolation, SecurityViolationKind, Severity};

/// Patterns that indicate dangerous operations reachable by tainted data.
#[derive(Debug, Clone)]
pub struct InjectionPolicy {
    /// Function name patterns for command execution.
    pub command_patterns: Vec<String>,
    /// Function name patterns for syscalls.
    pub syscall_patterns: Vec<String>,
    /// Function name patterns for format string operations.
    pub format_patterns: Vec<String>,
    /// Function name patterns for memory allocation (for overflow→corruption chains).
    pub alloc_patterns: Vec<String>,
    /// Function name patterns for privilege-sensitive operations.
    pub privilege_patterns: Vec<String>,
}

impl Default for InjectionPolicy {
    fn default() -> Self {
        Self {
            command_patterns: vec![
                "Command::new".into(),
                "Command::arg".into(),
                "std::process::Command".into(),
                "libc::system".into(),
                "libc::exec".into(),
                "libc::execve".into(),
                "libc::execvp".into(),
                "std::os::unix::process".into(),
                "tokio::process::Command".into(),
            ],
            syscall_patterns: vec![
                "libc::open".into(),
                "libc::write".into(),
                "libc::read".into(),
                "libc::ioctl".into(),
                "libc::mmap".into(),
                "libc::mprotect".into(),
                "std::fs::write".into(),
                "std::fs::remove_file".into(),
                "std::net::TcpStream::connect".into(),
            ],
            format_patterns: vec![
                "format!".into(),
                "println!".into(),
                "eprintln!".into(),
                "write!".into(),
                "writeln!".into(),
                "log::info".into(),
                "log::error".into(),
                "tracing::info".into(),
            ],
            alloc_patterns: vec![
                "Vec::with_capacity".into(),
                "Box::new".into(),
                "alloc::alloc".into(),
                "libc::malloc".into(),
                "libc::calloc".into(),
                "libc::realloc".into(),
            ],
            privilege_patterns: vec![
                "libc::setuid".into(),
                "libc::seteuid".into(),
                "libc::setgid".into(),
                "libc::chown".into(),
                "libc::chmod".into(),
                "std::fs::set_permissions".into(),
            ],
        }
    }
}

/// Detect injection vulnerabilities in a function.
///
/// Walks the MIR body looking for calls to dangerous functions where
/// the arguments may be influenced by tainted data. Uses the taint
/// analysis from trust-types as a foundation and adds injection-specific
/// pattern matching.
pub(crate) fn detect_injections(
    func: &VerifiableFunction,
    policy: &InjectionPolicy,
) -> Vec<SecurityViolation> {
    let mut violations = Vec::new();

    // Run taint analysis with an injection-aware policy
    let taint_policy = build_injection_taint_policy(policy);
    let taint_result = analyze_taint(&func.body, &taint_policy);

    // Classify taint violations into specific injection types
    for taint_violation in &taint_result.violations {
        if let Some(violation) = classify_injection(func, taint_violation, policy) {
            violations.push(violation);
        }
    }

    // Check for dangerous call patterns even without taint (for completeness)
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, span, .. } = &block.terminator {
            // Command execution with any arguments
            if matches_any(callee, &policy.command_patterns) && !args.is_empty() {
                let already_found = violations.iter().any(|v| {
                    matches!(&v.kind, SecurityViolationKind::CommandInjection { command_func, .. }
                        if command_func == callee)
                });
                if !already_found {
                    violations.push(SecurityViolation {
                        id: String::new(),
                        severity: Severity::High,
                        kind: SecurityViolationKind::CommandInjection {
                            command_func: callee.clone(),
                            taint_source: "static-detection".to_string(),
                        },
                        function: func.def_path.clone(),
                        location: Some(span.clone()),
                        description: format!(
                            "Call to dangerous function `{callee}` — verify arguments are not attacker-controlled"
                        ),
                        flow_path: vec![],
                        counterexample: None,
                        solver: "injection-detector".to_string(),
                        time_ms: 0,
                    });
                }
            }

            // Privilege-sensitive operations
            if matches_any(callee, &policy.privilege_patterns) {
                violations.push(SecurityViolation {
                    id: String::new(),
                    severity: Severity::High,
                    kind: SecurityViolationKind::PrivilegeEscalation {
                        from_priv: "current".to_string(),
                        to_priv: callee.clone(),
                        path_length: 1,
                    },
                    function: func.def_path.clone(),
                    location: Some(span.clone()),
                    description: format!(
                        "Privilege-sensitive operation `{callee}` — verify authorization path"
                    ),
                    flow_path: vec![],
                    counterexample: None,
                    solver: "injection-detector".to_string(),
                    time_ms: 0,
                });
            }
        }
    }

    violations
}

fn build_injection_taint_policy(policy: &InjectionPolicy) -> TaintPolicy {
    let mut taint_policy = default_web_policy();

    // Add command execution as sinks
    for pattern in &policy.command_patterns {
        taint_policy.sinks.push(TaintSink {
            label: SinkKind::Custom("command-exec".to_string()),
            pattern: pattern.clone(),
        });
    }

    // Add syscalls as sinks
    for pattern in &policy.syscall_patterns {
        taint_policy.sinks.push(TaintSink {
            label: SinkKind::Custom("syscall".to_string()),
            pattern: pattern.clone(),
        });
    }

    taint_policy
}

fn classify_injection(
    func: &VerifiableFunction,
    violation: &TaintFlowViolation,
    policy: &InjectionPolicy,
) -> Option<SecurityViolation> {
    let source_name = match &violation.source_label {
        TaintLabel::UserInput => "user-input",
        TaintLabel::NetworkData => "network-data",
        TaintLabel::FileData => "file-data",
        TaintLabel::Secret => "secret",
        TaintLabel::EnvVar => "env-var",
        TaintLabel::UnsafeBlock => "unsafe-block",
        TaintLabel::ExternCall => "extern-call",
        TaintLabel::Custom(name) => name.as_str(),
        _ => "unknown",
    };

    let (severity, kind) = if matches_any(&violation.sink_func, &policy.command_patterns) {
        (
            Severity::Critical,
            SecurityViolationKind::CommandInjection {
                command_func: violation.sink_func.clone(),
                taint_source: source_name.to_string(),
            },
        )
    } else if matches_any(&violation.sink_func, &policy.syscall_patterns) {
        (
            Severity::Critical,
            SecurityViolationKind::TaintedSyscall {
                syscall: violation.sink_func.clone(),
                taint_source: source_name.to_string(),
            },
        )
    } else {
        return None; // Not an injection-specific violation
    };

    Some(SecurityViolation {
        id: String::new(),
        severity,
        kind,
        function: func.def_path.clone(),
        location: Some(violation.sink_span.clone()),
        description: format!(
            "{source_name} data reaches dangerous operation `{}`",
            violation.sink_func,
        ),
        flow_path: violation.path.clone(),
        counterexample: None,
        solver: "injection-detector".to_string(),
        time_ms: 0,
    })
}

fn matches_any(name: &str, patterns: &[String]) -> bool {
    patterns.iter().any(|p| name.contains(p.as_str()))
}

// ---------------------------------------------------------------------------
// Fault injection framework for testing verification robustness
// ---------------------------------------------------------------------------

/// Where in a verification condition to inject a fault.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum InjectionPoint {
    /// Inject into the precondition (requires clause).
    PreCondition,
    /// Inject into the postcondition (ensures clause).
    PostCondition,
    /// Inject into a loop invariant.
    LoopInvariant,
    /// Inject into a type constraint (e.g., bound on a variable).
    TypeConstraint,
    /// Inject at a boundary value (off-by-one in comparisons).
    BoundaryValue,
}

/// What kind of fault to inject.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum FaultType {
    /// Negate a boolean sub-formula.
    FlipBoolean,
    /// Shift a constant by +1 or -1.
    OffByOne,
    /// Remove an entire conjunct from an And formula.
    RemoveConstraint,
    /// Weaken a strict bound (Lt -> Le, Gt -> Ge).
    WeakenBound,
    /// Swap left and right operands of a binary operator.
    SwapOperands,
    /// Replace a bounded integer with its type's MAX value.
    IntroduceOverflow,
}

/// A record of a single injected fault.
#[derive(Debug, Clone)]
pub(crate) struct InjectedFault {
    /// Original VC (before mutation).
    pub original: VerificationCondition,
    /// Mutated VC (after fault injection).
    pub mutated: VerificationCondition,
    /// Where the fault was injected.
    pub point: InjectionPoint,
    /// What fault was injected.
    pub fault: FaultType,
}

/// Inject a fault into a verification condition's formula.
///
/// Applies the given `fault` at the specified `point` within the VC's formula
/// tree. Returns a new VC with the mutated formula (the original is not
/// modified).
#[must_use]
pub(crate) fn inject_fault(
    vc: &VerificationCondition,
    point: InjectionPoint,
    fault: FaultType,
) -> VerificationCondition {
    let mutated_formula = apply_fault(&vc.formula, point, fault);
    VerificationCondition {
        kind: vc.kind.clone(),
        function: vc.function.clone(),
        location: vc.location.clone(),
        formula: mutated_formula,
        contract_metadata: None,
    }
}

/// Apply a fault transformation to a formula.
fn apply_fault(formula: &Formula, point: InjectionPoint, fault: FaultType) -> Formula {
    match fault {
        FaultType::FlipBoolean => flip_boolean(formula, point),
        FaultType::OffByOne => off_by_one(formula, point),
        FaultType::RemoveConstraint => remove_constraint(formula, point),
        FaultType::WeakenBound => weaken_bound(formula, point),
        FaultType::SwapOperands => swap_operands(formula, point),
        FaultType::IntroduceOverflow => introduce_overflow(formula, point),
    }
}

/// Negate the first boolean-like sub-formula found at the target point.
fn flip_boolean(formula: &Formula, _point: InjectionPoint) -> Formula {
    match formula {
        Formula::Bool(b) => Formula::Bool(!b),
        Formula::Not(inner) => *inner.clone(),
        Formula::And(conjuncts) if !conjuncts.is_empty() => {
            let mut new = conjuncts.clone();
            new[0] = Formula::Not(Box::new(new[0].clone()));
            Formula::And(new)
        }
        Formula::Implies(lhs, rhs) => {
            Formula::Implies(lhs.clone(), Box::new(Formula::Not(rhs.clone())))
        }
        other => Formula::Not(Box::new(other.clone())),
    }
}

/// Shift integer constants by +1.
fn off_by_one(formula: &Formula, _point: InjectionPoint) -> Formula {
    match formula {
        Formula::Int(n) => Formula::Int(n.wrapping_add(1)),
        Formula::BitVec { value, width } => Formula::BitVec {
            value: value.wrapping_add(1),
            width: *width,
        },
        Formula::Lt(lhs, rhs) => Formula::Lt(
            Box::new(off_by_one(lhs, _point)),
            rhs.clone(),
        ),
        Formula::Le(lhs, rhs) => Formula::Le(
            Box::new(off_by_one(lhs, _point)),
            rhs.clone(),
        ),
        Formula::And(conjuncts) => {
            Formula::And(conjuncts.iter().map(|c| off_by_one(c, _point)).collect())
        }
        other => other.clone(),
    }
}

/// Remove the first conjunct from an And formula.
fn remove_constraint(formula: &Formula, _point: InjectionPoint) -> Formula {
    match formula {
        Formula::And(conjuncts) if conjuncts.len() > 1 => {
            Formula::And(conjuncts[1..].to_vec())
        }
        Formula::Implies(_pre, post) => *post.clone(),
        other => other.clone(),
    }
}

/// Weaken strict bounds: Lt -> Le, Gt -> Ge.
fn weaken_bound(formula: &Formula, _point: InjectionPoint) -> Formula {
    match formula {
        Formula::Lt(lhs, rhs) => Formula::Le(lhs.clone(), rhs.clone()),
        Formula::Gt(lhs, rhs) => Formula::Ge(lhs.clone(), rhs.clone()),
        Formula::And(conjuncts) => {
            Formula::And(conjuncts.iter().map(|c| weaken_bound(c, _point)).collect())
        }
        other => other.clone(),
    }
}

/// Swap left/right operands of binary operators.
fn swap_operands(formula: &Formula, _point: InjectionPoint) -> Formula {
    match formula {
        Formula::Lt(lhs, rhs) => Formula::Lt(rhs.clone(), lhs.clone()),
        Formula::Le(lhs, rhs) => Formula::Le(rhs.clone(), lhs.clone()),
        Formula::Gt(lhs, rhs) => Formula::Gt(rhs.clone(), lhs.clone()),
        Formula::Ge(lhs, rhs) => Formula::Ge(rhs.clone(), lhs.clone()),
        Formula::Sub(lhs, rhs) => Formula::Sub(rhs.clone(), lhs.clone()),
        Formula::Div(lhs, rhs) => Formula::Div(rhs.clone(), lhs.clone()),
        Formula::And(conjuncts) => {
            Formula::And(conjuncts.iter().map(|c| swap_operands(c, _point)).collect())
        }
        other => other.clone(),
    }
}

/// Replace integer literals with a large value to simulate overflow.
fn introduce_overflow(formula: &Formula, _point: InjectionPoint) -> Formula {
    match formula {
        Formula::Int(_) => Formula::Int(i128::MAX),
        Formula::BitVec { width, .. } => Formula::BitVec {
            value: (1i128 << (*width - 1)) - 1, // max positive for width
            width: *width,
        },
        Formula::And(conjuncts) => {
            Formula::And(conjuncts.iter().map(|c| introduce_overflow(c, _point)).collect())
        }
        other => other.clone(),
    }
}

/// Systematic fault injection engine.
///
/// Runs all combinations of fault types and injection points against a set of
/// VCs, then checks which faults are detected by the verification backend.
pub(crate) struct FaultCampaign<'a> {
    /// VCs to inject faults into.
    vcs: &'a [VerificationCondition],
    /// Which fault types to try.
    fault_types: Vec<FaultType>,
    /// Which injection points to try.
    injection_points: Vec<InjectionPoint>,
}

/// Result of running a fault injection campaign.
#[derive(Debug, Clone)]
pub(crate) struct CampaignResult {
    /// Faults that were detected (mutated VC was not proved).
    pub detected_faults: Vec<InjectedFault>,
    /// Faults that were missed (mutated VC was still proved).
    pub missed_faults: Vec<InjectedFault>,
    /// Detection rate: detected / total.
    pub detection_rate: f64,
}

impl<'a> FaultCampaign<'a> {
    /// Create a campaign with all fault types and injection points.
    pub(crate) fn full(vcs: &'a [VerificationCondition]) -> Self {
        Self {
            vcs,
            fault_types: vec![
                FaultType::FlipBoolean,
                FaultType::OffByOne,
                FaultType::RemoveConstraint,
                FaultType::WeakenBound,
                FaultType::SwapOperands,
                FaultType::IntroduceOverflow,
            ],
            injection_points: vec![
                InjectionPoint::PreCondition,
                InjectionPoint::PostCondition,
                InjectionPoint::LoopInvariant,
                InjectionPoint::TypeConstraint,
                InjectionPoint::BoundaryValue,
            ],
        }
    }

    /// Create a campaign with specific fault types and injection points.
    pub(crate) fn custom(
        vcs: &'a [VerificationCondition],
        fault_types: Vec<FaultType>,
        injection_points: Vec<InjectionPoint>,
    ) -> Self {
        Self {
            vcs,
            fault_types,
            injection_points,
        }
    }

    /// Run the campaign against a verification backend.
    ///
    /// For each (vc, point, fault) triple, injects the fault and runs the
    /// mutated VC through the backend. If the backend still proves it, the
    /// fault was "missed" (the verifier is insensitive to that mutation).
    pub(crate) fn run(&self, backend: &dyn trust_router::VerificationBackend) -> CampaignResult {
        let mut detected = Vec::new();
        let mut missed = Vec::new();

        for vc in self.vcs {
            for &point in &self.injection_points {
                for &fault in &self.fault_types {
                    let mutated = inject_fault(vc, point, fault);
                    let result = backend.verify(&mutated);

                    let record = InjectedFault {
                        original: vc.clone(),
                        mutated: mutated.clone(),
                        point,
                        fault,
                    };

                    if result.is_proved() {
                        missed.push(record);
                    } else {
                        detected.push(record);
                    }
                }
            }
        }

        let total = detected.len() + missed.len();
        let detection_rate = if total == 0 {
            1.0
        } else {
            detected.len() as f64 / total as f64
        };

        CampaignResult {
            detected_faults: detected,
            missed_faults: missed,
            detection_rate,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_func(name: &str, body: VerifiableBody) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body,
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn span(line: u32) -> SourceSpan {
        SourceSpan {
            file: "test.rs".into(),
            line_start: line,
            col_start: 1,
            line_end: line,
            col_end: 40,
        }
    }

    #[test]
    fn test_detect_command_injection() {
        let body = VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("input".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "std::io::read_line".into(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: span(10),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "std::process::Command::new".into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: span(20),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        };

        let func = test_func("run_user_command", body);
        let violations = detect_injections(&func, &InjectionPolicy::default());

        assert!(!violations.is_empty());
        assert!(violations.iter().any(|v| {
            matches!(&v.kind, SecurityViolationKind::CommandInjection { .. })
        }));
    }

    #[test]
    fn test_detect_privilege_operation() {
        let body = VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "libc::setuid".into(),
                        args: vec![Operand::Constant(ConstValue::Int(0))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: span(10),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        };

        let func = test_func("escalate", body);
        let violations = detect_injections(&func, &InjectionPolicy::default());

        assert!(violations.iter().any(|v| {
            matches!(&v.kind, SecurityViolationKind::PrivilegeEscalation { .. })
        }));
    }

    #[test]
    fn test_safe_code_no_injections() {
        let body = VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
            ],
            blocks: vec![
                BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        };

        let func = test_func("safe_fn", body);
        let violations = detect_injections(&func, &InjectionPolicy::default());
        assert!(violations.is_empty());
    }

    #[test]
    fn test_default_policy_has_patterns() {
        let policy = InjectionPolicy::default();
        assert!(!policy.command_patterns.is_empty());
        assert!(!policy.syscall_patterns.is_empty());
        assert!(!policy.format_patterns.is_empty());
        assert!(!policy.alloc_patterns.is_empty());
        assert!(!policy.privilege_patterns.is_empty());
    }

    // -----------------------------------------------------------------------
    // Fault injection tests
    // -----------------------------------------------------------------------

    fn sample_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "test::add".to_string(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    #[test]
    fn test_flip_boolean_literal() {
        let vc = sample_vc(Formula::Bool(true));
        let mutated = inject_fault(&vc, InjectionPoint::PreCondition, FaultType::FlipBoolean);
        assert_eq!(mutated.formula, Formula::Bool(false));
    }

    #[test]
    fn test_flip_boolean_negation_removed() {
        let inner = Formula::Bool(true);
        let vc = sample_vc(Formula::Not(Box::new(inner.clone())));
        let mutated = inject_fault(&vc, InjectionPoint::PostCondition, FaultType::FlipBoolean);
        assert_eq!(mutated.formula, inner);
    }

    #[test]
    fn test_flip_boolean_and_negates_first() {
        let vc = sample_vc(Formula::And(vec![
            Formula::Bool(true),
            Formula::Bool(false),
        ]));
        let mutated = inject_fault(&vc, InjectionPoint::PreCondition, FaultType::FlipBoolean);
        match &mutated.formula {
            Formula::And(conjuncts) => {
                assert_eq!(conjuncts.len(), 2);
                assert!(matches!(&conjuncts[0], Formula::Not(_)));
            }
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn test_off_by_one_int() {
        let vc = sample_vc(Formula::Int(42));
        let mutated = inject_fault(&vc, InjectionPoint::BoundaryValue, FaultType::OffByOne);
        assert_eq!(mutated.formula, Formula::Int(43));
    }

    #[test]
    fn test_off_by_one_bitvec() {
        let vc = sample_vc(Formula::BitVec { value: 10, width: 32 });
        let mutated = inject_fault(&vc, InjectionPoint::BoundaryValue, FaultType::OffByOne);
        assert_eq!(mutated.formula, Formula::BitVec { value: 11, width: 32 });
    }

    #[test]
    fn test_remove_constraint_and() {
        let vc = sample_vc(Formula::And(vec![
            Formula::Bool(true),
            Formula::Bool(false),
            Formula::Int(1),
        ]));
        let mutated = inject_fault(
            &vc,
            InjectionPoint::LoopInvariant,
            FaultType::RemoveConstraint,
        );
        match &mutated.formula {
            Formula::And(conjuncts) => assert_eq!(conjuncts.len(), 2),
            other => panic!("expected And with 2 conjuncts, got {other:?}"),
        }
    }

    #[test]
    fn test_remove_constraint_implies() {
        let vc = sample_vc(Formula::Implies(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Int(42)),
        ));
        let mutated = inject_fault(
            &vc,
            InjectionPoint::PreCondition,
            FaultType::RemoveConstraint,
        );
        assert_eq!(mutated.formula, Formula::Int(42));
    }

    #[test]
    fn test_weaken_bound_lt_to_le() {
        let lhs = Box::new(Formula::Var("x".into(), Sort::Int));
        let rhs = Box::new(Formula::Int(10));
        let vc = sample_vc(Formula::Lt(lhs.clone(), rhs.clone()));
        let mutated = inject_fault(
            &vc,
            InjectionPoint::TypeConstraint,
            FaultType::WeakenBound,
        );
        assert!(matches!(mutated.formula, Formula::Le(_, _)));
    }

    #[test]
    fn test_weaken_bound_gt_to_ge() {
        let lhs = Box::new(Formula::Var("x".into(), Sort::Int));
        let rhs = Box::new(Formula::Int(0));
        let vc = sample_vc(Formula::Gt(lhs.clone(), rhs.clone()));
        let mutated = inject_fault(
            &vc,
            InjectionPoint::TypeConstraint,
            FaultType::WeakenBound,
        );
        assert!(matches!(mutated.formula, Formula::Ge(_, _)));
    }

    #[test]
    fn test_swap_operands_lt() {
        let lhs = Box::new(Formula::Var("a".into(), Sort::Int));
        let rhs = Box::new(Formula::Var("b".into(), Sort::Int));
        let vc = sample_vc(Formula::Lt(lhs.clone(), rhs.clone()));
        let mutated = inject_fault(
            &vc,
            InjectionPoint::PostCondition,
            FaultType::SwapOperands,
        );
        match &mutated.formula {
            Formula::Lt(new_lhs, new_rhs) => {
                assert_eq!(**new_lhs, Formula::Var("b".into(), Sort::Int));
                assert_eq!(**new_rhs, Formula::Var("a".into(), Sort::Int));
            }
            other => panic!("expected Lt, got {other:?}"),
        }
    }

    #[test]
    fn test_swap_operands_sub() {
        let lhs = Box::new(Formula::Int(10));
        let rhs = Box::new(Formula::Int(3));
        let vc = sample_vc(Formula::Sub(lhs, rhs));
        let mutated = inject_fault(
            &vc,
            InjectionPoint::PostCondition,
            FaultType::SwapOperands,
        );
        match &mutated.formula {
            Formula::Sub(new_lhs, new_rhs) => {
                assert_eq!(**new_lhs, Formula::Int(3));
                assert_eq!(**new_rhs, Formula::Int(10));
            }
            other => panic!("expected Sub, got {other:?}"),
        }
    }

    #[test]
    fn test_introduce_overflow_int() {
        let vc = sample_vc(Formula::Int(42));
        let mutated = inject_fault(
            &vc,
            InjectionPoint::BoundaryValue,
            FaultType::IntroduceOverflow,
        );
        assert_eq!(mutated.formula, Formula::Int(i128::MAX));
    }

    #[test]
    fn test_introduce_overflow_bitvec() {
        let vc = sample_vc(Formula::BitVec { value: 5, width: 8 });
        let mutated = inject_fault(
            &vc,
            InjectionPoint::BoundaryValue,
            FaultType::IntroduceOverflow,
        );
        match &mutated.formula {
            Formula::BitVec { value, width } => {
                assert_eq!(*width, 8);
                assert_eq!(*value, 127); // (1 << 7) - 1
            }
            other => panic!("expected BitVec, got {other:?}"),
        }
    }

    #[test]
    fn test_inject_fault_preserves_vc_metadata() {
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test::div".to_string(),
            location: SourceSpan {
                file: "div.rs".into(),
                line_start: 42,
                col_start: 5,
                line_end: 42,
                col_end: 20,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
        };

        let mutated = inject_fault(&vc, InjectionPoint::PreCondition, FaultType::FlipBoolean);
        assert!(matches!(mutated.kind, VcKind::DivisionByZero));
        assert_eq!(mutated.function, "test::div");
        assert_eq!(mutated.location.line_start, 42);
    }

    /// Mock backend that always proves (for testing missed faults).
    struct AlwaysProvesBackend;

    impl trust_router::VerificationBackend for AlwaysProvesBackend {
        fn name(&self) -> &str {
            "always-proves"
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Proved {
                solver: "always-proves".to_string(),
                time_ms: 0,
                strength: trust_types::ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, }
        }
    }

    /// Mock backend that always fails (for testing detected faults).
    struct AlwaysFailsBackend;

    impl trust_router::VerificationBackend for AlwaysFailsBackend {
        fn name(&self) -> &str {
            "always-fails"
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Failed {
                solver: "always-fails".to_string(),
                time_ms: 0,
                counterexample: None,
            }
        }
    }

    #[test]
    fn test_campaign_all_detected() {
        let vcs = vec![sample_vc(Formula::Bool(true))];
        let campaign = FaultCampaign::full(&vcs);
        let result = campaign.run(&AlwaysFailsBackend);

        assert!(result.missed_faults.is_empty());
        assert!(!result.detected_faults.is_empty());
        assert!((result.detection_rate - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_campaign_all_missed() {
        let vcs = vec![sample_vc(Formula::Bool(true))];
        let campaign = FaultCampaign::full(&vcs);
        let result = campaign.run(&AlwaysProvesBackend);

        assert!(result.detected_faults.is_empty());
        assert!(!result.missed_faults.is_empty());
        assert!(result.detection_rate < f64::EPSILON);
    }

    #[test]
    fn test_campaign_empty_vcs() {
        let vcs: Vec<VerificationCondition> = vec![];
        let campaign = FaultCampaign::full(&vcs);
        let result = campaign.run(&AlwaysFailsBackend);

        assert!(result.detected_faults.is_empty());
        assert!(result.missed_faults.is_empty());
        assert!((result.detection_rate - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_campaign_custom_subset() {
        let vcs = vec![sample_vc(Formula::Int(5))];
        let campaign = FaultCampaign::custom(
            &vcs,
            vec![FaultType::OffByOne],
            vec![InjectionPoint::BoundaryValue],
        );
        let result = campaign.run(&AlwaysFailsBackend);

        // 1 vc * 1 fault * 1 point = 1 injection
        assert_eq!(result.detected_faults.len(), 1);
        assert_eq!(result.missed_faults.len(), 0);
    }

    #[test]
    fn test_campaign_records_metadata() {
        let vcs = vec![sample_vc(Formula::Bool(true))];
        let campaign = FaultCampaign::custom(
            &vcs,
            vec![FaultType::FlipBoolean],
            vec![InjectionPoint::PreCondition],
        );
        let result = campaign.run(&AlwaysFailsBackend);

        assert_eq!(result.detected_faults.len(), 1);
        let fault = &result.detected_faults[0];
        assert_eq!(fault.point, InjectionPoint::PreCondition);
        assert_eq!(fault.fault, FaultType::FlipBoolean);
        assert_eq!(fault.original.formula, Formula::Bool(true));
        assert_eq!(fault.mutated.formula, Formula::Bool(false));
    }
}
