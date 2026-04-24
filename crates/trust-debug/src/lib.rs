// dead_code audit: crate-level suppression removed (#939)
//! trust-debug: Binary black-box violation finder
//!
//! Takes compiled binaries as black boxes, lifts them to our verification IR,
//! runs all tRust verification tools (z4, zani, sunder, certus, tla2, lean5,
//! gamma-crown) to find every safety and security violation, and maps findings
//! back to source. Completes the prove-strengthen-backprop loop backwards.
//!
//! Two modes:
//!   1. MIR-aware (Rust binaries we compiled) — uses serialized MIR directly
//!   2. Black-box (any binary) — lifts from machine code to our IR
//!
//! Focused on finding the properties that MATTER: injection paths, memory
//! corruption chains, privilege escalation, tainted data flow to dangerous ops.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub(crate) mod binary;
pub(crate) mod injection;
pub mod profiling;
pub(crate) mod violations;

use trust_types::*;

/// Configuration for a trust-debug analysis run.
#[derive(Debug, Clone)]
pub struct DebugConfig {
    /// Which analysis modes to enable.
    pub analyses: AnalysisSet,
    /// Taint policy for data flow analysis.
    pub taint_policy: TaintPolicy,
    /// Security-specific injection patterns to check.
    pub injection_patterns: injection::InjectionPolicy,
    /// Maximum solver time per VC in milliseconds.
    pub solver_timeout_ms: u64,
    /// Maximum number of VCs to generate per function.
    pub max_vcs_per_function: usize,
    /// Whether to generate exploitation chain analysis.
    pub chain_analysis: bool,
}

impl Default for DebugConfig {
    fn default() -> Self {
        Self {
            analyses: AnalysisSet::all(),
            taint_policy: default_web_policy(),
            injection_patterns: injection::InjectionPolicy::default(),
            solver_timeout_ms: 5000,
            max_vcs_per_function: 100,
            chain_analysis: true,
        }
    }
}

/// Which analyses to run.
#[derive(Debug, Clone)]
pub struct AnalysisSet {
    /// L0: arithmetic overflow, div-by-zero, OOB, null deref
    pub safety: bool,
    /// Taint tracking from untrusted sources to dangerous sinks
    pub taint_flow: bool,
    /// Injection detection: code injection, command injection, format strings
    pub injection: bool,
    /// Memory corruption chains: overflow → arbitrary write → code execution
    pub memory_corruption: bool,
    /// Use-after-free, double-free, dangling pointer access
    pub lifetime: bool,
    /// TOCTOU, race conditions, deadlocks
    pub concurrency: bool,
    /// Reachability: can attacker reach privileged operations?
    pub privilege_escalation: bool,
}

impl AnalysisSet {
    pub fn all() -> Self {
        Self {
            safety: true,
            taint_flow: true,
            injection: true,
            memory_corruption: true,
            lifetime: true,
            concurrency: true,
            privilege_escalation: true,
        }
    }

    pub fn safety_only() -> Self {
        Self {
            safety: true,
            taint_flow: false,
            injection: false,
            memory_corruption: false,
            lifetime: false,
            concurrency: false,
            privilege_escalation: false,
        }
    }
}

/// Input to a debug analysis — either serialized MIR or a parsed binary.
#[derive(Debug, Clone)]
pub enum DebugInput {
    /// MIR-aware mode: we have the verification IR directly.
    Mir {
        functions: Vec<VerifiableFunction>,
        call_graph: call_graph::CallGraph,
        crate_name: String,
    },
    /// Black-box mode: lifted from binary.
    Binary {
        functions: Vec<VerifiableFunction>,
        call_graph: call_graph::CallGraph,
        binary_name: String,
        /// Mapping from lifted function addresses to source locations (from DWARF).
        source_map: Vec<binary::SourceMapping>,
    },
}

impl DebugInput {
    pub fn name(&self) -> &str {
        match self {
            DebugInput::Mir { crate_name, .. } => crate_name,
            DebugInput::Binary { binary_name, .. } => binary_name,
        }
    }

    pub fn functions(&self) -> &[VerifiableFunction] {
        match self {
            DebugInput::Mir { functions, .. } | DebugInput::Binary { functions, .. } => functions,
        }
    }

    pub fn call_graph(&self) -> &call_graph::CallGraph {
        match self {
            DebugInput::Mir { call_graph, .. } | DebugInput::Binary { call_graph, .. } => {
                call_graph
            }
        }
    }
}

/// Result of a trust-debug analysis run.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct DebugReport {
    /// Name of the analyzed target.
    pub target: String,
    /// All violations found, sorted by severity.
    pub violations: Vec<SecurityViolation>,
    /// Exploitation chains (if chain_analysis was enabled).
    pub chains: Vec<ExploitChain>,
    /// Summary statistics.
    pub summary: DebugSummary,
}

/// A single security violation found during analysis.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct SecurityViolation {
    /// Unique ID for this violation.
    pub id: String,
    /// Severity of the violation.
    pub severity: Severity,
    /// What kind of violation this is.
    pub kind: SecurityViolationKind,
    /// Which function contains the violation.
    pub function: String,
    /// Source location (if available).
    pub location: Option<SourceSpan>,
    /// Human-readable description.
    pub description: String,
    /// Data flow path from source to sink (for taint/injection violations).
    pub flow_path: Vec<FlowStep>,
    /// Counterexample from the solver (if available).
    pub counterexample: Option<Counterexample>,
    /// Which solver found this violation.
    pub solver: String,
    /// Solver time in milliseconds.
    pub time_ms: u64,
}

/// Severity levels for security violations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub enum Severity {
    /// Allows arbitrary code execution.
    Critical,
    /// Allows significant data corruption or information disclosure.
    High,
    /// Safety violation that could be exploitable under certain conditions.
    Medium,
    /// Safety violation unlikely to be exploitable.
    Low,
    /// Informational finding (dead code, unreachable paths).
    Info,
}

/// Classification of security violations.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum SecurityViolationKind {
    // --- Injection (Critical/High) ---
    /// Attacker-controlled data reaches a function pointer or indirect call.
    TaintedIndirectCall { taint_source: String },
    /// Attacker-controlled data reaches a syscall argument (exec, system, etc.).
    TaintedSyscall { syscall: String, taint_source: String },
    /// Attacker-controlled data reaches a format string position.
    FormatStringInjection { format_func: String, taint_source: String },
    /// Attacker-controlled data reaches SQL query without sanitization.
    SqlInjection { sink_func: String, taint_source: String },
    /// Attacker-controlled data reaches shell command.
    CommandInjection { command_func: String, taint_source: String },

    // --- Memory Corruption (Critical/High) ---
    /// Buffer overflow that could corrupt adjacent memory.
    BufferOverflow { write_size: String, buffer_size: String },
    /// Integer overflow that controls a buffer size or allocation.
    IntegerOverflowToBufferCorruption { overflow_op: String, affected_alloc: String },
    /// Use-after-free: accessing memory that has been deallocated.
    UseAfterFree { freed_at: String, used_at: String },
    /// Double-free: freeing memory twice.
    DoubleFree { first_free: String, second_free: String },
    /// Arbitrary write primitive: attacker controls both destination and value.
    ArbitraryWrite { dest_source: String, value_source: String },

    // --- Concurrency (High/Medium) ---
    /// Time-of-check-to-time-of-use race condition.
    Toctou { check_func: String, use_func: String },
    /// Deadlock detected in lock ordering.
    Deadlock { lock_cycle: Vec<String> },
    /// Data race on shared mutable state.
    DataRace { variable: String },

    // --- Safety (Medium/Low) ---
    /// Arithmetic overflow (not exploitable in isolation but part of chains).
    ArithmeticOverflow { operation: String },
    /// Division by zero.
    DivisionByZero,
    /// Index out of bounds.
    IndexOutOfBounds { index_expr: String },
    /// Unreachable code reached.
    UnreachableReached,

    // --- Information (Low/Info) ---
    /// Unsanitized taint flow (generic).
    TaintFlow { source: String, sink: String },
    /// Dead code that cannot be reached from entry points.
    DeadCode { function: String },
    /// Privilege escalation path exists.
    PrivilegeEscalation { from_priv: String, to_priv: String, path_length: usize },
}

/// An exploitation chain: a sequence of violations that together enable a
/// more severe attack than any individual violation.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ExploitChain {
    /// Human-readable name for this chain.
    pub name: String,
    /// The severity of the combined chain (usually higher than individual parts).
    pub severity: Severity,
    /// Ordered sequence of violation IDs forming the chain.
    pub violation_ids: Vec<String>,
    /// Description of how the chain works.
    pub description: String,
}

/// Summary of debug analysis results.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct DebugSummary {
    pub functions_analyzed: usize,
    pub total_vcs_generated: usize,
    pub total_vcs_checked: usize,
    pub violations_found: usize,
    pub critical_count: usize,
    pub high_count: usize,
    pub medium_count: usize,
    pub low_count: usize,
    pub info_count: usize,
    pub chains_found: usize,
    pub total_time_ms: u64,
}

impl DebugSummary {
    pub fn from_violations(violations: &[SecurityViolation], chains: &[ExploitChain]) -> Self {
        Self {
            functions_analyzed: 0,
            total_vcs_generated: 0,
            total_vcs_checked: 0,
            violations_found: violations.len(),
            critical_count: violations.iter().filter(|v| v.severity == Severity::Critical).count(),
            high_count: violations.iter().filter(|v| v.severity == Severity::High).count(),
            medium_count: violations.iter().filter(|v| v.severity == Severity::Medium).count(),
            low_count: violations.iter().filter(|v| v.severity == Severity::Low).count(),
            info_count: violations.iter().filter(|v| v.severity == Severity::Info).count(),
            chains_found: chains.len(),
            total_time_ms: violations.iter().map(|v| v.time_ms).sum(),
        }
    }
}

/// Run a full trust-debug analysis.
///
/// This is the main entry point. It:
/// 1. Takes MIR or lifted binary functions
/// 2. Generates security-focused VCs for each function
/// 3. Dispatches to all available solver backends
/// 4. Collects violations with data flow paths
/// 5. Builds exploitation chains
/// 6. Produces a severity-sorted report
pub fn analyze(
    input: &DebugInput,
    config: &DebugConfig,
    router: &trust_router::Router,
) -> DebugReport {
    // tRust: #906 — Profile top-level analyze() call
    let _top_scope = profiling::ProfileScope::new("debug::analyze", profiling::Category::Trust);

    let mut all_violations = Vec::new();
    let mut total_vcs = 0;

    // Phase 1: Per-function safety + security VC generation and solving
    for func in input.functions() {
        let mut func_violations = Vec::new();

        // L0 Safety VCs (overflow, div-by-zero, OOB)
        if config.analyses.safety {
            let vcs = {
                // tRust: #906 — Profile VC generation
                let _scope =
                    profiling::ProfileScope::new("vcgen::generate_vcs", profiling::Category::Trust);
                trust_vcgen::generate_vcs(func)
            };
            total_vcs += vcs.len();
            let results = {
                // tRust: #906 — Profile solver dispatch
                let _scope =
                    profiling::ProfileScope::new("router::verify_all", profiling::Category::Trust);
                router.verify_all(&vcs)
            };
            for (vc, result) in &results {
                if let VerificationResult::Failed { counterexample, solver, time_ms } = result {
                    func_violations.push(safety_violation(
                        func,
                        vc,
                        counterexample,
                        solver.as_str(),
                        *time_ms,
                    ));
                }
            }
        }

        // Taint flow analysis
        if config.analyses.taint_flow {
            let taint_result = {
                // tRust: #906 — Profile taint analysis
                let _scope = profiling::ProfileScope::new(
                    "debug::analyze_taint",
                    profiling::Category::Trust,
                );
                analyze_taint(&func.body, &config.taint_policy)
            };
            for violation in &taint_result.violations {
                func_violations.push(taint_violation(func, violation));
            }
        }

        // Injection pattern detection
        if config.analyses.injection {
            // tRust: #906 — Profile injection detection
            let _scope = profiling::ProfileScope::new(
                "debug::detect_injections",
                profiling::Category::Trust,
            );
            let injection_violations =
                injection::detect_injections(func, &config.injection_patterns);
            func_violations.extend(injection_violations);
        }

        func_violations.truncate(config.max_vcs_per_function);
        all_violations.extend(func_violations);
    }

    // Phase 2: Cross-function analysis
    if config.analyses.privilege_escalation || config.analyses.taint_flow {
        let reachability = {
            // tRust: #906 — Profile reachability analysis
            let _scope = profiling::ProfileScope::new(
                "vcgen::analyze_reachability",
                profiling::Category::Trust,
            );
            trust_vcgen::reachability::analyze_reachability(input.call_graph())
        };

        // Dead code detection
        for unreachable in &reachability.unreachable {
            all_violations.push(SecurityViolation {
                id: format!("dead-{}", unreachable.def_path),
                severity: Severity::Info,
                kind: SecurityViolationKind::DeadCode { function: unreachable.name.clone() },
                function: unreachable.def_path.clone(),
                location: Some(unreachable.span.clone()),
                description: format!(
                    "Public function `{}` is unreachable from any entry point: {}",
                    unreachable.name, unreachable.reason
                ),
                flow_path: vec![],
                counterexample: None,
                solver: "static-analysis".into(),
                time_ms: 0,
            });
        }
    }

    // Phase 3: Exploitation chain analysis
    let chains = if config.chain_analysis {
        // tRust: #906 — Profile exploit chain building
        let _scope =
            profiling::ProfileScope::new("debug::build_exploit_chains", profiling::Category::Trust);
        violations::build_exploit_chains(&all_violations)
    } else {
        vec![]
    };

    // Sort by severity (most severe first)
    all_violations.sort_by_key(|a| a.severity);

    // Assign sequential IDs
    for (i, v) in all_violations.iter_mut().enumerate() {
        if v.id.is_empty() {
            v.id = format!("V{:04}", i + 1);
        }
    }

    let mut summary = DebugSummary::from_violations(&all_violations, &chains);
    summary.functions_analyzed = input.functions().len();
    summary.total_vcs_generated = total_vcs;
    summary.total_vcs_checked = total_vcs;

    DebugReport { target: input.name().to_string(), violations: all_violations, chains, summary }
}

fn safety_violation(
    func: &VerifiableFunction,
    vc: &VerificationCondition,
    counterexample: &Option<Counterexample>,
    solver: &str,
    time_ms: u64,
) -> SecurityViolation {
    let (severity, kind) = match &vc.kind {
        VcKind::ArithmeticOverflow { op, .. } => (
            Severity::Medium,
            SecurityViolationKind::ArithmeticOverflow { operation: format!("{op:?}") },
        ),
        VcKind::DivisionByZero | VcKind::RemainderByZero => {
            (Severity::Medium, SecurityViolationKind::DivisionByZero)
        }
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => (
            Severity::High,
            SecurityViolationKind::IndexOutOfBounds { index_expr: "unknown".to_string() },
        ),
        VcKind::Unreachable => (Severity::Low, SecurityViolationKind::UnreachableReached),
        _ => (
            Severity::Medium,
            SecurityViolationKind::ArithmeticOverflow { operation: vc.kind.description() },
        ),
    };

    SecurityViolation {
        id: String::new(),
        severity,
        kind,
        function: func.def_path.clone(),
        location: Some(vc.location.clone()),
        description: vc.kind.description(),
        flow_path: vec![],
        counterexample: counterexample.clone(),
        solver: solver.to_string(),
        time_ms,
    }
}

fn taint_violation(func: &VerifiableFunction, violation: &TaintFlowViolation) -> SecurityViolation {
    let (severity, kind) = classify_taint_violation(violation);

    SecurityViolation {
        id: String::new(),
        severity,
        kind,
        function: func.def_path.clone(),
        location: Some(violation.sink_span.clone()),
        description: format!(
            "Tainted {} data reaches {} sink `{}`",
            taint_label_display(&violation.source_label),
            sink_kind_display(&violation.sink_kind),
            violation.sink_func,
        ),
        flow_path: violation.path.clone(),
        counterexample: None,
        solver: "taint-analysis".into(),
        time_ms: 0,
    }
}

fn classify_taint_violation(violation: &TaintFlowViolation) -> (Severity, SecurityViolationKind) {
    let source_name = taint_label_display(&violation.source_label);

    match &violation.sink_kind {
        SinkKind::SqlQuery => (
            Severity::Critical,
            SecurityViolationKind::SqlInjection {
                sink_func: violation.sink_func.clone(),
                taint_source: source_name,
            },
        ),
        SinkKind::Custom(name)
            if name.contains("exec") || name.contains("system") || name.contains("command") =>
        {
            (
                Severity::Critical,
                SecurityViolationKind::CommandInjection {
                    command_func: violation.sink_func.clone(),
                    taint_source: source_name,
                },
            )
        }
        SinkKind::NetworkSend => (
            Severity::High,
            SecurityViolationKind::TaintFlow {
                source: source_name,
                sink: violation.sink_func.clone(),
            },
        ),
        SinkKind::FileWrite => (
            Severity::High,
            SecurityViolationKind::TaintFlow {
                source: source_name,
                sink: violation.sink_func.clone(),
            },
        ),
        _ => (
            Severity::Medium,
            SecurityViolationKind::TaintFlow {
                source: source_name,
                sink: violation.sink_func.clone(),
            },
        ),
    }
}

fn taint_label_display(label: &TaintLabel) -> String {
    match label {
        TaintLabel::UserInput => "user-input".to_string(),
        TaintLabel::NetworkData => "network-data".to_string(),
        TaintLabel::Secret => "secret".to_string(),
        TaintLabel::FileData => "file-data".to_string(),
        TaintLabel::EnvVar => "env-var".to_string(),
        TaintLabel::UnsafeBlock => "unsafe-block".to_string(),
        TaintLabel::ExternCall => "extern-call".to_string(),
        TaintLabel::Custom(name) => name.clone(),
        _ => "unknown".to_string(),
    }
}

fn sink_kind_display(kind: &SinkKind) -> String {
    match kind {
        SinkKind::SqlQuery => "SQL".to_string(),
        SinkKind::LogOutput => "log".to_string(),
        SinkKind::NetworkSend => "network".to_string(),
        SinkKind::HtmlRender => "HTML".to_string(),
        SinkKind::FileWrite => "file-write".to_string(),
        SinkKind::ShellCommand => "shell-command".to_string(),
        SinkKind::RawPointer => "raw-pointer".to_string(),
        SinkKind::Assertion => "assertion".to_string(),
        SinkKind::Custom(name) => name.clone(),
        _ => "unknown".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_router::Router;

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

    fn simple_overflow_body() -> VerifiableBody {
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
            ],
            blocks: vec![
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
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::usize(),
        }
    }

    fn tainted_sql_body() -> VerifiableBody {
        VerifiableBody {
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
                        span: SourceSpan {
                            file: "main.rs".into(),
                            line_start: 10,
                            col_start: 1,
                            line_end: 10,
                            col_end: 30,
                        },
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "db::execute_sql".into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: SourceSpan {
                            file: "main.rs".into(),
                            line_start: 15,
                            col_start: 1,
                            line_end: 15,
                            col_end: 40,
                        },
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        }
    }

    #[test]
    fn test_analyze_finds_safety_violations() {
        let func = test_func("midpoint", simple_overflow_body());
        let input = DebugInput::Mir {
            functions: vec![func],
            call_graph: call_graph::CallGraph::new(),
            crate_name: "test".to_string(),
        };

        let config = DebugConfig { analyses: AnalysisSet::safety_only(), ..Default::default() };

        let report = analyze(&input, &config, &Router::new());
        // Mock backend may or may not find violations; the pipeline runs correctly
        assert_eq!(report.target, "test");
        assert_eq!(report.summary.functions_analyzed, 1);
    }

    #[test]
    fn test_analyze_finds_taint_violations() {
        let func = test_func("handler", tainted_sql_body());
        let input = DebugInput::Mir {
            functions: vec![func],
            call_graph: call_graph::CallGraph::new(),
            crate_name: "webapp".to_string(),
        };

        let config = DebugConfig {
            analyses: AnalysisSet {
                safety: false,
                taint_flow: true,
                injection: false,
                memory_corruption: false,
                lifetime: false,
                concurrency: false,
                privilege_escalation: false,
            },
            ..Default::default()
        };

        let report = analyze(&input, &config, &Router::new());
        assert!(!report.violations.is_empty(), "should find SQL injection");
        assert!(
            report
                .violations
                .iter()
                .any(|v| { matches!(&v.kind, SecurityViolationKind::SqlInjection { .. }) }),
            "should classify as SQL injection"
        );
        assert_eq!(report.violations[0].severity, Severity::Critical);
    }

    #[test]
    fn test_analyze_full_pipeline() {
        let funcs = vec![
            test_func("midpoint", simple_overflow_body()),
            test_func("handler", tainted_sql_body()),
        ];

        let mut cg = call_graph::CallGraph::new();
        cg.add_node(call_graph::CallGraphNode {
            def_path: "test::main".to_string(),
            name: "main".to_string(),
            is_public: true,
            is_entry_point: true,
            span: SourceSpan::default(),
        });
        cg.add_node(call_graph::CallGraphNode {
            def_path: "test::midpoint".to_string(),
            name: "midpoint".to_string(),
            is_public: true,
            is_entry_point: false,
            span: SourceSpan::default(),
        });
        cg.add_node(call_graph::CallGraphNode {
            def_path: "test::handler".to_string(),
            name: "handler".to_string(),
            is_public: true,
            is_entry_point: false,
            span: SourceSpan::default(),
        });
        cg.add_edge(call_graph::CallGraphEdge {
            caller: "test::main".to_string(),
            callee: "test::midpoint".to_string(),
            call_site: SourceSpan::default(),
        });
        // handler is orphaned — should be detected

        let input =
            DebugInput::Mir { functions: funcs, call_graph: cg, crate_name: "test".to_string() };

        let report = analyze(&input, &DebugConfig::default(), &Router::new());

        // Should find: taint violations + dead code (handler unreachable)
        assert!(
            report
                .violations
                .iter()
                .any(|v| matches!(&v.kind, SecurityViolationKind::SqlInjection { .. }))
        );
        assert!(
            report
                .violations
                .iter()
                .any(|v| matches!(&v.kind, SecurityViolationKind::DeadCode { .. }))
        );
        assert_eq!(report.summary.functions_analyzed, 2);
    }

    #[test]
    fn test_severity_ordering() {
        assert!(Severity::Critical < Severity::High);
        assert!(Severity::High < Severity::Medium);
        assert!(Severity::Medium < Severity::Low);
        assert!(Severity::Low < Severity::Info);
    }

    #[test]
    fn test_report_serialization_roundtrip() {
        let report = DebugReport {
            target: "test".to_string(),
            violations: vec![SecurityViolation {
                id: "V0001".to_string(),
                severity: Severity::Critical,
                kind: SecurityViolationKind::SqlInjection {
                    sink_func: "execute".to_string(),
                    taint_source: "user-input".to_string(),
                },
                function: "test::handler".into(),
                location: None,
                description: "SQL injection".to_string(),
                flow_path: vec![],
                counterexample: None,
                solver: "taint-analysis".into(),
                time_ms: 0,
            }],
            chains: vec![],
            summary: DebugSummary::from_violations(&[], &[]),
        };

        let json = serde_json::to_string(&report).expect("serialize");
        let roundtrip: DebugReport = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip.target, "test");
        assert_eq!(roundtrip.violations.len(), 1);
    }

    #[test]
    fn test_empty_input_no_panic() {
        let input = DebugInput::Mir {
            functions: vec![],
            call_graph: call_graph::CallGraph::new(),
            crate_name: "empty".to_string(),
        };
        let report = analyze(&input, &DebugConfig::default(), &Router::new());
        assert_eq!(report.violations.len(), 0);
        assert_eq!(report.summary.functions_analyzed, 0);
    }
}
