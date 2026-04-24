// trust-router/tests/full_pipeline.rs: Full end-to-end pipeline integration tests
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::Arc;
use std::time::Duration;

use trust_report::build_json_report;
use trust_router::aggregation::{self, SolverContribution};
use trust_router::cegar_backend;
use trust_router::enrichment;
use trust_router::fallback;
use trust_router::health;
use trust_router::independence;
use trust_router::query_cache;
use trust_router::replay;
use trust_router::scheduler;
use trust_router::strategies::Strategy;
use trust_router::{BackendRole, Router, VerificationBackend};
use trust_symex::adapter::{AdapterConfig, replay_with_trace};
use trust_types::*;
use trust_vcgen::generate_vcs;

fn midpoint_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "get_midpoint".to_string(),
        def_path: "pipeline::get_midpoint".to_string(),
        span: SourceSpan {
            file: "src/pipeline.rs".to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 3,
            col_end: 1,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                LocalDecl { index: 4, ty: Ty::usize(), name: None },
                LocalDecl { index: 5, ty: Ty::usize(), name: None },
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
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(4)),
                                Operand::Constant(ConstValue::Uint(2, 64)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(5))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn division_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "divide".to_string(),
        def_path: "pipeline::divide".to_string(),
        span: SourceSpan {
            file: "src/pipeline.rs".to_string(),
            line_start: 10,
            col_start: 1,
            line_end: 12,
            col_end: 1,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn recursive_countdown_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "countdown".to_string(),
        def_path: "pipeline::countdown".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "countdown".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
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

fn proved_by(solver: &str, strength: ProofStrength) -> VerificationResult {
    VerificationResult::Proved {
        solver: solver.into(),
        time_ms: 1,
        strength,
        proof_certificate: None,
        solver_warnings: None,
    }
}

fn failed_by(solver: &str, counterexample: Option<Counterexample>) -> VerificationResult {
    VerificationResult::Failed { solver: solver.into(), time_ms: 1, counterexample }
}

fn unknown_by(solver: &str, reason: &str) -> VerificationResult {
    VerificationResult::Unknown { solver: solver.into(), time_ms: 1, reason: reason.to_string() }
}

fn division_vc() -> VerificationCondition {
    generate_vcs(&division_function())
        .into_iter()
        .find(|vc| matches!(vc.kind, VcKind::DivisionByZero))
        .expect("division function should produce a division-by-zero VC")
}

fn midpoint_vc() -> VerificationCondition {
    generate_vcs(&midpoint_function())
        .into_iter()
        .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
        .expect("midpoint should produce an overflow VC")
}

fn crate_result(
    crate_name: &str,
    functions: Vec<FunctionVerificationResult>,
) -> CrateVerificationResult {
    let mut result = CrateVerificationResult::new(crate_name);
    for function in functions {
        result.add_function(function);
    }
    result
}

fn function_result(
    function_path: String,
    function_name: String,
    results: Vec<(VerificationCondition, VerificationResult)>,
) -> FunctionVerificationResult {
    FunctionVerificationResult {
        function_path,
        function_name,
        results,
        from_notes: 0,
        with_assumptions: 0,
    }
}

fn handles_l0(vc: &VerificationCondition) -> bool {
    matches!(vc.kind.proof_level(), ProofLevel::L0Safety)
}

fn handles_postcondition(vc: &VerificationCondition) -> bool {
    matches!(vc.kind, VcKind::Postcondition)
}

fn handles_precondition(vc: &VerificationCondition) -> bool {
    matches!(vc.kind, VcKind::Precondition { .. })
}

fn handles_temporal(vc: &VerificationCondition) -> bool {
    matches!(
        vc.kind,
        VcKind::DeadState { .. }
            | VcKind::Deadlock
            | VcKind::Temporal { .. }
            | VcKind::Liveness { .. }
            | VcKind::Fairness { .. }
            | VcKind::RefinementViolation { .. }
            | VcKind::ProtocolViolation { .. }
    )
}

struct SpecialtyBackend {
    name: &'static str,
    role: BackendRole,
    can_handle_fn: fn(&VerificationCondition) -> bool,
    result: VerificationResult,
}

impl SpecialtyBackend {
    fn new(
        name: &'static str,
        role: BackendRole,
        can_handle_fn: fn(&VerificationCondition) -> bool,
        result: VerificationResult,
    ) -> Self {
        Self { name, role, can_handle_fn, result }
    }
}

impl VerificationBackend for SpecialtyBackend {
    fn name(&self) -> &str {
        self.name
    }

    fn role(&self) -> BackendRole {
        self.role
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        (self.can_handle_fn)(vc)
    }

    fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
        self.result.clone()
    }
}

struct ReplayFailureBackend;

impl VerificationBackend for ReplayFailureBackend {
    fn name(&self) -> &str {
        "cex"
    }

    fn role(&self) -> BackendRole {
        BackendRole::SmtSolver
    }

    fn can_handle(&self, _vc: &VerificationCondition) -> bool {
        true
    }

    fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
        failed_by(
            "cex",
            Some(Counterexample::new(vec![
                ("_local1".into(), CounterexampleValue::Uint(10)),
                ("_local2".into(), CounterexampleValue::Uint(0)),
            ])),
        )
    }
}

struct RejectingBackend;

impl VerificationBackend for RejectingBackend {
    fn name(&self) -> &str {
        "rejecting"
    }

    fn role(&self) -> BackendRole {
        BackendRole::General
    }

    fn can_handle(&self, _vc: &VerificationCondition) -> bool {
        true
    }

    fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
        unknown_by("rejecting", "unsupported theory in primary backend")
    }
}

struct FunctionOutcomeBackend;

impl VerificationBackend for FunctionOutcomeBackend {
    fn name(&self) -> &str {
        "portfolio"
    }

    fn role(&self) -> BackendRole {
        BackendRole::General
    }

    fn can_handle(&self, _vc: &VerificationCondition) -> bool {
        true
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        match vc.function.as_str() {
            "get_midpoint" => proved_by("portfolio", ProofStrength::smt_unsat()),
            "divide" => failed_by(
                "portfolio",
                Some(Counterexample::new(vec![("y".into(), CounterexampleValue::Uint(0))])),
            ),
            _ => unknown_by("portfolio", "no configured function outcome"),
        }
    }
}

#[test]
fn test_full_pipeline_cegar_backend_with_vcgen_output() {
    // Since #194 (PDR safety-only routing), NonTermination VCs are NOT routed
    // to CEGAR. We verify that vcgen emits a NonTermination VC and that the
    // router handles it via the fallback mock backend.
    let vcs = generate_vcs(&recursive_countdown_function());
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::NonTermination { .. })),
        "vcgen should emit a non-termination VC for recursion",
    );

    let router = Router::with_cegar(
        cegar_backend::CegarBackendConfig::default(),
        vec![Box::new(trust_router::mock_backend::MockBackend)],
    );
    let results = router.verify_all(&vcs);

    // NonTermination VC is handled by MockBackend, not CEGAR
    assert_eq!(results.len(), 1);

    let report = build_json_report("cegar_pipeline", &results);
    assert_eq!(report.summary.total_obligations, 1);
}

#[test]
fn test_full_pipeline_multi_backend_routing_by_proof_level() {
    let safety_vc = division_vc();
    let post_vc = VerificationCondition {
        kind: VcKind::Postcondition,
        function: "functional_post".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };
    let pre_vc = VerificationCondition {
        kind: VcKind::Precondition { callee: "callee".into() },
        function: "functional_pre".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };
    let domain_vc = VerificationCondition {
        kind: VcKind::Deadlock,
        function: "domain".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };
    let fallback_vc = VerificationCondition {
        kind: VcKind::ResilienceViolation {
            service: "storage".into(),
            failure_mode: "timeout".into(),
            reason: "transient".into(),
        },
        function: "resilience".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let router = Router::with_backends(vec![
        Box::new(SpecialtyBackend::new(
            "mock",
            BackendRole::General,
            |_| true,
            proved_by("mock", ProofStrength::smt_unsat()),
        )),
        Box::new(SpecialtyBackend::new(
            "certus",
            BackendRole::Ownership,
            handles_precondition,
            proved_by("certus", ProofStrength::deductive()),
        )),
        Box::new(SpecialtyBackend::new(
            "tla2",
            BackendRole::Temporal,
            handles_temporal,
            proved_by("tla2", ProofStrength::inductive()),
        )),
        Box::new(SpecialtyBackend::new(
            "zani",
            BackendRole::BoundedModelChecker,
            handles_l0,
            proved_by("zani", ProofStrength::bounded(8)),
        )),
        Box::new(SpecialtyBackend::new(
            "sunder",
            BackendRole::Deductive,
            handles_postcondition,
            proved_by("sunder", ProofStrength::deductive()),
        )),
    ]);

    let safety_result = router.verify_one(&safety_vc);
    let post_result = router.verify_one(&post_vc);
    let pre_result = router.verify_one(&pre_vc);
    let domain_result = router.verify_one(&domain_vc);
    let fallback_result = router.verify_one(&fallback_vc);

    assert_eq!(router.backend_plan(&safety_vc)[0].name, "zani");
    assert_eq!(router.backend_plan(&post_vc)[0].name, "sunder");
    assert_eq!(router.backend_plan(&pre_vc)[0].name, "certus");
    assert_eq!(router.backend_plan(&domain_vc)[0].name, "tla2");
    assert_eq!(router.backend_plan(&fallback_vc)[0].name, "mock");

    assert_eq!(safety_result.solver_name(), "zani");
    assert_eq!(post_result.solver_name(), "sunder");
    assert_eq!(pre_result.solver_name(), "certus");
    assert_eq!(domain_result.solver_name(), "tla2");
    assert_eq!(fallback_result.solver_name(), "mock");

    let results = vec![
        (safety_vc, safety_result),
        (post_vc, post_result),
        (pre_vc, pre_result),
        (domain_vc, domain_result),
        (fallback_vc, fallback_result),
    ];
    let report = build_json_report("routing_pipeline", &results);
    assert_eq!(report.summary.total_obligations, 5);
    assert_eq!(report.summary.total_proved, 5);
}

#[test]
fn test_full_pipeline_replay_counterexample() {
    let func = division_function();
    let vc = division_vc();
    let router = Router::with_backends(vec![Box::new(ReplayFailureBackend)]);

    let (result, replay_result) =
        router.verify_and_replay(&vc, Some(&func.body.blocks), &replay::ReplayConfig::default());

    assert!(matches!(result, VerificationResult::Failed { counterexample: Some(_), .. }));

    let replay_result =
        replay_result.expect("counterexample replay should run").expect("replay should succeed");
    match replay_result {
        replay::ReplayResult::RealBug(concrete) => {
            assert_eq!(concrete.trace, vec![0]);
            assert_eq!(concrete.counterexample.assignments.len(), 2);
        }
        replay::ReplayResult::Spurious(_) => {
            panic!("division-by-zero replay should classify as a real bug")
        }
    }

    let results = vec![(vc, result)];
    let report = build_json_report("replay_pipeline", &results);
    assert_eq!(report.summary.total_failed, 1);
}

#[test]
fn test_full_pipeline_query_cache_hit() {
    let vc = midpoint_vc();
    let router = Router::with_backends(vec![Box::new(trust_router::mock_backend::MockBackend)]);
    let mut cache = query_cache::QueryCache::new(8);

    assert!(matches!(cache.lookup(&vc.formula), query_cache::CacheLookupResult::Miss));

    let first = router.verify_one(&vc);
    cache.store(&vc.formula, first.clone());

    let hit = cache.lookup(&vc.formula);
    assert!(matches!(
        hit,
        query_cache::CacheLookupResult::Hit(ref cached)
            if cached.solver_name() == first.solver_name()
    ));

    let second = router.verify_one(&vc);
    let stats = cache.stats();
    assert_eq!(stats.entries, 1);
    assert_eq!(stats.hits, 1);
    assert_eq!(stats.misses, 1);
    assert_eq!(first.solver_name(), second.solver_name());

    let results = vec![(vc.clone(), first), (vc, second)];
    let report = build_json_report("cache_pipeline", &results);
    assert_eq!(report.summary.total_obligations, 2);
}

#[test]
fn test_full_pipeline_enrichment_adds_context() {
    let func = division_function();
    let vc = division_vc();
    let counterexample = Counterexample::new(vec![
        ("_local1".into(), CounterexampleValue::Uint(10)),
        ("_local2".into(), CounterexampleValue::Uint(0)),
    ]);
    let adapter_result =
        replay_with_trace(&counterexample, &vc, &func.body.blocks, &AdapterConfig::default())
            .expect("adapter replay should succeed");

    let diagnostic = enrichment::enrich_counterexample(&vc, &counterexample, &adapter_result);
    assert_eq!(diagnostic.violation_kind, enrichment::ViolationKind::DivisionByZero);
    assert!(diagnostic.violation_description.contains("Division by zero"));
    assert!(!diagnostic.relevant_variables.is_empty());
    assert!(diagnostic.closest_valid_state.is_some());

    let router = Router::with_backends(vec![Box::new(ReplayFailureBackend)]);
    let result = router.verify_one(&vc);
    let results = vec![(vc, result)];
    let report = build_json_report("enrichment_pipeline", &results);
    assert_eq!(report.summary.total_failed, 1);
}

#[test]
fn test_full_pipeline_health_monitoring() {
    let mut vcs = generate_vcs(&midpoint_function());
    vcs.extend(generate_vcs(&division_function()));
    let router = Router::with_backends(vec![Box::new(trust_router::mock_backend::MockBackend)]);
    let results = router.verify_all(&vcs);
    let mut monitor = health::HealthMonitor::new();

    for (_, result) in &results {
        monitor.record_result(
            result.solver_name(),
            Duration::from_millis(result.time_ms().max(1)),
            !matches!(result, VerificationResult::Timeout { .. }),
        );
    }

    let snapshot = monitor.get_health("mock");
    assert_eq!(snapshot.status, health::HealthStatus::Healthy);
    assert_eq!(snapshot.total_results, results.len());
    assert!(!monitor.circuit_breaker("mock"));

    let report = build_json_report("health_pipeline", &results);
    assert_eq!(report.summary.total_obligations, results.len());
}

#[test]
fn test_full_pipeline_aggregation_cross_function() {
    let midpoint = midpoint_function();
    let division = division_function();
    let mut vcs = generate_vcs(&midpoint);
    vcs.extend(generate_vcs(&division));

    let router = Router::with_backends(vec![Box::new(FunctionOutcomeBackend)]);
    let results = router.verify_all(&vcs);
    let midpoint_results: Vec<_> =
        results.iter().filter(|(vc, _)| vc.function == midpoint.name).cloned().collect();
    let division_results: Vec<_> =
        results.iter().filter(|(vc, _)| vc.function == division.name).cloned().collect();

    let crate_result = crate_result(
        "multi_fn",
        vec![
            function_result(midpoint.def_path.clone(), midpoint.name.clone(), midpoint_results),
            function_result(division.def_path.clone(), division.name.clone(), division_results),
        ],
    );
    let report = build_json_report("multi_fn", &crate_result.all_results());

    let aggregated = aggregation::aggregate(
        results
            .iter()
            .map(|(vc, result)| SolverContribution {
                solver: vc.function.as_str().to_string(),
                result: result.clone(),
                time_ms: result.time_ms(),
            })
            .collect(),
    );

    assert_eq!(report.functions.len(), 2);
    assert_eq!(report.summary.total_obligations, 2);
    assert_eq!(aggregated.solver_count(), 2);
    assert_eq!(aggregated.proved_count(), 1);
    assert_eq!(aggregated.failed_count(), 1);
    assert!(aggregated.merged_counterexample.is_some());
    assert!(aggregated.best.is_proved());
}

#[test]
fn test_full_pipeline_fallback_chain() {
    let vc = VerificationCondition { formula: Formula::Bool(false), ..division_vc() };
    let backends: Vec<Arc<dyn VerificationBackend>> =
        vec![Arc::new(RejectingBackend), Arc::new(trust_router::mock_backend::MockBackend)];
    let chain = fallback::FallbackChain::new(
        backends,
        fallback::FallbackPolicy::Sequential,
        fallback::RetryPolicy { max_retries: 0, ..fallback::RetryPolicy::default() },
    );

    let result = fallback::execute_with_fallback(&vc, &chain)
        .expect("fallback should reach the mock backend");

    assert_eq!(result.solver_used, "mock");
    assert_eq!(result.attempts, 2);
    assert_eq!(result.errors.len(), 1);
    assert_eq!(result.errors[0].1, fallback::SolverError::Unsupported);
    assert!(result.result.is_proved());

    let report = build_json_report("fallback_pipeline", &[(vc, result.result)]);
    assert_eq!(report.summary.total_proved, 1);
}

#[test]
fn test_full_pipeline_batch_scheduling() {
    let safety_vc = division_vc();
    let non_termination_vc = generate_vcs(&recursive_countdown_function())
        .into_iter()
        .find(|vc| matches!(vc.kind, VcKind::NonTermination { .. }))
        .expect("recursive function should produce a non-termination VC");
    let strategies =
        vec![Strategy::direct_smt(5_000), Strategy::cegar(32), Strategy::bounded_mc(16)];

    let safety_schedule =
        scheduler::build_schedule(&safety_vc, &strategies, &scheduler::SchedulerConfig::default());
    let cegar_schedule = scheduler::build_schedule(
        &non_termination_vc,
        &strategies,
        &scheduler::SchedulerConfig::default(),
    );

    assert_eq!(safety_schedule.strategy_names()[0], "direct-smt");
    // NonTermination VCs are NOT routed to CEGAR (#194: PDR safety-only routing).
    // They get direct-smt scheduling since kind_score returns None for NonTermination.
    assert_eq!(cegar_schedule.strategy_names()[0], "direct-smt");
    assert_eq!(cegar_schedule.budgets[0].priority, 0);
    assert!(cegar_schedule.total_allocated() >= Duration::from_secs(30));

    let router = Router::with_cegar(
        cegar_backend::CegarBackendConfig::default(),
        vec![Box::new(trust_router::mock_backend::MockBackend)],
    );
    let results = router.verify_all(&[safety_vc, non_termination_vc]);
    let report = build_json_report("schedule_pipeline", &results);
    assert_eq!(report.summary.total_obligations, 2);
}

#[test]
fn test_full_pipeline_independence_optimization() {
    let vc = VerificationCondition {
        formula: Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(10))),
        ]),
        ..division_vc()
    };

    let partitions = independence::partition(&vc.formula);
    assert!(partitions.was_split);
    assert_eq!(partitions.partitions.len(), 2);
    assert!(partitions.partitions.iter().all(|p| p.variables.len() == 1));

    let rebuilt = independence::reconstruct(&partitions.partitions);
    assert!(matches!(rebuilt, Formula::And(ref parts) if parts.len() == 2));

    let router = Router::with_backends(vec![Box::new(trust_router::mock_backend::MockBackend)]);
    let result = router.verify_one(&vc);
    let report = build_json_report("independence_pipeline", &[(vc, result)]);
    assert_eq!(report.summary.total_obligations, 1);
}
