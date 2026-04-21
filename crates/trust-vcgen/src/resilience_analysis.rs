// trust-vcgen/resilience_analysis.rs: Resilience analysis over VerifiableFunction
//
// Owns the executable analysis logic for resilience reporting:
// - external dependency extraction
// - panic path detection
// - unchecked arithmetic detection
// - error handling classification
//
// Shared data types remain in trust-types.
//
// Part of #162: Move resilience analysis from trust-types to trust-vcgen
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

/// Resilience analyzer: inspects a `VerifiableFunction` and produces a `ResilienceReport`.
pub struct ResilienceAnalysis;

impl ResilienceAnalysis {
    /// Analyze a function for resilience properties.
    ///
    /// Detects panic paths, unwrap calls, unchecked arithmetic, and classifies
    /// error handling patterns to produce a comprehensive resilience report.
    pub fn analyze_function(func: &VerifiableFunction) -> ResilienceReport {
        let panic_paths = Self::detect_panic_paths(func);
        let unchecked_arithmetic = Self::detect_unchecked_arithmetic(func);
        let error_handling = Self::detect_error_handling(func);
        let failure_model = extract_failure_model(func);
        let fault_model = Self::classify_fault_model(&panic_paths, &error_handling);
        let properties = Self::detect_properties(func, &panic_paths);
        let risk_score = Self::compute_risk_score(&panic_paths, &unchecked_arithmetic, &failure_model);
        let recommendations =
            Self::generate_recommendations(&panic_paths, &unchecked_arithmetic, &error_handling);

        ResilienceReport {
            function: func.def_path.clone(),
            fault_model,
            properties,
            risk_score,
            recommendations,
            panic_paths,
            unchecked_arithmetic,
            error_handling,
            failure_model,
        }
    }

    /// Detect all panic paths in the function body.
    fn detect_panic_paths(func: &VerifiableFunction) -> Vec<PanicPath> {
        let mut paths = Vec::new();

        for block in &func.body.blocks {
            match &block.terminator {
                Terminator::Assert { msg, span, .. } => {
                    let kind = match msg {
                        AssertMessage::Overflow(_) | AssertMessage::OverflowNeg => {
                            PanicKind::Overflow
                        }
                        AssertMessage::BoundsCheck => PanicKind::BoundsCheck,
                        AssertMessage::DivisionByZero | AssertMessage::RemainderByZero => {
                            PanicKind::DivisionByZero
                        }
                        _ => PanicKind::Assert,
                    };
                    paths.push(PanicPath {
                        block: block.id,
                        span: span.clone(),
                        description: format!("assert may fail: {}", assert_msg_description(msg)),
                        kind,
                    });
                }
                Terminator::Call { func: call_func, span, .. } => {
                    if let Some(kind) = detect_panic_call(call_func) {
                        paths.push(PanicPath {
                            block: block.id,
                            span: span.clone(),
                            description: format!("call to `{}` may panic", call_func),
                            kind,
                        });
                    }
                }
                Terminator::Unreachable => {
                    paths.push(PanicPath {
                        block: block.id,
                        span: SourceSpan::default(),
                        description: "unreachable terminator".to_string(),
                        kind: PanicKind::ExplicitPanic,
                    });
                }
                _ => {}
            }
        }

        paths
    }

    /// Detect unchecked arithmetic operations (non-checked BinaryOp with overflow-prone ops).
    fn detect_unchecked_arithmetic(func: &VerifiableFunction) -> Vec<UncheckedArithmetic> {
        let mut results = Vec::new();

        for block in &func.body.blocks {
            for stmt in &block.stmts {
                if let Statement::Assign { rvalue: Rvalue::BinaryOp(op, _, _), span, .. } = stmt {
                    if op.can_overflow() {
                        results.push(UncheckedArithmetic {
                            block: block.id,
                            op: *op,
                            span: span.clone(),
                            description: format!(
                                "unchecked {:?} may overflow (use CheckedBinaryOp instead)",
                                op
                            ),
                        });
                    }
                    if op.is_division() {
                        results.push(UncheckedArithmetic {
                            block: block.id,
                            op: *op,
                            span: span.clone(),
                            description: format!(
                                "unchecked {:?} may divide by zero (no preceding assert)",
                                op
                            ),
                        });
                    }
                }
            }
        }

        results
    }

    /// Detect error handling patterns from call terminators.
    fn detect_error_handling(func: &VerifiableFunction) -> Vec<ErrorHandlingPattern> {
        let mut patterns = Vec::new();

        for block in &func.body.blocks {
            if let Terminator::Call { func: call_func, dest, target, .. } = &block.terminator
                && let Some(target_block_id) = target
                && let Some(target_block) = func.body.blocks.iter().find(|b| b.id == *target_block_id)
            {
                let pattern =
                    classify_error_handling(call_func, block.id, dest, target_block);
                patterns.push(pattern);
            }
        }

        patterns
    }

    /// Classify the overall fault model from detected patterns.
    fn classify_fault_model(
        panic_paths: &[PanicPath],
        error_handling: &[ErrorHandlingPattern],
    ) -> FaultModel {
        let has_panics = panic_paths.iter().any(|p| {
            matches!(p.kind, PanicKind::Unwrap | PanicKind::Expect | PanicKind::ExplicitPanic)
        });
        let has_panicking_handler = error_handling
            .iter()
            .any(|e| matches!(e, ErrorHandlingPattern::Panicking { .. }));
        let has_propagation = error_handling
            .iter()
            .any(|e| matches!(e, ErrorHandlingPattern::Propagation { .. }));
        let has_swallowing = error_handling
            .iter()
            .any(|e| matches!(e, ErrorHandlingPattern::Swallowing { .. }));

        if has_panics || has_panicking_handler {
            FaultModel::PanicOnError
        } else if has_swallowing && !has_propagation {
            FaultModel::SilentCorruption
        } else if has_propagation {
            FaultModel::ReturnError
        } else if has_swallowing {
            FaultModel::SilentCorruption
        } else if panic_paths.is_empty() && error_handling.is_empty() {
            FaultModel::ReturnError
        } else {
            FaultModel::PanicOnError
        }
    }

    /// Detect resilience properties from function structure.
    fn detect_properties(
        func: &VerifiableFunction,
        panic_paths: &[PanicPath],
    ) -> Vec<ResilienceProperty> {
        let mut props = Vec::new();

        if panic_paths.is_empty() {
            props.push(ResilienceProperty::CrashConsistent);
        }

        if func.body.arg_count == 2 && func.body.blocks.len() <= 2 {
            let has_commutative_op = func.body.blocks.iter().any(|block| {
                block.stmts.iter().any(|stmt| {
                    matches!(
                        stmt,
                        Statement::Assign {
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add
                                    | BinOp::Mul
                                    | BinOp::BitAnd
                                    | BinOp::BitOr
                                    | BinOp::BitXor
                                    | BinOp::Eq
                                    | BinOp::Ne,
                                _,
                                _
                            ),
                            ..
                        } | Statement::Assign {
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add
                                    | BinOp::Mul
                                    | BinOp::BitAnd
                                    | BinOp::BitOr
                                    | BinOp::BitXor
                                    | BinOp::Eq
                                    | BinOp::Ne,
                                _,
                                _
                            ),
                            ..
                        }
                    )
                })
            });
            if has_commutative_op {
                props.push(ResilienceProperty::Commutative);
            }
        }

        props
    }

    /// Compute a risk score from 0.0 (safe) to 1.0 (high risk).
    fn compute_risk_score(
        panic_paths: &[PanicPath],
        unchecked_arithmetic: &[UncheckedArithmetic],
        failure_model: &FailureModel,
    ) -> f64 {
        let panic_score = (panic_paths.len() as f64 * 0.15).min(0.5);
        let arith_score = (unchecked_arithmetic.len() as f64 * 0.1).min(0.3);
        let dep_score = (failure_model.dependencies.len() as f64 * 0.05).min(0.2);
        (panic_score + arith_score + dep_score).min(1.0)
    }

    /// Generate recommendations for improving resilience.
    fn generate_recommendations(
        panic_paths: &[PanicPath],
        unchecked_arithmetic: &[UncheckedArithmetic],
        error_handling: &[ErrorHandlingPattern],
    ) -> Vec<String> {
        let mut recs = Vec::new();

        let unwrap_count =
            panic_paths.iter().filter(|p| matches!(p.kind, PanicKind::Unwrap)).count();
        if unwrap_count > 0 {
            recs.push(format!(
                "Replace {} unwrap() call(s) with proper error handling using `?` or match",
                unwrap_count
            ));
        }

        let expect_count =
            panic_paths.iter().filter(|p| matches!(p.kind, PanicKind::Expect)).count();
        if expect_count > 0 {
            recs.push(format!(
                "Replace {} expect() call(s) with `?` or match for recoverable errors",
                expect_count
            ));
        }

        if !unchecked_arithmetic.is_empty() {
            recs.push(format!(
                "Use checked arithmetic (checked_add, checked_mul, etc.) for {} operation(s)",
                unchecked_arithmetic.len()
            ));
        }

        let swallow_count = error_handling
            .iter()
            .filter(|e| matches!(e, ErrorHandlingPattern::Swallowing { .. }))
            .count();
        if swallow_count > 0 {
            recs.push(format!(
                "Investigate {} swallowed error(s) — silent error suppression may mask bugs",
                swallow_count
            ));
        }

        recs
    }
}

fn assert_msg_description(msg: &AssertMessage) -> String {
    match msg {
        AssertMessage::BoundsCheck => "index out of bounds".to_string(),
        AssertMessage::Overflow(op) => format!("{:?} overflow", op),
        AssertMessage::OverflowNeg => "negation overflow".to_string(),
        AssertMessage::DivisionByZero => "division by zero".to_string(),
        AssertMessage::RemainderByZero => "remainder by zero".to_string(),
        AssertMessage::ResumedAfterReturn => "resumed after return".to_string(),
        AssertMessage::ResumedAfterPanic => "resumed after panic".to_string(),
        AssertMessage::MisalignedPointerDereference => {
            "misaligned pointer dereference".to_string()
        }
        AssertMessage::ResumedAfterDrop => "resumed after drop".to_string(),
        AssertMessage::NullPointerDereference => "null pointer dereference".to_string(),
        AssertMessage::InvalidEnumConstruction => "invalid enum construction".to_string(),
        AssertMessage::Custom(s) => s.clone(),
        _ => "unknown".to_string(),
    }
}

/// Detect if a function call is a panic-inducing call.
fn detect_panic_call(func_path: &str) -> Option<PanicKind> {
    if func_path.contains("unwrap") && !func_path.contains("unwrap_or") {
        Some(PanicKind::Unwrap)
    } else if func_path.contains("expect") {
        Some(PanicKind::Expect)
    } else if func_path.contains("panic") {
        Some(PanicKind::ExplicitPanic)
    } else {
        None
    }
}

/// Classify how a call result is used in the target block.
fn classify_error_handling(
    call_func: &str,
    call_block: BlockId,
    dest: &Place,
    target_block: &BasicBlock,
) -> ErrorHandlingPattern {
    if let Terminator::Call { func: next_func, args, .. } = &target_block.terminator
        && next_func.contains("unwrap")
        && !next_func.contains("unwrap_or")
    {
        let uses_dest = args.iter().any(|arg| {
            matches!(arg, Operand::Copy(p) | Operand::Move(p) if p.local == dest.local)
        });
        if uses_dest {
            return ErrorHandlingPattern::Panicking {
                call_path: call_func.to_string(),
                block: call_block,
            };
        }
    }

    let dest_used = target_block.stmts.iter().any(|stmt| stmt_references_local(stmt, dest.local));
    let dest_used_in_term = terminator_references_local(&target_block.terminator, dest.local);

    if !dest_used && !dest_used_in_term {
        return ErrorHandlingPattern::Swallowing {
            call_path: call_func.to_string(),
            block: call_block,
        };
    }

    ErrorHandlingPattern::Propagation {
        call_path: call_func.to_string(),
        block: call_block,
    }
}

fn stmt_references_local(stmt: &Statement, local: usize) -> bool {
    match stmt {
        Statement::Assign { rvalue, .. } => rvalue_references_local(rvalue, local),
        Statement::Nop => false,
        _ => false,
    }
}

fn rvalue_references_local(rvalue: &Rvalue, local: usize) -> bool {
    match rvalue {
        Rvalue::Use(op) | Rvalue::Cast(op, _) | Rvalue::UnaryOp(_, op) => {
            operand_references_local(op, local)
        }
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            operand_references_local(a, local) || operand_references_local(b, local)
        }
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place) => place.local == local,
        Rvalue::Aggregate(_, ops) => ops.iter().any(|op| operand_references_local(op, local)),
        Rvalue::Repeat(op, _) => operand_references_local(op, local),
        _ => false,
    }
}

fn operand_references_local(operand: &Operand, local: usize) -> bool {
    match operand {
        Operand::Copy(p) | Operand::Move(p) => p.local == local,
        Operand::Constant(_) => false,
        _ => false,
    }
}

fn terminator_references_local(term: &Terminator, local: usize) -> bool {
    match term {
        Terminator::Call { args, .. } => {
            args.iter().any(|arg| operand_references_local(arg, local))
        }
        Terminator::SwitchInt { discr, .. } => operand_references_local(discr, local),
        Terminator::Assert { cond, .. } => operand_references_local(cond, local),
        Terminator::Drop { place, .. } => place.local == local,
        Terminator::Goto(_) | Terminator::Return | Terminator::Unreachable => false,
        _ => false,
    }
}

/// Known external call patterns for matching against MIR Call func names.
///
/// Maps substrings of def_path to (service_name, default_failure_modes).
const EXTERNAL_CALL_PATTERNS: &[(&str, &str, &[FailureMode])] = &[
    (
        "reqwest::Client::get",
        "http",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "reqwest::Client::post",
        "http",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "reqwest::Client::put",
        "http",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "reqwest::Client::delete",
        "http",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "hyper::Client::request",
        "http",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "sqlx::query",
        "database",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "diesel::RunQueryDsl::execute",
        "database",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "rusqlite::Connection::execute",
        "database",
        &[FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "redis::Commands::get",
        "redis",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "redis::Commands::set",
        "redis",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "redis::Connection::req_command",
        "redis",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    ("std::fs::read", "filesystem", &[FailureMode::Error]),
    ("std::fs::write", "filesystem", &[FailureMode::Error]),
    ("std::fs::File::open", "filesystem", &[FailureMode::Error]),
    ("std::fs::File::create", "filesystem", &[FailureMode::Error]),
    (
        "std::io::Read::read",
        "filesystem",
        &[FailureMode::Error, FailureMode::Partial],
    ),
    (
        "std::io::Write::write",
        "filesystem",
        &[FailureMode::Error, FailureMode::Partial],
    ),
    (
        "aws_sdk_s3::Client::get_object",
        "s3",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "aws_sdk_s3::Client::put_object",
        "s3",
        &[FailureMode::Timeout, FailureMode::Error, FailureMode::Unavailable],
    ),
    (
        "std::net::TcpStream::connect",
        "network",
        &[FailureMode::Timeout, FailureMode::Unavailable],
    ),
    (
        "tokio::net::TcpStream::connect",
        "network",
        &[FailureMode::Timeout, FailureMode::Unavailable],
    ),
];

fn strip_generics(path: &str) -> String {
    let mut result = String::with_capacity(path.len());
    let mut depth = 0u32;

    for ch in path.chars() {
        match ch {
            '<' => depth += 1,
            '>' => {
                depth = depth.saturating_sub(1);
            }
            _ if depth > 0 => {}
            _ => result.push(ch),
        }
    }

    while result.contains("::::") {
        result = result.replace("::::", "::");
    }

    result
}

/// Match a MIR Call func path against known external call patterns.
///
/// Returns (service_name, default_failure_modes) if matched.
pub fn match_external_call(func_path: &str) -> Option<(&'static str, Vec<FailureMode>)> {
    let normalized = strip_generics(func_path);
    let mut best_match: Option<(usize, &str, &[FailureMode])> = None;

    for &(pattern, service, modes) in EXTERNAL_CALL_PATTERNS {
        if normalized.contains(pattern) {
            let len = pattern.len();
            if best_match.as_ref().is_none_or(|(best_len, _, _)| len > *best_len) {
                best_match = Some((len, service, modes));
            }
        }
    }

    best_match.map(|(_, service, modes)| (service, modes.to_vec()))
}

/// Extract a failure model from a VerifiableFunction.
///
/// Walks all basic blocks, inspects Call terminators, and matches their
/// func path against known external call patterns. Builds a FailureModel
/// with detected external dependencies and their failure modes.
pub fn extract_failure_model(func: &VerifiableFunction) -> FailureModel {
    let mut model = FailureModel::new(&func.def_path);

    for block in &func.body.blocks {
        if let Terminator::Call { func: func_name, span, .. } = &block.terminator
            && let Some((service, failure_modes)) = match_external_call(func_name)
        {
            model.dependencies.push(ExternalDependency {
                name: service.to_string(),
                failure_modes,
                block: block.id,
                span: span.clone(),
                call_path: func_name.clone(),
            });
        }
    }

    model
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_simple_return_func(name: &str) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_match_external_call_http() {
        let result = match_external_call("reqwest::Client::<T>::get");
        assert!(result.is_some());
        let (service, modes) = result.unwrap();
        assert_eq!(service, "http");
        assert!(modes.contains(&FailureMode::Timeout));
        assert!(modes.contains(&FailureMode::Error));
        assert!(modes.contains(&FailureMode::Unavailable));
    }

    #[test]
    fn test_match_external_call_database() {
        let result = match_external_call("sqlx::query");
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, "database");
    }

    #[test]
    fn test_match_external_call_redis() {
        let result = match_external_call("redis::Commands::get");
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, "redis");
    }

    #[test]
    fn test_match_external_call_filesystem() {
        let result = match_external_call("std::fs::File::open");
        assert!(result.is_some());
        let (service, modes) = result.unwrap();
        assert_eq!(service, "filesystem");
        assert!(modes.contains(&FailureMode::Error));
    }

    #[test]
    fn test_match_external_call_network() {
        let result = match_external_call("std::net::TcpStream::connect");
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, "network");

        let result = match_external_call("tokio::net::TcpStream::connect");
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, "network");
    }

    #[test]
    fn test_match_external_call_no_match() {
        assert!(match_external_call("std::vec::Vec::push").is_none());
        assert!(match_external_call("my_crate::do_thing").is_none());
    }

    #[test]
    fn test_extract_failure_model() {
        let func = VerifiableFunction {
            name: "handle_request".to_string(),
            def_path: "server::handle_request".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::Unit, name: Some("cache_result".into()) },
                    LocalDecl { index: 2, ty: Ty::Unit, name: Some("db_result".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "redis::Commands::get".to_string(),
                            args: vec![],
                            dest: Place::local(1),
                            target: Some(BlockId(1)),
                            span: SourceSpan {
                                file: "server.rs".into(),
                                line_start: 10,
                                col_start: 4,
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
                            func: "sqlx::query".to_string(),
                            args: vec![],
                            dest: Place::local(2),
                            target: Some(BlockId(2)),
                            span: SourceSpan {
                                file: "server.rs".into(),
                                line_start: 15,
                                col_start: 4,
                                line_end: 15,
                                col_end: 40,
                            },
                            atomic: None,
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let model = extract_failure_model(&func);
        assert_eq!(model.function, "server::handle_request");
        assert_eq!(model.dependencies.len(), 2);
        assert_eq!(model.dependencies[0].name, "redis");
        assert_eq!(model.dependencies[1].name, "database");
        assert_eq!(model.failure_combination_count(), 16);
    }

    #[test]
    fn test_extract_failure_model_no_externals() {
        let func = VerifiableFunction {
            name: "add".to_string(),
            def_path: "math::add".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::usize(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let model = extract_failure_model(&func);
        assert!(model.is_empty());
    }

    #[test]
    fn test_analyze_pure_function_low_risk() {
        let func = make_simple_return_func("pure_fn");
        let report = ResilienceAnalysis::analyze_function(&func);

        assert_eq!(report.function, "test::pure_fn");
        assert!(report.panic_paths.is_empty());
        assert!(report.unchecked_arithmetic.is_empty());
        assert_eq!(report.risk_score, 0.0);
        assert!(report.recommendations.is_empty());
        assert!(report.properties.contains(&ResilienceProperty::CrashConsistent));
    }

    #[test]
    fn test_analyze_function_with_overflow_assert() {
        let func = VerifiableFunction {
            name: "add".to_string(),
            def_path: "math::add".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
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
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
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
        };

        let report = ResilienceAnalysis::analyze_function(&func);

        assert_eq!(report.panic_paths.len(), 1);
        assert_eq!(report.panic_paths[0].kind, PanicKind::Overflow);
        assert!(report.risk_score > 0.0);
    }

    #[test]
    fn test_analyze_function_with_unwrap_call() {
        let func = VerifiableFunction {
            name: "risky".to_string(),
            def_path: "mod::risky".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::Unit, name: Some("result".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "std::result::Result::unwrap".to_string(),
                            args: vec![],
                            dest: Place::local(1),
                            target: Some(BlockId(1)),
                            span: SourceSpan {
                                file: "test.rs".into(),
                                line_start: 5,
                                col_start: 1,
                                line_end: 5,
                                col_end: 20,
                            },
                            atomic: None,
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let report = ResilienceAnalysis::analyze_function(&func);

        assert_eq!(report.panic_paths.len(), 1);
        assert_eq!(report.panic_paths[0].kind, PanicKind::Unwrap);
        assert!(report.recommendations.iter().any(|r| r.contains("unwrap()")));
        assert!(report.risk_score > 0.0);
    }

    #[test]
    fn test_analyze_function_with_unchecked_arithmetic() {
        let func = VerifiableFunction {
            name: "unchecked_add".to_string(),
            def_path: "math::unchecked_add".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let report = ResilienceAnalysis::analyze_function(&func);

        assert_eq!(report.unchecked_arithmetic.len(), 1);
        assert_eq!(report.unchecked_arithmetic[0].op, BinOp::Add);
        assert!(report
            .recommendations
            .iter()
            .any(|r| r.contains("checked arithmetic")));
    }

    #[test]
    fn test_analyze_function_detects_division_risk() {
        let func = VerifiableFunction {
            name: "div".to_string(),
            def_path: "math::div".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let report = ResilienceAnalysis::analyze_function(&func);

        assert!(report
            .unchecked_arithmetic
            .iter()
            .any(|u| u.op == BinOp::Div));
    }

    #[test]
    fn test_analyze_function_detects_commutative() {
        let func = VerifiableFunction {
            name: "add".to_string(),
            def_path: "math::add".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let report = ResilienceAnalysis::analyze_function(&func);
        assert!(report.properties.contains(&ResilienceProperty::Commutative));
        assert!(report.properties.contains(&ResilienceProperty::CrashConsistent));
    }

    #[test]
    fn test_analyze_function_with_external_deps_and_unwrap() {
        let func = VerifiableFunction {
            name: "fetch_and_unwrap".to_string(),
            def_path: "server::fetch_and_unwrap".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::Unit, name: Some("resp".into()) },
                    LocalDecl { index: 2, ty: Ty::Unit, name: Some("value".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "redis::Commands::get".to_string(),
                            args: vec![],
                            dest: Place::local(1),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "core::result::Result::unwrap".to_string(),
                            args: vec![Operand::Move(Place::local(1))],
                            dest: Place::local(2),
                            target: Some(BlockId(2)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let report = ResilienceAnalysis::analyze_function(&func);

        assert!(report.panic_paths.iter().any(|p| p.kind == PanicKind::Unwrap));
        assert!(!report.failure_model.is_empty());
        assert_eq!(report.failure_model.dependencies[0].name, "redis");
        assert!(report
            .error_handling
            .iter()
            .any(|e| matches!(e, ErrorHandlingPattern::Panicking { .. })));
        assert_eq!(report.fault_model, FaultModel::PanicOnError);
        assert!(report.risk_score > 0.1);
    }

    #[test]
    fn test_risk_score_scales_with_issues() {
        let panic_paths_0: Vec<PanicPath> = vec![];
        let unchecked_0: Vec<UncheckedArithmetic> = vec![];
        let model_0 = FailureModel::new("f");
        let score_0 =
            ResilienceAnalysis::compute_risk_score(&panic_paths_0, &unchecked_0, &model_0);

        let panic_paths_2 = vec![
            PanicPath {
                block: BlockId(0),
                span: SourceSpan::default(),
                description: "unwrap".into(),
                kind: PanicKind::Unwrap,
            },
            PanicPath {
                block: BlockId(1),
                span: SourceSpan::default(),
                description: "expect".into(),
                kind: PanicKind::Expect,
            },
        ];
        let score_2 =
            ResilienceAnalysis::compute_risk_score(&panic_paths_2, &unchecked_0, &model_0);

        assert!(score_0 < score_2, "more panic paths = higher risk");
    }

    #[test]
    fn test_detect_panic_call_patterns() {
        assert_eq!(detect_panic_call("core::result::Result::unwrap"), Some(PanicKind::Unwrap));
        assert_eq!(detect_panic_call("core::option::Option::expect"), Some(PanicKind::Expect));
        assert_eq!(detect_panic_call("std::panic"), Some(PanicKind::ExplicitPanic));
        assert_eq!(detect_panic_call("std::vec::Vec::push"), None);
        assert_eq!(detect_panic_call("core::result::Result::unwrap_or"), None);
    }

    #[test]
    fn test_error_handling_swallowing_detected() {
        let func = VerifiableFunction {
            name: "swallow".to_string(),
            def_path: "test::swallow".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::Unit, name: Some("result".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "get_data".to_string(),
                            args: vec![],
                            dest: Place::local(1),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let report = ResilienceAnalysis::analyze_function(&func);
        assert!(report
            .error_handling
            .iter()
            .any(|e| matches!(e, ErrorHandlingPattern::Swallowing { .. })));
        assert_eq!(report.fault_model, FaultModel::SilentCorruption);
    }

    #[test]
    fn test_unreachable_terminator_detected_as_panic() {
        let func = VerifiableFunction {
            name: "unreachable_fn".to_string(),
            def_path: "test::unreachable_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Unreachable,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let report = ResilienceAnalysis::analyze_function(&func);
        assert_eq!(report.panic_paths.len(), 1);
        assert_eq!(report.panic_paths[0].kind, PanicKind::ExplicitPanic);
    }
}
