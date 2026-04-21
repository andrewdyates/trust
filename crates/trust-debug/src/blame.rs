// trust-debug/blame.rs: Proof failure blame attribution
//
// Traces proof failures (unsat cores, counterexamples) back to specific source
// elements, assigns confidence scores, and produces ranked blame reports.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::fmt::Write;

use trust_types::{
    Counterexample, CounterexampleValue, Formula, Sort, SourceSpan, VcKind,
    VerificationCondition, VerificationResult,
};

// ---------------------------------------------------------------------------
// BlameTarget
// ---------------------------------------------------------------------------

/// The kind of code element blamed for a proof failure.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum BlameTarget {
    /// A MIR statement (assignment, storage live/dead, etc.).
    Statement {
        /// Function containing the statement.
        function: String,
        /// Source location of the statement.
        location: SourceSpan,
        /// Optional description (e.g., "assignment to _3").
        description: String,
    },
    /// An expression within a statement or terminator.
    Expression {
        /// Function containing the expression.
        function: String,
        /// Source location.
        location: SourceSpan,
        /// The expression text or summary.
        description: String,
    },
    /// A specification annotation (requires, ensures, invariant).
    Specification {
        /// Function the spec is attached to.
        function: String,
        /// Source location of the spec.
        location: SourceSpan,
        /// The spec kind (e.g., "requires", "ensures").
        spec_kind: String,
    },
    /// An assumption made by the verifier (e.g., type bounds, well-formedness).
    Assumption {
        /// What the assumption is about.
        description: String,
        /// Source location if traceable.
        location: Option<SourceSpan>,
    },
}

impl BlameTarget {
    /// Returns the source location of this target, if available.
    #[must_use]
    pub(crate) fn location(&self) -> Option<&SourceSpan> {
        match self {
            BlameTarget::Statement { location, .. }
            | BlameTarget::Expression { location, .. }
            | BlameTarget::Specification { location, .. } => Some(location),
            BlameTarget::Assumption { location, .. } => location.as_ref(),
        }
    }

    /// Returns a short label for the target kind.
    #[must_use]
    pub(crate) fn kind_label(&self) -> &'static str {
        match self {
            BlameTarget::Statement { .. } => "statement",
            BlameTarget::Expression { .. } => "expression",
            BlameTarget::Specification { .. } => "specification",
            BlameTarget::Assumption { .. } => "assumption",
        }
    }
}

// ---------------------------------------------------------------------------
// BlameScore
// ---------------------------------------------------------------------------

/// A blame attribution: a target with a confidence score and explanation.
///
/// Note: derives PartialEq only (not Eq) because confidence is f64.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct BlameScore {
    /// The blamed code element.
    pub target: BlameTarget,
    /// Confidence that this target is the root cause, in [0.0, 1.0].
    pub confidence: f64,
    /// Human-readable explanation of why this target is blamed.
    pub explanation: String,
}

impl BlameScore {
    /// Create a new blame score.
    #[must_use]
    pub(crate) fn new(target: BlameTarget, confidence: f64, explanation: String) -> Self {
        Self {
            target,
            confidence: confidence.clamp(0.0, 1.0),
            explanation,
        }
    }
}

// ---------------------------------------------------------------------------
// BlameReport
// ---------------------------------------------------------------------------

/// A ranked list of blamed elements for a proof failure.
#[derive(Debug, Clone)]
pub(crate) struct BlameReport {
    /// The VC that failed.
    pub vc_function: String,
    /// The VC kind.
    pub vc_kind_description: String,
    /// Ranked blame entries, highest confidence first.
    pub entries: Vec<BlameScore>,
}

impl BlameReport {
    /// Returns true if the report has no blame entries.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Number of blame entries.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// The top-ranked blame target, if any.
    #[must_use]
    pub(crate) fn top(&self) -> Option<&BlameScore> {
        self.entries.first()
    }

    /// Format as a human-readable summary.
    #[must_use]
    pub(crate) fn format_summary(&self) -> String {
        let mut out = format!(
            "Blame report for {} ({})\n",
            self.vc_function, self.vc_kind_description
        );
        for (i, entry) in self.entries.iter().enumerate() {
            let _ = writeln!(out, 
                "  #{}: [{}] {:.0}% - {} ({})",
                i + 1,
                entry.target.kind_label(),
                entry.confidence * 100.0,
                entry.explanation,
                entry
                    .target
                    .location()
                    .map(|l| format!("{}:{}", l.file, l.line_start))
                    .unwrap_or_else(|| "unknown".into()),
            );
        }
        out
    }
}

// ---------------------------------------------------------------------------
// BlameAnalyzer
// ---------------------------------------------------------------------------

/// Traces proof failures to source locations by analyzing solver output.
///
/// Supports two primary analysis modes:
/// - Unsat core analysis: extracts blame from named assertions in the core
/// - Counterexample analysis: attributes blame from concrete variable values
#[derive(Debug, Clone)]
pub(crate) struct BlameAnalyzer {
    /// Weight for unsat core membership when scoring.
    pub(crate) core_weight: f64,
    /// Weight for counterexample value proximity.
    pub(crate) cex_weight: f64,
    /// Weight for specification-related blame.
    pub(crate) spec_weight: f64,
}

impl Default for BlameAnalyzer {
    fn default() -> Self {
        Self {
            core_weight: 0.8,
            cex_weight: 0.7,
            spec_weight: 0.6,
        }
    }
}

impl BlameAnalyzer {
    /// Create a new blame analyzer with default weights.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Analyze a proof failure and produce a blame report.
    ///
    /// Dispatches to `analyze_unsat_core` or `analyze_counterexample` based
    /// on the result type, then ranks all suspects.
    #[must_use]
    pub(crate) fn analyze(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
    ) -> BlameReport {
        let mut scores = Vec::new();

        match result {
            VerificationResult::Failed { counterexample, .. } => {
                if let Some(cex) = counterexample {
                    scores.extend(self.analyze_counterexample(vc, cex));
                }
                // Also extract structural blame from the VC itself
                scores.extend(self.analyze_vc_structure(vc));
            }
            VerificationResult::Unknown { .. } | VerificationResult::Timeout { .. } => {
                // For unknown/timeout, blame is structural only
                scores.extend(self.analyze_vc_structure(vc));
            }
            VerificationResult::Proved { .. } => {
                // Nothing to blame for proved VCs
            }
            _ => { /* unhandled variant -- skip */ }
        }

        rank_blame_targets(&mut scores);

        BlameReport {
            vc_function: vc.function.clone(),
            vc_kind_description: vc.kind.description(),
            entries: scores,
        }
    }

    /// Extract blame targets from an unsat core.
    ///
    /// An unsat core is a minimal set of named assertions that together are
    /// unsatisfiable. Each core element maps to a code element that contributes
    /// to the proof failure.
    #[must_use]
    pub(crate) fn analyze_unsat_core(
        &self,
        vc: &VerificationCondition,
        core_labels: &[String],
    ) -> Vec<BlameScore> {
        let mut scores = Vec::new();
        let total = core_labels.len().max(1) as f64;

        for (i, label) in core_labels.iter().enumerate() {
            // Core elements closer to the beginning are often more relevant
            let position_factor = 1.0 - (i as f64 / total) * 0.3;
            let confidence = self.core_weight * position_factor;

            let target = self.label_to_target(label, vc);
            scores.push(BlameScore::new(
                target,
                confidence,
                format!("In unsat core (element {}/{})", i + 1, core_labels.len()),
            ));
        }

        scores
    }

    /// Attribute blame from a counterexample's concrete values.
    ///
    /// Examines each variable assignment in the counterexample and determines
    /// which code elements are most likely responsible for the violation.
    #[must_use]
    pub(crate) fn analyze_counterexample(
        &self,
        vc: &VerificationCondition,
        cex: &Counterexample,
    ) -> Vec<BlameScore> {
        let mut scores = Vec::new();

        // Collect variables referenced in the formula
        let formula_vars = collect_formula_vars(&vc.formula);

        for (name, value) in &cex.assignments {
            let is_boundary = is_boundary_value(value);
            let in_formula = formula_vars.contains_key(name.as_str());

            // Variables at boundary values are more suspicious
            let boundary_boost = if is_boundary { 0.2 } else { 0.0 };
            // Variables in the formula are more relevant
            let formula_boost = if in_formula { 0.15 } else { 0.0 };

            let confidence = (self.cex_weight * 0.7 + boundary_boost + formula_boost).min(1.0);

            let target = BlameTarget::Expression {
                function: vc.function.clone(),
                location: vc.location.clone(),
                description: format!("{name} = {value}"),
            };

            let mut explanation = format!("Counterexample value: {name} = {value}");
            if is_boundary {
                explanation.push_str(" (boundary value)");
            }

            scores.push(BlameScore::new(target, confidence, explanation));
        }

        // If there's a trace, blame the last step more heavily
        if let Some(trace) = &cex.trace
            && let Some(last_step) = trace.steps.last() {
                let target = BlameTarget::Statement {
                    function: vc.function.clone(),
                    location: vc.location.clone(),
                    description: format!(
                        "Trace step {} (final state)",
                        last_step.step
                    ),
                };
                scores.push(BlameScore::new(
                    target,
                    self.cex_weight * 0.9,
                    "Final trace step before violation".to_string(),
                ));
            }

        scores
    }

    /// Extract structural blame from the VC kind itself.
    fn analyze_vc_structure(&self, vc: &VerificationCondition) -> Vec<BlameScore> {
        let mut scores = Vec::new();

        match &vc.kind {
            VcKind::ArithmeticOverflow { op, .. } => {
                scores.push(BlameScore::new(
                    BlameTarget::Expression {
                        function: vc.function.clone(),
                        location: vc.location.clone(),
                        description: format!("{op:?} operation"),
                    },
                    self.spec_weight,
                    format!("Arithmetic operation {op:?} may overflow"),
                ));
            }
            VcKind::DivisionByZero | VcKind::RemainderByZero => {
                scores.push(BlameScore::new(
                    BlameTarget::Expression {
                        function: vc.function.clone(),
                        location: vc.location.clone(),
                        description: "division/remainder operation".to_string(),
                    },
                    self.spec_weight,
                    "Divisor may be zero".to_string(),
                ));
            }
            VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => {
                scores.push(BlameScore::new(
                    BlameTarget::Expression {
                        function: vc.function.clone(),
                        location: vc.location.clone(),
                        description: "array/slice index".to_string(),
                    },
                    self.spec_weight,
                    "Index may exceed bounds".to_string(),
                ));
            }
            VcKind::Precondition { callee } => {
                scores.push(BlameScore::new(
                    BlameTarget::Specification {
                        function: callee.clone(),
                        location: vc.location.clone(),
                        spec_kind: "requires".to_string(),
                    },
                    self.spec_weight * 1.1,
                    format!("Precondition of '{callee}' not satisfied"),
                ));
                scores.push(BlameScore::new(
                    BlameTarget::Statement {
                        function: vc.function.clone(),
                        location: vc.location.clone(),
                        description: format!("call to {callee}"),
                    },
                    self.spec_weight * 0.9,
                    "Call site does not establish callee precondition".to_string(),
                ));
            }
            VcKind::Postcondition => {
                scores.push(BlameScore::new(
                    BlameTarget::Specification {
                        function: vc.function.clone(),
                        location: vc.location.clone(),
                        spec_kind: "ensures".to_string(),
                    },
                    self.spec_weight,
                    "Postcondition may be too strong".to_string(),
                ));
                scores.push(BlameScore::new(
                    BlameTarget::Statement {
                        function: vc.function.clone(),
                        location: vc.location.clone(),
                        description: "function body".to_string(),
                    },
                    self.spec_weight * 0.8,
                    "Function body does not establish postcondition".to_string(),
                ));
            }
            _ => {
                scores.push(BlameScore::new(
                    BlameTarget::Statement {
                        function: vc.function.clone(),
                        location: vc.location.clone(),
                        description: vc.kind.description(),
                    },
                    self.spec_weight * 0.5,
                    format!("Verification failed: {}", vc.kind.description()),
                ));
            }
        }

        scores
    }

    /// Convert an unsat core label to a blame target.
    fn label_to_target(&self, label: &str, vc: &VerificationCondition) -> BlameTarget {
        if label.starts_with("spec:") || label.starts_with("requires:") || label.starts_with("ensures:") {
            let spec_kind = label.split(':').next().unwrap_or("spec").to_string();
            BlameTarget::Specification {
                function: vc.function.clone(),
                location: vc.location.clone(),
                spec_kind,
            }
        } else if label.starts_with("assume:") {
            BlameTarget::Assumption {
                description: label.to_string(),
                location: Some(vc.location.clone()),
            }
        } else if label.starts_with("stmt:") || label.starts_with("assign:") {
            BlameTarget::Statement {
                function: vc.function.clone(),
                location: vc.location.clone(),
                description: label.to_string(),
            }
        } else {
            BlameTarget::Expression {
                function: vc.function.clone(),
                location: vc.location.clone(),
                description: label.to_string(),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Public helpers
// ---------------------------------------------------------------------------

/// Sort blame targets by confidence (descending), then deduplicate.
pub(crate) fn rank_blame_targets(scores: &mut Vec<BlameScore>) {
    // Sort by confidence descending (f64 partial_cmp, treat NaN as 0)
    scores.sort_by(|a, b| {
        b.confidence
            .partial_cmp(&a.confidence)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    // Deduplicate targets that are exactly equal, keeping highest confidence
    let mut seen: FxHashMap<String, usize> = FxHashMap::default();
    let mut deduplicated = Vec::new();

    for score in scores.drain(..) {
        let key = format!("{:?}", score.target);
        if let std::collections::hash_map::Entry::Vacant(e) = seen.entry(key) {
            e.insert(deduplicated.len());
            deduplicated.push(score);
        } else {
            // Already have this exact target with higher confidence (sorted)
        }
    }

    *scores = deduplicated;
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

/// Collect all variable names referenced in a formula.
fn collect_formula_vars(formula: &Formula) -> FxHashMap<&str, &Sort> {
    let mut vars = FxHashMap::default();
    collect_vars_recursive(formula, &mut vars);
    vars
}

fn collect_vars_recursive<'a>(formula: &'a Formula, vars: &mut FxHashMap<&'a str, &'a Sort>) {
    match formula {
        Formula::Var(name, sort) => {
            vars.insert(name.as_str(), sort);
        }
        other => {
            for child in other.children() {
                collect_vars_recursive(child, vars);
            }
        }
    }
}

/// Check if a counterexample value is at a type boundary (MAX, MIN, 0).
fn is_boundary_value(value: &CounterexampleValue) -> bool {
    match value {
        CounterexampleValue::Int(n) => {
            *n == 0 || *n == -1 || *n == i128::MAX || *n == i128::MIN
                || *n == i64::MAX as i128 || *n == i64::MIN as i128
                || *n == i32::MAX as i128 || *n == i32::MIN as i128
        }
        CounterexampleValue::Uint(n) => {
            *n == 0 || *n == u128::MAX
                || *n == u64::MAX as u128 || *n == u32::MAX as u128
                || *n == u16::MAX as u128 || *n == u8::MAX as u128
        }
        CounterexampleValue::Bool(_) => false,
        CounterexampleValue::Float(f) => {
            *f == 0.0 || f.is_infinite() || f.is_nan()
                || *f == f64::MAX || *f == f64::MIN
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{BinOp, CounterexampleValue, ProofStrength, Ty};

    fn test_span() -> SourceSpan {
        SourceSpan {
            file: "src/lib.rs".into(),
            line_start: 42,
            col_start: 5,
            line_end: 42,
            col_end: 20,
        }
    }

    fn overflow_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "test::add".into(),
            location: test_span(),
            formula: Formula::Gt(
                Box::new(Formula::Add(
                    Box::new(Formula::Var("a".into(), Sort::BitVec(64))),
                    Box::new(Formula::Var("b".into(), Sort::BitVec(64))),
                )),
                Box::new(Formula::UInt(u64::MAX as u128)),
            ),
            contract_metadata: None,
        }
    }

    fn div_zero_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test::divide".into(),
            location: test_span(),
            formula: Formula::Eq(
                Box::new(Formula::Var("divisor".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
        }
    }

    fn precondition_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Precondition {
                callee: "safe_sqrt".into(),
            },
            function: "test::caller".into(),
            location: test_span(),
            formula: Formula::Implies(
                Box::new(Formula::Ge(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                )),
                Box::new(Formula::Bool(false)),
            ),
            contract_metadata: None,
        }
    }

    fn postcondition_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Postcondition,
            function: "test::compute".into(),
            location: test_span(),
            formula: Formula::Implies(
                Box::new(Formula::Bool(true)),
                Box::new(Formula::Gt(
                    Box::new(Formula::Var("result".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                )),
            ),
            contract_metadata: None,
        }
    }

    // -------------------------------------------------------------------
    // BlameTarget tests
    // -------------------------------------------------------------------

    #[test]
    fn test_blame_target_location_statement() {
        let target = BlameTarget::Statement {
            function: "f".into(),
            location: test_span(),
            description: "assign".into(),
        };
        assert!(target.location().is_some());
        assert_eq!(target.kind_label(), "statement");
    }

    #[test]
    fn test_blame_target_location_assumption_none() {
        let target = BlameTarget::Assumption {
            description: "type bounds".into(),
            location: None,
        };
        assert!(target.location().is_none());
        assert_eq!(target.kind_label(), "assumption");
    }

    // -------------------------------------------------------------------
    // BlameScore tests
    // -------------------------------------------------------------------

    #[test]
    fn test_blame_score_clamps_confidence() {
        let target = BlameTarget::Assumption {
            description: "test".into(),
            location: None,
        };
        let score = BlameScore::new(target, 1.5, "over max".into());
        assert!((score.confidence - 1.0).abs() < f64::EPSILON);

        let target2 = BlameTarget::Assumption {
            description: "test".into(),
            location: None,
        };
        let score2 = BlameScore::new(target2, -0.5, "under min".into());
        assert!((score2.confidence - 0.0).abs() < f64::EPSILON);
    }

    // -------------------------------------------------------------------
    // analyze_unsat_core tests
    // -------------------------------------------------------------------

    #[test]
    fn test_analyze_unsat_core_basic() {
        let analyzer = BlameAnalyzer::new();
        let vc = overflow_vc();
        let core_labels = vec![
            "spec:overflow_check".into(),
            "stmt:assign_3".into(),
            "expr:add_op".into(),
        ];

        let scores = analyzer.analyze_unsat_core(&vc, &core_labels);
        assert_eq!(scores.len(), 3);
        // First element should have highest confidence
        assert!(scores[0].confidence >= scores[1].confidence);
        assert!(scores[1].confidence >= scores[2].confidence);
        // First should be a spec target
        assert_eq!(scores[0].target.kind_label(), "specification");
    }

    #[test]
    fn test_analyze_unsat_core_empty() {
        let analyzer = BlameAnalyzer::new();
        let vc = overflow_vc();
        let scores = analyzer.analyze_unsat_core(&vc, &[]);
        assert!(scores.is_empty());
    }

    // -------------------------------------------------------------------
    // analyze_counterexample tests
    // -------------------------------------------------------------------

    #[test]
    fn test_analyze_counterexample_boundary_values() {
        let analyzer = BlameAnalyzer::new();
        let vc = overflow_vc();
        let cex = Counterexample::new(vec![
            ("a".into(), CounterexampleValue::Uint(u64::MAX as u128)),
            ("b".into(), CounterexampleValue::Uint(1)),
        ]);

        let scores = analyzer.analyze_counterexample(&vc, &cex);
        assert_eq!(scores.len(), 2);

        // u64::MAX is a boundary value, so 'a' should have higher confidence
        let a_score = scores.iter().find(|s| s.explanation.contains("a =")).unwrap();
        let b_score = scores.iter().find(|s| s.explanation.contains("b =")).unwrap();
        assert!(
            a_score.confidence > b_score.confidence,
            "boundary value should have higher confidence"
        );
        assert!(a_score.explanation.contains("boundary"));
    }

    #[test]
    fn test_analyze_counterexample_with_formula_vars() {
        let analyzer = BlameAnalyzer::new();
        let vc = div_zero_vc();
        let cex = Counterexample::new(vec![
            ("divisor".into(), CounterexampleValue::Int(0)),
            ("unrelated".into(), CounterexampleValue::Int(42)),
        ]);

        let scores = analyzer.analyze_counterexample(&vc, &cex);
        assert_eq!(scores.len(), 2);

        // 'divisor' is in the formula AND is boundary (0), should score higher
        let divisor_score = scores
            .iter()
            .find(|s| s.explanation.contains("divisor"))
            .unwrap();
        let unrelated_score = scores
            .iter()
            .find(|s| s.explanation.contains("unrelated"))
            .unwrap();
        assert!(divisor_score.confidence > unrelated_score.confidence);
    }

    // -------------------------------------------------------------------
    // rank_blame_targets tests
    // -------------------------------------------------------------------

    #[test]
    fn test_rank_blame_targets_sorts_descending() {
        let mut scores = vec![
            BlameScore::new(
                BlameTarget::Assumption {
                    description: "low".into(),
                    location: None,
                },
                0.3,
                "low".into(),
            ),
            BlameScore::new(
                BlameTarget::Assumption {
                    description: "high".into(),
                    location: Some(test_span()),
                },
                0.9,
                "high".into(),
            ),
            BlameScore::new(
                BlameTarget::Assumption {
                    description: "mid".into(),
                    location: None,
                },
                0.6,
                "mid".into(),
            ),
        ];

        rank_blame_targets(&mut scores);
        assert!((scores[0].confidence - 0.9).abs() < f64::EPSILON);
        assert!((scores[1].confidence - 0.6).abs() < f64::EPSILON);
        assert!((scores[2].confidence - 0.3).abs() < f64::EPSILON);
    }

    // -------------------------------------------------------------------
    // Full analyze tests
    // -------------------------------------------------------------------

    #[test]
    fn test_analyze_overflow_failure() {
        let analyzer = BlameAnalyzer::new();
        let vc = overflow_vc();
        let cex = Counterexample::new(vec![
            ("a".into(), CounterexampleValue::Uint(u64::MAX as u128)),
            ("b".into(), CounterexampleValue::Uint(1)),
        ]);
        let result = VerificationResult::Failed {
            solver: "z4".into(),
            time_ms: 50,
            counterexample: Some(cex),
        };

        let report = analyzer.analyze(&vc, &result);
        assert!(!report.is_empty());
        assert_eq!(report.vc_function, "test::add");

        // Top blame should be high confidence
        let top = report.top().unwrap();
        assert!(top.confidence > 0.5);
    }

    #[test]
    fn test_analyze_precondition_failure() {
        let analyzer = BlameAnalyzer::new();
        let vc = precondition_vc();
        let cex = Counterexample::new(vec![
            ("x".into(), CounterexampleValue::Int(-1)),
        ]);
        let result = VerificationResult::Failed {
            solver: "z4".into(),
            time_ms: 10,
            counterexample: Some(cex),
        };

        let report = analyzer.analyze(&vc, &result);
        assert!(!report.is_empty());

        // Should blame the specification (requires)
        let has_spec = report
            .entries
            .iter()
            .any(|e| e.target.kind_label() == "specification");
        assert!(has_spec, "should blame a specification");
    }

    #[test]
    fn test_analyze_postcondition_failure() {
        let analyzer = BlameAnalyzer::new();
        let vc = postcondition_vc();
        let cex = Counterexample::new(vec![
            ("result".into(), CounterexampleValue::Int(0)),
        ]);
        let result = VerificationResult::Failed {
            solver: "z4".into(),
            time_ms: 10,
            counterexample: Some(cex),
        };

        let report = analyzer.analyze(&vc, &result);
        assert!(!report.is_empty());

        // Should blame both spec and statement
        let has_spec = report
            .entries
            .iter()
            .any(|e| e.target.kind_label() == "specification");
        let has_stmt = report
            .entries
            .iter()
            .any(|e| e.target.kind_label() == "statement");
        assert!(has_spec);
        assert!(has_stmt);
    }

    #[test]
    fn test_analyze_proved_empty_report() {
        let analyzer = BlameAnalyzer::new();
        let vc = overflow_vc();
        let result = VerificationResult::Proved {
            solver: "z4".into(),
            time_ms: 50,
            strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, };

        let report = analyzer.analyze(&vc, &result);
        assert!(report.is_empty());
    }

    #[test]
    fn test_analyze_timeout_structural_blame() {
        let analyzer = BlameAnalyzer::new();
        let vc = div_zero_vc();
        let result = VerificationResult::Timeout {
            solver: "z4".into(),
            timeout_ms: 5000,
        };

        let report = analyzer.analyze(&vc, &result);
        // Timeout still produces structural blame
        assert!(!report.is_empty());
    }

    #[test]
    fn test_blame_report_format_summary() {
        let analyzer = BlameAnalyzer::new();
        let vc = overflow_vc();
        let cex = Counterexample::new(vec![
            ("a".into(), CounterexampleValue::Uint(u64::MAX as u128)),
            ("b".into(), CounterexampleValue::Uint(1)),
        ]);
        let result = VerificationResult::Failed {
            solver: "z4".into(),
            time_ms: 50,
            counterexample: Some(cex),
        };

        let report = analyzer.analyze(&vc, &result);
        let summary = report.format_summary();
        assert!(summary.contains("test::add"));
        assert!(summary.contains("#1:"));
    }

    // -------------------------------------------------------------------
    // is_boundary_value tests
    // -------------------------------------------------------------------

    #[test]
    fn test_boundary_value_detection() {
        assert!(is_boundary_value(&CounterexampleValue::Uint(0)));
        assert!(is_boundary_value(&CounterexampleValue::Uint(u64::MAX as u128)));
        assert!(is_boundary_value(&CounterexampleValue::Uint(u32::MAX as u128)));
        assert!(is_boundary_value(&CounterexampleValue::Int(0)));
        assert!(is_boundary_value(&CounterexampleValue::Int(i64::MAX as i128)));
        assert!(is_boundary_value(&CounterexampleValue::Int(i64::MIN as i128)));
        assert!(!is_boundary_value(&CounterexampleValue::Uint(42)));
        assert!(!is_boundary_value(&CounterexampleValue::Int(42)));
        assert!(!is_boundary_value(&CounterexampleValue::Bool(true)));
    }
}
