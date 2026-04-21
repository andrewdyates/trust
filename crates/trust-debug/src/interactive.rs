// trust-debug/interactive.rs: Interactive proof debugging session
//
// Provides a session-based interface for stepping through proof failures,
// inspecting variable symbolic values, querying why obligations failed,
// and simplifying formulas interactively. Designed for integration with
// CLI and IDE debugging frontends.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::fmt::Write;

use trust_types::{Formula, VerificationCondition, VerificationResult};

use crate::proof_explain::ProofExplainer;

// ---------------------------------------------------------------------------
// DebugCommand
// ---------------------------------------------------------------------------

/// Commands available in an interactive debug session.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum DebugCommand {
    /// Step forward to the next obligation/trace step.
    StepForward,
    /// Step backward to the previous obligation/trace step.
    StepBack,
    /// Inspect a variable's symbolic value at the current position.
    Inspect { variable: String },
    /// Explain why the current obligation failed.
    Why,
    /// List all assumptions/preconditions active at the current position.
    Assumptions,
    /// Simplify the current obligation's formula for display.
    Simplify,
}

// ---------------------------------------------------------------------------
// SessionState
// ---------------------------------------------------------------------------

/// Tracks the current position within a debug session.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SessionState {
    /// Index of the current obligation being inspected (0-based).
    pub current_index: usize,
    /// Total number of obligations in the session.
    pub total_obligations: usize,
    /// History of commands executed in this session.
    pub command_history: Vec<DebugCommand>,
}

impl SessionState {
    /// Create a new session state for the given number of obligations.
    #[must_use]
    pub(crate) fn new(total_obligations: usize) -> Self {
        Self {
            current_index: 0,
            total_obligations,
            command_history: Vec::new(),
        }
    }

    /// Whether the session can step forward.
    #[must_use]
    pub(crate) fn can_step_forward(&self) -> bool {
        self.current_index + 1 < self.total_obligations
    }

    /// Whether the session can step backward.
    #[must_use]
    pub(crate) fn can_step_back(&self) -> bool {
        self.current_index > 0
    }
}

// ---------------------------------------------------------------------------
// ObligationEntry
// ---------------------------------------------------------------------------

/// A single obligation with its verification result, for session use.
#[derive(Debug, Clone)]
pub(crate) struct ObligationEntry {
    pub(crate) vc: VerificationCondition,
    pub(crate) result: VerificationResult,
}

// ---------------------------------------------------------------------------
// DebugResponse
// ---------------------------------------------------------------------------

/// The structured response from executing a debug command.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct DebugResponse {
    /// The command that produced this response.
    pub command: DebugCommand,
    /// Human-readable output text.
    pub output: String,
    /// Updated session state after the command.
    pub state_summary: String,
}

// ---------------------------------------------------------------------------
// DebugSession
// ---------------------------------------------------------------------------

/// Manages state for interactive proof exploration.
///
/// A session holds a set of verification obligations and their results,
/// allowing the user to step through them, inspect variables, and query
/// why particular obligations failed.
#[derive(Debug, Clone)]
pub(crate) struct DebugSession {
    /// The function being debugged.
    pub(crate) function_name: String,
    /// Obligations loaded into the session.
    pub(crate) obligations: Vec<ObligationEntry>,
    /// Current session state.
    pub(crate) state: SessionState,
    /// Variable name overrides for display.
    pub(crate) var_names: FxHashMap<String, String>,
}

impl DebugSession {
    /// Create a new debug session for a function's obligations.
    #[must_use]
    pub(crate) fn new(
        function_name: &str,
        obligations: Vec<(VerificationCondition, VerificationResult)>,
    ) -> Self {
        let total = obligations.len();
        let entries = obligations
            .into_iter()
            .map(|(vc, result)| ObligationEntry { vc, result })
            .collect();
        Self {
            function_name: function_name.to_string(),
            obligations: entries,
            state: SessionState::new(total),
            var_names: FxHashMap::default(),
        }
    }

    /// Add a human-readable name mapping for a solver variable.
    pub(crate) fn add_var_name(&mut self, solver_name: &str, source_name: &str) {
        self.var_names
            .insert(solver_name.to_string(), source_name.to_string());
    }

    /// Get the current session state.
    #[must_use]
    pub(crate) fn state(&self) -> &SessionState {
        &self.state
    }

    /// Get the current obligation (if any).
    #[must_use]
    pub(crate) fn current_obligation(&self) -> Option<&VerificationCondition> {
        self.obligations
            .get(self.state.current_index)
            .map(|e| &e.vc)
    }

    /// Get the current result (if any).
    #[must_use]
    pub(crate) fn current_result(&self) -> Option<&VerificationResult> {
        self.obligations
            .get(self.state.current_index)
            .map(|e| &e.result)
    }

    /// Execute a debug command and return the response.
    #[must_use]
    pub(crate) fn execute_command(&mut self, command: DebugCommand) -> DebugResponse {
        self.state.command_history.push(command.clone());

        match &command {
            DebugCommand::StepForward => self.step_forward(),
            DebugCommand::StepBack => self.step_back(),
            DebugCommand::Inspect { variable } => {
                let var = variable.clone();
                self.inspect_variable_response(&var, &command)
            }
            DebugCommand::Why => self.why_response(&command),
            DebugCommand::Assumptions => self.assumptions_response(&command),
            DebugCommand::Simplify => self.simplify_response(&command),
        }
    }

    fn step_forward(&mut self) -> DebugResponse {
        let cmd = DebugCommand::StepForward;
        if self.state.can_step_forward() {
            self.state.current_index += 1;
            let output = self.current_obligation_summary();
            DebugResponse {
                command: cmd,
                output,
                state_summary: self.state_summary(),
            }
        } else {
            DebugResponse {
                command: cmd,
                output: "Already at last obligation.".to_string(),
                state_summary: self.state_summary(),
            }
        }
    }

    fn step_back(&mut self) -> DebugResponse {
        let cmd = DebugCommand::StepBack;
        if self.state.can_step_back() {
            self.state.current_index -= 1;
            let output = self.current_obligation_summary();
            DebugResponse {
                command: cmd,
                output,
                state_summary: self.state_summary(),
            }
        } else {
            DebugResponse {
                command: cmd,
                output: "Already at first obligation.".to_string(),
                state_summary: self.state_summary(),
            }
        }
    }

    fn inspect_variable_response(
        &self,
        variable: &str,
        command: &DebugCommand,
    ) -> DebugResponse {
        let output = inspect_variable(&self.obligations, self.state.current_index, variable);
        DebugResponse {
            command: command.clone(),
            output,
            state_summary: self.state_summary(),
        }
    }

    fn why_response(&self, command: &DebugCommand) -> DebugResponse {
        let output = if let Some(entry) = self.obligations.get(self.state.current_index) {
            why_failed(&entry.vc, &entry.result)
        } else {
            "No obligation at current position.".to_string()
        };
        DebugResponse {
            command: command.clone(),
            output,
            state_summary: self.state_summary(),
        }
    }

    fn assumptions_response(&self, command: &DebugCommand) -> DebugResponse {
        let output = if let Some(entry) = self.obligations.get(self.state.current_index) {
            collect_assumptions(&entry.vc.formula)
        } else {
            "No obligation at current position.".to_string()
        };
        DebugResponse {
            command: command.clone(),
            output,
            state_summary: self.state_summary(),
        }
    }

    fn simplify_response(&self, command: &DebugCommand) -> DebugResponse {
        let output = if let Some(entry) = self.obligations.get(self.state.current_index) {
            simplify_formula(&entry.vc.formula)
        } else {
            "No obligation at current position.".to_string()
        };
        DebugResponse {
            command: command.clone(),
            output,
            state_summary: self.state_summary(),
        }
    }

    fn current_obligation_summary(&self) -> String {
        match self.obligations.get(self.state.current_index) {
            Some(entry) => {
                let status = match &entry.result {
                    VerificationResult::Proved { .. } => "PROVED",
                    VerificationResult::Failed { .. } => "FAILED",
                    VerificationResult::Unknown { .. } => "UNKNOWN",
                    VerificationResult::Timeout { .. } => "TIMEOUT",
                    _ => "unknown",
                };
                format!(
                    "[{}/{}] {} -- {} at {}:{}",
                    self.state.current_index + 1,
                    self.state.total_obligations,
                    entry.vc.kind.description(),
                    status,
                    entry.vc.location.file,
                    entry.vc.location.line_start,
                )
            }
            None => "No obligations loaded.".to_string(),
        }
    }

    fn state_summary(&self) -> String {
        format!(
            "Position {}/{} in {}",
            self.state.current_index + 1,
            self.state.total_obligations,
            self.function_name,
        )
    }
}

// ---------------------------------------------------------------------------
// Standalone functions
// ---------------------------------------------------------------------------

/// Inspect a variable's symbolic value at a given obligation index.
///
/// Searches the obligation's counterexample assignments and formula for
/// the variable, returning its value or formula-level reference.
#[must_use]
pub(crate) fn inspect_variable(
    obligations: &[ObligationEntry],
    index: usize,
    variable: &str,
) -> String {
    let Some(entry) = obligations.get(index) else {
        return format!("No obligation at index {index}.");
    };

    // Check counterexample first
    if let VerificationResult::Failed {
        counterexample: Some(ref cex),
        ..
    } = entry.result
        && let Some((name, value)) = cex
            .assignments
            .iter()
            .find(|(n, _)| n == variable)
        {
            return format!("{name} = {value} (concrete, from counterexample)");
        }

    // Check formula for variable references
    if formula_contains_var(&entry.vc.formula, variable) {
        return format!(
            "{variable} appears in formula for '{}' but has no concrete value.",
            entry.vc.kind.description()
        );
    }

    format!("Variable '{variable}' not found at this obligation.")
}

/// Explain why a particular obligation failed.
///
/// Uses the proof explainer to build a human-readable explanation.
#[must_use]
pub(crate) fn why_failed(vc: &VerificationCondition, result: &VerificationResult) -> String {
    let explainer = ProofExplainer::default();
    let explanation = explainer.explain(vc, result);

    let mut output = String::new();
    output.push_str(&explanation.summary);
    output.push('\n');

    if !explanation.reasoning.is_empty() {
        output.push_str("\nReasoning:\n");
        output.push_str(&explanation.reasoning.format_numbered());
    }

    if !explanation.conflicts.is_empty() {
        output.push_str("\nConflicts:\n");
        for conflict in &explanation.conflicts {
            let _ = writeln!(output, "  - {}", conflict.description);
            for c in &conflict.constraints {
                let _ = writeln!(output, "    * {c}");
            }
        }
    }

    if !explanation.suggestions.is_empty() {
        output.push_str("\nSuggested fixes:\n");
        for suggestion in &explanation.suggestions {
            let _ = writeln!(output, "  - {}", suggestion.description);
            if let Some(ref code) = suggestion.code_change {
                let _ = writeln!(output, "    Code: {code}");
            }
        }
    }

    output
}

/// Format a debug response as a single string.
#[must_use]
pub(crate) fn format_response(response: &DebugResponse) -> String {
    format!("{}\n--- {}", response.output, response.state_summary)
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Collect assumptions (preconditions, conjuncts) from a formula.
fn collect_assumptions(formula: &Formula) -> String {
    let mut assumptions = Vec::new();
    gather_assumptions(formula, &mut assumptions, 0);

    if assumptions.is_empty() {
        return "No explicit assumptions found in this obligation.".to_string();
    }

    let mut output = String::from("Active assumptions:\n");
    for (i, assumption) in assumptions.iter().enumerate() {
        let _ = writeln!(output, "  {}. {assumption}", i + 1);
    }
    output
}

/// Recursively gather assumption strings from a formula.
fn gather_assumptions(formula: &Formula, out: &mut Vec<String>, depth: usize) {
    if depth > 20 {
        return;
    }
    match formula {
        Formula::Implies(premise, _) => {
            out.push(formula_brief(premise));
        }
        Formula::And(conjuncts) => {
            for c in conjuncts {
                gather_assumptions(c, out, depth + 1);
            }
        }
        Formula::Forall(vars, body) => {
            let names: Vec<_> = vars.iter().map(|(n, _)| n.as_str()).collect();
            out.push(format!("forall {}", names.join(", ")));
            gather_assumptions(body, out, depth + 1);
        }
        _ => {
            let brief = formula_brief(formula);
            if !brief.is_empty() && brief != "true" && brief != "false" {
                out.push(brief);
            }
        }
    }
}

/// Produce a simplified view of a formula for display.
fn simplify_formula(formula: &Formula) -> String {
    let simplified = simplify_inner(formula);
    format!("Simplified: {simplified}")
}

/// Inner simplification: constant folding and trivial reduction.
fn simplify_inner(formula: &Formula) -> String {
    match formula {
        Formula::Bool(true) => "true".to_string(),
        Formula::Bool(false) => "false".to_string(),
        Formula::Int(n) => format!("{n}"),
        Formula::UInt(n) => format!("{n}"),
        Formula::Var(name, _) => name.clone(),
        Formula::Not(inner) => {
            match inner.as_ref() {
                Formula::Bool(true) => "false".to_string(),
                Formula::Bool(false) => "true".to_string(),
                Formula::Not(double) => simplify_inner(double),
                _ => format!("not({})", simplify_inner(inner)),
            }
        }
        Formula::And(terms) => {
            let simplified: Vec<_> = terms
                .iter()
                .map(simplify_inner)
                .filter(|s| s != "true")
                .collect();
            if simplified.is_empty() {
                "true".to_string()
            } else if simplified.iter().any(|s| s == "false") {
                "false".to_string()
            } else if simplified.len() == 1 {
                simplified.into_iter().next().unwrap_or_default()
            } else {
                simplified.join(" && ")
            }
        }
        Formula::Or(terms) => {
            let simplified: Vec<_> = terms
                .iter()
                .map(simplify_inner)
                .filter(|s| s != "false")
                .collect();
            if simplified.is_empty() {
                "false".to_string()
            } else if simplified.iter().any(|s| s == "true") {
                "true".to_string()
            } else if simplified.len() == 1 {
                simplified.into_iter().next().unwrap_or_default()
            } else {
                simplified.join(" || ")
            }
        }
        Formula::Implies(a, b) => {
            let sa = simplify_inner(a);
            let sb = simplify_inner(b);
            if sa == "true" {
                sb
            } else if sa == "false" || sb == "true" {
                "true".to_string()
            } else {
                format!("{sa} => {sb}")
            }
        }
        Formula::Eq(a, b) => format!("{} == {}", simplify_inner(a), simplify_inner(b)),
        Formula::Lt(a, b) => format!("{} < {}", simplify_inner(a), simplify_inner(b)),
        Formula::Le(a, b) => format!("{} <= {}", simplify_inner(a), simplify_inner(b)),
        Formula::Gt(a, b) => format!("{} > {}", simplify_inner(a), simplify_inner(b)),
        Formula::Ge(a, b) => format!("{} >= {}", simplify_inner(a), simplify_inner(b)),
        Formula::Add(a, b) => format!("{} + {}", simplify_inner(a), simplify_inner(b)),
        Formula::Sub(a, b) => format!("{} - {}", simplify_inner(a), simplify_inner(b)),
        Formula::Mul(a, b) => format!("{} * {}", simplify_inner(a), simplify_inner(b)),
        Formula::Div(a, b) => format!("{} / {}", simplify_inner(a), simplify_inner(b)),
        Formula::Rem(a, b) => format!("{} % {}", simplify_inner(a), simplify_inner(b)),
        _ => formula_brief(formula),
    }
}

/// Brief one-line summary of a formula (non-recursive).
fn formula_brief(formula: &Formula) -> String {
    match formula {
        Formula::Bool(b) => format!("{b}"),
        Formula::Int(n) => format!("{n}"),
        Formula::UInt(n) => format!("{n}"),
        Formula::Var(name, _) => name.clone(),
        Formula::Not(_) => "not(...)".to_string(),
        Formula::And(terms) => format!("({} conjuncts)", terms.len()),
        Formula::Or(terms) => format!("({} disjuncts)", terms.len()),
        Formula::Implies(_, _) => "(implication)".to_string(),
        Formula::Eq(a, b) => format!("{} == {}", formula_brief(a), formula_brief(b)),
        Formula::Lt(a, b) => format!("{} < {}", formula_brief(a), formula_brief(b)),
        Formula::Le(a, b) => format!("{} <= {}", formula_brief(a), formula_brief(b)),
        Formula::Gt(a, b) => format!("{} > {}", formula_brief(a), formula_brief(b)),
        Formula::Ge(a, b) => format!("{} >= {}", formula_brief(a), formula_brief(b)),
        Formula::Add(a, b) => format!("{} + {}", formula_brief(a), formula_brief(b)),
        Formula::Sub(a, b) => format!("{} - {}", formula_brief(a), formula_brief(b)),
        Formula::Forall(vars, _) => {
            let names: Vec<_> = vars.iter().map(|(n, _)| n.as_str()).collect();
            format!("forall {}", names.join(", "))
        }
        _ => format!("{:?}", std::mem::discriminant(formula)),
    }
}

/// Check if a formula contains a reference to the named variable.
fn formula_contains_var(formula: &Formula, name: &str) -> bool {
    match formula {
        Formula::Var(n, _) => n == name,
        other => other.children().iter().any(|c| formula_contains_var(c, name)),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{
        BinOp, Counterexample, CounterexampleValue, ProofStrength, Sort, SourceSpan, Ty, VcKind,
    };

    fn test_span() -> SourceSpan {
        SourceSpan {
            file: "src/main.rs".into(),
            line_start: 10,
            col_start: 1,
            line_end: 10,
            col_end: 30,
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

    fn failed_result_with_cex(
        assignments: Vec<(String, CounterexampleValue)>,
    ) -> VerificationResult {
        VerificationResult::Failed {
            solver: "z4".into(),
            time_ms: 42,
            counterexample: Some(Counterexample::new(assignments)),
        }
    }

    fn proved_result() -> VerificationResult {
        VerificationResult::Proved {
            solver: "z4".into(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, }
    }

    fn make_session() -> DebugSession {
        let obligations = vec![
            (
                overflow_vc(),
                failed_result_with_cex(vec![
                    ("a".into(), CounterexampleValue::Uint(u64::MAX as u128)),
                    ("b".into(), CounterexampleValue::Uint(1)),
                ]),
            ),
            (div_zero_vc(), proved_result()),
            (
                div_zero_vc(),
                failed_result_with_cex(vec![(
                    "divisor".into(),
                    CounterexampleValue::Int(0),
                )]),
            ),
        ];
        DebugSession::new("test::example", obligations)
    }

    // -----------------------------------------------------------------------
    // Test 1: Session creation and initial state
    // -----------------------------------------------------------------------

    #[test]
    fn test_session_creation_initial_state() {
        let session = make_session();
        assert_eq!(session.state().current_index, 0);
        assert_eq!(session.state().total_obligations, 3);
        assert!(session.state().command_history.is_empty());
        assert_eq!(session.function_name, "test::example");
    }

    // -----------------------------------------------------------------------
    // Test 2: Step forward
    // -----------------------------------------------------------------------

    #[test]
    fn test_step_forward_advances_position() {
        let mut session = make_session();
        let response = session.execute_command(DebugCommand::StepForward);
        assert_eq!(session.state().current_index, 1);
        assert!(response.output.contains("division by zero"));
        assert!(response.output.contains("PROVED"));
        assert!(response.state_summary.contains("2/3"));
    }

    // -----------------------------------------------------------------------
    // Test 3: Step forward at end
    // -----------------------------------------------------------------------

    #[test]
    fn test_step_forward_at_end_stays() {
        let mut session = make_session();
        let _ = session.execute_command(DebugCommand::StepForward);
        let _ = session.execute_command(DebugCommand::StepForward);
        // Now at index 2 (last)
        let response = session.execute_command(DebugCommand::StepForward);
        assert_eq!(session.state().current_index, 2);
        assert!(response.output.contains("Already at last"));
    }

    // -----------------------------------------------------------------------
    // Test 4: Step back
    // -----------------------------------------------------------------------

    #[test]
    fn test_step_back_decrements_position() {
        let mut session = make_session();
        let _ = session.execute_command(DebugCommand::StepForward);
        assert_eq!(session.state().current_index, 1);

        let response = session.execute_command(DebugCommand::StepBack);
        assert_eq!(session.state().current_index, 0);
        assert!(response.output.contains("arithmetic overflow"));
        assert!(response.output.contains("FAILED"));
    }

    // -----------------------------------------------------------------------
    // Test 5: Step back at start
    // -----------------------------------------------------------------------

    #[test]
    fn test_step_back_at_start_stays() {
        let mut session = make_session();
        let response = session.execute_command(DebugCommand::StepBack);
        assert_eq!(session.state().current_index, 0);
        assert!(response.output.contains("Already at first"));
    }

    // -----------------------------------------------------------------------
    // Test 6: Inspect variable found in counterexample
    // -----------------------------------------------------------------------

    #[test]
    fn test_inspect_variable_from_counterexample() {
        let mut session = make_session();
        let response = session.execute_command(DebugCommand::Inspect {
            variable: "a".to_string(),
        });
        assert!(response.output.contains("a ="));
        assert!(response.output.contains("concrete"));
        assert!(response.output.contains("counterexample"));
    }

    // -----------------------------------------------------------------------
    // Test 7: Inspect variable in formula but not counterexample
    // -----------------------------------------------------------------------

    #[test]
    fn test_inspect_variable_in_formula_only() {
        let mut session = make_session();
        // Move to the proved obligation (index 1) -- no counterexample
        let _ = session.execute_command(DebugCommand::StepForward);

        let response = session.execute_command(DebugCommand::Inspect {
            variable: "divisor".to_string(),
        });
        assert!(response.output.contains("divisor"));
        assert!(response.output.contains("appears in formula"));
    }

    // -----------------------------------------------------------------------
    // Test 8: Inspect nonexistent variable
    // -----------------------------------------------------------------------

    #[test]
    fn test_inspect_variable_not_found() {
        let mut session = make_session();
        let response = session.execute_command(DebugCommand::Inspect {
            variable: "nonexistent".to_string(),
        });
        assert!(response.output.contains("not found"));
    }

    // -----------------------------------------------------------------------
    // Test 9: Why command on failed obligation
    // -----------------------------------------------------------------------

    #[test]
    fn test_why_failed_obligation() {
        let mut session = make_session();
        let response = session.execute_command(DebugCommand::Why);
        assert!(response.output.contains("FAILED"));
        assert!(response.output.contains("counterexample"));
        assert!(response.output.contains("Reasoning"));
    }

    // -----------------------------------------------------------------------
    // Test 10: Why command on proved obligation
    // -----------------------------------------------------------------------

    #[test]
    fn test_why_proved_obligation() {
        let mut session = make_session();
        let _ = session.execute_command(DebugCommand::StepForward);
        let response = session.execute_command(DebugCommand::Why);
        assert!(response.output.contains("PROVED"));
    }

    // -----------------------------------------------------------------------
    // Test 11: Assumptions command
    // -----------------------------------------------------------------------

    #[test]
    fn test_assumptions_command() {
        // Build a VC with an implication (premise => conclusion)
        let vc = VerificationCondition {
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
                Box::new(Formula::Bool(true)),
            ),
            contract_metadata: None,
        };
        let result = proved_result();
        let mut session = DebugSession::new("test::caller", vec![(vc, result)]);

        let response = session.execute_command(DebugCommand::Assumptions);
        assert!(response.output.contains("assumptions"));
    }

    // -----------------------------------------------------------------------
    // Test 12: Simplify command
    // -----------------------------------------------------------------------

    #[test]
    fn test_simplify_command() {
        // Formula: And([true, x > 0]) should simplify to just "x > 0"
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test::f".into(),
            location: test_span(),
            formula: Formula::And(vec![
                Formula::Bool(true),
                Formula::Gt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
            ]),
            contract_metadata: None,
        };
        let result = proved_result();
        let mut session = DebugSession::new("test::f", vec![(vc, result)]);

        let response = session.execute_command(DebugCommand::Simplify);
        assert!(response.output.contains("Simplified"));
        assert!(response.output.contains("x > 0"));
        // The "true" conjunct should be removed
        assert!(!response.output.contains("true &&"));
    }

    // -----------------------------------------------------------------------
    // Test 13: Format response
    // -----------------------------------------------------------------------

    #[test]
    fn test_format_response_includes_state() {
        let mut session = make_session();
        let response = session.execute_command(DebugCommand::Why);
        let formatted = format_response(&response);
        assert!(formatted.contains("---"));
        assert!(formatted.contains("Position 1/3"));
        assert!(formatted.contains("test::example"));
    }

    // -----------------------------------------------------------------------
    // Test 14: Command history tracking
    // -----------------------------------------------------------------------

    #[test]
    fn test_command_history_tracks_all_commands() {
        let mut session = make_session();
        let _ = session.execute_command(DebugCommand::StepForward);
        let _ = session.execute_command(DebugCommand::Why);
        let _ = session.execute_command(DebugCommand::StepBack);
        let _ = session.execute_command(DebugCommand::Inspect {
            variable: "x".to_string(),
        });

        assert_eq!(session.state().command_history.len(), 4);
        assert_eq!(session.state().command_history[0], DebugCommand::StepForward);
        assert_eq!(session.state().command_history[1], DebugCommand::Why);
        assert_eq!(session.state().command_history[2], DebugCommand::StepBack);
    }

    // -----------------------------------------------------------------------
    // Test 15: Empty session handles commands gracefully
    // -----------------------------------------------------------------------

    #[test]
    fn test_empty_session_no_panic() {
        let mut session = DebugSession::new("empty::func", vec![]);
        assert_eq!(session.state().total_obligations, 0);

        let r1 = session.execute_command(DebugCommand::StepForward);
        assert!(r1.output.contains("Already at last"));

        let r2 = session.execute_command(DebugCommand::Why);
        assert!(r2.output.contains("No obligation"));

        let r3 = session.execute_command(DebugCommand::Inspect {
            variable: "x".to_string(),
        });
        assert!(r3.output.contains("No obligation"));

        let r4 = session.execute_command(DebugCommand::Assumptions);
        assert!(r4.output.contains("No obligation"));

        let r5 = session.execute_command(DebugCommand::Simplify);
        assert!(r5.output.contains("No obligation"));
    }

    // -----------------------------------------------------------------------
    // Test 16: Simplify constant folding
    // -----------------------------------------------------------------------

    #[test]
    fn test_simplify_constant_folding() {
        // not(not(x)) should simplify to x
        let formula = Formula::Not(Box::new(Formula::Not(Box::new(Formula::Var(
            "x".into(),
            Sort::Bool,
        )))));
        let result = simplify_inner(&formula);
        assert_eq!(result, "x");

        // Implies(true, body) => body
        let formula2 = Formula::Implies(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Var("y".into(), Sort::Int)),
        );
        let result2 = simplify_inner(&formula2);
        assert_eq!(result2, "y");

        // Or with false terms removed
        let formula3 = Formula::Or(vec![
            Formula::Bool(false),
            Formula::Var("z".into(), Sort::Bool),
        ]);
        let result3 = simplify_inner(&formula3);
        assert_eq!(result3, "z");
    }
}
