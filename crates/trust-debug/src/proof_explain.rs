// trust-debug/proof_explain.rs: Proof explanation and VC visualization
//
// Converts solver output (models, unsat cores) into human-readable explanations.
// Maps VC terms back to source code, builds reasoning chains, identifies conflicts,
// suggests fixes, and exports VC graphs as DOT for visualization.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};
use std::fmt::Write as FmtWrite;

use trust_types::{
    Formula, Sort, SourceSpan, VcKind, VerificationCondition, VerificationResult,
};

// ---------------------------------------------------------------------------
// ProofExplainer
// ---------------------------------------------------------------------------

/// Converts solver model/unsat core into a human-readable explanation.
///
/// Given a VC and its verification result, produces a structured explanation
/// of WHY the property holds or fails, in terms the programmer understands.
#[derive(Debug, Clone)]
pub(crate) struct ProofExplainer {
    /// Maximum depth when traversing formula trees for explanation.
    max_depth: usize,
}

impl Default for ProofExplainer {
    fn default() -> Self {
        Self { max_depth: 20 }
    }
}

/// A structured explanation of a verification result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Explanation {
    /// One-line summary of the result.
    pub summary: String,
    /// Detailed reasoning chain from hypothesis to conclusion.
    pub reasoning: ReasonChain,
    /// Source locations involved.
    pub source_mappings: Vec<SourceMapping>,
    /// If the VC failed, which constraints conflict.
    pub conflicts: Vec<Conflict>,
    /// Suggested fixes (if any).
    pub suggestions: Vec<FixSuggestion>,
}

impl ProofExplainer {
    #[must_use]
    pub(crate) fn new(max_depth: usize) -> Self {
        Self { max_depth }
    }

    /// Explain a verification result for a given VC.
    #[must_use]
    pub(crate) fn explain(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
    ) -> Explanation {
        let mapper = SourceMapper::new();
        let source_mappings = mapper.map_formula(&vc.formula, &vc.location);

        match result {
            VerificationResult::Proved { solver, strength, .. } => {
                let summary = format!(
                    "Property '{}' PROVED by {} ({:?})",
                    vc.kind.description(),
                    solver,
                    strength.assurance
                );
                let reasoning = self.build_proof_chain(vc);
                Explanation {
                    summary,
                    reasoning,
                    source_mappings,
                    conflicts: vec![],
                    suggestions: vec![],
                }
            }
            VerificationResult::Failed { solver, counterexample, .. } => {
                let summary = format!(
                    "Property '{}' FAILED (counterexample from {})",
                    vc.kind.description(),
                    solver,
                );
                let reasoning = self.build_failure_chain(vc, counterexample.as_ref());
                let conflict_explainer = ConflictExplainer::new();
                let conflicts = conflict_explainer.find_conflicts(vc, counterexample.as_ref());
                let fix_suggester = FixSuggester::new();
                let suggestions = fix_suggester.suggest(vc, &conflicts);
                Explanation {
                    summary,
                    reasoning,
                    source_mappings,
                    conflicts,
                    suggestions,
                }
            }
            VerificationResult::Unknown { solver, reason, .. } => {
                let summary = format!(
                    "Property '{}' UNKNOWN by {} ({})",
                    vc.kind.description(),
                    solver,
                    reason
                );
                Explanation {
                    summary,
                    reasoning: ReasonChain { steps: vec![ReasonStep {
                        description: format!("Solver could not determine result: {reason}"),
                        source: None,
                    }] },
                    source_mappings,
                    conflicts: vec![],
                    suggestions: vec![],
                }
            }
            VerificationResult::Timeout { solver, timeout_ms } => {
                let summary = format!(
                    "Property '{}' TIMEOUT by {} after {}ms",
                    vc.kind.description(),
                    solver,
                    timeout_ms
                );
                Explanation {
                    summary,
                    reasoning: ReasonChain { steps: vec![ReasonStep {
                        description: format!("Solver timed out after {timeout_ms}ms"),
                        source: None,
                    }] },
                    source_mappings,
                    conflicts: vec![],
                    suggestions: vec![FixSuggestion {
                        description: "Increase solver timeout or simplify the function".into(),
                        code_change: None,
                        location: Some(vc.location.clone()),
                    }],
                }
            }
            _ => Explanation {
                summary: "Unknown verification result".into(),
                reasoning: ReasonChain { steps: vec![] },
                source_mappings: vec![],
                conflicts: vec![],
                suggestions: vec![],
            }
        }
    }

    /// Build a reasoning chain for a proved VC.
    fn build_proof_chain(&self, vc: &VerificationCondition) -> ReasonChain {
        let mut steps = Vec::new();

        steps.push(ReasonStep {
            description: format!("Goal: verify '{}'", vc.kind.description()),
            source: Some(vc.location.clone()),
        });

        // Walk the formula to build intermediate reasoning steps
        self.explain_formula(&vc.formula, &mut steps, 0);

        steps.push(ReasonStep {
            description: "Solver confirmed: no inputs violate this property".into(),
            source: None,
        });

        ReasonChain { steps }
    }

    /// Build a reasoning chain for a failed VC (with counterexample).
    fn build_failure_chain(
        &self,
        vc: &VerificationCondition,
        counterexample: Option<&trust_types::Counterexample>,
    ) -> ReasonChain {
        let mut steps = Vec::new();

        steps.push(ReasonStep {
            description: format!("Goal: verify '{}'", vc.kind.description()),
            source: Some(vc.location.clone()),
        });

        // Explain the counterexample values
        if let Some(cex) = counterexample {
            steps.push(ReasonStep {
                description: "Counterexample found with these values:".into(),
                source: None,
            });
            for (name, value) in &cex.assignments {
                steps.push(ReasonStep {
                    description: format!("  {name} = {value}"),
                    source: None,
                });
            }
            // Explain why these values violate the property
            self.explain_violation_with_cex(vc, cex, &mut steps);
        } else {
            steps.push(ReasonStep {
                description: "Property violated (no counterexample details available)".into(),
                source: None,
            });
        }

        ReasonChain { steps }
    }

    /// Explain how counterexample values lead to a violation.
    fn explain_violation_with_cex(
        &self,
        vc: &VerificationCondition,
        cex: &trust_types::Counterexample,
        steps: &mut Vec<ReasonStep>,
    ) {
        match &vc.kind {
            VcKind::ArithmeticOverflow { op, operand_tys } => {
                let (a_name, a_val) = cex.assignments.first().map_or(
                    ("a".to_string(), "?".to_string()),
                    |(n, v)| (n.clone(), v.to_string()),
                );
                let (b_name, b_val) = cex.assignments.get(1).map_or(
                    ("b".to_string(), "?".to_string()),
                    |(n, v)| (n.clone(), v.to_string()),
                );
                steps.push(ReasonStep {
                    description: format!(
                        "With {a_name}={a_val} and {b_name}={b_val}, \
                         {op:?} on {:?} overflows",
                        operand_tys.0
                    ),
                    source: Some(vc.location.clone()),
                });
            }
            VcKind::DivisionByZero | VcKind::RemainderByZero => {
                let divisor = cex.assignments.iter().find(|(n, _)| {
                    n.contains("divisor") || n.contains("rhs") || n.contains("_2")
                });
                let desc = if let Some((name, val)) = divisor {
                    format!("{name} = {val} (zero divisor)")
                } else {
                    "Divisor is zero".to_string()
                };
                steps.push(ReasonStep {
                    description: desc,
                    source: Some(vc.location.clone()),
                });
            }
            VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => {
                steps.push(ReasonStep {
                    description: "Index exceeds array/slice bounds".into(),
                    source: Some(vc.location.clone()),
                });
            }
            VcKind::Precondition { callee } => {
                steps.push(ReasonStep {
                    description: format!("Precondition of '{callee}' not satisfied at call site"),
                    source: Some(vc.location.clone()),
                });
            }
            VcKind::Postcondition => {
                steps.push(ReasonStep {
                    description: "Function does not satisfy its postcondition for these inputs".into(),
                    source: Some(vc.location.clone()),
                });
            }
            _ => {
                steps.push(ReasonStep {
                    description: format!("Property '{}' violated", vc.kind.description()),
                    source: Some(vc.location.clone()),
                });
            }
        }
    }

    /// Recursively explain a formula's structure as reasoning steps.
    fn explain_formula(
        &self,
        formula: &Formula,
        steps: &mut Vec<ReasonStep>,
        depth: usize,
    ) {
        if depth >= self.max_depth {
            return;
        }

        match formula {
            Formula::Implies(premise, conclusion) => {
                steps.push(ReasonStep {
                    description: format!(
                        "If {} then {}",
                        formula_summary(premise),
                        formula_summary(conclusion)
                    ),
                    source: None,
                });
            }
            Formula::And(conjuncts) => {
                if conjuncts.len() <= 5 {
                    for c in conjuncts {
                        self.explain_formula(c, steps, depth + 1);
                    }
                } else {
                    steps.push(ReasonStep {
                        description: format!(
                            "Conjunction of {} constraints",
                            conjuncts.len()
                        ),
                        source: None,
                    });
                }
            }
            Formula::Forall(vars, body) => {
                let var_names: Vec<_> = vars.iter().map(|(n, _)| n.as_str()).collect();
                steps.push(ReasonStep {
                    description: format!(
                        "For all {}: {}",
                        var_names.join(", "),
                        formula_summary(body)
                    ),
                    source: None,
                });
            }
            _ => {
                // Leaf or simple comparison: just summarize
                let s = formula_summary(formula);
                if !s.is_empty() && s != "true" {
                    steps.push(ReasonStep {
                        description: s,
                        source: None,
                    });
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SourceMapper
// ---------------------------------------------------------------------------

/// Maps VC formula terms back to source code locations and variable names.
///
/// When a formula contains `Var("_3", Int)`, this maps it back to the
/// original variable name and source location (e.g., `x` at line 42).
#[derive(Debug, Clone, Default)]
pub(crate) struct SourceMapper {
    /// Variable name overrides: solver variable name -> source variable name.
    var_names: FxHashMap<String, String>,
}

/// A mapping from a formula term to a source location.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SourceMapping {
    /// The variable name in the formula (solver-level name).
    pub formula_var: String,
    /// The human-readable source variable name (if known).
    pub source_name: Option<String>,
    /// Source location where this variable is defined/used.
    pub location: SourceSpan,
}

impl SourceMapper {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Add a known variable name mapping.
    pub(crate) fn add_var_name(&mut self, solver_name: &str, source_name: &str) {
        self.var_names.insert(solver_name.to_string(), source_name.to_string());
    }

    /// Extract all variable references from a formula and map them to source.
    #[must_use]
    pub(crate) fn map_formula(
        &self,
        formula: &Formula,
        default_span: &SourceSpan,
    ) -> Vec<SourceMapping> {
        let mut mappings = Vec::new();
        let mut seen = FxHashSet::default();
        self.collect_vars(formula, default_span, &mut mappings, &mut seen);
        mappings
    }

    /// Recursively collect variable references from a formula.
    fn collect_vars(
        &self,
        formula: &Formula,
        default_span: &SourceSpan,
        mappings: &mut Vec<SourceMapping>,
        seen: &mut FxHashSet<String>,
    ) {
        match formula {
            Formula::Var(name, _sort) => {
                if seen.insert(name.clone()) {
                    mappings.push(SourceMapping {
                        formula_var: name.clone(),
                        source_name: self.var_names.get(name).cloned()
                            .or_else(|| human_readable_name(name)),
                        location: default_span.clone(),
                    });
                }
            }
            other => {
                for child in other.children() {
                    self.collect_vars(child, default_span, mappings, seen);
                }
            }
        }
    }
}

/// Try to derive a human-readable name from a solver variable name.
///
/// Solver variables often look like `_1`, `_2` (MIR local indices) or
/// `add_overflow_check_3`. This extracts meaningful parts.
fn human_readable_name(solver_name: &str) -> Option<String> {
    // MIR-style _N locals don't have meaningful names
    if solver_name.starts_with('_') && solver_name[1..].parse::<u32>().is_ok() {
        return None;
    }
    // Strip common prefixes
    let cleaned = solver_name
        .replace("__", "::")
        .replace("_check_", " check ");
    Some(cleaned)
}

// ---------------------------------------------------------------------------
// ReasonChain
// ---------------------------------------------------------------------------

/// A chain of reasoning steps from hypothesis to conclusion.
///
/// Each step is a human-readable statement that explains one logical
/// step in the proof or counterexample trace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ReasonChain {
    /// Ordered reasoning steps.
    pub steps: Vec<ReasonStep>,
}

impl ReasonChain {
    #[must_use]
    pub(crate) fn new(steps: Vec<ReasonStep>) -> Self {
        Self { steps }
    }

    /// Number of steps in the chain.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.steps.len()
    }

    /// Whether the chain is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    /// Format the chain as a numbered list.
    #[must_use]
    pub(crate) fn format_numbered(&self) -> String {
        let mut out = String::new();
        for (i, step) in self.steps.iter().enumerate() {
            let _ = write!(out, "{}. {}", i + 1, step.description);
            if let Some(ref loc) = step.source {
                let _ = write!(out, " [{}:{}]", loc.file, loc.line_start);
            }
            out.push('\n');
        }
        out
    }
}

/// A single reasoning step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ReasonStep {
    /// Human-readable description of this step.
    pub description: String,
    /// Source location this step refers to (if any).
    pub source: Option<SourceSpan>,
}

// ---------------------------------------------------------------------------
// ConflictExplainer
// ---------------------------------------------------------------------------

/// For failed VCs, explains which constraints conflict and why.
///
/// When a VC is SAT (meaning the negation of the property is satisfiable,
/// i.e., a violation exists), this identifies the conflicting constraints.
#[derive(Debug, Clone, Default)]
pub(crate) struct ConflictExplainer;

/// A conflict between constraints in a VC.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Conflict {
    /// Human-readable description of the conflict.
    pub description: String,
    /// The conflicting constraint formulas (as human-readable strings).
    pub constraints: Vec<String>,
    /// Source locations of the conflicting constraints.
    pub locations: Vec<SourceSpan>,
}

impl ConflictExplainer {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self
    }

    /// Find conflicts in a failed VC given a counterexample.
    #[must_use]
    pub(crate) fn find_conflicts(
        &self,
        vc: &VerificationCondition,
        counterexample: Option<&trust_types::Counterexample>,
    ) -> Vec<Conflict> {
        let mut conflicts = Vec::new();

        match &vc.kind {
            VcKind::ArithmeticOverflow { op, operand_tys } => {
                let values = counterexample.map(|cex| {
                    cex.assignments.iter()
                        .map(|(n, v)| format!("{n}={v}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                }).unwrap_or_else(|| "unknown values".into());

                conflicts.push(Conflict {
                    description: format!(
                        "Operation {op:?} on {:?} can overflow with {values}",
                        operand_tys.0
                    ),
                    constraints: vec![
                        format!("operand values: {values}"),
                        format!("type bounds: {:?} max", operand_tys.0),
                    ],
                    locations: vec![vc.location.clone()],
                });
            }
            VcKind::DivisionByZero | VcKind::RemainderByZero => {
                conflicts.push(Conflict {
                    description: "Divisor can be zero".into(),
                    constraints: vec![
                        "divisor == 0 is reachable".into(),
                        "division requires divisor != 0".into(),
                    ],
                    locations: vec![vc.location.clone()],
                });
            }
            VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => {
                conflicts.push(Conflict {
                    description: "Index can exceed array bounds".into(),
                    constraints: vec![
                        "index >= array.len() is reachable".into(),
                        "array access requires index < array.len()".into(),
                    ],
                    locations: vec![vc.location.clone()],
                });
            }
            VcKind::Precondition { callee } => {
                let spec_conflict = self.extract_spec_conflicts(vc);
                if spec_conflict.is_empty() {
                    conflicts.push(Conflict {
                        description: format!(
                            "Call to '{callee}' does not satisfy its precondition"
                        ),
                        constraints: vec![
                            format!("callee requires: precondition of '{callee}'"),
                            "caller provides: current state at call site".into(),
                        ],
                        locations: vec![vc.location.clone()],
                    });
                } else {
                    conflicts.extend(spec_conflict);
                }
            }
            VcKind::Postcondition => {
                conflicts.push(Conflict {
                    description: "Function body does not establish postcondition".into(),
                    constraints: vec![
                        "postcondition requires: ensures clause".into(),
                        "function body provides: computed return value".into(),
                    ],
                    locations: vec![vc.location.clone()],
                });
            }
            _ => {
                conflicts.push(Conflict {
                    description: format!("Property '{}' violated", vc.kind.description()),
                    constraints: vec![formula_summary(&vc.formula)],
                    locations: vec![vc.location.clone()],
                });
            }
        }

        conflicts
    }

    /// Extract conflicts from spec annotations (requires/ensures).
    fn extract_spec_conflicts(&self, vc: &VerificationCondition) -> Vec<Conflict> {
        // Walk the formula looking for Implies(precond, body) patterns
        if let Formula::Implies(premise, conclusion) = &vc.formula {
            let premise_desc = formula_summary(premise);
            let conclusion_desc = formula_summary(conclusion);
            if !premise_desc.is_empty() && !conclusion_desc.is_empty() {
                return vec![Conflict {
                    description: "Specification conflict".into(),
                    constraints: vec![
                        format!("requires: {premise_desc}"),
                        format!("but: {conclusion_desc}"),
                    ],
                    locations: vec![vc.location.clone()],
                }];
            }
        }
        vec![]
    }
}

// ---------------------------------------------------------------------------
// FixSuggester
// ---------------------------------------------------------------------------

/// Based on conflict analysis, suggests code changes to fix violations.
#[derive(Debug, Clone, Default)]
pub(crate) struct FixSuggester;

/// A suggested code change to fix a verification failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FixSuggestion {
    /// Human-readable description of the fix.
    pub description: String,
    /// Suggested code change (if concrete enough).
    pub code_change: Option<String>,
    /// Where the fix should be applied.
    pub location: Option<SourceSpan>,
}

impl FixSuggester {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self
    }

    /// Suggest fixes for the given conflicts.
    #[must_use]
    pub(crate) fn suggest(
        &self,
        vc: &VerificationCondition,
        conflicts: &[Conflict],
    ) -> Vec<FixSuggestion> {
        let mut suggestions = Vec::new();

        match &vc.kind {
            VcKind::ArithmeticOverflow { op, .. } => {
                suggestions.push(FixSuggestion {
                    description: format!(
                        "Use checked_{} or saturating_{} instead of {op:?}",
                        op_method_name(op),
                        op_method_name(op),
                    ),
                    code_change: Some(format!(
                        "a.checked_{}(b).expect(\"overflow\")",
                        op_method_name(op)
                    )),
                    location: Some(vc.location.clone()),
                });
                suggestions.push(FixSuggestion {
                    description: "Add a precondition bounding the input values".into(),
                    code_change: Some(
                        "#[requires(a <= MAX / 2 && b <= MAX / 2)]".into()
                    ),
                    location: Some(vc.location.clone()),
                });
            }
            VcKind::DivisionByZero | VcKind::RemainderByZero => {
                suggestions.push(FixSuggestion {
                    description: "Add a guard checking the divisor is non-zero".into(),
                    code_change: Some("if divisor != 0 { a / divisor } else { /* handle */ }".into()),
                    location: Some(vc.location.clone()),
                });
                suggestions.push(FixSuggestion {
                    description: "Add a precondition requiring non-zero divisor".into(),
                    code_change: Some("#[requires(divisor != 0)]".into()),
                    location: Some(vc.location.clone()),
                });
            }
            VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => {
                suggestions.push(FixSuggestion {
                    description: "Use .get() instead of direct indexing".into(),
                    code_change: Some("arr.get(index).ok_or(Error::OutOfBounds)?".into()),
                    location: Some(vc.location.clone()),
                });
                suggestions.push(FixSuggestion {
                    description: "Add a bounds check before indexing".into(),
                    code_change: Some("assert!(index < arr.len());".into()),
                    location: Some(vc.location.clone()),
                });
            }
            VcKind::Precondition { callee } => {
                suggestions.push(FixSuggestion {
                    description: format!(
                        "Ensure '{callee}' precondition is satisfied before the call"
                    ),
                    code_change: None,
                    location: Some(vc.location.clone()),
                });
            }
            VcKind::Postcondition => {
                suggestions.push(FixSuggestion {
                    description: "Fix the function body to satisfy its ensures clause, \
                                  or weaken the postcondition"
                        .into(),
                    code_change: None,
                    location: Some(vc.location.clone()),
                });
            }
            _ => {
                // Generic suggestion for unknown VC kinds
                for conflict in conflicts {
                    suggestions.push(FixSuggestion {
                        description: format!("Address: {}", conflict.description),
                        code_change: None,
                        location: conflict.locations.first().cloned(),
                    });
                }
            }
        }

        suggestions
    }
}

/// Map a `BinOp` to its checked method name suffix.
fn op_method_name(op: &trust_types::BinOp) -> &'static str {
    match op {
        trust_types::BinOp::Add => "add",
        trust_types::BinOp::Sub => "sub",
        trust_types::BinOp::Mul => "mul",
        trust_types::BinOp::Div => "div",
        trust_types::BinOp::Rem => "rem",
        trust_types::BinOp::Shl => "shl",
        trust_types::BinOp::Shr => "shr",
        _ => "op",
    }
}

// ---------------------------------------------------------------------------
// DotExporter
// ---------------------------------------------------------------------------

/// Exports a VC formula as a DOT graph for visualization.
///
/// Each formula node becomes a graph node; edges connect parent to children.
/// Useful for understanding complex verification conditions visually.
#[derive(Debug, Clone)]
pub(crate) struct DotExporter {
    /// Whether to include sort annotations on variable nodes.
    show_sorts: bool,
    /// Maximum tree depth to render.
    max_depth: usize,
}

impl Default for DotExporter {
    fn default() -> Self {
        Self { show_sorts: true, max_depth: 30 }
    }
}

/// A node in the DOT graph.
#[derive(Debug, Clone)]
struct DotNode {
    id: usize,
    label: String,
    shape: &'static str,
    color: &'static str,
}

impl DotExporter {
    #[must_use]
    pub(crate) fn new(show_sorts: bool, max_depth: usize) -> Self {
        Self { show_sorts, max_depth }
    }

    /// Export a VC's formula as a DOT graph string.
    #[must_use]
    pub(crate) fn export_vc(&self, vc: &VerificationCondition) -> String {
        let mut nodes = Vec::new();
        let mut edges: Vec<(usize, usize)> = Vec::new();
        let mut next_id = 0;

        // Add a root node for the VC metadata
        let root_id = next_id;
        nodes.push(DotNode {
            id: root_id,
            label: format!("VC: {}", vc.kind.description()),
            shape: "box",
            color: "lightblue",
        });
        next_id += 1;

        // Recursively build the formula tree
        let formula_root = self.build_dot_tree(
            &vc.formula,
            &mut nodes,
            &mut edges,
            &mut next_id,
            0,
        );
        edges.push((root_id, formula_root));

        self.render_dot(&nodes, &edges)
    }

    /// Export a standalone formula as DOT.
    #[must_use]
    pub(crate) fn export_formula(&self, formula: &Formula) -> String {
        let mut nodes = Vec::new();
        let mut edges: Vec<(usize, usize)> = Vec::new();
        let mut next_id = 0;

        self.build_dot_tree(formula, &mut nodes, &mut edges, &mut next_id, 0);

        self.render_dot(&nodes, &edges)
    }

    /// Recursively build DOT nodes for a formula.
    fn build_dot_tree(
        &self,
        formula: &Formula,
        nodes: &mut Vec<DotNode>,
        edges: &mut Vec<(usize, usize)>,
        next_id: &mut usize,
        depth: usize,
    ) -> usize {
        let my_id = *next_id;
        *next_id += 1;

        if depth >= self.max_depth {
            nodes.push(DotNode {
                id: my_id,
                label: "...".into(),
                shape: "plaintext",
                color: "gray",
            });
            return my_id;
        }

        let (label, shape, color) = self.classify_node(formula);
        nodes.push(DotNode { id: my_id, label, shape, color });

        for child in formula.children() {
            let child_id = self.build_dot_tree(child, nodes, edges, next_id, depth + 1);
            edges.push((my_id, child_id));
        }

        my_id
    }

    /// Classify a formula node for DOT rendering.
    fn classify_node(&self, formula: &Formula) -> (String, &'static str, &'static str) {
        match formula {
            Formula::Bool(b) => (format!("{b}"), "ellipse", "lightgreen"),
            Formula::Int(n) => (format!("{n}"), "ellipse", "lightyellow"),
            Formula::UInt(n) => (format!("{n}u"), "ellipse", "lightyellow"),
            Formula::BitVec { value, width } => {
                (format!("bv{value}[{width}]"), "ellipse", "lightyellow")
            }
            Formula::Var(name, sort) => {
                let label = if self.show_sorts {
                    format!("{name}: {}", sort_name(sort))
                } else {
                    name.clone()
                };
                (label, "ellipse", "lightcyan")
            }
            Formula::Not(_) => ("NOT".into(), "diamond", "salmon"),
            Formula::And(_) => ("AND".into(), "diamond", "salmon"),
            Formula::Or(_) => ("OR".into(), "diamond", "salmon"),
            Formula::Implies(_, _) => ("=>".into(), "diamond", "salmon"),
            Formula::Eq(_, _) => ("=".into(), "box", "lightyellow"),
            Formula::Lt(_, _) => ("<".into(), "box", "lightyellow"),
            Formula::Le(_, _) => ("<=".into(), "box", "lightyellow"),
            Formula::Gt(_, _) => (">".into(), "box", "lightyellow"),
            Formula::Ge(_, _) => (">=".into(), "box", "lightyellow"),
            Formula::Add(_, _) => ("+".into(), "circle", "white"),
            Formula::Sub(_, _) => ("-".into(), "circle", "white"),
            Formula::Mul(_, _) => ("*".into(), "circle", "white"),
            Formula::Div(_, _) => ("/".into(), "circle", "white"),
            Formula::Rem(_, _) => ("%".into(), "circle", "white"),
            Formula::Neg(_) => ("neg".into(), "circle", "white"),
            Formula::BvAdd(_, _, w) => (format!("+[{w}]"), "circle", "wheat"),
            Formula::BvSub(_, _, w) => (format!("-[{w}]"), "circle", "wheat"),
            Formula::BvMul(_, _, w) => (format!("*[{w}]"), "circle", "wheat"),
            Formula::BvUDiv(_, _, w) => (format!("udiv[{w}]"), "circle", "wheat"),
            Formula::BvSDiv(_, _, w) => (format!("sdiv[{w}]"), "circle", "wheat"),
            Formula::BvURem(_, _, w) => (format!("urem[{w}]"), "circle", "wheat"),
            Formula::BvSRem(_, _, w) => (format!("srem[{w}]"), "circle", "wheat"),
            Formula::BvAnd(_, _, w) => (format!("&[{w}]"), "circle", "wheat"),
            Formula::BvOr(_, _, w) => (format!("|[{w}]"), "circle", "wheat"),
            Formula::BvXor(_, _, w) => (format!("^[{w}]"), "circle", "wheat"),
            Formula::BvNot(_, w) => (format!("~[{w}]"), "circle", "wheat"),
            Formula::BvShl(_, _, w) => (format!("<<[{w}]"), "circle", "wheat"),
            Formula::BvLShr(_, _, w) => (format!(">>[{w}]"), "circle", "wheat"),
            Formula::BvAShr(_, _, w) => (format!(">>a[{w}]"), "circle", "wheat"),
            Formula::BvULt(_, _, _) => ("ult".into(), "box", "wheat"),
            Formula::BvULe(_, _, _) => ("ule".into(), "box", "wheat"),
            Formula::BvSLt(_, _, _) => ("slt".into(), "box", "wheat"),
            Formula::BvSLe(_, _, _) => ("sle".into(), "box", "wheat"),
            Formula::BvToInt(_, _, _) => ("bv2int".into(), "box", "thistle"),
            Formula::IntToBv(_, _) => ("int2bv".into(), "box", "thistle"),
            Formula::BvExtract { high, low, .. } => {
                (format!("[{high}:{low}]"), "box", "thistle")
            }
            Formula::BvConcat(_, _) => ("concat".into(), "box", "thistle"),
            Formula::BvZeroExt(_, n) => (format!("zext({n})"), "box", "thistle"),
            Formula::BvSignExt(_, n) => (format!("sext({n})"), "box", "thistle"),
            Formula::Ite(_, _, _) => ("ITE".into(), "diamond", "gold"),
            Formula::Forall(vars, _) => {
                let names: Vec<_> = vars.iter().map(|(n, _)| n.as_str()).collect();
                (format!("forall {}", names.join(",")), "hexagon", "plum")
            }
            Formula::Exists(vars, _) => {
                let names: Vec<_> = vars.iter().map(|(n, _)| n.as_str()).collect();
                (format!("exists {}", names.join(",")), "hexagon", "plum")
            }
            Formula::Select(_, _) => ("select".into(), "box", "lightgray"),
            Formula::Store(_, _, _) => ("store".into(), "box", "lightgray"),
            _ => ("unknown".into(), "ellipse", "white"),
        }
    }

    /// Render the final DOT string from nodes and edges.
    fn render_dot(&self, nodes: &[DotNode], edges: &[(usize, usize)]) -> String {
        let mut out = String::from("digraph vc {\n");
        out.push_str("  rankdir=TB;\n");
        out.push_str("  node [fontname=\"Helvetica\", fontsize=10];\n\n");

        for node in nodes {
            let _ = writeln!(
                out,
                "  n{} [label=\"{}\", shape={}, style=filled, fillcolor=\"{}\"];",
                node.id,
                node.label.replace('"', "\\\""),
                node.shape,
                node.color
            );
        }

        out.push('\n');

        for (from, to) in edges {
            let _ = writeln!(out, "  n{from} -> n{to};");
        }

        out.push_str("}\n");
        out
    }
}

/// Get a short name for a Sort.
fn sort_name(sort: &Sort) -> String {
    match sort {
        Sort::Bool => "Bool".into(),
        Sort::Int => "Int".into(),
        Sort::BitVec(w) => format!("BV{w}"),
        Sort::Array(k, v) => format!("Array<{},{}>", sort_name(k), sort_name(v)),
        _ => "unknown".to_string(),
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Produce a short human-readable summary of a formula.
fn formula_summary(formula: &Formula) -> String {
    match formula {
        Formula::Bool(true) => "true".into(),
        Formula::Bool(false) => "false".into(),
        Formula::Int(n) => format!("{n}"),
        Formula::UInt(n) => format!("{n}"),
        Formula::BitVec { value, width } => format!("bv{value}[{width}]"),
        Formula::Var(name, _) => name.clone(),
        Formula::Not(inner) => format!("not({})", formula_summary(inner)),
        Formula::And(terms) => {
            if terms.len() <= 3 {
                let parts: Vec<_> = terms.iter().map(formula_summary).collect();
                parts.join(" && ")
            } else {
                format!("({} conjuncts)", terms.len())
            }
        }
        Formula::Or(terms) => {
            if terms.len() <= 3 {
                let parts: Vec<_> = terms.iter().map(formula_summary).collect();
                parts.join(" || ")
            } else {
                format!("({} disjuncts)", terms.len())
            }
        }
        Formula::Implies(a, b) => {
            format!("{} => {}", formula_summary(a), formula_summary(b))
        }
        Formula::Eq(a, b) => format!("{} == {}", formula_summary(a), formula_summary(b)),
        Formula::Lt(a, b) => format!("{} < {}", formula_summary(a), formula_summary(b)),
        Formula::Le(a, b) => format!("{} <= {}", formula_summary(a), formula_summary(b)),
        Formula::Gt(a, b) => format!("{} > {}", formula_summary(a), formula_summary(b)),
        Formula::Ge(a, b) => format!("{} >= {}", formula_summary(a), formula_summary(b)),
        Formula::Add(a, b) => format!("{} + {}", formula_summary(a), formula_summary(b)),
        Formula::Sub(a, b) => format!("{} - {}", formula_summary(a), formula_summary(b)),
        Formula::Mul(a, b) => format!("{} * {}", formula_summary(a), formula_summary(b)),
        Formula::Div(a, b) => format!("{} / {}", formula_summary(a), formula_summary(b)),
        Formula::Rem(a, b) => format!("{} % {}", formula_summary(a), formula_summary(b)),
        Formula::Neg(a) => format!("-{}", formula_summary(a)),
        Formula::Forall(vars, _) => {
            let names: Vec<_> = vars.iter().map(|(n, _)| n.as_str()).collect();
            format!("forall {}", names.join(", "))
        }
        Formula::Exists(vars, _) => {
            let names: Vec<_> = vars.iter().map(|(n, _)| n.as_str()).collect();
            format!("exists {}", names.join(", "))
        }
        Formula::Ite(c, t, e) => {
            format!(
                "if {} then {} else {}",
                formula_summary(c),
                formula_summary(t),
                formula_summary(e)
            )
        }
        Formula::Select(arr, idx) => {
            format!("{}[{}]", formula_summary(arr), formula_summary(idx))
        }
        Formula::Store(arr, idx, val) => {
            format!(
                "store({}, {}, {})",
                formula_summary(arr),
                formula_summary(idx),
                formula_summary(val)
            )
        }
        // Bitvector ops: abbreviated
        Formula::BvAdd(a, b, w) => format!("bvadd{w}({}, {})", formula_summary(a), formula_summary(b)),
        Formula::BvSub(a, b, w) => format!("bvsub{w}({}, {})", formula_summary(a), formula_summary(b)),
        Formula::BvMul(a, b, w) => format!("bvmul{w}({}, {})", formula_summary(a), formula_summary(b)),
        _ => format!("{:?}", std::mem::discriminant(formula)),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{
        BinOp, Counterexample, CounterexampleValue, ProofStrength, SourceSpan, Ty,
    };

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
            formula: Formula::And(vec![
                Formula::Var("a".into(), Sort::BitVec(64)),
                Formula::Var("b".into(), Sort::BitVec(64)),
                Formula::Gt(
                    Box::new(Formula::Add(
                        Box::new(Formula::Var("a".into(), Sort::BitVec(64))),
                        Box::new(Formula::Var("b".into(), Sort::BitVec(64))),
                    )),
                    Box::new(Formula::UInt(u64::MAX as u128)),
                ),
            ]),
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

    fn index_oob_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::IndexOutOfBounds,
            function: "test::access".into(),
            location: test_span(),
            formula: Formula::Ge(
                Box::new(Formula::Var("index".into(), Sort::Int)),
                Box::new(Formula::Var("len".into(), Sort::Int)),
            ),
            contract_metadata: None,
        }
    }

    fn precondition_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Precondition { callee: "safe_sqrt".into() },
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

    // -----------------------------------------------------------------------
    // ProofExplainer tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_explainer_overflow_proved() {
        let explainer = ProofExplainer::default();
        let vc = overflow_vc();
        let result = VerificationResult::Proved {
            solver: "z4".into(),
            time_ms: 50,
            strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, };

        let explanation = explainer.explain(&vc, &result);
        assert!(explanation.summary.contains("PROVED"));
        assert!(explanation.summary.contains("z4"));
        assert!(!explanation.reasoning.is_empty());
        assert!(explanation.conflicts.is_empty());
    }

    #[test]
    fn test_proof_explainer_overflow_failed() {
        let explainer = ProofExplainer::default();
        let vc = overflow_vc();
        let cex = Counterexample::new(vec![
            ("a".into(), CounterexampleValue::Uint(u64::MAX as u128)),
            ("b".into(), CounterexampleValue::Uint(1)),
        ]);
        let result = VerificationResult::Failed {
            solver: "z4".into(),
            time_ms: 30,
            counterexample: Some(cex),
        };

        let explanation = explainer.explain(&vc, &result);
        assert!(explanation.summary.contains("FAILED"));
        assert!(explanation.summary.contains("counterexample"));
        assert!(!explanation.reasoning.is_empty());
        assert!(!explanation.conflicts.is_empty());
        assert!(!explanation.suggestions.is_empty());

        // Should suggest checked_add
        let has_checked = explanation.suggestions.iter().any(|s| {
            s.description.contains("checked_add")
        });
        assert!(has_checked, "should suggest checked_add");
    }

    #[test]
    fn test_proof_explainer_div_zero() {
        let explainer = ProofExplainer::default();
        let vc = div_zero_vc();
        let cex = Counterexample::new(vec![
            ("divisor".into(), CounterexampleValue::Int(0)),
        ]);
        let result = VerificationResult::Failed {
            solver: "z4".into(),
            time_ms: 10,
            counterexample: Some(cex),
        };

        let explanation = explainer.explain(&vc, &result);
        assert!(explanation.summary.contains("FAILED"));

        // Should suggest guard check
        let has_guard = explanation.suggestions.iter().any(|s| {
            s.description.contains("guard") || s.description.contains("non-zero")
        });
        assert!(has_guard, "should suggest divisor guard");

        // Conflicts should mention zero divisor
        let has_zero = explanation.conflicts.iter().any(|c| {
            c.description.contains("zero")
        });
        assert!(has_zero, "conflict should mention zero");
    }

    #[test]
    fn test_proof_explainer_index_oob() {
        let explainer = ProofExplainer::default();
        let vc = index_oob_vc();
        let cex = Counterexample::new(vec![
            ("index".into(), CounterexampleValue::Uint(10)),
            ("len".into(), CounterexampleValue::Uint(5)),
        ]);
        let result = VerificationResult::Failed {
            solver: "z4".into(),
            time_ms: 15,
            counterexample: Some(cex),
        };

        let explanation = explainer.explain(&vc, &result);
        assert!(explanation.summary.contains("FAILED"));

        // Should suggest .get()
        let has_get = explanation.suggestions.iter().any(|s| {
            s.description.contains(".get()")
        });
        assert!(has_get, "should suggest .get()");
    }

    #[test]
    fn test_proof_explainer_timeout() {
        let explainer = ProofExplainer::default();
        let vc = overflow_vc();
        let result = VerificationResult::Timeout {
            solver: "z4".into(),
            timeout_ms: 5000,
        };

        let explanation = explainer.explain(&vc, &result);
        assert!(explanation.summary.contains("TIMEOUT"));
        assert!(explanation.summary.contains("5000ms"));
        assert!(!explanation.suggestions.is_empty());
    }

    #[test]
    fn test_proof_explainer_unknown() {
        let explainer = ProofExplainer::default();
        let vc = overflow_vc();
        let result = VerificationResult::Unknown {
            solver: "z4".into(),
            time_ms: 1000,
            reason: "quantifier instantiation limit".into(),
        };

        let explanation = explainer.explain(&vc, &result);
        assert!(explanation.summary.contains("UNKNOWN"));
        assert!(explanation.summary.contains("quantifier"));
    }

    // -----------------------------------------------------------------------
    // SourceMapper tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_source_mapper_collects_vars() {
        let mapper = SourceMapper::new();
        let formula = Formula::Add(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Var("y".into(), Sort::Int)),
        );
        let span = test_span();

        let mappings = mapper.map_formula(&formula, &span);
        assert_eq!(mappings.len(), 2);
        assert_eq!(mappings[0].formula_var, "x");
        assert_eq!(mappings[1].formula_var, "y");
    }

    #[test]
    fn test_source_mapper_deduplicates() {
        let mapper = SourceMapper::new();
        let formula = Formula::And(vec![
            Formula::Var("x".into(), Sort::Int),
            Formula::Var("x".into(), Sort::Int),
            Formula::Var("y".into(), Sort::Int),
        ]);
        let span = test_span();

        let mappings = mapper.map_formula(&formula, &span);
        assert_eq!(mappings.len(), 2, "should deduplicate x");
    }

    #[test]
    fn test_source_mapper_with_name_overrides() {
        let mut mapper = SourceMapper::new();
        mapper.add_var_name("_1", "counter");
        mapper.add_var_name("_2", "limit");

        let formula = Formula::Lt(
            Box::new(Formula::Var("_1".into(), Sort::Int)),
            Box::new(Formula::Var("_2".into(), Sort::Int)),
        );
        let span = test_span();

        let mappings = mapper.map_formula(&formula, &span);
        assert_eq!(mappings.len(), 2);
        assert_eq!(mappings[0].source_name, Some("counter".into()));
        assert_eq!(mappings[1].source_name, Some("limit".into()));
    }

    #[test]
    fn test_source_mapper_mir_locals_no_name() {
        let mapper = SourceMapper::new();
        let formula = Formula::Var("_3".into(), Sort::Int);
        let span = test_span();

        let mappings = mapper.map_formula(&formula, &span);
        assert_eq!(mappings.len(), 1);
        // MIR local _3 has no human-readable name
        assert_eq!(mappings[0].source_name, None);
    }

    // -----------------------------------------------------------------------
    // ReasonChain tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_reason_chain_format() {
        let chain = ReasonChain::new(vec![
            ReasonStep {
                description: "Goal: verify no overflow".into(),
                source: Some(test_span()),
            },
            ReasonStep {
                description: "a + b overflows when a = MAX, b = 1".into(),
                source: None,
            },
        ]);

        assert_eq!(chain.len(), 2);
        assert!(!chain.is_empty());

        let formatted = chain.format_numbered();
        assert!(formatted.contains("1. Goal: verify no overflow"));
        assert!(formatted.contains("[src/lib.rs:42]"));
        assert!(formatted.contains("2. a + b overflows"));
    }

    // -----------------------------------------------------------------------
    // ConflictExplainer tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_conflict_explainer_overflow() {
        let explainer = ConflictExplainer::new();
        let vc = overflow_vc();
        let cex = Counterexample::new(vec![
            ("a".into(), CounterexampleValue::Uint(u64::MAX as u128)),
            ("b".into(), CounterexampleValue::Uint(1)),
        ]);

        let conflicts = explainer.find_conflicts(&vc, Some(&cex));
        assert!(!conflicts.is_empty());
        assert!(conflicts[0].description.contains("overflow"));
    }

    #[test]
    fn test_conflict_explainer_div_zero() {
        let explainer = ConflictExplainer::new();
        let vc = div_zero_vc();

        let conflicts = explainer.find_conflicts(&vc, None);
        assert!(!conflicts.is_empty());
        assert!(conflicts[0].description.contains("zero"));
        assert!(conflicts[0].constraints.len() >= 2);
    }

    #[test]
    fn test_conflict_explainer_precondition() {
        let explainer = ConflictExplainer::new();
        let vc = precondition_vc();

        let conflicts = explainer.find_conflicts(&vc, None);
        assert!(!conflicts.is_empty());
        // Should detect the Implies pattern in the formula
        assert!(conflicts[0].constraints.len() >= 2);
    }

    #[test]
    fn test_conflict_explainer_postcondition() {
        let vc = VerificationCondition {
            kind: VcKind::Postcondition,
            function: "test::compute".into(),
            location: test_span(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };
        let explainer = ConflictExplainer::new();
        let conflicts = explainer.find_conflicts(&vc, None);
        assert!(!conflicts.is_empty());
        assert!(conflicts[0].description.contains("postcondition"));
    }

    // -----------------------------------------------------------------------
    // FixSuggester tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_fix_suggester_overflow() {
        let suggester = FixSuggester::new();
        let vc = overflow_vc();
        let conflicts = vec![Conflict {
            description: "overflow".into(),
            constraints: vec![],
            locations: vec![test_span()],
        }];

        let suggestions = suggester.suggest(&vc, &conflicts);
        assert!(suggestions.len() >= 2);

        let has_checked = suggestions.iter().any(|s| {
            s.code_change.as_ref().is_some_and(|c| c.contains("checked_add"))
        });
        assert!(has_checked);

        let has_requires = suggestions.iter().any(|s| {
            s.code_change.as_ref().is_some_and(|c| c.contains("#[requires"))
        });
        assert!(has_requires);
    }

    #[test]
    fn test_fix_suggester_div_zero() {
        let suggester = FixSuggester::new();
        let vc = div_zero_vc();

        let suggestions = suggester.suggest(&vc, &[]);
        assert!(suggestions.len() >= 2);

        let has_guard = suggestions.iter().any(|s| {
            s.code_change.as_ref().is_some_and(|c| c.contains("!= 0"))
        });
        assert!(has_guard);
    }

    #[test]
    fn test_fix_suggester_index_oob() {
        let suggester = FixSuggester::new();
        let vc = index_oob_vc();

        let suggestions = suggester.suggest(&vc, &[]);
        let has_get = suggestions.iter().any(|s| {
            s.code_change.as_ref().is_some_and(|c| c.contains(".get("))
        });
        assert!(has_get);
    }

    #[test]
    fn test_fix_suggester_postcondition() {
        let suggester = FixSuggester::new();
        let vc = VerificationCondition {
            kind: VcKind::Postcondition,
            function: "test::compute".into(),
            location: test_span(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };

        let suggestions = suggester.suggest(&vc, &[]);
        assert!(!suggestions.is_empty());
        assert!(suggestions[0].description.contains("postcondition"));
    }

    // -----------------------------------------------------------------------
    // DotExporter tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_dot_exporter_simple_formula() {
        let exporter = DotExporter::default();
        let formula = Formula::Add(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(1)),
        );

        let dot = exporter.export_formula(&formula);
        assert!(dot.starts_with("digraph vc {"));
        assert!(dot.contains("n0"));
        assert!(dot.contains("n1"));
        assert!(dot.contains("n2"));
        assert!(dot.contains("->"));
        assert!(dot.ends_with("}\n"));
    }

    #[test]
    fn test_dot_exporter_vc() {
        let exporter = DotExporter::default();
        let vc = overflow_vc();

        let dot = exporter.export_vc(&vc);
        assert!(dot.contains("VC: arithmetic overflow"));
        assert!(dot.contains("AND"));
        assert!(dot.contains("digraph"));
    }

    #[test]
    fn test_dot_exporter_respects_max_depth() {
        let exporter = DotExporter::new(true, 1);

        // Build a deep formula: a + (b + (c + d))
        let deep = Formula::Add(
            Box::new(Formula::Var("a".into(), Sort::Int)),
            Box::new(Formula::Add(
                Box::new(Formula::Var("b".into(), Sort::Int)),
                Box::new(Formula::Add(
                    Box::new(Formula::Var("c".into(), Sort::Int)),
                    Box::new(Formula::Var("d".into(), Sort::Int)),
                )),
            )),
        );

        let dot = exporter.export_formula(&deep);
        // At max_depth=1, deeper nodes should be truncated to "..."
        assert!(dot.contains("..."));
    }

    #[test]
    fn test_dot_exporter_boolean_connectives() {
        let exporter = DotExporter::default();
        let formula = Formula::Or(vec![
            Formula::Not(Box::new(Formula::Var("p".into(), Sort::Bool))),
            Formula::Var("q".into(), Sort::Bool),
        ]);

        let dot = exporter.export_formula(&formula);
        assert!(dot.contains("OR"));
        assert!(dot.contains("NOT"));
    }

    #[test]
    fn test_dot_exporter_quantifiers() {
        let exporter = DotExporter::default();
        let formula = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Ge(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );

        let dot = exporter.export_formula(&formula);
        assert!(dot.contains("forall"));
    }

    #[test]
    fn test_dot_exporter_bitvector_ops() {
        let exporter = DotExporter::default();
        let formula = Formula::BvAdd(
            Box::new(Formula::Var("a".into(), Sort::BitVec(32))),
            Box::new(Formula::Var("b".into(), Sort::BitVec(32))),
            32,
        );

        let dot = exporter.export_formula(&formula);
        assert!(dot.contains("+[32]"));
    }

    // -----------------------------------------------------------------------
    // Integration: full explanation pipeline
    // -----------------------------------------------------------------------

    #[test]
    fn test_full_explanation_overflow() {
        let explainer = ProofExplainer::default();
        let vc = overflow_vc();
        let cex = Counterexample::new(vec![
            ("a".into(), CounterexampleValue::Uint(u64::MAX as u128)),
            ("b".into(), CounterexampleValue::Uint(1)),
        ]);
        let result = VerificationResult::Failed {
            solver: "z4".into(),
            time_ms: 42,
            counterexample: Some(cex),
        };

        let explanation = explainer.explain(&vc, &result);

        // Full pipeline: summary + reasoning + source mappings + conflicts + suggestions
        assert!(explanation.summary.contains("FAILED"));
        assert!(!explanation.reasoning.is_empty());
        assert!(!explanation.source_mappings.is_empty());
        assert!(!explanation.conflicts.is_empty());
        assert!(!explanation.suggestions.is_empty());

        // Reason chain should mention counterexample values
        let chain_text = explanation.reasoning.format_numbered();
        assert!(chain_text.contains("a ="));
        assert!(chain_text.contains("b ="));

        // DOT export of the VC should work too
        let exporter = DotExporter::default();
        let dot = exporter.export_vc(&vc);
        assert!(dot.contains("digraph"));
    }

    #[test]
    fn test_full_explanation_null_deref() {
        let vc = VerificationCondition {
            kind: VcKind::Assertion { message: "null pointer dereference".into() },
            function: "test::deref_ptr".into(),
            location: test_span(),
            formula: Formula::Eq(
                Box::new(Formula::Var("ptr".into(), Sort::BitVec(64))),
                Box::new(Formula::BitVec { value: 0, width: 64 }),
            ),
            contract_metadata: None,
        };

        let explainer = ProofExplainer::default();
        let cex = Counterexample::new(vec![
            ("ptr".into(), CounterexampleValue::Uint(0)),
        ]);
        let result = VerificationResult::Failed {
            solver: "z4".into(),
            time_ms: 5,
            counterexample: Some(cex),
        };

        let explanation = explainer.explain(&vc, &result);
        assert!(explanation.summary.contains("FAILED"));
        assert!(!explanation.reasoning.is_empty());

        // Source mapper should find `ptr`
        let has_ptr = explanation.source_mappings.iter().any(|m| m.formula_var == "ptr");
        assert!(has_ptr);
    }

    #[test]
    fn test_full_explanation_conflicting_specs() {
        // Postcondition says result > 0, but precondition allows x = 0
        let vc = VerificationCondition {
            kind: VcKind::Postcondition,
            function: "test::must_be_positive".into(),
            location: test_span(),
            formula: Formula::Implies(
                Box::new(Formula::Ge(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                )),
                Box::new(Formula::Gt(
                    Box::new(Formula::Var("result".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                )),
            ),
            contract_metadata: None,
        };

        let explainer = ProofExplainer::default();
        let cex = Counterexample::new(vec![
            ("x".into(), CounterexampleValue::Int(0)),
            ("result".into(), CounterexampleValue::Int(0)),
        ]);
        let result = VerificationResult::Failed {
            solver: "z4".into(),
            time_ms: 10,
            counterexample: Some(cex),
        };

        let explanation = explainer.explain(&vc, &result);
        assert!(explanation.summary.contains("FAILED"));

        // Conflicts should mention postcondition
        let has_postc = explanation.conflicts.iter().any(|c| {
            c.description.contains("postcondition")
        });
        assert!(has_postc);

        // Suggestions should mention weaken or fix
        assert!(!explanation.suggestions.is_empty());
    }

    // -----------------------------------------------------------------------
    // formula_summary helper tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_formula_summary_literals() {
        assert_eq!(formula_summary(&Formula::Bool(true)), "true");
        assert_eq!(formula_summary(&Formula::Bool(false)), "false");
        assert_eq!(formula_summary(&Formula::Int(42)), "42");
        assert_eq!(formula_summary(&Formula::UInt(100)), "100");
    }

    #[test]
    fn test_formula_summary_comparison() {
        let f = Formula::Lt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(10)),
        );
        assert_eq!(formula_summary(&f), "x < 10");
    }

    #[test]
    fn test_formula_summary_arithmetic() {
        let f = Formula::Add(
            Box::new(Formula::Var("a".into(), Sort::Int)),
            Box::new(Formula::Var("b".into(), Sort::Int)),
        );
        assert_eq!(formula_summary(&f), "a + b");
    }

    #[test]
    fn test_formula_summary_large_conjunction() {
        let terms: Vec<_> = (0..10)
            .map(|i| Formula::Var(format!("x{i}"), Sort::Int))
            .collect();
        let f = Formula::And(terms);
        assert_eq!(formula_summary(&f), "(10 conjuncts)");
    }

    #[test]
    fn test_human_readable_name_mir_local() {
        assert_eq!(human_readable_name("_3"), None);
        assert_eq!(human_readable_name("_0"), None);
    }

    #[test]
    fn test_human_readable_name_named_var() {
        assert_eq!(
            human_readable_name("counter"),
            Some("counter".into())
        );
        assert_eq!(
            human_readable_name("add__overflow"),
            Some("add::overflow".into())
        );
    }

    #[test]
    fn test_sort_name() {
        assert_eq!(sort_name(&Sort::Bool), "Bool");
        assert_eq!(sort_name(&Sort::Int), "Int");
        assert_eq!(sort_name(&Sort::BitVec(32)), "BV32");
        assert_eq!(
            sort_name(&Sort::Array(Box::new(Sort::Int), Box::new(Sort::BitVec(8)))),
            "Array<Int,BV8>"
        );
    }
}
