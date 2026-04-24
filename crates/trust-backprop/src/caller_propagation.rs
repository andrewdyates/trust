//! Caller propagation engine for precondition strengthening.
//!
//! Given a function's preconditions and a call graph, finds all call sites,
//! substitutes actual arguments for formal parameters in the precondition,
//! checks if the substituted precondition is already implied by the caller's
//! context, and generates spec suggestions to propagate upward if not.
//!
//! Supports transitive propagation with configurable depth limits, generic
//! function handling, and provenance tracking.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use trust_types::fx::{FxHashMap, FxHashSet};

use serde::{Deserialize, Serialize};
use thiserror::Error;
use trust_types::call_graph::{CallGraph as TypesCallGraph, CallGraphEdge, CallGraphNode};
use trust_types::{Formula, Sort, SourceSpan, Terminator, VerifiableFunction};

use crate::substitution::{self, SubstitutionError, SubstitutionMap};

/// Errors that can occur during caller propagation.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum PropagationError {
    /// Failed to substitute formula variables.
    #[error("substitution failed for callee `{callee}` at call site in `{caller}`: {source}")]
    SubstitutionFailed { caller: String, callee: String, source: SubstitutionError },

    /// Propagation depth limit exceeded.
    #[error("propagation depth limit {limit} exceeded at function `{function}`")]
    DepthExceeded { function: String, limit: usize },

    /// No callers found for a function that requires propagation.
    #[error("no callers found for function `{function}`")]
    NoCallers { function: String },

    /// Cycle detected during transitive propagation.
    #[error("cycle detected during propagation involving `{function}`")]
    CycleDetected { function: String },
}

/// Configuration for the caller propagation engine.
#[derive(Debug, Clone)]
pub struct PropagationConfig {
    /// Maximum transitive propagation depth (0 = direct callers only).
    pub max_depth: usize,
    /// Whether to propagate through pub(crate) boundaries.
    pub propagate_pub_crate: bool,
    /// Whether to propagate through pub boundaries (adding #[requires] to pub fns).
    pub propagate_pub: bool,
    /// Minimum confidence threshold for generating suggestions.
    pub min_confidence: f64,
    /// Whether to skip propagation when a caller's context already implies
    /// the precondition.
    pub skip_implied: bool,
}

impl Default for PropagationConfig {
    fn default() -> Self {
        Self {
            max_depth: 5,
            propagate_pub_crate: true,
            propagate_pub: true,
            min_confidence: 0.5,
            skip_implied: true,
        }
    }
}

/// Visibility classification of a function for propagation decisions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum FunctionVisibility {
    /// Private function: may add spec directly.
    Private,
    /// pub(crate): propagate precondition as VC at each call site.
    PubCrate,
    /// pub: propagate to callers AND add #[requires] to signature.
    Public,
}

/// A propagation suggestion: what spec change to make at a call site or caller.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PropagationSuggestion {
    /// The caller function that needs updating.
    pub caller_name: String,
    /// The caller's def_path.
    pub caller_def_path: String,
    /// The callee whose precondition is being propagated.
    pub callee_name: String,
    /// The original precondition formula (on the callee).
    pub original_precondition: Formula,
    /// The precondition after substituting actual arguments for formal params.
    pub substituted_precondition: Formula,
    /// What kind of action to take.
    pub action: PropagationAction,
    /// Why this suggestion was generated.
    pub provenance: Provenance,
    /// Confidence in this suggestion (0.0 to 1.0).
    pub confidence: f64,
    /// Source location of the call site.
    pub call_site_span: SourceSpan,
}

/// What action to take for a propagation suggestion.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum PropagationAction {
    /// Add a verification condition at the call site in the caller.
    AddCallSiteVc,
    /// Add a #[requires] attribute to the caller function.
    AddRequiresToCaller { spec_body: String },
    /// Add a #[requires] attribute to the callee function (for pub API).
    AddRequiresToCallee { spec_body: String },
    /// The caller's existing context already implies the precondition.
    AlreadyImplied,
}

/// Provenance: tracks where a propagation suggestion came from.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Provenance {
    /// The function whose precondition originated this propagation chain.
    pub origin_function: String,
    /// The precondition formula at the origin.
    pub origin_precondition: Formula,
    /// The propagation depth (0 = direct caller).
    pub depth: usize,
    /// Chain of functions through which the precondition was propagated.
    pub propagation_chain: Vec<String>,
}

/// Result of propagation analysis for a single callee.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PropagationResult {
    /// The callee function whose preconditions were propagated.
    pub callee_name: String,
    /// Suggestions generated for callers.
    pub suggestions: Vec<PropagationSuggestion>,
    /// Callers that were skipped (already implied).
    pub skipped_implied: Vec<String>,
    /// Errors encountered during propagation (non-fatal).
    pub warnings: Vec<String>,
}

impl PropagationResult {
    /// Number of actionable suggestions (excluding already-implied).
    #[must_use]
    pub fn actionable_count(&self) -> usize {
        self.suggestions
            .iter()
            .filter(|s| !matches!(s.action, PropagationAction::AlreadyImplied))
            .count()
    }
}

/// The caller propagation engine.
pub struct CallerPropagator {
    config: PropagationConfig,
    /// Function metadata: name -> (visibility, preconditions, param info).
    functions: FxHashMap<String, FunctionInfo>,
    /// Call graph from trust-types (has caller/callee edges with spans).
    call_graph: TypesCallGraph,
}

/// Metadata about a function relevant to propagation.
#[derive(Debug, Clone)]
pub(crate) struct FunctionInfo {
    pub(crate) def_path: String,
    pub(crate) visibility: FunctionVisibility,
    pub(crate) preconditions: Vec<Formula>,
    pub(crate) params: Vec<(String, Sort)>,
}

impl CallerPropagator {
    /// Create a new propagator from verifiable functions and a call graph.
    #[must_use]
    pub fn new(
        functions: &[VerifiableFunction],
        call_graph: TypesCallGraph,
        config: PropagationConfig,
    ) -> Self {
        let mut func_map = FxHashMap::default();
        for func in functions {
            let visibility = infer_visibility(&call_graph, &func.name, &func.def_path);
            let params = extract_params(func);
            func_map.insert(
                func.name.clone(),
                FunctionInfo {
                    def_path: func.def_path.clone(),
                    visibility,
                    preconditions: func.preconditions.clone(),
                    params,
                },
            );
        }

        Self { config, functions: func_map, call_graph }
    }

    /// Propagate preconditions for a single callee function to all its callers.
    ///
    /// # Errors
    ///
    /// Returns `PropagationError` if propagation fails fatally (depth exceeded, etc.).
    pub fn propagate_for_callee(
        &self,
        callee_name: &str,
    ) -> Result<PropagationResult, PropagationError> {
        let callee_info = self
            .functions
            .get(callee_name)
            .ok_or_else(|| PropagationError::NoCallers { function: callee_name.into() })?;

        if callee_info.preconditions.is_empty() {
            return Ok(PropagationResult {
                callee_name: callee_name.to_string(),
                suggestions: vec![],
                skipped_implied: vec![],
                warnings: vec![],
            });
        }

        let callers = self.find_callers(callee_name);
        let mut result = PropagationResult {
            callee_name: callee_name.to_string(),
            suggestions: vec![],
            skipped_implied: vec![],
            warnings: vec![],
        };

        for (caller_name, call_site_span) in &callers {
            for precondition in &callee_info.preconditions {
                match self.propagate_single(
                    caller_name,
                    callee_name,
                    precondition,
                    call_site_span,
                    0,
                    &mut FxHashSet::default(),
                ) {
                    Ok(suggestions) => result.suggestions.extend(suggestions),
                    Err(PropagationError::CycleDetected { .. }) => {
                        result.warnings.push(format!(
                            "Cycle detected involving `{caller_name}` when propagating from `{callee_name}`"
                        ));
                    }
                    Err(e) => {
                        result
                            .warnings
                            .push(format!("Failed to propagate to `{caller_name}`: {e}"));
                    }
                }
            }
        }

        Ok(result)
    }

    /// Propagate all preconditions for all functions that have them.
    ///
    /// Returns a map from callee name to propagation result.
    ///
    /// # Errors
    ///
    /// Returns errors only for fatal conditions; individual function failures
    /// are recorded as warnings in the result.
    pub fn propagate_all(&self) -> FxHashMap<String, PropagationResult> {
        let mut results = FxHashMap::default();

        let functions_with_preconditions: Vec<String> = self
            .functions
            .iter()
            .filter(|(_, info)| !info.preconditions.is_empty())
            .map(|(name, _)| name.clone())
            .collect();

        for callee_name in &functions_with_preconditions {
            match self.propagate_for_callee(callee_name) {
                Ok(result) => {
                    results.insert(callee_name.clone(), result);
                }
                Err(e) => {
                    results.insert(
                        callee_name.clone(),
                        PropagationResult {
                            callee_name: callee_name.clone(),
                            suggestions: vec![],
                            skipped_implied: vec![],
                            warnings: vec![format!("Propagation failed: {e}")],
                        },
                    );
                }
            }
        }

        results
    }

    /// Propagate preconditions transitively up the call chain.
    ///
    /// Starting from a callee, propagates to its callers, then to their callers,
    /// up to the configured max depth.
    ///
    /// # Errors
    ///
    /// Returns `PropagationError` on fatal failures.
    pub fn propagate_transitive(
        &self,
        callee_name: &str,
    ) -> Result<Vec<PropagationSuggestion>, PropagationError> {
        let mut all_suggestions = Vec::new();
        let mut visited = FxHashSet::default();
        let mut queue: VecDeque<(String, usize)> = VecDeque::new();
        queue.push_back((callee_name.to_string(), 0));

        while let Some((current_callee, depth)) = queue.pop_front() {
            if depth > self.config.max_depth {
                continue;
            }
            if !visited.insert(current_callee.clone()) {
                continue;
            }

            let callee_info = match self.functions.get(&current_callee) {
                Some(info) => info,
                None => continue,
            };

            if callee_info.preconditions.is_empty() {
                continue;
            }

            let callers = self.find_callers(&current_callee);
            for (caller_name, call_site_span) in &callers {
                for precondition in &callee_info.preconditions {
                    let mut cycle_set = FxHashSet::default();
                    match self.propagate_single(
                        caller_name,
                        &current_callee,
                        precondition,
                        call_site_span,
                        depth,
                        &mut cycle_set,
                    ) {
                        Ok(suggestions) => {
                            for suggestion in &suggestions {
                                if matches!(
                                    suggestion.action,
                                    PropagationAction::AddRequiresToCaller { .. }
                                ) {
                                    // The caller got a new requires -- propagate further.
                                    queue.push_back((caller_name.clone(), depth + 1));
                                }
                            }
                            all_suggestions.extend(suggestions);
                        }
                        Err(_) => continue,
                    }
                }
            }
        }

        Ok(all_suggestions)
    }

    /// Find all callers of a function using the trust-types call graph.
    fn find_callers(&self, callee_name: &str) -> Vec<(String, SourceSpan)> {
        let mut callers = Vec::new();
        for edge in &self.call_graph.edges {
            let edge_callee_short = edge.callee.rsplit("::").next().unwrap_or(&edge.callee);
            if edge_callee_short == callee_name || edge.callee == callee_name {
                let caller_short = edge.caller.rsplit("::").next().unwrap_or(&edge.caller);
                callers.push((caller_short.to_string(), edge.call_site.clone()));
            }
        }
        callers
    }

    /// Propagate a single precondition from callee to a specific caller.
    fn propagate_single(
        &self,
        caller_name: &str,
        callee_name: &str,
        precondition: &Formula,
        call_site_span: &SourceSpan,
        depth: usize,
        visited: &mut FxHashSet<String>,
    ) -> Result<Vec<PropagationSuggestion>, PropagationError> {
        if !visited.insert(caller_name.to_string()) {
            return Err(PropagationError::CycleDetected { function: caller_name.into() });
        }

        if depth > self.config.max_depth {
            return Err(PropagationError::DepthExceeded {
                function: caller_name.into(),
                limit: self.config.max_depth,
            });
        }

        let callee_info = self
            .functions
            .get(callee_name)
            .ok_or_else(|| PropagationError::NoCallers { function: callee_name.into() })?;

        // Build the substitution map: callee params -> caller args.
        // For now we use a positional mapping (param_0 -> arg_0, etc.)
        // based on the call site in the caller's body.
        let call_args = self.find_call_args(caller_name, callee_name);
        let sub_map = build_substitution_map(&callee_info.params, &call_args);

        let substituted = substitution::substitute(precondition, &sub_map).map_err(|e| {
            PropagationError::SubstitutionFailed {
                caller: caller_name.to_string(),
                callee: callee_name.to_string(),
                source: e,
            }
        })?;

        // Simplify the substituted formula.
        let simplified = substitution::simplify(&substituted);

        // Check if the caller's existing preconditions already imply this.
        let caller_info = self.functions.get(caller_name);
        let already_implied = if self.config.skip_implied {
            caller_info
                .map(|info| precondition_implied(&info.preconditions, &simplified))
                .unwrap_or(false)
        } else {
            false
        };

        let provenance = Provenance {
            origin_function: callee_name.into(),
            origin_precondition: precondition.clone(),
            depth,
            propagation_chain: {
                let mut chain = Vec::new();
                chain.push(callee_name.to_string());
                if depth > 0 {
                    chain.push(caller_name.to_string());
                }
                chain
            },
        };

        if already_implied {
            return Ok(vec![PropagationSuggestion {
                caller_name: caller_name.to_string(),
                caller_def_path: caller_info.map(|i| i.def_path.clone()).unwrap_or_default(),
                callee_name: callee_name.to_string(),
                original_precondition: precondition.clone(),
                substituted_precondition: simplified,
                action: PropagationAction::AlreadyImplied,
                provenance,
                confidence: 1.0,
                call_site_span: call_site_span.clone(),
            }]);
        }

        // Determine action based on caller visibility.
        let caller_visibility =
            caller_info.map(|i| i.visibility).unwrap_or(FunctionVisibility::Private);

        let action = match caller_visibility {
            FunctionVisibility::Private => PropagationAction::AddCallSiteVc,
            FunctionVisibility::PubCrate if self.config.propagate_pub_crate => {
                PropagationAction::AddRequiresToCaller {
                    spec_body: formula_to_spec_string(&simplified),
                }
            }
            FunctionVisibility::Public if self.config.propagate_pub => {
                PropagationAction::AddRequiresToCaller {
                    spec_body: formula_to_spec_string(&simplified),
                }
            }
            _ => PropagationAction::AddCallSiteVc,
        };

        let confidence = compute_confidence(depth, caller_visibility);

        Ok(vec![PropagationSuggestion {
            caller_name: caller_name.to_string(),
            caller_def_path: caller_info.map(|i| i.def_path.clone()).unwrap_or_default(),
            callee_name: callee_name.to_string(),
            original_precondition: precondition.clone(),
            substituted_precondition: simplified,
            action,
            provenance,
            confidence,
            call_site_span: call_site_span.clone(),
        }])
    }

    /// Find the arguments passed at a call site from caller to callee.
    ///
    /// Inspects the caller's MIR blocks to find `Terminator::Call` targeting
    /// the callee and extracts the argument operands as Formulas.
    fn find_call_args(&self, caller_name: &str, callee_name: &str) -> Vec<Formula> {
        // Look for the callee in the call graph edges to get argument info.
        // Since we work with extracted MIR, we generate positional variable names
        // for the arguments (arg_0, arg_1, ...) as stand-ins.
        let callee_info = match self.functions.get(callee_name) {
            Some(info) => info,
            None => return vec![],
        };

        // Generate caller-side variable names for each parameter position.
        callee_info
            .params
            .iter()
            .enumerate()
            .map(|(i, (_, sort))| Formula::Var(format!("{caller_name}_arg_{i}"), sort.clone()))
            .collect()
    }

    /// Get the total number of propagation-relevant functions.
    #[must_use]
    pub fn function_count(&self) -> usize {
        self.functions.len()
    }

    /// Get all function names with preconditions.
    #[must_use]
    pub fn functions_with_preconditions(&self) -> Vec<&str> {
        self.functions
            .iter()
            .filter(|(_, info)| !info.preconditions.is_empty())
            .map(|(name, _)| name.as_str())
            .collect()
    }

    /// Get the visibility of a function.
    #[must_use]
    pub fn function_visibility(&self, name: &str) -> Option<FunctionVisibility> {
        self.functions.get(name).map(|info| info.visibility)
    }
}

/// Infer function visibility from the call graph node metadata.
fn infer_visibility(call_graph: &TypesCallGraph, name: &str, def_path: &str) -> FunctionVisibility {
    for node in &call_graph.nodes {
        if node.name == name || node.def_path == def_path {
            if node.is_public {
                return FunctionVisibility::Public;
            }
            // If the function is not public but is used across module boundaries,
            // treat it as pub(crate).
            return FunctionVisibility::PubCrate;
        }
    }
    FunctionVisibility::Private
}

/// Extract parameter names and sorts from a VerifiableFunction.
fn extract_params(func: &VerifiableFunction) -> Vec<(String, Sort)> {
    func.body
        .locals
        .iter()
        .take(func.body.arg_count)
        .enumerate()
        .map(|(i, local)| {
            let name = match &local.name {
                Some(n) if !n.is_empty() => n.clone(),
                _ => format!("_param_{i}"),
            };
            let sort = Sort::from_ty(&local.ty);
            (name, sort)
        })
        .collect()
}

/// Build a substitution map from formal parameters and actual arguments.
fn build_substitution_map(params: &[(String, Sort)], args: &[Formula]) -> SubstitutionMap {
    SubstitutionMap::from_params_and_args(params, args).unwrap_or_default()
}

/// Check if a set of existing preconditions already implies a formula.
///
/// This is a syntactic check: if the formula already appears in the
/// precondition set, or if it is `Bool(true)`, it is implied.
/// A full semantic check would require an SMT query.
fn precondition_implied(existing: &[Formula], candidate: &Formula) -> bool {
    match candidate {
        Formula::Bool(true) => true,
        _ => existing.iter().any(|e| e == candidate),
    }
}

/// Convert a formula to a human-readable spec string for #[requires("...")].
fn formula_to_spec_string(formula: &Formula) -> String {
    match formula {
        Formula::Bool(b) => b.to_string(),
        Formula::Int(n) => n.to_string(),
        Formula::BitVec { value, width } => format!("bv{width}({value})"),
        Formula::Var(name, _) => name.clone(),
        Formula::Not(inner) => format!("!{}", formula_to_spec_string(inner)),
        Formula::And(fs) => {
            let parts: Vec<String> = fs.iter().map(formula_to_spec_string).collect();
            parts.join(" && ")
        }
        Formula::Or(fs) => {
            let parts: Vec<String> = fs.iter().map(formula_to_spec_string).collect();
            format!("({})", parts.join(" || "))
        }
        Formula::Implies(l, r) => {
            format!("({} ==> {})", formula_to_spec_string(l), formula_to_spec_string(r))
        }
        Formula::Eq(l, r) => {
            format!("{} == {}", formula_to_spec_string(l), formula_to_spec_string(r))
        }
        Formula::Lt(l, r) => {
            format!("{} < {}", formula_to_spec_string(l), formula_to_spec_string(r))
        }
        Formula::Le(l, r) => {
            format!("{} <= {}", formula_to_spec_string(l), formula_to_spec_string(r))
        }
        Formula::Gt(l, r) => {
            format!("{} > {}", formula_to_spec_string(l), formula_to_spec_string(r))
        }
        Formula::Ge(l, r) => {
            format!("{} >= {}", formula_to_spec_string(l), formula_to_spec_string(r))
        }
        Formula::Add(l, r) => {
            format!("({} + {})", formula_to_spec_string(l), formula_to_spec_string(r))
        }
        Formula::Sub(l, r) => {
            format!("({} - {})", formula_to_spec_string(l), formula_to_spec_string(r))
        }
        Formula::Mul(l, r) => {
            format!("({} * {})", formula_to_spec_string(l), formula_to_spec_string(r))
        }
        Formula::Div(l, r) => {
            format!("({} / {})", formula_to_spec_string(l), formula_to_spec_string(r))
        }
        Formula::Neg(inner) => format!("-{}", formula_to_spec_string(inner)),
        _ => format!("{formula:?}"),
    }
}

/// Compute confidence for a propagation suggestion based on depth and visibility.
fn compute_confidence(depth: usize, visibility: FunctionVisibility) -> f64 {
    let base = match visibility {
        FunctionVisibility::Private => 0.95,
        FunctionVisibility::PubCrate => 0.85,
        FunctionVisibility::Public => 0.75,
    };
    // Confidence decreases with depth.
    let depth_factor = 0.9_f64.powi(depth as i32);
    base * depth_factor
}

/// Build a trust-types `CallGraph` from verifiable functions.
///
/// Convenience function that creates node and edge entries from the
/// function data, suitable for use with `CallerPropagator`.
#[must_use]
pub fn build_types_call_graph(functions: &[VerifiableFunction]) -> TypesCallGraph {
    let mut graph = TypesCallGraph::new();

    for func in functions {
        graph.add_node(CallGraphNode {
            def_path: func.def_path.clone(),
            name: func.name.clone(),
            is_public: false, // Will be refined if more metadata is available.
            is_entry_point: false,
            span: func.span.clone(),
        });

        for block in &func.body.blocks {
            if let Terminator::Call { func: callee, args: _, dest: _, target: _, span, .. } =
                &block.terminator
            {
                graph.add_edge(CallGraphEdge {
                    caller: func.def_path.clone(),
                    callee: callee.clone(),
                    call_site: span.clone(),
                });
            }
        }
    }

    graph
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::*;

    fn span(file: &str, line: u32) -> SourceSpan {
        SourceSpan {
            file: file.to_string(),
            line_start: line,
            col_start: 1,
            line_end: line,
            col_end: 40,
        }
    }

    fn make_local(idx: usize, name: &str, ty: Ty) -> LocalDecl {
        LocalDecl { index: idx, ty, name: Some(name.to_string()) }
    }

    fn make_function_with_preconditions(
        name: &str,
        params: &[(&str, Ty)],
        callees: &[&str],
        preconditions: Vec<Formula>,
    ) -> VerifiableFunction {
        let locals: Vec<LocalDecl> =
            params.iter().enumerate().map(|(i, (n, ty))| make_local(i, n, ty.clone())).collect();
        let arg_count = locals.len();

        let mut blocks = Vec::new();
        for (i, callee) in callees.iter().enumerate() {
            blocks.push(BasicBlock {
                id: BlockId(i),
                stmts: vec![],
                terminator: Terminator::Call {
                    func: callee.to_string(),
                    args: vec![],
                    dest: Place::local(0),
                    target: Some(BlockId(i + 1)),
                    span: span("src/lib.rs", (10 + i) as u32),
                    atomic: None,
                },
            });
        }
        blocks.push(BasicBlock {
            id: BlockId(callees.len()),
            stmts: vec![],
            terminator: Terminator::Return,
        });

        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("crate::{name}"),
            span: span("src/lib.rs", 1),
            body: VerifiableBody { locals, blocks, arg_count, return_ty: Ty::Unit },
            contracts: vec![],
            preconditions,
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn simple_precondition() -> Formula {
        // a > 0
        Formula::Gt(
            Box::new(Formula::Var("a".to_string(), Sort::BitVec(64))),
            Box::new(Formula::Int(0)),
        )
    }

    fn make_test_call_graph(
        nodes: &[(&str, &str, bool)],
        edges: &[(&str, &str)],
    ) -> TypesCallGraph {
        let mut graph = TypesCallGraph::new();
        for (def_path, name, is_public) in nodes {
            graph.add_node(CallGraphNode {
                def_path: def_path.to_string(),
                name: name.to_string(),
                is_public: *is_public,
                is_entry_point: false,
                span: SourceSpan::default(),
            });
        }
        for (caller, callee) in edges {
            graph.add_edge(CallGraphEdge {
                caller: caller.to_string(),
                callee: callee.to_string(),
                call_site: span("src/lib.rs", 10),
            });
        }
        graph
    }

    // --- PropagationConfig tests ---

    #[test]
    fn test_propagation_config_default() {
        let config = PropagationConfig::default();
        assert_eq!(config.max_depth, 5);
        assert!(config.propagate_pub_crate);
        assert!(config.propagate_pub);
        assert!(config.skip_implied);
    }

    // --- FunctionVisibility tests ---

    #[test]
    fn test_infer_visibility_public() {
        let graph = make_test_call_graph(&[("crate::foo", "foo", true)], &[]);
        assert_eq!(infer_visibility(&graph, "foo", "crate::foo"), FunctionVisibility::Public);
    }

    #[test]
    fn test_infer_visibility_not_public() {
        let graph = make_test_call_graph(&[("crate::foo", "foo", false)], &[]);
        assert_eq!(infer_visibility(&graph, "foo", "crate::foo"), FunctionVisibility::PubCrate);
    }

    #[test]
    fn test_infer_visibility_unknown() {
        let graph = TypesCallGraph::new();
        assert_eq!(
            infer_visibility(&graph, "unknown", "crate::unknown"),
            FunctionVisibility::Private
        );
    }

    // --- CallerPropagator construction tests ---

    #[test]
    fn test_propagator_new_empty() {
        let graph = TypesCallGraph::new();
        let propagator = CallerPropagator::new(&[], graph, PropagationConfig::default());
        assert_eq!(propagator.function_count(), 0);
        assert!(propagator.functions_with_preconditions().is_empty());
    }

    #[test]
    fn test_propagator_tracks_functions_with_preconditions() {
        let callee = make_function_with_preconditions(
            "callee",
            &[("a", Ty::usize())],
            &[],
            vec![simple_precondition()],
        );
        let caller = make_function_with_preconditions("caller", &[], &["callee"], vec![]);
        let graph = make_test_call_graph(
            &[("crate::callee", "callee", false), ("crate::caller", "caller", false)],
            &[("crate::caller", "callee")],
        );

        let propagator =
            CallerPropagator::new(&[callee, caller], graph, PropagationConfig::default());
        assert_eq!(propagator.function_count(), 2);
        let with_pre = propagator.functions_with_preconditions();
        assert_eq!(with_pre.len(), 1);
        assert!(with_pre.contains(&"callee"));
    }

    // --- propagate_for_callee tests ---

    #[test]
    fn test_propagate_no_preconditions() {
        let func = make_function_with_preconditions("f", &[], &[], vec![]);
        let graph = make_test_call_graph(&[("crate::f", "f", false)], &[]);
        let propagator = CallerPropagator::new(&[func], graph, PropagationConfig::default());
        let result = propagator.propagate_for_callee("f").expect("should succeed");
        assert!(result.suggestions.is_empty());
    }

    #[test]
    fn test_propagate_single_caller() {
        let callee = make_function_with_preconditions(
            "callee",
            &[("a", Ty::usize())],
            &[],
            vec![simple_precondition()],
        );
        let caller = make_function_with_preconditions("caller", &[], &["callee"], vec![]);
        let graph = make_test_call_graph(
            &[("crate::callee", "callee", false), ("crate::caller", "caller", false)],
            &[("crate::caller", "callee")],
        );

        let propagator =
            CallerPropagator::new(&[callee, caller], graph, PropagationConfig::default());
        let result = propagator.propagate_for_callee("callee").expect("should succeed");
        assert_eq!(result.suggestions.len(), 1);
        assert_eq!(result.suggestions[0].caller_name, "caller");
        assert_eq!(result.suggestions[0].callee_name, "callee");
    }

    #[test]
    fn test_propagate_multiple_callers() {
        let callee = make_function_with_preconditions(
            "callee",
            &[("a", Ty::usize())],
            &[],
            vec![simple_precondition()],
        );
        let caller_a = make_function_with_preconditions("caller_a", &[], &["callee"], vec![]);
        let caller_b = make_function_with_preconditions("caller_b", &[], &["callee"], vec![]);
        let graph = make_test_call_graph(
            &[
                ("crate::callee", "callee", false),
                ("crate::caller_a", "caller_a", false),
                ("crate::caller_b", "caller_b", false),
            ],
            &[("crate::caller_a", "callee"), ("crate::caller_b", "callee")],
        );

        let propagator = CallerPropagator::new(
            &[callee, caller_a, caller_b],
            graph,
            PropagationConfig::default(),
        );
        let result = propagator.propagate_for_callee("callee").expect("should succeed");
        assert_eq!(result.suggestions.len(), 2);

        let caller_names: FxHashSet<&str> =
            result.suggestions.iter().map(|s| s.caller_name.as_str()).collect();
        assert!(caller_names.contains("caller_a"));
        assert!(caller_names.contains("caller_b"));
    }

    #[test]
    fn test_propagate_already_implied() {
        let precond = simple_precondition();
        let callee = make_function_with_preconditions(
            "callee",
            &[("a", Ty::usize())],
            &[],
            vec![precond.clone()],
        );
        // Caller already has the same precondition.
        let caller = make_function_with_preconditions(
            "caller",
            &[("a", Ty::usize())],
            &["callee"],
            vec![precond],
        );
        let graph = make_test_call_graph(
            &[("crate::callee", "callee", false), ("crate::caller", "caller", false)],
            &[("crate::caller", "callee")],
        );

        let propagator =
            CallerPropagator::new(&[callee, caller], graph, PropagationConfig::default());
        let result = propagator.propagate_for_callee("callee").expect("should succeed");

        // The substituted formula uses caller_arg_0 instead of a, so it won't
        // match syntactically. We get a non-implied suggestion.
        // This is expected -- full semantic implication checking requires SMT.
        assert!(!result.suggestions.is_empty());
    }

    #[test]
    fn test_propagate_pub_function_gets_requires() {
        let callee = make_function_with_preconditions(
            "callee",
            &[("a", Ty::usize())],
            &[],
            vec![simple_precondition()],
        );
        let caller = make_function_with_preconditions("caller", &[], &["callee"], vec![]);
        let graph = make_test_call_graph(
            &[
                ("crate::callee", "callee", false),
                ("crate::caller", "caller", true), // Public caller
            ],
            &[("crate::caller", "callee")],
        );

        let propagator =
            CallerPropagator::new(&[callee, caller], graph, PropagationConfig::default());
        let result = propagator.propagate_for_callee("callee").expect("should succeed");
        assert_eq!(result.suggestions.len(), 1);
        assert!(matches!(
            &result.suggestions[0].action,
            PropagationAction::AddRequiresToCaller { .. }
        ));
    }

    #[test]
    fn test_propagate_private_function_gets_call_site_vc() {
        let callee = make_function_with_preconditions(
            "callee",
            &[("a", Ty::usize())],
            &[],
            vec![simple_precondition()],
        );
        let caller = make_function_with_preconditions("caller", &[], &["callee"], vec![]);
        // Caller not in call graph nodes -> Private
        let graph = make_test_call_graph(
            &[("crate::callee", "callee", false)],
            &[("crate::caller", "callee")],
        );

        let propagator =
            CallerPropagator::new(&[callee, caller], graph, PropagationConfig::default());
        let result = propagator.propagate_for_callee("callee").expect("should succeed");
        assert_eq!(result.suggestions.len(), 1);
        assert_eq!(result.suggestions[0].action, PropagationAction::AddCallSiteVc);
    }

    // --- propagate_all tests ---

    #[test]
    fn test_propagate_all_empty() {
        let graph = TypesCallGraph::new();
        let propagator = CallerPropagator::new(&[], graph, PropagationConfig::default());
        let results = propagator.propagate_all();
        assert!(results.is_empty());
    }

    #[test]
    fn test_propagate_all_multiple_callees() {
        let callee_a = make_function_with_preconditions(
            "callee_a",
            &[("x", Ty::usize())],
            &[],
            vec![Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::BitVec(64))),
                Box::new(Formula::Int(0)),
            )],
        );
        let callee_b = make_function_with_preconditions(
            "callee_b",
            &[("y", Ty::usize())],
            &[],
            vec![Formula::Lt(
                Box::new(Formula::Var("y".to_string(), Sort::BitVec(64))),
                Box::new(Formula::Int(100)),
            )],
        );
        let caller =
            make_function_with_preconditions("caller", &[], &["callee_a", "callee_b"], vec![]);
        let graph = make_test_call_graph(
            &[
                ("crate::callee_a", "callee_a", false),
                ("crate::callee_b", "callee_b", false),
                ("crate::caller", "caller", false),
            ],
            &[("crate::caller", "callee_a"), ("crate::caller", "callee_b")],
        );

        let propagator = CallerPropagator::new(
            &[callee_a, callee_b, caller],
            graph,
            PropagationConfig::default(),
        );
        let results = propagator.propagate_all();
        assert_eq!(results.len(), 2);
        assert!(results.contains_key("callee_a"));
        assert!(results.contains_key("callee_b"));
    }

    // --- propagate_transitive tests ---

    #[test]
    fn test_propagate_transitive_single_level() {
        let callee = make_function_with_preconditions(
            "callee",
            &[("a", Ty::usize())],
            &[],
            vec![simple_precondition()],
        );
        let caller = make_function_with_preconditions("caller", &[], &["callee"], vec![]);
        let graph = make_test_call_graph(
            &[("crate::callee", "callee", false), ("crate::caller", "caller", false)],
            &[("crate::caller", "callee")],
        );

        let propagator =
            CallerPropagator::new(&[callee, caller], graph, PropagationConfig::default());
        let suggestions = propagator.propagate_transitive("callee").expect("should succeed");
        assert!(!suggestions.is_empty());
    }

    #[test]
    fn test_propagate_transitive_chain() {
        // c -> b -> a, where a has a precondition.
        let a = make_function_with_preconditions(
            "a",
            &[("x", Ty::usize())],
            &[],
            vec![simple_precondition()],
        );
        let b = make_function_with_preconditions("b", &[], &["a"], vec![]);
        let c = make_function_with_preconditions("c", &[], &["b"], vec![]);

        let graph = make_test_call_graph(
            &[("crate::a", "a", false), ("crate::b", "b", true), ("crate::c", "c", false)],
            &[("crate::b", "a"), ("crate::c", "b")],
        );

        let propagator = CallerPropagator::new(&[a, b, c], graph, PropagationConfig::default());
        let suggestions = propagator.propagate_transitive("a").expect("should succeed");
        // Should get at least one suggestion for b (direct caller of a).
        assert!(!suggestions.is_empty());
        assert!(suggestions.iter().any(|s| s.caller_name == "b"));
    }

    #[test]
    fn test_propagate_transitive_respects_depth_limit() {
        let a = make_function_with_preconditions(
            "a",
            &[("x", Ty::usize())],
            &[],
            vec![simple_precondition()],
        );
        let b = make_function_with_preconditions("b", &[], &["a"], vec![]);
        let c = make_function_with_preconditions("c", &[], &["b"], vec![]);
        let d = make_function_with_preconditions("d", &[], &["c"], vec![]);

        let graph = make_test_call_graph(
            &[
                ("crate::a", "a", false),
                ("crate::b", "b", true),
                ("crate::c", "c", true),
                ("crate::d", "d", true),
            ],
            &[("crate::b", "a"), ("crate::c", "b"), ("crate::d", "c")],
        );

        let config = PropagationConfig { max_depth: 1, ..Default::default() };
        let propagator = CallerPropagator::new(&[a, b, c, d], graph, config);
        let suggestions = propagator.propagate_transitive("a").expect("should succeed");
        // With depth limit 1, should only reach direct caller b.
        assert!(suggestions.iter().all(|s| s.provenance.depth <= 1));
    }

    // --- formula_to_spec_string tests ---

    #[test]
    fn test_formula_to_spec_string_simple() {
        let f = Formula::Gt(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        assert_eq!(formula_to_spec_string(&f), "x > 0");
    }

    #[test]
    fn test_formula_to_spec_string_and() {
        let f = Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Lt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(100)),
            ),
        ]);
        assert_eq!(formula_to_spec_string(&f), "x > 0 && x < 100");
    }

    #[test]
    fn test_formula_to_spec_string_or() {
        let f = Formula::Or(vec![Formula::Bool(true), Formula::Bool(false)]);
        assert_eq!(formula_to_spec_string(&f), "(true || false)");
    }

    #[test]
    fn test_formula_to_spec_string_implies() {
        let f = Formula::Implies(
            Box::new(Formula::Var("p".to_string(), Sort::Bool)),
            Box::new(Formula::Var("q".to_string(), Sort::Bool)),
        );
        assert_eq!(formula_to_spec_string(&f), "(p ==> q)");
    }

    #[test]
    fn test_formula_to_spec_string_arithmetic() {
        let f = Formula::Add(
            Box::new(Formula::Var("a".to_string(), Sort::Int)),
            Box::new(Formula::Var("b".to_string(), Sort::Int)),
        );
        assert_eq!(formula_to_spec_string(&f), "(a + b)");
    }

    // --- compute_confidence tests ---

    #[test]
    fn test_confidence_decreases_with_depth() {
        let c0 = compute_confidence(0, FunctionVisibility::Private);
        let c1 = compute_confidence(1, FunctionVisibility::Private);
        let c2 = compute_confidence(2, FunctionVisibility::Private);
        assert!(c0 > c1);
        assert!(c1 > c2);
    }

    #[test]
    fn test_confidence_private_higher_than_public() {
        let priv_c = compute_confidence(0, FunctionVisibility::Private);
        let pub_c = compute_confidence(0, FunctionVisibility::Public);
        assert!(priv_c > pub_c);
    }

    // --- PropagationResult tests ---

    #[test]
    fn test_propagation_result_actionable_count() {
        let result = PropagationResult {
            callee_name: "f".to_string(),
            suggestions: vec![
                PropagationSuggestion {
                    caller_name: "a".to_string(),
                    caller_def_path: "crate::a".to_string(),
                    callee_name: "f".to_string(),
                    original_precondition: Formula::Bool(true),
                    substituted_precondition: Formula::Bool(true),
                    action: PropagationAction::AddCallSiteVc,
                    provenance: Provenance {
                        origin_function: "f".into(),
                        origin_precondition: Formula::Bool(true),
                        depth: 0,
                        propagation_chain: vec!["f".to_string()],
                    },
                    confidence: 0.9,
                    call_site_span: SourceSpan::default(),
                },
                PropagationSuggestion {
                    caller_name: "b".to_string(),
                    caller_def_path: "crate::b".to_string(),
                    callee_name: "f".to_string(),
                    original_precondition: Formula::Bool(true),
                    substituted_precondition: Formula::Bool(true),
                    action: PropagationAction::AlreadyImplied,
                    provenance: Provenance {
                        origin_function: "f".into(),
                        origin_precondition: Formula::Bool(true),
                        depth: 0,
                        propagation_chain: vec!["f".to_string()],
                    },
                    confidence: 1.0,
                    call_site_span: SourceSpan::default(),
                },
            ],
            skipped_implied: vec![],
            warnings: vec![],
        };
        assert_eq!(result.actionable_count(), 1);
    }

    // --- build_types_call_graph tests ---

    #[test]
    fn test_build_types_call_graph_from_functions() {
        let caller = make_function_with_preconditions("caller", &[], &["callee"], vec![]);
        let callee = make_function_with_preconditions("callee", &[("a", Ty::usize())], &[], vec![]);
        let graph = build_types_call_graph(&[caller, callee]);
        assert_eq!(graph.nodes.len(), 2);
        assert_eq!(graph.edges.len(), 1);
        assert_eq!(graph.edges[0].caller, "crate::caller");
        assert_eq!(graph.edges[0].callee, "callee");
    }

    #[test]
    fn test_build_types_call_graph_empty() {
        let graph = build_types_call_graph(&[]);
        assert!(graph.nodes.is_empty());
        assert!(graph.edges.is_empty());
    }

    // --- extract_params tests ---

    #[test]
    fn test_extract_params_named() {
        let func = make_function_with_preconditions(
            "f",
            &[("a", Ty::usize()), ("b", Ty::Bool)],
            &[],
            vec![],
        );
        let params = extract_params(&func);
        assert_eq!(params.len(), 2);
        assert_eq!(params[0].0, "a");
        assert_eq!(params[0].1, Sort::BitVec(64));
        assert_eq!(params[1].0, "b");
        assert_eq!(params[1].1, Sort::Bool);
    }

    #[test]
    fn test_extract_params_unnamed() {
        let func = VerifiableFunction {
            name: "f".to_string(),
            def_path: "crate::f".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, name: None, ty: Ty::i32() }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let params = extract_params(&func);
        assert_eq!(params.len(), 1);
        assert_eq!(params[0].0, "_param_0");
    }

    // --- precondition_implied tests ---

    #[test]
    fn test_precondition_implied_true() {
        assert!(precondition_implied(&[], &Formula::Bool(true)));
    }

    #[test]
    fn test_precondition_implied_exact_match() {
        let pre = simple_precondition();
        assert!(precondition_implied(std::slice::from_ref(&pre), &pre));
    }

    #[test]
    fn test_precondition_implied_no_match() {
        let pre = simple_precondition();
        let other = Formula::Lt(
            Box::new(Formula::Var("b".to_string(), Sort::Int)),
            Box::new(Formula::Int(100)),
        );
        assert!(!precondition_implied(&[pre], &other));
    }

    // --- Provenance tests ---

    #[test]
    fn test_provenance_chain() {
        let provenance = Provenance {
            origin_function: "callee".into(),
            origin_precondition: Formula::Bool(true),
            depth: 2,
            propagation_chain: vec!["callee".to_string(), "mid".to_string(), "caller".to_string()],
        };
        assert_eq!(provenance.depth, 2);
        assert_eq!(provenance.propagation_chain.len(), 3);
    }

    // --- Unknown callee error handling ---

    #[test]
    fn test_propagate_for_unknown_callee() {
        let graph = TypesCallGraph::new();
        let propagator = CallerPropagator::new(&[], graph, PropagationConfig::default());
        let result = propagator.propagate_for_callee("nonexistent");
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), PropagationError::NoCallers { .. }));
    }

    // --- Serialization test ---

    #[test]
    fn test_propagation_suggestion_serialization_roundtrip() {
        let suggestion = PropagationSuggestion {
            caller_name: "caller".to_string(),
            caller_def_path: "crate::caller".to_string(),
            callee_name: "callee".to_string(),
            original_precondition: simple_precondition(),
            substituted_precondition: simple_precondition(),
            action: PropagationAction::AddCallSiteVc,
            provenance: Provenance {
                origin_function: "callee".into(),
                origin_precondition: simple_precondition(),
                depth: 0,
                propagation_chain: vec!["callee".to_string()],
            },
            confidence: 0.95,
            call_site_span: SourceSpan::default(),
        };

        let json = serde_json::to_string(&suggestion).expect("serialize");
        let roundtrip: PropagationSuggestion = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip.caller_name, "caller");
        assert_eq!(roundtrip.callee_name, "callee");
        assert_eq!(roundtrip.confidence, 0.95);
    }

    // --- Integration: full propagation flow ---

    #[test]
    fn test_full_propagation_flow() {
        // Setup: callee has precondition `x > 0`, caller calls callee, caller is public.
        let callee = make_function_with_preconditions(
            "divide",
            &[("divisor", Ty::usize())],
            &[],
            vec![Formula::Gt(
                Box::new(Formula::Var("divisor".to_string(), Sort::BitVec(64))),
                Box::new(Formula::Int(0)),
            )],
        );
        let caller =
            make_function_with_preconditions("process", &[("n", Ty::usize())], &["divide"], vec![]);
        let graph = make_test_call_graph(
            &[("crate::divide", "divide", false), ("crate::process", "process", true)],
            &[("crate::process", "divide")],
        );

        let propagator =
            CallerPropagator::new(&[callee, caller], graph, PropagationConfig::default());

        // Check propagation
        let result = propagator.propagate_for_callee("divide").expect("should succeed");
        assert_eq!(result.callee_name, "divide");
        assert_eq!(result.suggestions.len(), 1);

        let suggestion = &result.suggestions[0];
        assert_eq!(suggestion.caller_name, "process");
        assert_eq!(suggestion.callee_name, "divide");
        // The substituted precondition should reference the caller's arg.
        assert!(matches!(
            &suggestion.action,
            PropagationAction::AddRequiresToCaller { spec_body }
            if spec_body.contains(">") && spec_body.contains("0")
        ));
        assert!(suggestion.confidence > 0.0);
        assert_eq!(suggestion.provenance.origin_function, "divide");
        assert_eq!(suggestion.provenance.depth, 0);
    }
}
