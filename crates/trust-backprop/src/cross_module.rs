//! Cross-module rewrite planning.
//!
//! When a callee gets a new precondition via trust-strengthen, every call site
//! must be updated with a corresponding check. This module plans rewrites that
//! span multiple files, ordered callee-first so preconditions are established
//! before caller-site checks are generated.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use serde::{Deserialize, Serialize};
use trust_strengthen::{Proposal, ProposalKind};

use crate::dependency::{topological_order, CallGraph};
use crate::SourceRewrite;

/// A cross-module rewrite plan: an ordered list of per-file rewrites.
///
/// Files are ordered so that callees are rewritten before their callers,
/// ensuring new preconditions are in place when caller checks are generated.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CrossModulePlan {
    /// Ordered list of (file_path, rewrites) pairs. Callees first.
    pub file_rewrites: Vec<(String, Vec<SourceRewrite>)>,
    /// Summary of the cross-module plan.
    pub summary: String,
}

impl CrossModulePlan {
    /// Total number of rewrites across all files.
    #[must_use]
    pub fn total_rewrites(&self) -> usize {
        self.file_rewrites.iter().map(|(_, rw)| rw.len()).sum()
    }

    /// Whether the plan is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.file_rewrites.iter().all(|(_, rw)| rw.is_empty())
    }

    /// Return the number of files affected.
    #[must_use]
    pub fn file_count(&self) -> usize {
        self.file_rewrites.len()
    }
}

/// Plan cross-module rewrites based on proposals and a call graph.
///
/// When a proposal adds a precondition to a callee, this generates
/// corresponding assertion rewrites at each call site in the caller.
/// Rewrites are ordered callee-first via topological sort of the call graph.
///
/// # Arguments
///
/// * `proposals` - Proposals from trust-strengthen (each targets one function).
/// * `call_graph` - The call graph built from `VerifiableFunction` data.
/// * `function_files` - Map from function name to its source file path.
///
/// # Returns
///
/// A `CrossModulePlan` with file rewrites ordered callee-first.
#[must_use]
pub fn plan_cross_module_rewrites(
    proposals: &[Proposal],
    call_graph: &CallGraph,
    function_files: &FxHashMap<String, String>,
) -> CrossModulePlan {
    let order = topological_order(call_graph);

    // Index proposals by function name for quick lookup.
    let mut proposals_by_fn: FxHashMap<&str, Vec<&Proposal>> = FxHashMap::default();
    for proposal in proposals {
        proposals_by_fn
            .entry(proposal.function_name.as_str())
            .or_default()
            .push(proposal);
    }

    // Collect per-file rewrites, maintaining callee-first order.
    let mut file_rewrites_map: FxHashMap<String, Vec<SourceRewrite>> = FxHashMap::default();
    let mut file_order: Vec<String> = Vec::new();

    for func_name in &order {
        // Apply direct proposals for this function.
        if let Some(func_proposals) = proposals_by_fn.get(func_name.as_str()) {
            for proposal in func_proposals {
                let file_path = function_files
                    .get(func_name.as_str())
                    .cloned()
                    .unwrap_or_else(|| proposal.function_path.clone());
                let rewrites = file_rewrites_map.entry(file_path.clone()).or_default();
                if !file_order.contains(&file_path) {
                    file_order.push(file_path);
                }
                rewrites.extend(crate::proposal_to_rewrites(proposal));
            }
        }

        // If this function got a new precondition, generate caller-site checks.
        let new_preconditions: Vec<&str> = proposals_by_fn
            .get(func_name.as_str())
            .map(|ps| {
                ps.iter()
                    .filter_map(|p| match &p.kind {
                        ProposalKind::AddPrecondition { spec_body } => Some(spec_body.as_str()),
                        _ => None,
                    })
                    .collect()
            })
            .unwrap_or_default();

        if new_preconditions.is_empty() {
            continue;
        }

        // For each caller, generate a check assertion at the call site.
        let callers = call_graph.callers(func_name);
        for caller in &callers {
            let caller_file = match function_files.get(caller.as_str()) {
                Some(f) => f.clone(),
                None => continue,
            };

            let rewrites = file_rewrites_map.entry(caller_file.clone()).or_default();
            if !file_order.contains(&caller_file) {
                file_order.push(caller_file.clone());
            }

            for spec_body in &new_preconditions {
                rewrites.push(SourceRewrite {
                    file_path: caller_file.clone(),
                    offset: 0, // Real offset resolved later by proposal_converter.
                    kind: crate::RewriteKind::InsertAssertion {
                        assertion: format!(
                            "// tRust: caller must satisfy {func_name}'s precondition\n\
                             debug_assert!({spec_body}, \"precondition of {func_name}\");"
                        ),
                    },
                    function_name: caller.clone(),
                    rationale: format!(
                        "Callee `{func_name}` gained precondition `{spec_body}`; \
                         caller `{caller}` needs corresponding check"
                    ),
                });
            }
        }
    }

    let result: Vec<(String, Vec<SourceRewrite>)> = file_order
        .into_iter()
        .filter_map(|f| {
            let rw = file_rewrites_map.remove(&f)?;
            if rw.is_empty() {
                None
            } else {
                Some((f, rw))
            }
        })
        .collect();

    let total = result.iter().map(|(_, rw)| rw.len()).sum::<usize>();
    let file_count = result.len();
    CrossModulePlan {
        file_rewrites: result,
        summary: format!("Cross-module plan: {total} rewrites across {file_count} files"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dependency::build_call_graph;
    use trust_types::*;

    /// Helper: make a VerifiableFunction with specified callees.
    fn make_function(name: &str, callees: &[&str]) -> VerifiableFunction {
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
                    span: SourceSpan::default(),
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
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![],
                blocks,
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn make_precondition_proposal(func: &str, spec: &str) -> Proposal {
        Proposal {
            function_path: format!("src/{func}.rs"),
            function_name: func.into(),
            kind: ProposalKind::AddPrecondition {
                spec_body: spec.into(),
            },
            confidence: 0.9,
            rationale: "test".into(),
        }
    }

    fn make_file_map(entries: &[(&str, &str)]) -> FxHashMap<String, String> {
        entries
            .iter()
            .map(|(k, v)| (k.to_string(), v.to_string()))
            .collect()
    }

    #[test]
    fn test_plan_cross_module_empty() {
        let graph = build_call_graph(&[]);
        let file_map = FxHashMap::default();
        let plan = plan_cross_module_rewrites(&[], &graph, &file_map);
        assert!(plan.is_empty());
        assert_eq!(plan.total_rewrites(), 0);
        assert_eq!(plan.file_count(), 0);
    }

    #[test]
    fn test_plan_cross_module_single_proposal_no_callers() {
        let funcs = vec![make_function("helper", &[])];
        let graph = build_call_graph(&funcs);
        let file_map = make_file_map(&[("helper", "src/helper.rs")]);
        let proposals = vec![make_precondition_proposal("helper", "x > 0")];

        let plan = plan_cross_module_rewrites(&proposals, &graph, &file_map);
        assert_eq!(plan.total_rewrites(), 1); // Just the precondition itself.
        assert_eq!(plan.file_count(), 1);
    }

    #[test]
    fn test_plan_cross_module_propagates_to_caller() {
        // caller -> callee. Add precondition to callee. Caller should get a check.
        let funcs = vec![
            make_function("caller", &["callee"]),
            make_function("callee", &[]),
        ];
        let graph = build_call_graph(&funcs);
        let file_map = make_file_map(&[
            ("caller", "src/caller.rs"),
            ("callee", "src/callee.rs"),
        ]);
        let proposals = vec![make_precondition_proposal("callee", "x > 0")];

        let plan = plan_cross_module_rewrites(&proposals, &graph, &file_map);
        // 1 for the callee's precondition + 1 for caller's check
        assert_eq!(plan.total_rewrites(), 2);
        assert_eq!(plan.file_count(), 2);

        // Callee file should come first (callee-first ordering).
        assert_eq!(plan.file_rewrites[0].0, "src/callee.rs");
        assert_eq!(plan.file_rewrites[1].0, "src/caller.rs");

        // Caller's rewrite should be an assertion mentioning the precondition.
        let caller_rewrites = &plan.file_rewrites[1].1;
        assert_eq!(caller_rewrites.len(), 1);
        match &caller_rewrites[0].kind {
            crate::RewriteKind::InsertAssertion { assertion } => {
                assert!(
                    assertion.contains("x > 0"),
                    "assertion should contain spec body: {assertion}"
                );
            }
            other => panic!("expected InsertAssertion, got {other:?}"),
        }
    }

    #[test]
    fn test_plan_cross_module_multiple_callers() {
        // a -> c, b -> c. Add precondition to c. Both a and b get checks.
        let funcs = vec![
            make_function("a", &["c"]),
            make_function("b", &["c"]),
            make_function("c", &[]),
        ];
        let graph = build_call_graph(&funcs);
        let file_map = make_file_map(&[
            ("a", "src/a.rs"),
            ("b", "src/b.rs"),
            ("c", "src/c.rs"),
        ]);
        let proposals = vec![make_precondition_proposal("c", "n != 0")];

        let plan = plan_cross_module_rewrites(&proposals, &graph, &file_map);
        // 1 (callee precondition) + 2 (one check per caller)
        assert_eq!(plan.total_rewrites(), 3);

        // c's file should appear first.
        assert_eq!(plan.file_rewrites[0].0, "src/c.rs");
    }

    #[test]
    fn test_plan_cross_module_chain_ordering() {
        // a -> b -> c. Add precondition to c.
        // c gets the precondition, b gets a check, a does NOT (a doesn't call c directly).
        let funcs = vec![
            make_function("a", &["b"]),
            make_function("b", &["c"]),
            make_function("c", &[]),
        ];
        let graph = build_call_graph(&funcs);
        let file_map = make_file_map(&[
            ("a", "src/a.rs"),
            ("b", "src/b.rs"),
            ("c", "src/c.rs"),
        ]);
        let proposals = vec![make_precondition_proposal("c", "i < len")];

        let plan = plan_cross_module_rewrites(&proposals, &graph, &file_map);
        // 1 (c's precondition) + 1 (b's caller check). a doesn't call c.
        assert_eq!(plan.total_rewrites(), 2);

        // Order: c first, then b.
        assert_eq!(plan.file_rewrites[0].0, "src/c.rs");
        assert_eq!(plan.file_rewrites[1].0, "src/b.rs");
    }

    #[test]
    fn test_plan_cross_module_non_precondition_no_propagation() {
        // caller -> callee. Add safe arithmetic to callee. No caller propagation.
        let funcs = vec![
            make_function("caller", &["callee"]),
            make_function("callee", &[]),
        ];
        let graph = build_call_graph(&funcs);
        let file_map = make_file_map(&[
            ("caller", "src/caller.rs"),
            ("callee", "src/callee.rs"),
        ]);
        let proposals = vec![Proposal {
            function_path: "src/callee.rs".into(),
            function_name: "callee".into(),
            kind: ProposalKind::SafeArithmetic {
                original: "a + b".into(),
                replacement: "a.checked_add(b).unwrap()".into(),
            },
            confidence: 0.8,
            rationale: "safe arithmetic".into(),
        }];

        let plan = plan_cross_module_rewrites(&proposals, &graph, &file_map);
        // Only the callee's rewrite; no caller propagation for SafeArithmetic.
        assert_eq!(plan.total_rewrites(), 1);
        assert_eq!(plan.file_count(), 1);
    }

    #[test]
    fn test_plan_cross_module_same_file() {
        // Two functions in the same file.
        let funcs = vec![
            make_function("outer", &["inner"]),
            make_function("inner", &[]),
        ];
        let graph = build_call_graph(&funcs);
        let file_map = make_file_map(&[
            ("outer", "src/lib.rs"),
            ("inner", "src/lib.rs"),
        ]);
        let proposals = vec![make_precondition_proposal("inner", "x >= 0")];

        let plan = plan_cross_module_rewrites(&proposals, &graph, &file_map);
        // Both the precondition and caller check are in the same file.
        assert_eq!(plan.total_rewrites(), 2);
        // Should be merged into one file entry.
        assert_eq!(plan.file_count(), 1);
        assert_eq!(plan.file_rewrites[0].0, "src/lib.rs");
        assert_eq!(plan.file_rewrites[0].1.len(), 2);
    }

    #[test]
    fn test_plan_cross_module_summary() {
        let funcs = vec![make_function("f", &[])];
        let graph = build_call_graph(&funcs);
        let file_map = make_file_map(&[("f", "src/f.rs")]);
        let proposals = vec![make_precondition_proposal("f", "true")];

        let plan = plan_cross_module_rewrites(&proposals, &graph, &file_map);
        assert!(plan.summary.contains("1 rewrites"));
        assert!(plan.summary.contains("1 files"));
    }
}
