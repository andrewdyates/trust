// trust-testgen: Test coverage analysis for verification conditions
//
// Tracks which VCs are covered by generated tests and identifies gaps.
// Provides coverage goals, progress tracking, and test suggestions.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use trust_types::fx::{FxHashMap, FxHashSet};

use trust_types::VerificationCondition;

use crate::{vc_kind_suffix, GeneratedTest};

/// Error type for coverage operations.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum CoverageError {
    #[error("unknown VC identifier: {0}")]
    UnknownVc(String),

    #[error("no VCs registered in coverage map")]
    EmptyMap,
}

/// Unique identifier for a verification condition.
///
/// Combines function name and VC kind tag for deduplication.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VcId {
    /// Function the VC belongs to.
    pub(crate) function: String,
    /// VC kind tag (e.g., "arithmetic_overflow").
    pub(crate) kind_tag: String,
    /// Index to disambiguate multiple VCs of the same kind in one function.
    pub(crate) index: usize,
}

impl VcId {
    /// Create a new VC identifier.
    #[must_use]
    pub fn new(function: impl Into<String>, kind_tag: impl Into<String>, index: usize) -> Self {
        Self {
            function: function.into(),
            kind_tag: kind_tag.into(),
            index,
        }
    }

    /// Create from a VerificationCondition, using the given index.
    #[must_use]
    pub fn from_vc(vc: &VerificationCondition, index: usize) -> Self {
        Self::new(&vc.function, vc_kind_suffix(&vc.kind), index)
    }

    /// Human-readable display string.
    #[must_use]
    pub fn display(&self) -> String {
        format!("{}::{}[{}]", self.function, self.kind_tag, self.index)
    }
}

/// Map tracking which VCs are covered by which tests.
#[derive(Debug, Clone, Default)]
pub struct CoverageMap {
    /// All known VCs.
    vcs: BTreeSet<VcId>,
    /// Mapping from VC to covering test names.
    covered_by: BTreeMap<VcId, FxHashSet<String>>,
    /// Mapping from test name to covered VCs.
    covers: FxHashMap<String, FxHashSet<VcId>>,
}

impl CoverageMap {
    /// Create a new empty coverage map.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a VC as known (may or may not be covered yet).
    pub fn register_vc(&mut self, vc_id: VcId) {
        self.vcs.insert(vc_id);
    }

    /// Register all VCs from a slice of verification conditions.
    pub fn register_all(&mut self, vcs: &[VerificationCondition]) {
        // Track per-function+kind counts for index assignment.
        let mut counters: FxHashMap<(String, String), usize> = FxHashMap::default();
        for vc in vcs {
            let key = (vc.function.clone(), vc_kind_suffix(&vc.kind));
            let idx = counters.entry(key).or_insert(0);
            self.register_vc(VcId::from_vc(vc, *idx));
            *idx += 1;
        }
    }

    /// Record that a test covers a VC.
    pub fn record_coverage(&mut self, test_name: &str, vc_id: VcId) {
        self.vcs.insert(vc_id.clone());
        self.covered_by
            .entry(vc_id.clone())
            .or_default()
            .insert(test_name.to_string());
        self.covers
            .entry(test_name.to_string())
            .or_default()
            .insert(vc_id);
    }

    /// Number of registered VCs.
    #[must_use]
    pub fn total_vcs(&self) -> usize {
        self.vcs.len()
    }

    /// Number of VCs with at least one covering test.
    #[must_use]
    pub fn covered_vcs(&self) -> usize {
        self.vcs
            .iter()
            .filter(|vc| {
                self.covered_by
                    .get(*vc)
                    .is_some_and(|tests| !tests.is_empty())
            })
            .count()
    }

    /// Number of VCs with no covering test.
    #[must_use]
    pub fn uncovered_vcs(&self) -> usize {
        self.total_vcs() - self.covered_vcs()
    }

    /// Get the set of test names covering a VC.
    #[must_use]
    pub fn tests_for_vc(&self, vc_id: &VcId) -> Option<&FxHashSet<String>> {
        self.covered_by.get(vc_id)
    }

    /// Get the set of VCs covered by a test.
    #[must_use]
    pub fn vcs_for_test(&self, test_name: &str) -> Option<&FxHashSet<VcId>> {
        self.covers.get(test_name)
    }

    /// All registered VC IDs.
    #[must_use]
    pub fn all_vcs(&self) -> &BTreeSet<VcId> {
        &self.vcs
    }

    /// All uncovered VC IDs.
    #[must_use]
    pub fn uncovered_vc_ids(&self) -> Vec<&VcId> {
        self.vcs
            .iter()
            .filter(|vc| {
                self.covered_by
                    .get(*vc)
                    .is_none_or(|tests| tests.is_empty())
            })
            .collect()
    }
}

/// Computed coverage analysis results.
#[derive(Debug, Clone)]
pub struct CoverageAnalysis {
    /// Fraction of VCs with at least one test (0.0 to 1.0).
    pub(crate) vc_coverage: f64,
    /// Number of distinct VC kinds covered vs total distinct kinds.
    pub(crate) kind_coverage: f64,
    /// Number of distinct functions with at least one covered VC.
    pub(crate) function_coverage: f64,
    /// Total VCs.
    pub(crate) total_vcs: usize,
    /// Covered VCs.
    pub(crate) covered_vcs: usize,
    /// Uncovered VCs.
    pub(crate) uncovered_vcs: usize,
    /// Total distinct functions.
    pub(crate) total_functions: usize,
    /// Functions with at least one covered VC.
    pub(crate) covered_functions: usize,
}

impl CoverageAnalysis {
    /// Compute coverage analysis from a coverage map.
    #[must_use]
    pub fn from_map(map: &CoverageMap) -> Self {
        let total_vcs = map.total_vcs();
        let covered_vcs = map.covered_vcs();
        let uncovered_vcs = map.uncovered_vcs();

        let vc_coverage = if total_vcs == 0 {
            1.0
        } else {
            covered_vcs as f64 / total_vcs as f64
        };

        // Kind coverage: distinct VC kind tags
        let all_kinds: FxHashSet<&str> = map.vcs.iter().map(|vc| vc.kind_tag.as_str()).collect();
        let covered_kinds: FxHashSet<&str> = map
            .covered_by
            .iter()
            .filter(|(_, tests)| !tests.is_empty())
            .map(|(vc, _)| vc.kind_tag.as_str())
            .collect();
        let kind_coverage = if all_kinds.is_empty() {
            1.0
        } else {
            covered_kinds.len() as f64 / all_kinds.len() as f64
        };

        // Function coverage: distinct functions
        let all_functions: FxHashSet<&str> =
            map.vcs.iter().map(|vc| vc.function.as_str()).collect();
        let covered_functions_set: FxHashSet<&str> = map
            .covered_by
            .iter()
            .filter(|(_, tests)| !tests.is_empty())
            .map(|(vc, _)| vc.function.as_str())
            .collect();
        let total_functions = all_functions.len();
        let covered_functions = covered_functions_set.len();
        let function_coverage = if total_functions == 0 {
            1.0
        } else {
            covered_functions as f64 / total_functions as f64
        };

        Self {
            vc_coverage,
            kind_coverage,
            function_coverage,
            total_vcs,
            covered_vcs,
            uncovered_vcs,
            total_functions,
            covered_functions,
        }
    }
}

/// Gap analysis: identify specific uncovered areas.
#[derive(Debug, Clone)]
pub struct CoverageGap {
    /// The uncovered VC.
    pub(crate) vc_id: VcId,
    /// Human-readable description of why this gap matters.
    pub(crate) description: String,
}

/// Identify VCs without any test coverage.
#[must_use]
pub fn gap_analysis(map: &CoverageMap) -> Vec<CoverageGap> {
    map.uncovered_vc_ids()
        .into_iter()
        .map(|vc_id| {
            let description = format!(
                "No tests cover {} in function {}",
                vc_id.kind_tag, vc_id.function,
            );
            CoverageGap {
                vc_id: vc_id.clone(),
                description,
            }
        })
        .collect()
}

/// Summary statistics for a coverage report.
#[derive(Debug, Clone)]
pub struct CoverageReport {
    /// Coverage analysis.
    pub(crate) analysis: CoverageAnalysis,
    /// Coverage gaps.
    pub(crate) gaps: Vec<CoverageGap>,
    /// Per-function coverage breakdown.
    pub(crate) per_function: BTreeMap<String, FunctionCoverage>,
}

/// Per-function coverage breakdown.
#[derive(Debug, Clone)]
pub struct FunctionCoverage {
    /// Total VCs for this function.
    pub(crate) total: usize,
    /// Covered VCs for this function.
    pub(crate) covered: usize,
    /// Uncovered VC kind tags.
    pub(crate) uncovered_kinds: Vec<String>,
}

/// Generate a full coverage report.
#[must_use]
pub fn coverage_report(map: &CoverageMap) -> CoverageReport {
    let analysis = CoverageAnalysis::from_map(map);
    let gaps = gap_analysis(map);

    // Per-function breakdown
    let mut per_function: BTreeMap<String, (usize, usize, Vec<String>)> = BTreeMap::new();
    for vc_id in &map.vcs {
        let entry = per_function
            .entry(vc_id.function.clone())
            .or_insert((0, 0, Vec::new()));
        entry.0 += 1;
        let is_covered = map
            .covered_by
            .get(vc_id)
            .is_some_and(|tests| !tests.is_empty());
        if is_covered {
            entry.1 += 1;
        } else {
            entry.2.push(vc_id.kind_tag.clone());
        }
    }

    let per_function = per_function
        .into_iter()
        .map(|(func, (total, covered, uncovered_kinds))| {
            (
                func,
                FunctionCoverage {
                    total,
                    covered,
                    uncovered_kinds,
                },
            )
        })
        .collect();

    CoverageReport { analysis, gaps, per_function }
}

/// Propose new tests to fill coverage gaps.
///
/// For each uncovered VC, generates a placeholder test targeting that property.
#[must_use]
pub fn suggest_tests(gaps: &[CoverageGap]) -> Vec<GeneratedTest> {
    gaps.iter()
        .enumerate()
        .map(|(i, gap)| {
            let func_ident = crate::sanitize_ident(&gap.vc_id.function);
            let name = format!(
                "test_cover_{func_ident}_{}_{}",
                gap.vc_id.kind_tag, i,
            );
            let code = format!(
                "#[test]\n\
                 fn {name}() {{\n\
                 \x20   // Suggested test to cover: {desc}\n\
                 \x20   // Function: {func}\n\
                 \x20   // VC kind: {kind}\n\
                 \x20   // PLACEHOLDER: implement test with concrete inputs\n\
                 \x20   assert!(true, \"placeholder for coverage gap\");\n\
                 }}",
                desc = gap.description,
                func = gap.vc_id.function,
                kind = gap.vc_id.kind_tag,
            );
            GeneratedTest {
                name,
                code,
                boundary_values: vec![],
            }
        })
        .collect()
}

/// Coverage goal types.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CoverageGoal {
    /// Cover all registered VCs.
    AllVCs,
    /// Cover all distinct VC kind tags.
    AllKinds,
    /// Cover all functions (at least one VC per function).
    AllFunctions,
    /// Cover specific VC kinds.
    Targeted(Vec<String>),
}

/// Compute progress toward a coverage goal (0.0 to 1.0).
#[must_use]
pub fn progress_toward_goal(map: &CoverageMap, goal: &CoverageGoal) -> f64 {
    match goal {
        CoverageGoal::AllVCs => {
            let analysis = CoverageAnalysis::from_map(map);
            analysis.vc_coverage
        }
        CoverageGoal::AllKinds => {
            let analysis = CoverageAnalysis::from_map(map);
            analysis.kind_coverage
        }
        CoverageGoal::AllFunctions => {
            let analysis = CoverageAnalysis::from_map(map);
            analysis.function_coverage
        }
        CoverageGoal::Targeted(kinds) => {
            if kinds.is_empty() {
                return 1.0;
            }
            let target_set: FxHashSet<&str> = kinds.iter().map(|s| s.as_str()).collect();
            let total = map
                .vcs
                .iter()
                .filter(|vc| target_set.contains(vc.kind_tag.as_str()))
                .count();
            if total == 0 {
                return 1.0;
            }
            let covered = map
                .vcs
                .iter()
                .filter(|vc| target_set.contains(vc.kind_tag.as_str()))
                .filter(|vc| {
                    map.covered_by
                        .get(*vc)
                        .is_some_and(|tests| !tests.is_empty())
                })
                .count();
            covered as f64 / total as f64
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{Formula, SourceSpan, VcKind};

    fn make_vc(function: &str, kind: VcKind) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: function.to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    // -----------------------------------------------------------------------
    // VcId
    // -----------------------------------------------------------------------

    #[test]
    fn test_vc_id_new() {
        let id = VcId::new("func", "overflow", 0);
        assert_eq!(id.function, "func");
        assert_eq!(id.kind_tag, "overflow");
        assert_eq!(id.index, 0);
    }

    #[test]
    fn test_vc_id_from_vc() {
        let vc = make_vc("math::add", VcKind::DivisionByZero);
        let id = VcId::from_vc(&vc, 3);
        assert_eq!(id.function, "math::add");
        assert_eq!(id.kind_tag, "division_by_zero");
        assert_eq!(id.index, 3);
    }

    #[test]
    fn test_vc_id_display() {
        let id = VcId::new("f", "overflow", 2);
        assert_eq!(id.display(), "f::overflow[2]");
    }

    // -----------------------------------------------------------------------
    // CoverageMap
    // -----------------------------------------------------------------------

    #[test]
    fn test_coverage_map_empty() {
        let map = CoverageMap::new();
        assert_eq!(map.total_vcs(), 0);
        assert_eq!(map.covered_vcs(), 0);
        assert_eq!(map.uncovered_vcs(), 0);
    }

    #[test]
    fn test_coverage_map_register_vc() {
        let mut map = CoverageMap::new();
        map.register_vc(VcId::new("f", "overflow", 0));
        assert_eq!(map.total_vcs(), 1);
        assert_eq!(map.covered_vcs(), 0);
        assert_eq!(map.uncovered_vcs(), 1);
    }

    #[test]
    fn test_coverage_map_record_coverage() {
        let mut map = CoverageMap::new();
        let vc_id = VcId::new("f", "overflow", 0);
        map.register_vc(vc_id.clone());
        map.record_coverage("test_a", vc_id.clone());

        assert_eq!(map.total_vcs(), 1);
        assert_eq!(map.covered_vcs(), 1);
        assert_eq!(map.uncovered_vcs(), 0);

        let tests = map.tests_for_vc(&vc_id).unwrap();
        assert!(tests.contains("test_a"));

        let vcs = map.vcs_for_test("test_a").unwrap();
        assert!(vcs.contains(&vc_id));
    }

    #[test]
    fn test_coverage_map_multiple_tests_same_vc() {
        let mut map = CoverageMap::new();
        let vc_id = VcId::new("f", "overflow", 0);
        map.record_coverage("test_a", vc_id.clone());
        map.record_coverage("test_b", vc_id.clone());

        assert_eq!(map.covered_vcs(), 1);
        let tests = map.tests_for_vc(&vc_id).unwrap();
        assert_eq!(tests.len(), 2);
    }

    #[test]
    fn test_coverage_map_register_all() {
        let mut map = CoverageMap::new();
        let vcs = vec![
            make_vc("f", VcKind::DivisionByZero),
            make_vc("f", VcKind::DivisionByZero),
            make_vc("g", VcKind::Postcondition),
        ];
        map.register_all(&vcs);
        assert_eq!(map.total_vcs(), 3);
    }

    #[test]
    fn test_coverage_map_uncovered_vc_ids() {
        let mut map = CoverageMap::new();
        let vc1 = VcId::new("f", "overflow", 0);
        let vc2 = VcId::new("g", "div_zero", 0);
        map.register_vc(vc1.clone());
        map.register_vc(vc2.clone());
        map.record_coverage("test_a", vc1);

        let uncovered = map.uncovered_vc_ids();
        assert_eq!(uncovered.len(), 1);
        assert_eq!(uncovered[0], &vc2);
    }

    #[test]
    fn test_coverage_map_unknown_test() {
        let map = CoverageMap::new();
        assert!(map.vcs_for_test("nonexistent").is_none());
    }

    #[test]
    fn test_coverage_map_unknown_vc() {
        let map = CoverageMap::new();
        let vc_id = VcId::new("f", "overflow", 0);
        assert!(map.tests_for_vc(&vc_id).is_none());
    }

    // -----------------------------------------------------------------------
    // CoverageAnalysis
    // -----------------------------------------------------------------------

    #[test]
    fn test_analysis_empty_map() {
        let map = CoverageMap::new();
        let analysis = CoverageAnalysis::from_map(&map);
        assert!((analysis.vc_coverage - 1.0).abs() < f64::EPSILON);
        assert!((analysis.kind_coverage - 1.0).abs() < f64::EPSILON);
        assert!((analysis.function_coverage - 1.0).abs() < f64::EPSILON);
        assert_eq!(analysis.total_vcs, 0);
    }

    #[test]
    fn test_analysis_partial_coverage() {
        let mut map = CoverageMap::new();
        map.register_vc(VcId::new("f", "overflow", 0));
        map.register_vc(VcId::new("f", "div_zero", 0));
        map.register_vc(VcId::new("g", "overflow", 0));

        map.record_coverage("test_a", VcId::new("f", "overflow", 0));

        let analysis = CoverageAnalysis::from_map(&map);
        assert!((analysis.vc_coverage - 1.0 / 3.0).abs() < 0.01);
        assert_eq!(analysis.total_vcs, 3);
        assert_eq!(analysis.covered_vcs, 1);
        assert_eq!(analysis.uncovered_vcs, 2);
        // kind coverage: "overflow" is covered, "div_zero" is not -> 1/2
        assert!((analysis.kind_coverage - 0.5).abs() < 0.01);
        // function coverage: "f" covered, "g" not -> 1/2
        assert!((analysis.function_coverage - 0.5).abs() < 0.01);
    }

    #[test]
    fn test_analysis_full_coverage() {
        let mut map = CoverageMap::new();
        let vc1 = VcId::new("f", "overflow", 0);
        let vc2 = VcId::new("g", "div_zero", 0);
        map.register_vc(vc1.clone());
        map.register_vc(vc2.clone());
        map.record_coverage("test_a", vc1);
        map.record_coverage("test_b", vc2);

        let analysis = CoverageAnalysis::from_map(&map);
        assert!((analysis.vc_coverage - 1.0).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // Gap analysis
    // -----------------------------------------------------------------------

    #[test]
    fn test_gap_analysis_no_gaps() {
        let mut map = CoverageMap::new();
        let vc = VcId::new("f", "overflow", 0);
        map.register_vc(vc.clone());
        map.record_coverage("test_a", vc);

        let gaps = gap_analysis(&map);
        assert!(gaps.is_empty());
    }

    #[test]
    fn test_gap_analysis_with_gaps() {
        let mut map = CoverageMap::new();
        map.register_vc(VcId::new("f", "overflow", 0));
        map.register_vc(VcId::new("g", "div_zero", 0));
        map.record_coverage("test_a", VcId::new("f", "overflow", 0));

        let gaps = gap_analysis(&map);
        assert_eq!(gaps.len(), 1);
        assert_eq!(gaps[0].vc_id.function, "g");
        assert!(gaps[0].description.contains("div_zero"));
    }

    #[test]
    fn test_gap_analysis_empty_map() {
        let map = CoverageMap::new();
        let gaps = gap_analysis(&map);
        assert!(gaps.is_empty());
    }

    // -----------------------------------------------------------------------
    // Coverage report
    // -----------------------------------------------------------------------

    #[test]
    fn test_coverage_report_per_function() {
        let mut map = CoverageMap::new();
        map.register_vc(VcId::new("f", "overflow", 0));
        map.register_vc(VcId::new("f", "div_zero", 0));
        map.register_vc(VcId::new("g", "postcondition", 0));
        map.record_coverage("test_a", VcId::new("f", "overflow", 0));

        let report = coverage_report(&map);
        assert_eq!(report.per_function.len(), 2);

        let f_cov = &report.per_function["f"];
        assert_eq!(f_cov.total, 2);
        assert_eq!(f_cov.covered, 1);
        assert_eq!(f_cov.uncovered_kinds, vec!["div_zero"]);

        let g_cov = &report.per_function["g"];
        assert_eq!(g_cov.total, 1);
        assert_eq!(g_cov.covered, 0);
        assert_eq!(g_cov.uncovered_kinds, vec!["postcondition"]);
    }

    // -----------------------------------------------------------------------
    // Suggest tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_suggest_tests_empty_gaps() {
        let suggestions = suggest_tests(&[]);
        assert!(suggestions.is_empty());
    }

    #[test]
    fn test_suggest_tests_generates_placeholders() {
        let gaps = vec![
            CoverageGap {
                vc_id: VcId::new("math::add", "overflow", 0),
                description: "No tests cover overflow in math::add".into(),
            },
            CoverageGap {
                vc_id: VcId::new("buf::get", "index_out_of_bounds", 0),
                description: "No tests cover index_out_of_bounds in buf::get".into(),
            },
        ];

        let suggestions = suggest_tests(&gaps);
        assert_eq!(suggestions.len(), 2);

        assert!(suggestions[0].name.contains("math__add"));
        assert!(suggestions[0].name.contains("overflow"));
        assert!(suggestions[0].code.contains("#[test]"));
        assert!(suggestions[0].code.contains("math::add"));

        assert!(suggestions[1].name.contains("buf__get"));
        assert!(suggestions[1].name.contains("index_out_of_bounds"));
    }

    // -----------------------------------------------------------------------
    // Coverage goals
    // -----------------------------------------------------------------------

    #[test]
    fn test_progress_all_vcs_empty() {
        let map = CoverageMap::new();
        let progress = progress_toward_goal(&map, &CoverageGoal::AllVCs);
        assert!((progress - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_progress_all_vcs_partial() {
        let mut map = CoverageMap::new();
        map.register_vc(VcId::new("f", "overflow", 0));
        map.register_vc(VcId::new("g", "div_zero", 0));
        map.record_coverage("test_a", VcId::new("f", "overflow", 0));

        let progress = progress_toward_goal(&map, &CoverageGoal::AllVCs);
        assert!((progress - 0.5).abs() < 0.01);
    }

    #[test]
    fn test_progress_all_vcs_full() {
        let mut map = CoverageMap::new();
        let vc = VcId::new("f", "overflow", 0);
        map.register_vc(vc.clone());
        map.record_coverage("test_a", vc);

        let progress = progress_toward_goal(&map, &CoverageGoal::AllVCs);
        assert!((progress - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_progress_all_kinds() {
        let mut map = CoverageMap::new();
        map.register_vc(VcId::new("f", "overflow", 0));
        map.register_vc(VcId::new("f", "div_zero", 0));
        map.register_vc(VcId::new("g", "overflow", 0));
        map.record_coverage("test_a", VcId::new("f", "overflow", 0));

        // "overflow" is covered, "div_zero" is not -> 50%
        let progress = progress_toward_goal(&map, &CoverageGoal::AllKinds);
        assert!((progress - 0.5).abs() < 0.01);
    }

    #[test]
    fn test_progress_all_functions() {
        let mut map = CoverageMap::new();
        map.register_vc(VcId::new("f", "overflow", 0));
        map.register_vc(VcId::new("g", "div_zero", 0));
        map.record_coverage("test_a", VcId::new("f", "overflow", 0));

        let progress = progress_toward_goal(&map, &CoverageGoal::AllFunctions);
        assert!((progress - 0.5).abs() < 0.01);
    }

    #[test]
    fn test_progress_targeted_empty_targets() {
        let map = CoverageMap::new();
        let progress = progress_toward_goal(&map, &CoverageGoal::Targeted(vec![]));
        assert!((progress - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_progress_targeted_partial() {
        let mut map = CoverageMap::new();
        map.register_vc(VcId::new("f", "overflow", 0));
        map.register_vc(VcId::new("f", "div_zero", 0));
        map.register_vc(VcId::new("g", "postcondition", 0));
        map.record_coverage("test_a", VcId::new("f", "overflow", 0));

        // Target only overflow and div_zero -> 1 out of 2
        let progress = progress_toward_goal(
            &map,
            &CoverageGoal::Targeted(vec!["overflow".into(), "div_zero".into()]),
        );
        assert!((progress - 0.5).abs() < 0.01);
    }

    #[test]
    fn test_progress_targeted_no_matching_vcs() {
        let mut map = CoverageMap::new();
        map.register_vc(VcId::new("f", "overflow", 0));

        let progress = progress_toward_goal(
            &map,
            &CoverageGoal::Targeted(vec!["nonexistent".into()]),
        );
        assert!((progress - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_coverage_goal_equality() {
        assert_eq!(CoverageGoal::AllVCs, CoverageGoal::AllVCs);
        assert_ne!(CoverageGoal::AllVCs, CoverageGoal::AllKinds);
        assert_eq!(
            CoverageGoal::Targeted(vec!["a".into()]),
            CoverageGoal::Targeted(vec!["a".into()]),
        );
    }
}
