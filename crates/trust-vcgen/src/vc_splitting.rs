// trust-vcgen/vc_splitting.rs: VC splitting strategies (#344)
//
// Breaks large verification conditions into independently-verifiable fragments.
// Supports multiple splitting strategies (conjunct-based, variable-based,
// path-based, depth-based) and fragment result merging.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Strategy for splitting a VC into fragments.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum SplitStrategy {
    /// Split by top-level conjuncts (AND clauses).
    ByConjunct,
    /// Split by variable independence (disjoint variable sets).
    ByVariable,
    /// Split by execution path.
    ByPath,
    /// Split by formula depth (max nesting).
    ByDepth(usize),
    /// Custom named strategy for extensibility.
    Custom(String),
}

/// A fragment of a split verification condition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VcFragment {
    /// Unique identifier within a split result.
    pub id: usize,
    /// The formula text for this fragment.
    pub formula: String,
    /// Variables referenced in this fragment.
    pub variables: Vec<String>,
    /// IDs of other fragments this one depends on.
    pub dependencies: Vec<usize>,
}

/// Result of splitting a VC.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SplitResult {
    /// The independent fragments.
    pub fragments: Vec<VcFragment>,
    /// Which strategy was used.
    pub strategy_used: SplitStrategy,
    /// Size of the original VC (character count).
    pub original_size: usize,
}

/// Configuration for the VC splitter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SplitConfig {
    /// Maximum size (character count) for a single fragment.
    pub max_fragment_size: usize,
    /// Minimum number of fragments to produce.
    pub min_fragments: usize,
    /// Whether to preserve shared sub-expressions across fragments.
    pub preserve_sharing: bool,
}

impl Default for SplitConfig {
    fn default() -> Self {
        Self {
            max_fragment_size: 10_000,
            min_fragments: 1,
            preserve_sharing: true,
        }
    }
}

/// Result of verifying a single fragment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FragmentResult {
    /// Fragment was verified successfully.
    Verified,
    /// Fragment verification failed with a reason.
    Failed(String),
    /// Fragment verification result is unknown / timed out.
    Unknown,
}

// ---------------------------------------------------------------------------
// VcSplitter
// ---------------------------------------------------------------------------

/// Splits verification conditions into independently-verifiable fragments.
pub struct VcSplitter {
    config: SplitConfig,
}

impl VcSplitter {
    /// Create a new splitter with the given configuration.
    #[must_use]
    pub fn new(config: SplitConfig) -> Self {
        Self { config }
    }

    /// Split a VC string using the specified strategy.
    #[must_use]
    pub fn split_vc(&self, vc: &str, strategy: &SplitStrategy) -> SplitResult {
        let original_size = vc.len();
        let fragments = match strategy {
            SplitStrategy::ByConjunct => self.split_by_conjuncts_to_fragments(vc),
            SplitStrategy::ByVariable => self.split_by_variables(vc),
            SplitStrategy::ByPath => self.split_by_paths(vc),
            SplitStrategy::ByDepth(max_depth) => self.split_by_depth(vc, *max_depth),
            SplitStrategy::Custom(_) => {
                // Custom strategies return the VC as a single fragment.
                vec![VcFragment {
                    id: 0,
                    formula: vc.to_string(),
                    variables: extract_variables(vc),
                    dependencies: vec![],
                }]
            }
        };

        SplitResult {
            fragments,
            strategy_used: strategy.clone(),
            original_size,
        }
    }

    /// Choose the optimal splitting strategy and apply it.
    #[must_use]
    pub fn optimal_split(&self, vc: &str) -> SplitResult {
        // Try conjunct splitting first (most common and effective).
        let conjunct_result = self.split_vc(vc, &SplitStrategy::ByConjunct);
        if conjunct_result.fragments.len() >= self.config.min_fragments
            && conjunct_result.fragments.len() > 1
        {
            return conjunct_result;
        }

        // Try variable-based splitting.
        let var_result = self.split_vc(vc, &SplitStrategy::ByVariable);
        if var_result.fragments.len() >= self.config.min_fragments && var_result.fragments.len() > 1
        {
            return var_result;
        }

        // Fall back to path splitting.
        let path_result = self.split_vc(vc, &SplitStrategy::ByPath);
        if path_result.fragments.len() >= self.config.min_fragments
            && path_result.fragments.len() > 1
        {
            return path_result;
        }

        // Last resort: depth-based splitting.
        self.split_vc(vc, &SplitStrategy::ByDepth(3))
    }

    /// Estimate difficulty of verifying a fragment (heuristic score).
    ///
    /// Higher values indicate harder fragments. Based on formula size
    /// and variable count.
    #[must_use]
    pub fn estimate_difficulty(&self, fragment: &VcFragment) -> usize {
        let size_score = fragment.formula.len();
        let var_score = fragment.variables.len() * 10;
        let dep_score = fragment.dependencies.len() * 5;
        size_score + var_score + dep_score
    }

    /// Merge individual fragment results into an overall result.
    ///
    /// All fragments must be `Verified` for the overall result to be `Verified`.
    /// Any `Failed` result makes the whole result `Failed`.
    /// Otherwise the result is `Unknown`.
    #[must_use]
    pub fn merge_results(&self, results: &[(usize, FragmentResult)]) -> FragmentResult {
        if results.is_empty() {
            return FragmentResult::Unknown;
        }

        let mut has_unknown = false;
        for (_, result) in results {
            match result {
                FragmentResult::Failed(reason) => {
                    return FragmentResult::Failed(reason.clone());
                }
                FragmentResult::Unknown => {
                    has_unknown = true;
                }
                FragmentResult::Verified => {}
            }
        }

        if has_unknown {
            FragmentResult::Unknown
        } else {
            FragmentResult::Verified
        }
    }

    /// Check whether all fragments in a split were successfully verified.
    ///
    /// Returns `true` only if every fragment has a `Verified` result
    /// and all fragment IDs in the split are covered.
    #[must_use]
    pub fn reassemble_proof(
        &self,
        results: &[(usize, FragmentResult)],
        split: &SplitResult,
    ) -> bool {
        if results.len() != split.fragments.len() {
            return false;
        }

        let result_ids: FxHashSet<usize> = results.iter().map(|(id, _)| *id).collect();
        let fragment_ids: FxHashSet<usize> = split.fragments.iter().map(|f| f.id).collect();

        if result_ids != fragment_ids {
            return false;
        }

        results.iter().all(|(_, r)| matches!(r, FragmentResult::Verified))
    }

    /// Split a VC string by top-level conjuncts (AND connectives).
    ///
    /// Splits on ` && ` at the top level (not inside parentheses).
    #[must_use]
    pub fn split_by_conjuncts(&self, vc: &str) -> Vec<String> {
        split_top_level_and(vc)
    }

    // --- Internal helpers ---

    fn split_by_conjuncts_to_fragments(&self, vc: &str) -> Vec<VcFragment> {
        let conjuncts = split_top_level_and(vc);
        conjuncts
            .into_iter()
            .enumerate()
            .map(|(i, formula)| {
                let variables = extract_variables(&formula);
                VcFragment {
                    id: i,
                    formula,
                    variables,
                    dependencies: vec![],
                }
            })
            .collect()
    }

    fn split_by_variables(&self, vc: &str) -> Vec<VcFragment> {
        let conjuncts = split_top_level_and(vc);
        if conjuncts.len() <= 1 {
            return vec![VcFragment {
                id: 0,
                formula: vc.to_string(),
                variables: extract_variables(vc),
                dependencies: vec![],
            }];
        }

        // Group conjuncts by shared variables.
        let conjunct_vars: Vec<FxHashSet<String>> = conjuncts
            .iter()
            .map(|c| extract_variables(c).into_iter().collect())
            .collect();

        let groups = group_by_shared_variables(&conjuncts, &conjunct_vars);
        groups
            .into_iter()
            .enumerate()
            .map(|(i, formula)| {
                let variables = extract_variables(&formula);
                VcFragment {
                    id: i,
                    formula,
                    variables,
                    dependencies: vec![],
                }
            })
            .collect()
    }

    fn split_by_paths(&self, vc: &str) -> Vec<VcFragment> {
        // Split on top-level OR (disjunction = paths).
        let paths = split_top_level_or(vc);
        paths
            .into_iter()
            .enumerate()
            .map(|(i, formula)| {
                let variables = extract_variables(&formula);
                VcFragment {
                    id: i,
                    formula,
                    variables,
                    dependencies: vec![],
                }
            })
            .collect()
    }

    fn split_by_depth(&self, vc: &str, max_depth: usize) -> Vec<VcFragment> {
        let parts = split_at_depth(vc, max_depth);
        parts
            .into_iter()
            .enumerate()
            .map(|(i, formula)| {
                let variables = extract_variables(&formula);
                // Depth-split fragments depend on their predecessor.
                let dependencies = if i > 0 { vec![i - 1] } else { vec![] };
                VcFragment {
                    id: i,
                    formula,
                    variables,
                    dependencies,
                }
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Free functions
// ---------------------------------------------------------------------------

/// Extract variable names from a formula string.
///
/// Identifies identifiers that look like variable names (alphabetic start,
/// alphanumeric/underscore body, not keywords).
fn extract_variables(formula: &str) -> Vec<String> {
    let keywords: FxHashSet<&str> = [
        "and", "or", "not", "true", "false", "forall", "exists", "let", "if", "then", "else",
        "implies", "iff",
    ]
    .into_iter()
    .collect();

    let mut vars = Vec::new();
    let mut seen = FxHashSet::default();
    let mut chars = formula.chars().peekable();

    while let Some(&ch) = chars.peek() {
        if ch.is_alphabetic() || ch == '_' {
            let mut ident = String::new();
            while let Some(&c) = chars.peek() {
                if c.is_alphanumeric() || c == '_' {
                    ident.push(c);
                    chars.next();
                } else {
                    break;
                }
            }
            if !keywords.contains(ident.as_str()) && !seen.contains(&ident) {
                seen.insert(ident.clone());
                vars.push(ident);
            }
        } else {
            chars.next();
        }
    }

    vars
}

/// Split a formula string on top-level ` && ` (not inside parentheses).
fn split_top_level_and(formula: &str) -> Vec<String> {
    split_top_level(formula, " && ")
}

/// Split a formula string on top-level ` || ` (not inside parentheses).
fn split_top_level_or(formula: &str) -> Vec<String> {
    split_top_level(formula, " || ")
}

/// Generic top-level split on a delimiter, respecting parenthesis nesting.
fn split_top_level(formula: &str, delimiter: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut depth: usize = 0;
    let bytes = formula.as_bytes();
    let delim_bytes = delimiter.as_bytes();
    let delim_len = delim_bytes.len();
    let mut i = 0;

    while i < bytes.len() {
        if bytes[i] == b'(' {
            depth += 1;
            current.push('(');
            i += 1;
        } else if bytes[i] == b')' {
            depth = depth.saturating_sub(1);
            current.push(')');
            i += 1;
        } else if depth == 0
            && i + delim_len <= bytes.len()
            && &bytes[i..i + delim_len] == delim_bytes
        {
            let trimmed = current.trim().to_string();
            if !trimmed.is_empty() {
                parts.push(trimmed);
            }
            current.clear();
            i += delim_len;
        } else {
            current.push(bytes[i] as char);
            i += 1;
        }
    }

    let trimmed = current.trim().to_string();
    if !trimmed.is_empty() {
        parts.push(trimmed);
    }

    if parts.is_empty() {
        parts.push(formula.to_string());
    }

    parts
}

/// Group conjuncts by shared variables using union-find.
fn group_by_shared_variables(
    conjuncts: &[String],
    conjunct_vars: &[FxHashSet<String>],
) -> Vec<String> {
    let n = conjuncts.len();
    let mut parent: Vec<usize> = (0..n).collect();

    fn find(parent: &mut [usize], x: usize) -> usize {
        if parent[x] != x {
            parent[x] = find(parent, parent[x]);
        }
        parent[x]
    }

    fn union(parent: &mut [usize], a: usize, b: usize) {
        let ra = find(parent, a);
        let rb = find(parent, b);
        if ra != rb {
            parent[rb] = ra;
        }
    }

    // Union conjuncts that share variables.
    for i in 0..n {
        for j in (i + 1)..n {
            if !conjunct_vars[i].is_disjoint(&conjunct_vars[j]) {
                union(&mut parent, i, j);
            }
        }
    }

    // Group by root.
    let mut groups: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
    for i in 0..n {
        let root = find(&mut parent, i);
        groups.entry(root).or_default().push(i);
    }

    groups
        .into_values()
        .map(|indices| {
            indices
                .iter()
                .map(|&i| conjuncts[i].as_str())
                .collect::<Vec<_>>()
                .join(" && ")
        })
        .collect()
}

/// Split a formula at a given nesting depth.
fn split_at_depth(formula: &str, max_depth: usize) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut depth: usize = 0;

    for ch in formula.chars() {
        if ch == '(' {
            depth += 1;
            if depth > max_depth && !current.trim().is_empty() {
                parts.push(current.trim().to_string());
                current.clear();
            }
            current.push(ch);
        } else if ch == ')' {
            current.push(ch);
            depth = depth.saturating_sub(1);
            if depth < max_depth && !current.trim().is_empty() {
                parts.push(current.trim().to_string());
                current.clear();
            }
        } else {
            current.push(ch);
        }
    }

    let remaining = current.trim().to_string();
    if !remaining.is_empty() {
        parts.push(remaining);
    }

    if parts.is_empty() {
        parts.push(formula.to_string());
    }

    parts
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn default_splitter() -> VcSplitter {
        VcSplitter::new(SplitConfig::default())
    }

    #[test]
    fn test_split_by_conjuncts_basic() {
        let splitter = default_splitter();
        let parts = splitter.split_by_conjuncts("a > 0 && b > 0 && c > 0");
        assert_eq!(parts, vec!["a > 0", "b > 0", "c > 0"]);
    }

    #[test]
    fn test_split_by_conjuncts_preserves_parens() {
        let splitter = default_splitter();
        let parts = splitter.split_by_conjuncts("(a && b) && c");
        assert_eq!(parts, vec!["(a && b)", "c"]);
    }

    #[test]
    fn test_split_by_conjuncts_single_clause() {
        let splitter = default_splitter();
        let parts = splitter.split_by_conjuncts("x > 0");
        assert_eq!(parts, vec!["x > 0"]);
    }

    #[test]
    fn test_split_vc_by_conjunct_strategy() {
        let splitter = default_splitter();
        let result = splitter.split_vc("a > 0 && b < 10", &SplitStrategy::ByConjunct);
        assert_eq!(result.fragments.len(), 2);
        assert_eq!(result.strategy_used, SplitStrategy::ByConjunct);
        assert_eq!(result.original_size, "a > 0 && b < 10".len());
        assert_eq!(result.fragments[0].formula, "a > 0");
        assert_eq!(result.fragments[1].formula, "b < 10");
    }

    #[test]
    fn test_split_vc_by_variable_independent() {
        let splitter = default_splitter();
        let result = splitter.split_vc("a > 0 && b < 10", &SplitStrategy::ByVariable);
        // a and b are independent variables, should split into 2 groups.
        assert_eq!(result.fragments.len(), 2);
        assert_eq!(result.strategy_used, SplitStrategy::ByVariable);
    }

    #[test]
    fn test_split_vc_by_variable_shared() {
        let splitter = default_splitter();
        let result = splitter.split_vc("a > 0 && a < 10", &SplitStrategy::ByVariable);
        // Both conjuncts share variable 'a', so they stay together.
        assert_eq!(result.fragments.len(), 1);
    }

    #[test]
    fn test_split_vc_by_path() {
        let splitter = default_splitter();
        let result = splitter.split_vc("a > 0 || b < 10", &SplitStrategy::ByPath);
        assert_eq!(result.fragments.len(), 2);
        assert_eq!(result.fragments[0].formula, "a > 0");
        assert_eq!(result.fragments[1].formula, "b < 10");
    }

    #[test]
    fn test_split_vc_custom_strategy() {
        let splitter = default_splitter();
        let result = splitter.split_vc("a && b", &SplitStrategy::Custom("test".to_string()));
        // Custom strategy returns the whole VC as one fragment.
        assert_eq!(result.fragments.len(), 1);
        assert_eq!(result.fragments[0].formula, "a && b");
    }

    #[test]
    fn test_estimate_difficulty_scales_with_size() {
        let splitter = default_splitter();
        let small = VcFragment {
            id: 0,
            formula: "x > 0".to_string(),
            variables: vec!["x".to_string()],
            dependencies: vec![],
        };
        let large = VcFragment {
            id: 1,
            formula: "x > 0 && y > 0 && z > 0 && w > 0".to_string(),
            variables: vec![
                "x".to_string(),
                "y".to_string(),
                "z".to_string(),
                "w".to_string(),
            ],
            dependencies: vec![0],
        };
        assert!(splitter.estimate_difficulty(&large) > splitter.estimate_difficulty(&small));
    }

    #[test]
    fn test_merge_results_all_verified() {
        let splitter = default_splitter();
        let results = vec![
            (0, FragmentResult::Verified),
            (1, FragmentResult::Verified),
        ];
        assert_eq!(splitter.merge_results(&results), FragmentResult::Verified);
    }

    #[test]
    fn test_merge_results_one_failed() {
        let splitter = default_splitter();
        let results = vec![
            (0, FragmentResult::Verified),
            (1, FragmentResult::Failed("timeout".to_string())),
        ];
        let merged = splitter.merge_results(&results);
        assert!(matches!(merged, FragmentResult::Failed(reason) if reason == "timeout"));
    }

    #[test]
    fn test_merge_results_one_unknown() {
        let splitter = default_splitter();
        let results = vec![
            (0, FragmentResult::Verified),
            (1, FragmentResult::Unknown),
        ];
        assert_eq!(splitter.merge_results(&results), FragmentResult::Unknown);
    }

    #[test]
    fn test_merge_results_empty() {
        let splitter = default_splitter();
        assert_eq!(
            splitter.merge_results(&[]),
            FragmentResult::Unknown
        );
    }

    #[test]
    fn test_reassemble_proof_success() {
        let splitter = default_splitter();
        let split = splitter.split_vc("a > 0 && b > 0", &SplitStrategy::ByConjunct);
        let results = vec![
            (0, FragmentResult::Verified),
            (1, FragmentResult::Verified),
        ];
        assert!(splitter.reassemble_proof(&results, &split));
    }

    #[test]
    fn test_reassemble_proof_failure() {
        let splitter = default_splitter();
        let split = splitter.split_vc("a > 0 && b > 0", &SplitStrategy::ByConjunct);
        let results = vec![
            (0, FragmentResult::Verified),
            (1, FragmentResult::Failed("cex found".to_string())),
        ];
        assert!(!splitter.reassemble_proof(&results, &split));
    }

    #[test]
    fn test_reassemble_proof_missing_fragment() {
        let splitter = default_splitter();
        let split = splitter.split_vc("a > 0 && b > 0", &SplitStrategy::ByConjunct);
        // Only one result for two fragments.
        let results = vec![(0, FragmentResult::Verified)];
        assert!(!splitter.reassemble_proof(&results, &split));
    }

    #[test]
    fn test_optimal_split_prefers_conjunct() {
        let splitter = VcSplitter::new(SplitConfig {
            min_fragments: 2,
            ..SplitConfig::default()
        });
        let result = splitter.optimal_split("x > 0 && y < 10");
        assert_eq!(result.strategy_used, SplitStrategy::ByConjunct);
        assert_eq!(result.fragments.len(), 2);
    }

    #[test]
    fn test_extract_variables_filters_keywords() {
        let vars = extract_variables("forall x. (x > 0 and y < 10)");
        assert!(vars.contains(&"x".to_string()));
        assert!(vars.contains(&"y".to_string()));
        assert!(!vars.contains(&"forall".to_string()));
        assert!(!vars.contains(&"and".to_string()));
    }

    #[test]
    fn test_fragment_dependencies_in_depth_split() {
        let splitter = default_splitter();
        let result = splitter.split_vc("((a > 0))", &SplitStrategy::ByDepth(1));
        // Depth split fragments after the first should depend on the predecessor.
        for frag in &result.fragments {
            if frag.id > 0 {
                assert!(
                    frag.dependencies.contains(&(frag.id - 1)),
                    "fragment {} should depend on {}",
                    frag.id,
                    frag.id - 1,
                );
            }
        }
    }

    #[test]
    fn test_split_config_default() {
        let config = SplitConfig::default();
        assert_eq!(config.max_fragment_size, 10_000);
        assert_eq!(config.min_fragments, 1);
        assert!(config.preserve_sharing);
    }
}
