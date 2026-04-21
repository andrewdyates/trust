// trust-cache/impact_analysis.rs: Change impact analysis for incremental verification
//
// Given a code change (diff), determines which VCs need re-verification and
// which cached proofs remain valid. Integrates with DependencyTracker from
// invalidation.rs for transitive dependency propagation.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use trust_types::fx::{FxHashMap, FxHashSet};
use std::fmt;
use std::time::{SystemTime, UNIX_EPOCH};

use crate::invalidation::DependencyTracker;

// ---------------------------------------------------------------------------
// ChangeKind + ChangeEntry
// ---------------------------------------------------------------------------

/// The kind of source-level change detected.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ChangeKind {
    /// Function body was modified.
    FunctionBody,
    /// Function signature (params/return type) was modified.
    FunctionSignature,
    /// A type definition (struct/enum/trait) was modified.
    TypeDefinition,
    /// A spec (requires/ensures/invariant) was modified.
    SpecChange,
    /// A definition was added (new function/type).
    Added,
    /// A definition was removed.
    Removed,
}

impl fmt::Display for ChangeKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FunctionBody => write!(f, "function body"),
            Self::FunctionSignature => write!(f, "function signature"),
            Self::TypeDefinition => write!(f, "type definition"),
            Self::SpecChange => write!(f, "spec change"),
            Self::Added => write!(f, "added"),
            Self::Removed => write!(f, "removed"),
        }
    }
}

/// A single changed definition within a changeset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChangeEntry {
    /// The def_path of the changed definition (e.g. `crate::module::function`).
    pub def_path: String,
    /// What kind of change was detected.
    pub kind: ChangeKind,
    /// Optional human-readable description of the change.
    pub description: String,
}

// ---------------------------------------------------------------------------
// ChangeSet
// ---------------------------------------------------------------------------

/// A set of changes detected between two versions of a codebase.
///
/// Constructed by parsing a git diff, AST diff, or programmatically adding
/// entries. Each entry identifies a changed function/type by its def_path.
#[derive(Debug, Clone, Default)]
pub struct ChangeSet {
    entries: Vec<ChangeEntry>,
    /// Quick lookup by def_path.
    by_path: FxHashMap<String, Vec<usize>>,
}

impl ChangeSet {
    /// Create an empty changeset.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a change entry to this changeset.
    pub fn add(&mut self, def_path: &str, kind: ChangeKind, description: &str) {
        let idx = self.entries.len();
        self.entries.push(ChangeEntry {
            def_path: def_path.to_string(),
            kind,
            description: description.to_string(),
        });
        self.by_path.entry(def_path.to_string()).or_default().push(idx);
    }

    /// Add a function body change.
    pub fn add_function_body_change(&mut self, def_path: &str) {
        self.add(def_path, ChangeKind::FunctionBody, "function body modified");
    }

    /// Add a type definition change.
    pub fn add_type_change(&mut self, def_path: &str) {
        self.add(def_path, ChangeKind::TypeDefinition, "type definition modified");
    }

    /// Add a spec change (requires/ensures/invariant).
    pub fn add_spec_change(&mut self, def_path: &str) {
        self.add(def_path, ChangeKind::SpecChange, "specification modified");
    }

    /// Add a new definition.
    pub fn add_added(&mut self, def_path: &str) {
        self.add(def_path, ChangeKind::Added, "definition added");
    }

    /// Add a removed definition.
    pub fn add_removed(&mut self, def_path: &str) {
        self.add(def_path, ChangeKind::Removed, "definition removed");
    }

    /// All change entries in this changeset.
    #[must_use]
    pub fn entries(&self) -> &[ChangeEntry] {
        &self.entries
    }

    /// All unique def_paths that have changes.
    #[must_use]
    pub fn changed_paths(&self) -> FxHashSet<String> {
        self.by_path.keys().cloned().collect()
    }

    /// Get all changes for a specific def_path.
    #[must_use]
    pub fn changes_for(&self, def_path: &str) -> Vec<&ChangeEntry> {
        self.by_path
            .get(def_path)
            .map(|indices| indices.iter().map(|&i| &self.entries[i]).collect())
            .unwrap_or_default()
    }

    /// Whether a specific def_path has any changes.
    #[must_use]
    pub fn is_changed(&self, def_path: &str) -> bool {
        self.by_path.contains_key(def_path)
    }

    /// Whether this changeset is empty (no changes detected).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Number of change entries (a single def_path may have multiple entries).
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Number of unique changed definitions.
    #[must_use]
    pub fn changed_count(&self) -> usize {
        self.by_path.len()
    }

    /// Parse a simplified diff format into a changeset.
    ///
    /// Each line should be `<+/- /M/S> <def_path>`:
    /// - `+ crate::foo` means `foo` was added
    /// - `- crate::bar` means `bar` was removed
    /// - `M crate::baz` means `baz` body was modified
    /// - `S crate::qux` means `qux` spec was modified
    /// - `T crate::MyType` means type `MyType` was modified
    ///
    /// Lines that don't match are silently skipped.
    #[must_use]
    pub fn from_diff_lines(lines: &str) -> Self {
        let mut cs = Self::new();
        for line in lines.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let mut parts = line.splitn(2, ' ');
            let Some(prefix) = parts.next() else { continue };
            let Some(path) = parts.next() else { continue };
            let path = path.trim();
            match prefix {
                "+" => cs.add_added(path),
                "-" => cs.add_removed(path),
                "M" => cs.add_function_body_change(path),
                "S" => cs.add_spec_change(path),
                "T" => cs.add_type_change(path),
                _ => {} // skip unrecognized
            }
        }
        cs
    }
}

// ---------------------------------------------------------------------------
// DependencyGraph
// ---------------------------------------------------------------------------

/// A dependency graph that tracks which VCs depend on which definitions.
///
/// Wraps [`DependencyTracker`] from invalidation.rs and adds VC-level
/// dependency tracking. Each VC is associated with a set of definitions
/// (functions, types) it depends on.
#[derive(Debug, Clone, Default)]
pub struct DependencyGraph {
    /// Function-level dependencies (delegates to DependencyTracker).
    func_deps: DependencyTracker,
    /// VC -> set of def_paths it depends on.
    vc_deps: FxHashMap<String, FxHashSet<String>>,
    /// Reverse: def_path -> set of VCs that depend on it.
    def_to_vcs: FxHashMap<String, FxHashSet<String>>,
    /// Type -> set of functions that use this type.
    type_users: FxHashMap<String, FxHashSet<String>>,
}

impl DependencyGraph {
    /// Create an empty dependency graph.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Register that `function` calls `callee`.
    pub fn add_call_dependency(&mut self, function: &str, callee: &str) {
        self.func_deps.add_dependency(function, callee);
    }

    /// Register that `function` uses `type_path`.
    pub fn add_type_usage(&mut self, function: &str, type_path: &str) {
        self.type_users
            .entry(type_path.to_string())
            .or_default()
            .insert(function.to_string());
    }

    /// Register that a VC (by id) depends on a set of definitions.
    pub fn add_vc_dependency(&mut self, vc_id: &str, def_path: &str) {
        self.vc_deps
            .entry(vc_id.to_string())
            .or_default()
            .insert(def_path.to_string());
        self.def_to_vcs
            .entry(def_path.to_string())
            .or_default()
            .insert(vc_id.to_string());
    }

    /// Get all VCs that depend on a given definition.
    #[must_use]
    pub fn vcs_depending_on(&self, def_path: &str) -> FxHashSet<String> {
        self.def_to_vcs.get(def_path).cloned().unwrap_or_default()
    }

    /// Get all definitions that a VC depends on.
    #[must_use]
    pub fn vc_dependencies(&self, vc_id: &str) -> FxHashSet<String> {
        self.vc_deps.get(vc_id).cloned().unwrap_or_default()
    }

    /// Get all functions that use a type.
    #[must_use]
    pub fn type_users(&self, type_path: &str) -> FxHashSet<String> {
        self.type_users.get(type_path).cloned().unwrap_or_default()
    }

    /// Access the underlying function dependency tracker.
    #[must_use]
    pub fn func_deps(&self) -> &DependencyTracker {
        &self.func_deps
    }

    /// Mutable access to the underlying function dependency tracker.
    pub fn func_deps_mut(&mut self) -> &mut DependencyTracker {
        &mut self.func_deps
    }

    /// Number of tracked VCs.
    #[must_use]
    pub fn vc_count(&self) -> usize {
        self.vc_deps.len()
    }

    /// Number of tracked type-usage relationships.
    #[must_use]
    pub fn type_usage_count(&self) -> usize {
        self.type_users.values().map(|s| s.len()).sum()
    }

    /// Whether the graph is completely empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.func_deps.is_empty()
            && self.vc_deps.is_empty()
            && self.type_users.is_empty()
    }
}

// ---------------------------------------------------------------------------
// TransitiveClosure
// ---------------------------------------------------------------------------

/// Computes the transitive closure of impacted definitions.
///
/// Given a set of directly changed definitions and a dependency graph,
/// computes all definitions that are transitively affected. Handles both
/// function call chains and type-usage propagation.
pub struct TransitiveClosure;

impl TransitiveClosure {
    /// Compute all impacted def_paths given a set of directly changed paths.
    ///
    /// Returns the union of:
    /// 1. All directly changed paths
    /// 2. All transitive function dependents (callers of changed functions)
    /// 3. All functions that use a changed type (and their transitive dependents)
    #[must_use]
    pub fn compute(changed: &FxHashSet<String>, graph: &DependencyGraph) -> FxHashSet<String> {
        let mut impacted = changed.clone();
        let mut worklist: VecDeque<String> = changed.iter().cloned().collect();

        // Phase 1: Propagate through type-usage edges.
        // If a type changed, all functions using that type are impacted.
        let mut type_affected = FxHashSet::default();
        for path in changed {
            for user in graph.type_users(path) {
                if impacted.insert(user.clone()) {
                    type_affected.insert(user.clone());
                    worklist.push_back(user);
                }
            }
        }

        // Phase 2: Propagate through call-graph edges (transitive dependents).
        // Process all changed functions + type-affected functions.
        let seeds: FxHashSet<String> = changed.union(&type_affected).cloned().collect();
        for seed in &seeds {
            for dep in graph.func_deps.transitive_dependents(seed) {
                if impacted.insert(dep.clone()) {
                    worklist.push_back(dep);
                }
            }
        }

        impacted
    }
}

// ---------------------------------------------------------------------------
// ConservativeMode
// ---------------------------------------------------------------------------

/// Strategy for handling incomplete dependency information.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum ConservativeMode {
    /// Only re-verify what the dependency graph says is affected.
    /// Fast but may miss affected VCs if the graph is incomplete.
    #[default]
    Precise,
    /// Re-verify all VCs in modules that contain any changed definition.
    /// Over-approximates but safe when dependency info is incomplete.
    ModuleLevel,
    /// Re-verify everything. Maximum safety, minimum caching benefit.
    ReVerifyAll,
}

impl ConservativeMode {
    /// Whether this mode is conservative (may over-approximate).
    #[must_use]
    pub fn is_conservative(&self) -> bool {
        !matches!(self, Self::Precise)
    }
}

// ---------------------------------------------------------------------------
// ReVerifyReason
// ---------------------------------------------------------------------------

/// Why a VC or function needs re-verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReVerifyReason {
    /// The def_path being re-verified.
    pub def_path: String,
    /// Whether this is a direct change or transitive impact.
    pub is_direct: bool,
    /// The chain of dependencies from the root change to this definition.
    /// For direct changes: just [def_path].
    /// For transitive: [root_change, ..., def_path].
    pub chain: Vec<String>,
    /// Human-readable explanation.
    pub explanation: String,
}

// ---------------------------------------------------------------------------
// CacheDecision
// ---------------------------------------------------------------------------

/// Decision for a single VC: re-verify or use cached result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CacheDecision {
    /// Use the cached proof — nothing this VC depends on has changed.
    UseCached {
        /// The def_path of the function this VC belongs to.
        def_path: String,
    },
    /// Must re-verify — at least one dependency has changed.
    ReVerify {
        /// The def_path of the function this VC belongs to.
        def_path: String,
        /// Why this VC needs re-verification.
        reason: ReVerifyReason,
    },
}

impl CacheDecision {
    /// The def_path this decision applies to.
    #[must_use]
    pub fn def_path(&self) -> &str {
        match self {
            Self::UseCached { def_path } | Self::ReVerify { def_path, .. } => def_path,
        }
    }

    /// Whether this is a cache hit (use cached result).
    #[must_use]
    pub fn is_cached(&self) -> bool {
        matches!(self, Self::UseCached { .. })
    }

    /// Whether this needs re-verification.
    #[must_use]
    pub fn needs_reverify(&self) -> bool {
        matches!(self, Self::ReVerify { .. })
    }
}

// ---------------------------------------------------------------------------
// ImpactAnalyzer
// ---------------------------------------------------------------------------

/// Given a ChangeSet and DependencyGraph, computes the minimal set of
/// functions/VCs that need re-verification.
///
/// This is the main entry point for change impact analysis. It combines:
/// - Direct change detection (from ChangeSet)
/// - Transitive dependency propagation (from DependencyGraph + TransitiveClosure)
/// - Conservative mode handling (for incomplete dependency info)
/// - VC-level impact computation
pub struct ImpactAnalyzer {
    mode: ConservativeMode,
    /// All known functions (for module-level conservative mode).
    all_known_functions: FxHashSet<String>,
}

impl ImpactAnalyzer {
    /// Create a new ImpactAnalyzer with the given conservative mode.
    #[must_use]
    pub fn new(mode: ConservativeMode) -> Self {
        Self {
            mode,
            all_known_functions: FxHashSet::default(),
        }
    }

    /// Register all known functions (needed for ConservativeMode::ModuleLevel and ReVerifyAll).
    pub fn register_known_functions(&mut self, functions: impl IntoIterator<Item = String>) {
        self.all_known_functions = functions.into_iter().collect();
    }

    /// Compute the set of functions that need re-verification.
    ///
    /// Returns a set of def_paths and their reasons for re-verification.
    #[must_use]
    pub fn compute_impact(
        &self,
        changes: &ChangeSet,
        graph: &DependencyGraph,
    ) -> ImpactResult {
        match self.mode {
            ConservativeMode::ReVerifyAll => self.reverify_all(changes),
            ConservativeMode::ModuleLevel => self.module_level_impact(changes, graph),
            ConservativeMode::Precise => self.precise_impact(changes, graph),
        }
    }

    /// Precise mode: only re-verify what the dependency graph says is affected.
    fn precise_impact(&self, changes: &ChangeSet, graph: &DependencyGraph) -> ImpactResult {
        let changed_paths = changes.changed_paths();
        let all_impacted = TransitiveClosure::compute(&changed_paths, graph);

        let mut reverify = BTreeMap::new();
        let mut cached = BTreeSet::new();

        for path in &all_impacted {
            let is_direct = changed_paths.contains(path);
            let chain = if is_direct {
                vec![path.clone()]
            } else {
                self.find_impact_chain(path, &changed_paths, graph)
            };
            let explanation = if is_direct {
                let kinds: Vec<String> = changes
                    .changes_for(path)
                    .iter()
                    .map(|e| e.kind.to_string())
                    .collect();
                format!("directly changed: {}", kinds.join(", "))
            } else {
                format!("transitively affected via: {}", chain.join(" -> "))
            };
            reverify.insert(
                path.clone(),
                ReVerifyReason {
                    def_path: path.clone(),
                    is_direct,
                    chain,
                    explanation,
                },
            );
        }

        // Everything known but not impacted is cached.
        for path in &self.all_known_functions {
            if !all_impacted.contains(path) {
                cached.insert(path.clone());
            }
        }

        ImpactResult { reverify, cached, mode: self.mode }
    }

    /// Module-level mode: re-verify all functions in modules containing changes.
    fn module_level_impact(&self, changes: &ChangeSet, graph: &DependencyGraph) -> ImpactResult {
        let changed_paths = changes.changed_paths();
        // Extract module prefixes from changed paths.
        let changed_modules: FxHashSet<String> = changed_paths
            .iter()
            .filter_map(|p| {
                // Extract module prefix: "crate::module::func" -> "crate::module"
                p.rsplit_once("::").map(|(prefix, _)| prefix.to_string())
            })
            .collect();

        // Also include precise transitive impacts.
        let transitive = TransitiveClosure::compute(&changed_paths, graph);

        let mut reverify = BTreeMap::new();
        let mut cached = BTreeSet::new();

        for path in &self.all_known_functions {
            let in_changed_module = changed_modules
                .iter()
                .any(|module| path.starts_with(module));
            let in_transitive = transitive.contains(path);

            if in_changed_module || in_transitive {
                let is_direct = changed_paths.contains(path);
                let explanation = if is_direct {
                    "directly changed".to_string()
                } else if in_transitive {
                    "transitively affected".to_string()
                } else {
                    "conservative: same module as changed definition".to_string()
                };
                reverify.insert(
                    path.clone(),
                    ReVerifyReason {
                        def_path: path.clone(),
                        is_direct,
                        chain: vec![path.clone()],
                        explanation,
                    },
                );
            } else {
                cached.insert(path.clone());
            }
        }

        // Also include the changed paths themselves (they might not be in all_known_functions).
        for path in &changed_paths {
            if !reverify.contains_key(path) {
                reverify.insert(
                    path.clone(),
                    ReVerifyReason {
                        def_path: path.clone(),
                        is_direct: true,
                        chain: vec![path.clone()],
                        explanation: "directly changed".to_string(),
                    },
                );
            }
        }

        ImpactResult { reverify, cached, mode: self.mode }
    }

    /// Re-verify everything.
    fn reverify_all(&self, changes: &ChangeSet) -> ImpactResult {
        let changed_paths = changes.changed_paths();
        let mut reverify = BTreeMap::new();

        for path in &self.all_known_functions {
            let is_direct = changed_paths.contains(path);
            reverify.insert(
                path.clone(),
                ReVerifyReason {
                    def_path: path.clone(),
                    is_direct,
                    chain: vec![path.clone()],
                    explanation: if is_direct {
                        "directly changed".to_string()
                    } else {
                        "conservative: re-verify-all mode".to_string()
                    },
                },
            );
        }

        // Include changed paths not in known functions.
        for path in &changed_paths {
            if !reverify.contains_key(path) {
                reverify.insert(
                    path.clone(),
                    ReVerifyReason {
                        def_path: path.clone(),
                        is_direct: true,
                        chain: vec![path.clone()],
                        explanation: "directly changed".to_string(),
                    },
                );
            }
        }

        ImpactResult {
            reverify,
            cached: BTreeSet::new(),
            mode: self.mode,
        }
    }

    /// Find the impact chain from a changed root to the given path.
    fn find_impact_chain(
        &self,
        target: &str,
        changed_paths: &FxHashSet<String>,
        graph: &DependencyGraph,
    ) -> Vec<String> {
        // BFS from each changed path through reverse deps to find target.
        for root in changed_paths {
            if let Some(chain) = bfs_path(&graph.func_deps, root, target) {
                return chain;
            }
        }
        // Also check type-usage paths.
        for root in changed_paths {
            for user in graph.type_users(root) {
                if user == target {
                    return vec![root.clone(), target.to_string()];
                }
                if let Some(mut chain) = bfs_path(&graph.func_deps, &user, target) {
                    chain.insert(0, root.clone());
                    return chain;
                }
            }
        }
        // Fallback.
        vec![target.to_string()]
    }
}

/// BFS through reverse dependency edges from `start` to find `target`.
fn bfs_path(deps: &DependencyTracker, start: &str, target: &str) -> Option<Vec<String>> {
    if start == target {
        return Some(vec![start.to_string()]);
    }

    let mut visited: FxHashMap<String, String> = FxHashMap::default();
    let mut queue = VecDeque::new();
    queue.push_back(start.to_string());
    visited.insert(start.to_string(), String::new());

    while let Some(current) = queue.pop_front() {
        for dep in deps.direct_dependents(&current) {
            if visited.contains_key(&dep) {
                continue;
            }
            visited.insert(dep.clone(), current.clone());
            if dep == target {
                // Reconstruct path.
                let mut path = vec![target.to_string()];
                let mut node = target.to_string();
                while let Some(pred) = visited.get(&node) {
                    if pred.is_empty() {
                        break;
                    }
                    path.push(pred.clone());
                    node = pred.clone();
                }
                path.reverse();
                return Some(path);
            }
            queue.push_back(dep);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// ImpactResult
// ---------------------------------------------------------------------------

/// The result of an impact analysis: which functions need re-verification
/// and which can use cached results.
#[derive(Debug, Clone)]
pub struct ImpactResult {
    /// Functions that need re-verification, keyed by def_path.
    pub reverify: BTreeMap<String, ReVerifyReason>,
    /// Functions whose cached results remain valid.
    pub cached: BTreeSet<String>,
    /// Which conservative mode was used.
    pub mode: ConservativeMode,
}

impl ImpactResult {
    /// Number of functions that need re-verification.
    #[must_use]
    pub fn reverify_count(&self) -> usize {
        self.reverify.len()
    }

    /// Number of functions that can use cached results.
    #[must_use]
    pub fn cached_count(&self) -> usize {
        self.cached.len()
    }

    /// Whether a specific function needs re-verification.
    #[must_use]
    pub fn needs_reverify(&self, def_path: &str) -> bool {
        self.reverify.contains_key(def_path)
    }

    /// Whether a specific function can use its cached result.
    #[must_use]
    pub fn is_cached(&self, def_path: &str) -> bool {
        self.cached.contains(def_path)
    }

    /// Get the re-verification reason for a function.
    #[must_use]
    pub fn reason_for(&self, def_path: &str) -> Option<&ReVerifyReason> {
        self.reverify.get(def_path)
    }

    /// Generate a DeltaReport summarizing what was re-verified vs cached.
    #[must_use]
    pub fn to_delta_report(&self) -> DeltaReport {
        let reverified: Vec<DeltaEntry> = self
            .reverify
            .iter()
            .map(|(path, reason)| DeltaEntry {
                def_path: path.clone(),
                action: DeltaAction::ReVerify,
                justification: reason.explanation.clone(),
                is_direct_change: reason.is_direct,
            })
            .collect();

        let cached: Vec<DeltaEntry> = self
            .cached
            .iter()
            .map(|path| DeltaEntry {
                def_path: path.clone(),
                action: DeltaAction::UseCached,
                justification: "no dependency on any changed definition".to_string(),
                is_direct_change: false,
            })
            .collect();

        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);

        DeltaReport {
            entries: reverified.into_iter().chain(cached).collect(),
            total_reverified: self.reverify.len(),
            total_cached: self.cached.len(),
            mode: self.mode,
            timestamp,
        }
    }
}

// ---------------------------------------------------------------------------
// DeltaReport
// ---------------------------------------------------------------------------

/// What action was taken for a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeltaAction {
    /// The function was re-verified.
    ReVerify,
    /// The cached result was used.
    UseCached,
}

impl fmt::Display for DeltaAction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ReVerify => write!(f, "re-verify"),
            Self::UseCached => write!(f, "use-cached"),
        }
    }
}

/// A single entry in a delta report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeltaEntry {
    /// The def_path this entry is about.
    pub def_path: String,
    /// What action was taken.
    pub action: DeltaAction,
    /// Human-readable justification for the action.
    pub justification: String,
    /// Whether this was a directly changed definition.
    pub is_direct_change: bool,
}

/// A report of what was re-verified vs cached in an incremental verification run.
///
/// Provides a complete audit trail: for every function that was considered,
/// the report shows whether it was re-verified or cached and why.
#[derive(Debug, Clone)]
pub struct DeltaReport {
    /// All entries (re-verified first, then cached).
    pub entries: Vec<DeltaEntry>,
    /// Count of re-verified functions.
    pub total_reverified: usize,
    /// Count of cached functions.
    pub total_cached: usize,
    /// Which conservative mode was used.
    pub mode: ConservativeMode,
    /// Unix timestamp of when this report was generated.
    pub timestamp: u64,
}

impl DeltaReport {
    /// Total number of functions considered.
    #[must_use]
    pub fn total(&self) -> usize {
        self.total_reverified + self.total_cached
    }

    /// Cache hit rate as a fraction [0.0, 1.0].
    #[must_use]
    pub fn cache_hit_rate(&self) -> f64 {
        let total = self.total();
        if total == 0 {
            return 0.0;
        }
        self.total_cached as f64 / total as f64
    }

    /// Get all entries with a specific action.
    #[must_use]
    pub fn entries_with_action(&self, action: DeltaAction) -> Vec<&DeltaEntry> {
        self.entries.iter().filter(|e| e.action == action).collect()
    }

    /// Get all directly-changed entries.
    #[must_use]
    pub fn direct_changes(&self) -> Vec<&DeltaEntry> {
        self.entries.iter().filter(|e| e.is_direct_change).collect()
    }

    /// Format a human-readable summary.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "{} re-verified, {} cached ({:.0}% hit rate, mode: {:?})",
            self.total_reverified,
            self.total_cached,
            self.cache_hit_rate() * 100.0,
            self.mode,
        )
    }
}

impl fmt::Display for DeltaReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Delta Report ===")?;
        writeln!(f, "{}", self.summary())?;
        writeln!(f)?;

        let reverified = self.entries_with_action(DeltaAction::ReVerify);
        if !reverified.is_empty() {
            writeln!(f, "Re-verified ({}):", reverified.len())?;
            for entry in &reverified {
                let marker = if entry.is_direct_change { "*" } else { " " };
                writeln!(f, "  {marker} {} — {}", entry.def_path, entry.justification)?;
            }
            writeln!(f)?;
        }

        let cached = self.entries_with_action(DeltaAction::UseCached);
        if !cached.is_empty() {
            writeln!(f, "Cached ({}):", cached.len())?;
            for entry in &cached {
                writeln!(f, "    {} — {}", entry.def_path, entry.justification)?;
            }
        }

        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- ChangeSet tests --

    #[test]
    fn test_changeset_empty() {
        let cs = ChangeSet::new();
        assert!(cs.is_empty());
        assert_eq!(cs.len(), 0);
        assert_eq!(cs.changed_count(), 0);
        assert!(cs.changed_paths().is_empty());
    }

    #[test]
    fn test_changeset_add_entries() {
        let mut cs = ChangeSet::new();
        cs.add_function_body_change("crate::foo");
        cs.add_type_change("crate::MyType");
        cs.add_spec_change("crate::bar");

        assert_eq!(cs.len(), 3);
        assert_eq!(cs.changed_count(), 3);
        assert!(cs.is_changed("crate::foo"));
        assert!(cs.is_changed("crate::MyType"));
        assert!(cs.is_changed("crate::bar"));
        assert!(!cs.is_changed("crate::baz"));
    }

    #[test]
    fn test_changeset_multiple_changes_same_path() {
        let mut cs = ChangeSet::new();
        cs.add_function_body_change("crate::foo");
        cs.add_spec_change("crate::foo");

        assert_eq!(cs.len(), 2);
        assert_eq!(cs.changed_count(), 1);

        let changes = cs.changes_for("crate::foo");
        assert_eq!(changes.len(), 2);
        assert_eq!(changes[0].kind, ChangeKind::FunctionBody);
        assert_eq!(changes[1].kind, ChangeKind::SpecChange);
    }

    #[test]
    fn test_changeset_changes_for_unknown() {
        let cs = ChangeSet::new();
        assert!(cs.changes_for("unknown").is_empty());
    }

    #[test]
    fn test_changeset_from_diff_lines() {
        let diff = "
            + crate::new_fn
            - crate::old_fn
            M crate::modified_fn
            S crate::spec_changed
            T crate::MyStruct
            # comment line
        ";
        let cs = ChangeSet::from_diff_lines(diff);

        assert_eq!(cs.len(), 5);
        assert!(cs.is_changed("crate::new_fn"));
        assert!(cs.is_changed("crate::old_fn"));
        assert!(cs.is_changed("crate::modified_fn"));
        assert!(cs.is_changed("crate::spec_changed"));
        assert!(cs.is_changed("crate::MyStruct"));

        assert_eq!(cs.changes_for("crate::new_fn")[0].kind, ChangeKind::Added);
        assert_eq!(cs.changes_for("crate::old_fn")[0].kind, ChangeKind::Removed);
        assert_eq!(cs.changes_for("crate::modified_fn")[0].kind, ChangeKind::FunctionBody);
        assert_eq!(cs.changes_for("crate::spec_changed")[0].kind, ChangeKind::SpecChange);
        assert_eq!(cs.changes_for("crate::MyStruct")[0].kind, ChangeKind::TypeDefinition);
    }

    #[test]
    fn test_changeset_from_diff_lines_empty() {
        let cs = ChangeSet::from_diff_lines("");
        assert!(cs.is_empty());

        let cs2 = ChangeSet::from_diff_lines("# only comments\n# here");
        assert!(cs2.is_empty());
    }

    #[test]
    fn test_changeset_from_diff_lines_skips_invalid() {
        let diff = "M crate::valid\nINVALID LINE\nX bad\n+ crate::also_valid";
        let cs = ChangeSet::from_diff_lines(diff);
        assert_eq!(cs.len(), 2);
    }

    #[test]
    fn test_changeset_added_removed() {
        let mut cs = ChangeSet::new();
        cs.add_added("crate::new_fn");
        cs.add_removed("crate::old_fn");

        assert_eq!(cs.changes_for("crate::new_fn")[0].kind, ChangeKind::Added);
        assert_eq!(cs.changes_for("crate::old_fn")[0].kind, ChangeKind::Removed);
    }

    // -- DependencyGraph tests --

    #[test]
    fn test_dep_graph_empty() {
        let graph = DependencyGraph::new();
        assert!(graph.is_empty());
        assert_eq!(graph.vc_count(), 0);
        assert_eq!(graph.type_usage_count(), 0);
    }

    #[test]
    fn test_dep_graph_call_dependency() {
        let mut graph = DependencyGraph::new();
        graph.add_call_dependency("caller", "callee");

        let deps = graph.func_deps().direct_dependencies("caller");
        assert!(deps.contains("callee"));
    }

    #[test]
    fn test_dep_graph_type_usage() {
        let mut graph = DependencyGraph::new();
        graph.add_type_usage("crate::foo", "crate::MyType");
        graph.add_type_usage("crate::bar", "crate::MyType");

        let users = graph.type_users("crate::MyType");
        assert_eq!(users.len(), 2);
        assert!(users.contains("crate::foo"));
        assert!(users.contains("crate::bar"));
        assert_eq!(graph.type_usage_count(), 2);
    }

    #[test]
    fn test_dep_graph_type_users_unknown() {
        let graph = DependencyGraph::new();
        assert!(graph.type_users("unknown").is_empty());
    }

    #[test]
    fn test_dep_graph_vc_dependency() {
        let mut graph = DependencyGraph::new();
        graph.add_vc_dependency("vc_1", "crate::foo");
        graph.add_vc_dependency("vc_1", "crate::bar");
        graph.add_vc_dependency("vc_2", "crate::foo");

        assert_eq!(graph.vc_count(), 2);

        let vc1_deps = graph.vc_dependencies("vc_1");
        assert_eq!(vc1_deps.len(), 2);
        assert!(vc1_deps.contains("crate::foo"));
        assert!(vc1_deps.contains("crate::bar"));

        let foo_vcs = graph.vcs_depending_on("crate::foo");
        assert_eq!(foo_vcs.len(), 2);
        assert!(foo_vcs.contains("vc_1"));
        assert!(foo_vcs.contains("vc_2"));
    }

    #[test]
    fn test_dep_graph_vc_deps_unknown() {
        let graph = DependencyGraph::new();
        assert!(graph.vc_dependencies("unknown").is_empty());
        assert!(graph.vcs_depending_on("unknown").is_empty());
    }

    // -- TransitiveClosure tests --

    #[test]
    fn test_transitive_closure_empty() {
        let graph = DependencyGraph::new();
        let changed: FxHashSet<String> = FxHashSet::default();
        let result = TransitiveClosure::compute(&changed, &graph);
        assert!(result.is_empty());
    }

    #[test]
    fn test_transitive_closure_direct_only() {
        let graph = DependencyGraph::new();
        let changed: FxHashSet<String> = ["crate::foo".to_string()].into();
        let result = TransitiveClosure::compute(&changed, &graph);
        assert_eq!(result.len(), 1);
        assert!(result.contains("crate::foo"));
    }

    #[test]
    fn test_transitive_closure_call_chain() {
        // A calls B calls C. If C changes, all three are impacted.
        let mut graph = DependencyGraph::new();
        graph.add_call_dependency("A", "B");
        graph.add_call_dependency("B", "C");

        let changed: FxHashSet<String> = ["C".to_string()].into();
        let result = TransitiveClosure::compute(&changed, &graph);
        assert_eq!(result.len(), 3);
        assert!(result.contains("A"));
        assert!(result.contains("B"));
        assert!(result.contains("C"));
    }

    #[test]
    fn test_transitive_closure_type_propagation() {
        // foo uses MyType. If MyType changes, foo must re-verify.
        let mut graph = DependencyGraph::new();
        graph.add_type_usage("crate::foo", "crate::MyType");

        let changed: FxHashSet<String> = ["crate::MyType".to_string()].into();
        let result = TransitiveClosure::compute(&changed, &graph);
        assert!(result.contains("crate::MyType"));
        assert!(result.contains("crate::foo"));
    }

    #[test]
    fn test_transitive_closure_type_plus_call_chain() {
        // foo uses MyType. bar calls foo. If MyType changes, both foo and bar are impacted.
        let mut graph = DependencyGraph::new();
        graph.add_type_usage("crate::foo", "crate::MyType");
        graph.add_call_dependency("crate::bar", "crate::foo");

        let changed: FxHashSet<String> = ["crate::MyType".to_string()].into();
        let result = TransitiveClosure::compute(&changed, &graph);
        assert!(result.contains("crate::MyType"));
        assert!(result.contains("crate::foo"));
        assert!(result.contains("crate::bar"));
    }

    // -- ConservativeMode tests --

    #[test]
    fn test_conservative_mode_defaults() {
        assert_eq!(ConservativeMode::default(), ConservativeMode::Precise);
    }

    #[test]
    fn test_conservative_mode_is_conservative() {
        assert!(!ConservativeMode::Precise.is_conservative());
        assert!(ConservativeMode::ModuleLevel.is_conservative());
        assert!(ConservativeMode::ReVerifyAll.is_conservative());
    }

    // -- ImpactAnalyzer: single function change --

    #[test]
    fn test_impact_single_function_change() {
        let mut cs = ChangeSet::new();
        cs.add_function_body_change("crate::foo");

        let graph = DependencyGraph::new();
        let mut analyzer = ImpactAnalyzer::new(ConservativeMode::Precise);
        analyzer.register_known_functions(
            ["crate::foo", "crate::bar", "crate::baz"]
                .iter()
                .map(|s| s.to_string()),
        );

        let result = analyzer.compute_impact(&cs, &graph);

        assert_eq!(result.reverify_count(), 1);
        assert_eq!(result.cached_count(), 2);
        assert!(result.needs_reverify("crate::foo"));
        assert!(result.is_cached("crate::bar"));
        assert!(result.is_cached("crate::baz"));

        let reason = result.reason_for("crate::foo").unwrap();
        assert!(reason.is_direct);
        assert!(reason.explanation.contains("directly changed"));
    }

    // -- ImpactAnalyzer: type change propagation --

    #[test]
    fn test_impact_type_change_propagation() {
        let mut cs = ChangeSet::new();
        cs.add_type_change("crate::MyType");

        let mut graph = DependencyGraph::new();
        graph.add_type_usage("crate::foo", "crate::MyType");
        graph.add_type_usage("crate::bar", "crate::MyType");
        // baz does not use MyType.

        let mut analyzer = ImpactAnalyzer::new(ConservativeMode::Precise);
        analyzer.register_known_functions(
            ["crate::foo", "crate::bar", "crate::baz"]
                .iter()
                .map(|s| s.to_string()),
        );

        let result = analyzer.compute_impact(&cs, &graph);

        assert!(result.needs_reverify("crate::MyType"));
        assert!(result.needs_reverify("crate::foo"));
        assert!(result.needs_reverify("crate::bar"));
        assert!(result.is_cached("crate::baz"));
    }

    #[test]
    fn test_impact_type_change_transitive_propagation() {
        // MyType changed. foo uses MyType. bar calls foo.
        // All three must re-verify.
        let mut cs = ChangeSet::new();
        cs.add_type_change("crate::MyType");

        let mut graph = DependencyGraph::new();
        graph.add_type_usage("crate::foo", "crate::MyType");
        graph.add_call_dependency("crate::bar", "crate::foo");

        let mut analyzer = ImpactAnalyzer::new(ConservativeMode::Precise);
        analyzer.register_known_functions(
            ["crate::foo", "crate::bar", "crate::baz"]
                .iter()
                .map(|s| s.to_string()),
        );

        let result = analyzer.compute_impact(&cs, &graph);
        assert!(result.needs_reverify("crate::MyType"));
        assert!(result.needs_reverify("crate::foo"));
        assert!(result.needs_reverify("crate::bar"));
        assert!(result.is_cached("crate::baz"));
    }

    // -- ImpactAnalyzer: no-op change detection --

    #[test]
    fn test_impact_no_changes() {
        let cs = ChangeSet::new();
        let graph = DependencyGraph::new();
        let mut analyzer = ImpactAnalyzer::new(ConservativeMode::Precise);
        analyzer.register_known_functions(
            ["crate::foo", "crate::bar"].iter().map(|s| s.to_string()),
        );

        let result = analyzer.compute_impact(&cs, &graph);

        assert_eq!(result.reverify_count(), 0);
        assert_eq!(result.cached_count(), 2);
        assert!(result.is_cached("crate::foo"));
        assert!(result.is_cached("crate::bar"));
    }

    // -- ImpactAnalyzer: conservative modes --

    #[test]
    fn test_impact_reverify_all_mode() {
        let mut cs = ChangeSet::new();
        cs.add_function_body_change("crate::foo");

        let graph = DependencyGraph::new();
        let mut analyzer = ImpactAnalyzer::new(ConservativeMode::ReVerifyAll);
        analyzer.register_known_functions(
            ["crate::foo", "crate::bar", "crate::baz"]
                .iter()
                .map(|s| s.to_string()),
        );

        let result = analyzer.compute_impact(&cs, &graph);

        // All known functions should be re-verified.
        assert_eq!(result.reverify_count(), 3);
        assert_eq!(result.cached_count(), 0);
        assert!(result.needs_reverify("crate::foo"));
        assert!(result.needs_reverify("crate::bar"));
        assert!(result.needs_reverify("crate::baz"));
    }

    #[test]
    fn test_impact_module_level_mode() {
        let mut cs = ChangeSet::new();
        cs.add_function_body_change("crate::mod_a::foo");

        let graph = DependencyGraph::new();
        let mut analyzer = ImpactAnalyzer::new(ConservativeMode::ModuleLevel);
        analyzer.register_known_functions(
            [
                "crate::mod_a::foo",
                "crate::mod_a::bar",
                "crate::mod_b::baz",
            ]
            .iter()
            .map(|s| s.to_string()),
        );

        let result = analyzer.compute_impact(&cs, &graph);

        // mod_a functions re-verified, mod_b cached.
        assert!(result.needs_reverify("crate::mod_a::foo"));
        assert!(result.needs_reverify("crate::mod_a::bar"));
        assert!(result.is_cached("crate::mod_b::baz"));
    }

    // -- DeltaReport tests --

    #[test]
    fn test_delta_report_from_impact_result() {
        let mut cs = ChangeSet::new();
        cs.add_function_body_change("crate::foo");

        let graph = DependencyGraph::new();
        let mut analyzer = ImpactAnalyzer::new(ConservativeMode::Precise);
        analyzer.register_known_functions(
            ["crate::foo", "crate::bar"].iter().map(|s| s.to_string()),
        );

        let result = analyzer.compute_impact(&cs, &graph);
        let report = result.to_delta_report();

        assert_eq!(report.total_reverified, 1);
        assert_eq!(report.total_cached, 1);
        assert_eq!(report.total(), 2);
        assert_eq!(report.mode, ConservativeMode::Precise);
        assert!(report.timestamp > 0);

        let reverified = report.entries_with_action(DeltaAction::ReVerify);
        assert_eq!(reverified.len(), 1);
        assert_eq!(reverified[0].def_path, "crate::foo");
        assert!(reverified[0].is_direct_change);

        let cached = report.entries_with_action(DeltaAction::UseCached);
        assert_eq!(cached.len(), 1);
        assert_eq!(cached[0].def_path, "crate::bar");
        assert!(!cached[0].is_direct_change);
    }

    #[test]
    fn test_delta_report_cache_hit_rate() {
        let mut cs = ChangeSet::new();
        cs.add_function_body_change("crate::foo");

        let graph = DependencyGraph::new();
        let mut analyzer = ImpactAnalyzer::new(ConservativeMode::Precise);
        analyzer.register_known_functions(
            ["crate::foo", "crate::bar", "crate::baz", "crate::qux"]
                .iter()
                .map(|s| s.to_string()),
        );

        let result = analyzer.compute_impact(&cs, &graph);
        let report = result.to_delta_report();

        // 1 re-verified, 3 cached -> 75% hit rate.
        assert!((report.cache_hit_rate() - 0.75).abs() < 0.001);
    }

    #[test]
    fn test_delta_report_cache_hit_rate_empty() {
        let cs = ChangeSet::new();
        let graph = DependencyGraph::new();
        let analyzer = ImpactAnalyzer::new(ConservativeMode::Precise);

        let result = analyzer.compute_impact(&cs, &graph);
        let report = result.to_delta_report();

        assert_eq!(report.cache_hit_rate(), 0.0);
    }

    #[test]
    fn test_delta_report_summary() {
        let mut cs = ChangeSet::new();
        cs.add_function_body_change("crate::foo");

        let graph = DependencyGraph::new();
        let mut analyzer = ImpactAnalyzer::new(ConservativeMode::Precise);
        analyzer.register_known_functions(
            ["crate::foo", "crate::bar"].iter().map(|s| s.to_string()),
        );

        let result = analyzer.compute_impact(&cs, &graph);
        let report = result.to_delta_report();
        let summary = report.summary();

        assert!(summary.contains("1 re-verified"));
        assert!(summary.contains("1 cached"));
        assert!(summary.contains("50%"));
        assert!(summary.contains("Precise"));
    }

    #[test]
    fn test_delta_report_display() {
        let mut cs = ChangeSet::new();
        cs.add_function_body_change("crate::foo");

        let graph = DependencyGraph::new();
        let mut analyzer = ImpactAnalyzer::new(ConservativeMode::Precise);
        analyzer.register_known_functions(
            ["crate::foo", "crate::bar"].iter().map(|s| s.to_string()),
        );

        let result = analyzer.compute_impact(&cs, &graph);
        let report = result.to_delta_report();
        let display = format!("{report}");

        assert!(display.contains("Delta Report"));
        assert!(display.contains("Re-verified"));
        assert!(display.contains("Cached"));
        assert!(display.contains("crate::foo"));
        assert!(display.contains("crate::bar"));
    }

    #[test]
    fn test_delta_report_direct_changes() {
        let mut cs = ChangeSet::new();
        cs.add_function_body_change("crate::foo");

        let mut graph = DependencyGraph::new();
        graph.add_call_dependency("crate::bar", "crate::foo");

        let mut analyzer = ImpactAnalyzer::new(ConservativeMode::Precise);
        analyzer.register_known_functions(
            ["crate::foo", "crate::bar", "crate::baz"]
                .iter()
                .map(|s| s.to_string()),
        );

        let result = analyzer.compute_impact(&cs, &graph);
        let report = result.to_delta_report();

        let direct = report.direct_changes();
        assert_eq!(direct.len(), 1);
        assert_eq!(direct[0].def_path, "crate::foo");
    }

    // -- CacheDecision tests --

    #[test]
    fn test_cache_decision_properties() {
        let cached = CacheDecision::UseCached {
            def_path: "crate::foo".to_string(),
        };
        assert!(cached.is_cached());
        assert!(!cached.needs_reverify());
        assert_eq!(cached.def_path(), "crate::foo");

        let reverify = CacheDecision::ReVerify {
            def_path: "crate::bar".to_string(),
            reason: ReVerifyReason {
                def_path: "crate::bar".to_string(),
                is_direct: true,
                chain: vec!["crate::bar".to_string()],
                explanation: "test".to_string(),
            },
        };
        assert!(!reverify.is_cached());
        assert!(reverify.needs_reverify());
        assert_eq!(reverify.def_path(), "crate::bar");
    }

    // -- ChangeKind Display --

    #[test]
    fn test_change_kind_display() {
        assert_eq!(ChangeKind::FunctionBody.to_string(), "function body");
        assert_eq!(ChangeKind::FunctionSignature.to_string(), "function signature");
        assert_eq!(ChangeKind::TypeDefinition.to_string(), "type definition");
        assert_eq!(ChangeKind::SpecChange.to_string(), "spec change");
        assert_eq!(ChangeKind::Added.to_string(), "added");
        assert_eq!(ChangeKind::Removed.to_string(), "removed");
    }

    // -- DeltaAction Display --

    #[test]
    fn test_delta_action_display() {
        assert_eq!(DeltaAction::ReVerify.to_string(), "re-verify");
        assert_eq!(DeltaAction::UseCached.to_string(), "use-cached");
    }

    // -- Integration: complex scenario --

    #[test]
    fn test_impact_complex_diamond_with_type() {
        // Diamond call graph + type usage:
        //   main calls foo and bar
        //   foo calls helper
        //   bar calls helper
        //   helper uses MyType
        //   MyType changes
        //
        // Expected: MyType, helper, foo, bar, main all re-verify.
        // unrelated stays cached.
        let mut cs = ChangeSet::new();
        cs.add_type_change("crate::MyType");

        let mut graph = DependencyGraph::new();
        graph.add_type_usage("crate::helper", "crate::MyType");
        graph.add_call_dependency("crate::foo", "crate::helper");
        graph.add_call_dependency("crate::bar", "crate::helper");
        graph.add_call_dependency("crate::main", "crate::foo");
        graph.add_call_dependency("crate::main", "crate::bar");

        let mut analyzer = ImpactAnalyzer::new(ConservativeMode::Precise);
        analyzer.register_known_functions(
            [
                "crate::main",
                "crate::foo",
                "crate::bar",
                "crate::helper",
                "crate::unrelated",
            ]
            .iter()
            .map(|s| s.to_string()),
        );

        let result = analyzer.compute_impact(&cs, &graph);

        assert!(result.needs_reverify("crate::MyType"));
        assert!(result.needs_reverify("crate::helper"));
        assert!(result.needs_reverify("crate::foo"));
        assert!(result.needs_reverify("crate::bar"));
        assert!(result.needs_reverify("crate::main"));
        assert!(result.is_cached("crate::unrelated"));
        assert_eq!(result.cached_count(), 1);
    }

    #[test]
    fn test_impact_multiple_changes() {
        // Two functions changed simultaneously.
        let mut cs = ChangeSet::new();
        cs.add_function_body_change("crate::foo");
        cs.add_spec_change("crate::bar");

        let mut graph = DependencyGraph::new();
        graph.add_call_dependency("crate::caller_foo", "crate::foo");
        graph.add_call_dependency("crate::caller_bar", "crate::bar");

        let mut analyzer = ImpactAnalyzer::new(ConservativeMode::Precise);
        analyzer.register_known_functions(
            [
                "crate::foo",
                "crate::bar",
                "crate::caller_foo",
                "crate::caller_bar",
                "crate::isolated",
            ]
            .iter()
            .map(|s| s.to_string()),
        );

        let result = analyzer.compute_impact(&cs, &graph);
        assert!(result.needs_reverify("crate::foo"));
        assert!(result.needs_reverify("crate::bar"));
        assert!(result.needs_reverify("crate::caller_foo"));
        assert!(result.needs_reverify("crate::caller_bar"));
        assert!(result.is_cached("crate::isolated"));
    }

    #[test]
    fn test_impact_reverify_all_includes_unknown_changed() {
        // Changed function not in known set is still included.
        let mut cs = ChangeSet::new();
        cs.add_function_body_change("crate::unknown_fn");

        let graph = DependencyGraph::new();
        let mut analyzer = ImpactAnalyzer::new(ConservativeMode::ReVerifyAll);
        analyzer
            .register_known_functions(["crate::known"].iter().map(|s| s.to_string()));

        let result = analyzer.compute_impact(&cs, &graph);
        assert!(result.needs_reverify("crate::known"));
        assert!(result.needs_reverify("crate::unknown_fn"));
    }

    #[test]
    fn test_impact_module_level_includes_transitive() {
        // Module-level mode should also include transitive deps across modules.
        let mut cs = ChangeSet::new();
        cs.add_function_body_change("crate::mod_a::foo");

        let mut graph = DependencyGraph::new();
        graph.add_call_dependency("crate::mod_b::bar", "crate::mod_a::foo");

        let mut analyzer = ImpactAnalyzer::new(ConservativeMode::ModuleLevel);
        analyzer.register_known_functions(
            [
                "crate::mod_a::foo",
                "crate::mod_a::helper",
                "crate::mod_b::bar",
                "crate::mod_b::other",
            ]
            .iter()
            .map(|s| s.to_string()),
        );

        let result = analyzer.compute_impact(&cs, &graph);
        // mod_a functions: re-verify (same module).
        assert!(result.needs_reverify("crate::mod_a::foo"));
        assert!(result.needs_reverify("crate::mod_a::helper"));
        // mod_b::bar: re-verify (transitive dep on changed function).
        assert!(result.needs_reverify("crate::mod_b::bar"));
        // mod_b::other: cached (no dependency, different module).
        assert!(result.is_cached("crate::mod_b::other"));
    }

    // -- BFS path finding --

    #[test]
    fn test_bfs_path_direct() {
        let mut deps = DependencyTracker::new();
        deps.add_dependency("B", "A");

        let path = bfs_path(&deps, "A", "B");
        assert_eq!(path, Some(vec!["A".to_string(), "B".to_string()]));
    }

    #[test]
    fn test_bfs_path_chain() {
        let mut deps = DependencyTracker::new();
        deps.add_dependency("B", "A");
        deps.add_dependency("C", "B");

        let path = bfs_path(&deps, "A", "C");
        assert_eq!(
            path,
            Some(vec!["A".to_string(), "B".to_string(), "C".to_string()])
        );
    }

    #[test]
    fn test_bfs_path_no_connection() {
        let deps = DependencyTracker::new();
        let path = bfs_path(&deps, "A", "B");
        assert_eq!(path, None);
    }

    #[test]
    fn test_bfs_path_self() {
        let deps = DependencyTracker::new();
        let path = bfs_path(&deps, "A", "A");
        assert_eq!(path, Some(vec!["A".to_string()]));
    }

    // -- Reason explanation tests --

    #[test]
    fn test_impact_reason_direct_shows_change_kinds() {
        let mut cs = ChangeSet::new();
        cs.add_function_body_change("crate::foo");
        cs.add_spec_change("crate::foo");

        let graph = DependencyGraph::new();
        let analyzer = ImpactAnalyzer::new(ConservativeMode::Precise);

        let result = analyzer.compute_impact(&cs, &graph);
        let reason = result.reason_for("crate::foo").unwrap();
        assert!(reason.explanation.contains("function body"));
        assert!(reason.explanation.contains("spec change"));
    }

    #[test]
    fn test_impact_reason_transitive_shows_chain() {
        let mut cs = ChangeSet::new();
        cs.add_function_body_change("crate::leaf");

        let mut graph = DependencyGraph::new();
        graph.add_call_dependency("crate::mid", "crate::leaf");
        graph.add_call_dependency("crate::top", "crate::mid");

        let mut analyzer = ImpactAnalyzer::new(ConservativeMode::Precise);
        analyzer.register_known_functions(
            ["crate::leaf", "crate::mid", "crate::top"]
                .iter()
                .map(|s| s.to_string()),
        );

        let result = analyzer.compute_impact(&cs, &graph);

        let reason_top = result.reason_for("crate::top").unwrap();
        assert!(!reason_top.is_direct);
        assert!(reason_top.explanation.contains("transitively affected"));
    }
}
