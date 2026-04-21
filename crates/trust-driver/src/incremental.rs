// trust-driver/incremental.rs: Incremental verification tracking
//
// Tracks which functions have been verified, their content hashes, and
// dependency relationships. When source changes, computes the minimal set
// of functions that need re-verification via transitive dependency analysis.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use trust_types::fx::{FxHashMap, FxHashSet};
use std::io::{BufRead, Write as IoWrite};
use std::path::Path;
use std::time::{Duration, SystemTime};

use trust_types::VerificationResult;

// ---------------------------------------------------------------------------
// Content hashing
// ---------------------------------------------------------------------------

/// A content hash identifying a function body + specification.
///
/// Wraps a hex string produced by hashing the function body, contracts,
/// and spec annotations. Two functions with the same `ContentHash` are
/// assumed identical for caching purposes.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ContentHash(pub(crate) String);

impl ContentHash {
    /// Create a `ContentHash` from a pre-computed hex string.
    #[must_use]
    pub(crate) fn new(hex: String) -> Self {
        Self(hex)
    }

    /// Return the hex representation.
    #[must_use]
    pub(crate) fn as_str(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for ContentHash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Compute a content hash for a function body represented as bytes.
///
/// Uses `DefaultHasher` (SipHash) for a fast, deterministic hash.
/// For production use with adversarial inputs, consider SHA-256.
#[must_use]
pub(crate) fn compute_function_hash(body: &[u8], spec: &[u8]) -> ContentHash {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let mut hasher = DefaultHasher::new();
    body.hash(&mut hasher);
    spec.hash(&mut hasher);
    ContentHash(format!("{:016x}", hasher.finish()))
}

// ---------------------------------------------------------------------------
// Dependency graph
// ---------------------------------------------------------------------------

/// A directed graph of function call dependencies.
///
/// Maps each function to its callees (forward edges) and callers (reverse
/// edges). Both directions are maintained for efficient impact analysis.
#[derive(Debug, Clone, Default)]
pub(crate) struct DependencyGraph {
    /// function -> set of functions it calls
    callees: FxHashMap<String, FxHashSet<String>>,
    /// function -> set of functions that call it
    callers: FxHashMap<String, FxHashSet<String>>,
}

impl DependencyGraph {
    /// Create an empty dependency graph.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Register a function in the graph (even if it has no edges).
    pub(crate) fn add_function(&mut self, name: &str) {
        self.callees.entry(name.to_string()).or_default();
        self.callers.entry(name.to_string()).or_default();
    }

    /// Record that `caller` calls `callee`.
    pub(crate) fn add_edge(&mut self, caller: &str, callee: &str) {
        self.callees.entry(caller.to_string()).or_default().insert(callee.to_string());
        self.callers.entry(callee.to_string()).or_default().insert(caller.to_string());
        // Ensure both nodes exist in both maps.
        self.callees.entry(callee.to_string()).or_default();
        self.callers.entry(caller.to_string()).or_default();
    }

    /// Return the set of functions directly called by `function`.
    #[must_use]
    pub(crate) fn callees_of(&self, function: &str) -> FxHashSet<String> {
        self.callees.get(function).cloned().unwrap_or_default()
    }

    /// Return the set of functions that directly call `function`.
    #[must_use]
    pub(crate) fn callers_of(&self, function: &str) -> FxHashSet<String> {
        self.callers.get(function).cloned().unwrap_or_default()
    }

    /// Return all function names known to the graph.
    #[must_use]
    pub(crate) fn all_functions(&self) -> FxHashSet<String> {
        let mut fns: FxHashSet<String> = self.callees.keys().cloned().collect();
        fns.extend(self.callers.keys().cloned());
        fns
    }

    /// Return the number of functions in the graph.
    #[must_use]
    pub(crate) fn function_count(&self) -> usize {
        self.all_functions().len()
    }

    /// Compute the transitive closure of callers (reverse dependencies).
    ///
    /// Given a set of changed functions, returns all functions that
    /// transitively depend on any changed function (i.e., all callers
    /// up the call chain).
    #[must_use]
    pub(crate) fn transitive_callers(&self, roots: &FxHashSet<String>) -> FxHashSet<String> {
        let mut visited = FxHashSet::default();
        let mut queue: VecDeque<String> = roots.iter().cloned().collect();

        while let Some(func) = queue.pop_front() {
            if !visited.insert(func.clone()) {
                continue;
            }
            if let Some(callers) = self.callers.get(&func) {
                for caller in callers {
                    if !visited.contains(caller) {
                        queue.push_back(caller.clone());
                    }
                }
            }
        }

        visited
    }

    /// Compute the transitive closure of callees (forward dependencies).
    #[must_use]
    pub(crate) fn transitive_callees(&self, roots: &FxHashSet<String>) -> FxHashSet<String> {
        let mut visited = FxHashSet::default();
        let mut queue: VecDeque<String> = roots.iter().cloned().collect();

        while let Some(func) = queue.pop_front() {
            if !visited.insert(func.clone()) {
                continue;
            }
            if let Some(callees) = self.callees.get(&func) {
                for callee in callees {
                    if !visited.contains(callee) {
                        queue.push_back(callee.clone());
                    }
                }
            }
        }

        visited
    }

    /// Produce a topological ordering of the graph (callees before callers).
    ///
    /// Returns `None` if the graph contains a cycle.
    #[must_use]
    pub(crate) fn topological_order(&self) -> Option<Vec<String>> {
        let all = self.all_functions();
        let mut in_degree: FxHashMap<String, usize> = FxHashMap::default();

        for func in &all {
            in_degree.entry(func.clone()).or_insert(0);
            for callee in self.callees_of(func) {
                *in_degree.entry(callee).or_insert(0) += 1;
            }
        }

        // Wait -- topological sort for "callees before callers" means
        // we want functions with no callees first. Actually, standard
        // topo sort: a -> b means a depends on b, so b comes first.
        // Our edges: caller -> callee. We want callees first.
        // So we use reverse edges for Kahn's: in-degree = number of callers.
        let mut in_deg: FxHashMap<String, usize> = FxHashMap::default();
        for func in &all {
            in_deg.entry(func.clone()).or_insert(0);
        }
        for func in &all {
            for callee in self.callees_of(func) {
                // callee is depended upon by func, so callee has an incoming
                // edge from func in the "depends-on" view. But we want
                // callees first, so we count callers as in-degree.
                *in_deg.entry(callee).or_insert(0) += 1;
            }
        }

        // Hmm, that gives us callers-first. Let me think again.
        // We want: if A calls B, then B should be verified before A.
        // So B < A in the ordering. Edge: A -> B (A calls B).
        // In topo sort, if edge A -> B means "A must come after B",
        // then in-degree of A = number of things A depends on = callees of A.

        let mut in_deg2: FxHashMap<String, usize> = FxHashMap::default();
        for func in &all {
            let count = self.callees_of(func).len();
            in_deg2.insert(func.clone(), count);
        }

        let mut queue: VecDeque<String> =
            in_deg2.iter().filter(|(_, &deg)| deg == 0).map(|(f, _)| f.clone()).collect();

        // Sort initial queue for determinism.
        let mut sorted_queue: Vec<String> = queue.drain(..).collect();
        sorted_queue.sort();
        queue.extend(sorted_queue);

        let mut order = Vec::new();
        while let Some(func) = queue.pop_front() {
            order.push(func.clone());
            // For each caller of func, decrement their in-degree
            // (because func is now "done" and one of caller's deps is resolved).
            let callers = self.callers_of(&func);
            let mut callers_sorted: Vec<_> = callers.into_iter().collect();
            callers_sorted.sort();
            for caller in callers_sorted {
                if let Some(deg) = in_deg2.get_mut(&caller) {
                    *deg = deg.saturating_sub(1);
                    if *deg == 0 {
                        queue.push_back(caller);
                    }
                }
            }
        }

        if order.len() == all.len() {
            Some(order)
        } else {
            None // Cycle detected.
        }
    }
}

// ---------------------------------------------------------------------------
// Cached verification entry
// ---------------------------------------------------------------------------

/// A cached verification result for a single function.
#[derive(Debug, Clone)]
pub(crate) struct CachedResult {
    /// Content hash at the time of verification.
    pub hash: ContentHash,
    /// The verification outcome.
    pub result: CachedVerificationOutcome,
    /// When this result was recorded.
    pub verified_at: SystemTime,
    /// How long verification took.
    pub elapsed: Duration,
    // tRust: F13 fix — store full VC counts so cache hits report accurate statistics.
    /// Proof frontier at the time of verification (VC granularity).
    pub frontier: Option<trust_convergence::ProofFrontier>,
    /// Number of VCs dispatched during verification.
    pub vcs_dispatched: usize,
    /// Number of VCs that failed during verification.
    pub vcs_failed: usize,
}

/// Simplified verification outcome for caching.
///
/// We don't store the full `VerificationResult` because it contains
/// solver-specific details. We only need to know the outcome.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum CachedVerificationOutcome {
    /// Function was proved correct.
    Proved,
    /// Function verification failed (counterexample found).
    Failed,
    /// Verification result was unknown / inconclusive.
    Unknown,
    /// Verification timed out.
    Timeout,
}

impl CachedVerificationOutcome {
    /// Convert from a `trust_types::VerificationResult`.
    #[must_use]
    pub(crate) fn from_verification_result(result: &VerificationResult) -> Self {
        match result {
            VerificationResult::Proved { .. } => Self::Proved,
            VerificationResult::Failed { .. } => Self::Failed,
            VerificationResult::Unknown { .. } => Self::Unknown,
            VerificationResult::Timeout { .. } => Self::Timeout,
            _ => Self::Unknown, // tRust: future VerificationResult variants
        }
    }

    /// Return a short string label for serialization.
    #[must_use]
    pub(crate) fn as_label(&self) -> &'static str {
        match self {
            Self::Proved => "proved",
            Self::Failed => "failed",
            Self::Unknown => "unknown",
            Self::Timeout => "timeout",
        }
    }

    /// Parse from a label string.
    #[must_use]
    pub(crate) fn from_label(s: &str) -> Option<Self> {
        match s {
            "proved" => Some(Self::Proved),
            "failed" => Some(Self::Failed),
            "unknown" => Some(Self::Unknown),
            "timeout" => Some(Self::Timeout),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Incremental cache
// ---------------------------------------------------------------------------

/// Persists verification results keyed by function name + content hash.
///
/// Cache entries are invalidated when the content hash changes.
#[derive(Debug, Clone, Default)]
pub(crate) struct IncrementalCache {
    entries: BTreeMap<String, CachedResult>,
}

impl IncrementalCache {
    /// Create an empty cache.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Record a verification result for a function.
    pub(crate) fn mark_verified(
        &mut self,
        fn_name: &str,
        hash: ContentHash,
        outcome: CachedVerificationOutcome,
        elapsed: Duration,
    ) {
        self.entries.insert(
            fn_name.to_string(),
            CachedResult {
                hash,
                result: outcome,
                verified_at: SystemTime::now(),
                elapsed,
                frontier: None,
                vcs_dispatched: 0,
                vcs_failed: 0,
            },
        );
    }

    /// Record a verification result with full VC granularity.
    // tRust: F13 fix -- preserves frontier counts through cache.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn mark_verified_with_frontier(
        &mut self,
        fn_name: &str,
        hash: ContentHash,
        outcome: CachedVerificationOutcome,
        elapsed: Duration,
        frontier: trust_convergence::ProofFrontier,
        vcs_dispatched: usize,
        vcs_failed: usize,
    ) {
        self.entries.insert(
            fn_name.to_string(),
            CachedResult {
                hash,
                result: outcome,
                verified_at: SystemTime::now(),
                elapsed,
                frontier: Some(frontier),
                vcs_dispatched,
                vcs_failed,
            },
        );
    }

    /// Check whether a function needs re-verification.
    ///
    /// Returns `true` if:
    /// - The function has never been verified.
    /// - The current hash differs from the cached hash.
    #[must_use]
    pub(crate) fn should_reverify(&self, fn_name: &str, current_hash: &ContentHash) -> bool {
        match self.entries.get(fn_name) {
            None => true,
            Some(cached) => cached.hash != *current_hash,
        }
    }

    /// Look up the cached result for a function.
    #[must_use]
    pub(crate) fn get(&self, fn_name: &str) -> Option<&CachedResult> {
        self.entries.get(fn_name)
    }

    /// Return all function names with cached results.
    #[must_use]
    pub(crate) fn cached_functions(&self) -> Vec<String> {
        self.entries.keys().cloned().collect()
    }

    /// Return the number of cached entries.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// Return whether the cache is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Remove a function from the cache.
    pub(crate) fn invalidate(&mut self, fn_name: &str) {
        self.entries.remove(fn_name);
    }

    /// Remove all entries from the cache.
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
    }

    /// Return functions whose cached results are stale given current hashes.
    ///
    /// A result is stale if the function's current content hash differs
    /// from the hash stored in the cache.
    #[must_use]
    pub(crate) fn stale_results(&self, current_hashes: &FxHashMap<String, ContentHash>) -> Vec<String> {
        let mut stale = Vec::new();
        for (fn_name, cached) in &self.entries {
            match current_hashes.get(fn_name) {
                Some(current_hash) if *current_hash != cached.hash => {
                    stale.push(fn_name.clone());
                }
                None => {
                    // Function no longer exists -- it's stale.
                    stale.push(fn_name.clone());
                }
                _ => {}
            }
        }
        stale.sort();
        stale
    }
}

// ---------------------------------------------------------------------------
// Incremental state (combines graph + cache)
// ---------------------------------------------------------------------------

/// Top-level incremental verification state.
///
/// Combines a dependency graph with a verification cache to support
/// efficient change-impact analysis and result persistence.
#[derive(Debug, Clone, Default)]
pub(crate) struct IncrementalState {
    /// The call dependency graph.
    pub graph: DependencyGraph,
    /// Cached verification results.
    pub cache: IncrementalCache,
}

impl IncrementalState {
    /// Create a new empty incremental state.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Given a set of changed functions, compute the full set that needs
    /// re-verification: the changed functions plus all their transitive callers.
    #[must_use]
    pub(crate) fn change_impact(&self, changed_fns: &FxHashSet<String>) -> FxHashSet<String> {
        self.graph.transitive_callers(changed_fns)
    }

    /// Convenience: mark a function as verified and update the cache.
    pub(crate) fn mark_verified(
        &mut self,
        fn_name: &str,
        hash: ContentHash,
        outcome: CachedVerificationOutcome,
        elapsed: Duration,
    ) {
        self.cache.mark_verified(fn_name, hash, outcome, elapsed);
    }

    /// Convenience: check if a function needs re-verification.
    #[must_use]
    pub(crate) fn should_reverify(&self, fn_name: &str, current_hash: &ContentHash) -> bool {
        self.cache.should_reverify(fn_name, current_hash)
    }

    /// Return functions with stale cached results.
    #[must_use]
    pub(crate) fn stale_results(&self, current_hashes: &FxHashMap<String, ContentHash>) -> Vec<String> {
        self.cache.stale_results(current_hashes)
    }
}

// ---------------------------------------------------------------------------
// Persistence (simple text format, no serde dependency)
// ---------------------------------------------------------------------------

/// Errors from incremental state persistence.
#[derive(Debug, thiserror::Error)]
pub(crate) enum IncrementalError {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    #[error("parse error at line {line}: {message}")]
    Parse { line: usize, message: String },
}

/// File format (v2, backward-compatible with v1):
/// ```text
/// # trust-driver incremental state v2
/// [edges]
/// caller -> callee
/// ...
/// [cache]
/// fn_name\thash\toutcome\telapsed_ms\ttrusted\tcertified\truntime_checked\tfailed\tunknown\tvcs_dispatched\tvcs_failed
/// ...
/// ```
/// v1 format (4 fields per cache line) is still accepted on load; missing
/// frontier fields default to zero.
impl IncrementalState {
    /// Save the incremental state to a file.
    pub(crate) fn save_state(&self, path: &Path) -> Result<(), IncrementalError> {
        let file = std::fs::File::create(path)?;
        let mut w = std::io::BufWriter::new(file);

        writeln!(w, "# trust-driver incremental state v2")?;
        writeln!(w)?;

        // Write edges.
        writeln!(w, "[edges]")?;
        // Use BTreeSet for deterministic output.
        let all_fns: BTreeSet<String> = self.graph.all_functions().into_iter().collect();
        for func in &all_fns {
            let callees = self.graph.callees_of(func);
            let mut sorted_callees: Vec<_> = callees.into_iter().collect();
            sorted_callees.sort();
            for callee in sorted_callees {
                writeln!(w, "{func} -> {callee}")?;
            }
        }
        writeln!(w)?;

        // tRust: F13 fix -- write cache with full frontier counts.
        writeln!(w, "[cache]")?;
        for (fn_name, cached) in &self.cache.entries {
            let elapsed_ms = cached.elapsed.as_millis();
            let (t, c, rc, f, u) = match &cached.frontier {
                Some(fr) => (fr.trusted, fr.certified, fr.runtime_checked, fr.failed, fr.unknown),
                None => (0, 0, 0, 0, 0),
            };
            writeln!(
                w,
                "{fn_name}\t{}\t{}\t{elapsed_ms}\t{t}\t{c}\t{rc}\t{f}\t{u}\t{}\t{}",
                cached.hash,
                cached.result.as_label(),
                cached.vcs_dispatched,
                cached.vcs_failed,
            )?;
        }

        w.flush()?;
        Ok(())
    }

    /// Load incremental state from a file.
    pub(crate) fn load_state(path: &Path) -> Result<Self, IncrementalError> {
        let file = std::fs::File::open(path)?;
        let reader = std::io::BufReader::new(file);

        let mut state = IncrementalState::new();
        let mut section = "";

        for (line_num, line_result) in reader.lines().enumerate() {
            let line = line_result?;
            let trimmed = line.trim();

            // Skip comments and blank lines.
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }

            // Section headers.
            if trimmed == "[edges]" {
                section = "edges";
                continue;
            }
            if trimmed == "[cache]" {
                section = "cache";
                continue;
            }

            match section {
                "edges" => {
                    // Format: caller -> callee
                    let parts: Vec<&str> = trimmed.splitn(3, " -> ").collect();
                    if parts.len() != 2 {
                        return Err(IncrementalError::Parse {
                            line: line_num + 1,
                            message: format!("expected 'caller -> callee', got: {trimmed}"),
                        });
                    }
                    state.graph.add_edge(parts[0].trim(), parts[1].trim());
                }
                "cache" => {
                    // tRust: F13 fix -- accept both v1 (4 fields) and v2 (11 fields).
                    let parts: Vec<&str> = trimmed.split('\t').collect();
                    if parts.len() != 4 && parts.len() != 11 {
                        return Err(IncrementalError::Parse {
                            line: line_num + 1,
                            message: format!(
                                "expected 4 or 11 tab-separated fields, got {}",
                                parts.len()
                            ),
                        });
                    }
                    let fn_name = parts[0];
                    let hash = ContentHash::new(parts[1].to_string());
                    let outcome =
                        CachedVerificationOutcome::from_label(parts[2]).ok_or_else(|| {
                            IncrementalError::Parse {
                                line: line_num + 1,
                                message: format!("unknown outcome: {}", parts[2]),
                            }
                        })?;
                    let elapsed_ms: u64 =
                        parts[3].parse().map_err(|_| IncrementalError::Parse {
                            line: line_num + 1,
                            message: format!("invalid elapsed_ms: {}", parts[3]),
                        })?;

                    // Parse frontier fields if present (v2 format).
                    let (frontier, vcs_dispatched, vcs_failed) = if parts.len() == 11 {
                        let parse_u32 = |idx: usize| -> Result<u32, IncrementalError> {
                            parts[idx].parse().map_err(|_| IncrementalError::Parse {
                                line: line_num + 1,
                                message: format!("invalid u32 at field {}: {}", idx, parts[idx]),
                            })
                        };
                        let parse_usize = |idx: usize| -> Result<usize, IncrementalError> {
                            parts[idx].parse().map_err(|_| IncrementalError::Parse {
                                line: line_num + 1,
                                message: format!("invalid usize at field {}: {}", idx, parts[idx]),
                            })
                        };
                        let fr = trust_convergence::ProofFrontier {
                            trusted: parse_u32(4)?,
                            certified: parse_u32(5)?,
                            runtime_checked: parse_u32(6)?,
                            failed: parse_u32(7)?,
                            unknown: parse_u32(8)?,
                        };
                        let vd = parse_usize(9)?;
                        let vf = parse_usize(10)?;
                        (Some(fr), vd, vf)
                    } else {
                        (None, 0, 0)
                    };

                    state.cache.entries.insert(
                        fn_name.to_string(),
                        CachedResult {
                            hash,
                            result: outcome,
                            verified_at: SystemTime::now(),
                            elapsed: Duration::from_millis(elapsed_ms),
                            frontier,
                            vcs_dispatched,
                            vcs_failed,
                        },
                    );
                }
                _ => {
                    return Err(IncrementalError::Parse {
                        line: line_num + 1,
                        message: format!("unexpected content outside section: {trimmed}"),
                    });
                }
            }
        }

        Ok(state)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- ContentHash tests ---------------------------------------------------

    #[test]
    fn test_compute_function_hash_deterministic() {
        let h1 = compute_function_hash(b"fn foo() { 1 + 1 }", b"requires(x > 0)");
        let h2 = compute_function_hash(b"fn foo() { 1 + 1 }", b"requires(x > 0)");
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_compute_function_hash_differs_on_body() {
        let h1 = compute_function_hash(b"fn foo() { 1 + 1 }", b"");
        let h2 = compute_function_hash(b"fn foo() { 1 + 2 }", b"");
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_compute_function_hash_differs_on_spec() {
        let h1 = compute_function_hash(b"fn foo() { 1 }", b"requires(x > 0)");
        let h2 = compute_function_hash(b"fn foo() { 1 }", b"requires(x > 1)");
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_content_hash_display() {
        let h = ContentHash::new("abc123".to_string());
        assert_eq!(h.as_str(), "abc123");
        assert_eq!(format!("{h}"), "abc123");
    }

    // -- DependencyGraph tests -----------------------------------------------

    #[test]
    fn test_graph_add_edge() {
        let mut g = DependencyGraph::new();
        g.add_edge("main", "helper");
        g.add_edge("main", "utils::parse");

        assert!(g.callees_of("main").contains("helper"));
        assert!(g.callees_of("main").contains("utils::parse"));
        assert!(g.callers_of("helper").contains("main"));
        assert_eq!(g.function_count(), 3);
    }

    #[test]
    fn test_graph_add_function_no_edges() {
        let mut g = DependencyGraph::new();
        g.add_function("isolated");
        assert_eq!(g.function_count(), 1);
        assert!(g.callees_of("isolated").is_empty());
        assert!(g.callers_of("isolated").is_empty());
    }

    #[test]
    fn test_graph_transitive_callers() {
        let mut g = DependencyGraph::new();
        // A calls B, B calls C
        g.add_edge("A", "B");
        g.add_edge("B", "C");
        g.add_edge("D", "C"); // D also calls C

        let changed: FxHashSet<String> = ["C"].iter().map(|s| s.to_string()).collect();
        let impact = g.transitive_callers(&changed);

        // C changed -> B and A and D need re-verification (plus C itself)
        assert!(impact.contains("C"));
        assert!(impact.contains("B"));
        assert!(impact.contains("A"));
        assert!(impact.contains("D"));
        assert_eq!(impact.len(), 4);
    }

    #[test]
    fn test_graph_transitive_callees() {
        let mut g = DependencyGraph::new();
        g.add_edge("A", "B");
        g.add_edge("B", "C");

        let roots: FxHashSet<String> = ["A"].iter().map(|s| s.to_string()).collect();
        let deps = g.transitive_callees(&roots);

        assert!(deps.contains("A"));
        assert!(deps.contains("B"));
        assert!(deps.contains("C"));
        assert_eq!(deps.len(), 3);
    }

    #[test]
    fn test_graph_topological_order_linear() {
        let mut g = DependencyGraph::new();
        g.add_edge("A", "B");
        g.add_edge("B", "C");

        let order = g.topological_order().expect("no cycle");
        // C has no callees -> first, then B, then A
        let pos_a = order.iter().position(|f| f == "A").unwrap();
        let pos_b = order.iter().position(|f| f == "B").unwrap();
        let pos_c = order.iter().position(|f| f == "C").unwrap();
        assert!(pos_c < pos_b);
        assert!(pos_b < pos_a);
    }

    #[test]
    fn test_graph_topological_order_diamond() {
        let mut g = DependencyGraph::new();
        // A calls B and C; both call D
        g.add_edge("A", "B");
        g.add_edge("A", "C");
        g.add_edge("B", "D");
        g.add_edge("C", "D");

        let order = g.topological_order().expect("no cycle");
        let pos_a = order.iter().position(|f| f == "A").unwrap();
        let pos_b = order.iter().position(|f| f == "B").unwrap();
        let pos_c = order.iter().position(|f| f == "C").unwrap();
        let pos_d = order.iter().position(|f| f == "D").unwrap();
        assert!(pos_d < pos_b);
        assert!(pos_d < pos_c);
        assert!(pos_b < pos_a);
        assert!(pos_c < pos_a);
    }

    #[test]
    fn test_graph_topological_order_cycle() {
        let mut g = DependencyGraph::new();
        g.add_edge("A", "B");
        g.add_edge("B", "A"); // cycle

        assert!(g.topological_order().is_none());
    }

    // -- IncrementalCache tests ----------------------------------------------

    #[test]
    fn test_cache_should_reverify_empty() {
        let cache = IncrementalCache::new();
        let hash = ContentHash::new("abc".to_string());
        assert!(cache.should_reverify("fn_a", &hash));
    }

    #[test]
    fn test_cache_should_reverify_same_hash() {
        let mut cache = IncrementalCache::new();
        let hash = ContentHash::new("abc".to_string());
        cache.mark_verified(
            "fn_a",
            hash.clone(),
            CachedVerificationOutcome::Proved,
            Duration::from_millis(100),
        );
        assert!(!cache.should_reverify("fn_a", &hash));
    }

    #[test]
    fn test_cache_should_reverify_different_hash() {
        let mut cache = IncrementalCache::new();
        let old_hash = ContentHash::new("abc".to_string());
        let new_hash = ContentHash::new("def".to_string());
        cache.mark_verified(
            "fn_a",
            old_hash,
            CachedVerificationOutcome::Proved,
            Duration::from_millis(100),
        );
        assert!(cache.should_reverify("fn_a", &new_hash));
    }

    #[test]
    fn test_cache_stale_results() {
        let mut cache = IncrementalCache::new();
        let h1 = ContentHash::new("hash1".to_string());
        let h2 = ContentHash::new("hash2".to_string());
        cache.mark_verified("fn_a", h1, CachedVerificationOutcome::Proved, Duration::ZERO);
        cache.mark_verified("fn_b", h2.clone(), CachedVerificationOutcome::Failed, Duration::ZERO);

        let mut current = FxHashMap::default();
        current.insert("fn_a".to_string(), ContentHash::new("hash1_new".to_string()));
        current.insert("fn_b".to_string(), h2); // unchanged

        let stale = cache.stale_results(&current);
        assert_eq!(stale, vec!["fn_a"]);
    }

    #[test]
    fn test_cache_stale_removed_function() {
        let mut cache = IncrementalCache::new();
        cache.mark_verified(
            "fn_gone",
            ContentHash::new("x".to_string()),
            CachedVerificationOutcome::Proved,
            Duration::ZERO,
        );

        let current = FxHashMap::default(); // fn_gone no longer exists
        let stale = cache.stale_results(&current);
        assert_eq!(stale, vec!["fn_gone"]);
    }

    #[test]
    fn test_cache_invalidate() {
        let mut cache = IncrementalCache::new();
        cache.mark_verified(
            "fn_a",
            ContentHash::new("h".to_string()),
            CachedVerificationOutcome::Proved,
            Duration::ZERO,
        );
        assert_eq!(cache.len(), 1);
        cache.invalidate("fn_a");
        assert_eq!(cache.len(), 0);
    }

    // -- IncrementalState (combined) tests -----------------------------------

    #[test]
    fn test_state_change_impact() {
        let mut state = IncrementalState::new();
        state.graph.add_edge("entry", "helper");
        state.graph.add_edge("helper", "leaf");

        let changed: FxHashSet<String> = ["leaf"].iter().map(|s| s.to_string()).collect();
        let impact = state.change_impact(&changed);

        assert!(impact.contains("leaf"));
        assert!(impact.contains("helper"));
        assert!(impact.contains("entry"));
    }

    #[test]
    fn test_state_mark_and_query() {
        let mut state = IncrementalState::new();
        let hash = ContentHash::new("h1".to_string());
        state.mark_verified(
            "fn_x",
            hash.clone(),
            CachedVerificationOutcome::Proved,
            Duration::from_millis(50),
        );
        assert!(!state.should_reverify("fn_x", &hash));
        assert!(state.should_reverify("fn_x", &ContentHash::new("h2".to_string())));
    }

    // -- Persistence tests ---------------------------------------------------

    #[test]
    fn test_save_and_load_roundtrip() {
        let mut state = IncrementalState::new();
        state.graph.add_edge("main", "helper");
        state.graph.add_edge("helper", "leaf");
        state.cache.mark_verified(
            "main",
            ContentHash::new("aaa".to_string()),
            CachedVerificationOutcome::Proved,
            Duration::from_millis(42),
        );
        state.cache.mark_verified(
            "helper",
            ContentHash::new("bbb".to_string()),
            CachedVerificationOutcome::Failed,
            Duration::from_millis(100),
        );

        let dir = std::env::temp_dir().join("trust_incr_test");
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join("test_state.txt");

        state.save_state(&path).expect("save should succeed");
        let loaded = IncrementalState::load_state(&path).expect("load should succeed");

        // Check graph.
        assert!(loaded.graph.callees_of("main").contains("helper"));
        assert!(loaded.graph.callees_of("helper").contains("leaf"));
        assert_eq!(loaded.graph.function_count(), 3);

        // Check cache.
        assert_eq!(loaded.cache.len(), 2);
        let main_cached = loaded.cache.get("main").expect("main should be cached");
        assert_eq!(main_cached.hash, ContentHash::new("aaa".to_string()));
        assert_eq!(main_cached.result, CachedVerificationOutcome::Proved);
        assert_eq!(main_cached.elapsed, Duration::from_millis(42));

        let helper_cached = loaded.cache.get("helper").expect("helper should be cached");
        assert_eq!(helper_cached.result, CachedVerificationOutcome::Failed);

        // Clean up.
        let _ = std::fs::remove_file(&path);
        let _ = std::fs::remove_dir(&dir);
    }

    #[test]
    fn test_load_parse_error() {
        let dir = std::env::temp_dir().join("trust_incr_test2");
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join("bad_state.txt");
        std::fs::write(&path, "garbage\n").expect("write should succeed");

        let result = IncrementalState::load_state(&path);
        assert!(result.is_err());

        let _ = std::fs::remove_file(&path);
        let _ = std::fs::remove_dir(&dir);
    }

    #[test]
    fn test_cached_verification_outcome_labels() {
        let cases = [
            (CachedVerificationOutcome::Proved, "proved"),
            (CachedVerificationOutcome::Failed, "failed"),
            (CachedVerificationOutcome::Unknown, "unknown"),
            (CachedVerificationOutcome::Timeout, "timeout"),
        ];
        for (outcome, label) in &cases {
            assert_eq!(outcome.as_label(), *label);
            assert_eq!(CachedVerificationOutcome::from_label(label).as_ref(), Some(outcome));
        }
        assert_eq!(CachedVerificationOutcome::from_label("bogus"), None);
    }
}
