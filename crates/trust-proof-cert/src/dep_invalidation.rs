// trust-proof-cert dependency-aware certificate invalidation
//
// Integrates the dependency graph (dependency_tracker) with the content-addressed
// store (content_store) to transitively invalidate certificates when function
// bodies change. Uses MIR body hashes (not function names) for staleness detection.
//
// Part of #430: Proof certificate storage, distribution, and chain verification.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use trust_types::fx::{FxHashMap, FxHashSet};

use crate::composition::ChangeKind;
use crate::content_store::{ContentId, ContentStore};
use crate::dependency_tracker::DependencyGraph;
use crate::FunctionHash;

/// Hash of a function's MIR body, for staleness detection.
///
/// Unlike `FunctionHash` which may be computed from the function name,
/// `BodyHash` is always computed from the actual MIR representation,
/// making staleness detection accurate even when functions are renamed.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct BodyHash(pub [u8; 32]);

impl BodyHash {
    /// Compute from raw MIR bytes.
    pub fn from_mir(mir_bytes: &[u8]) -> Self {
        use sha2::{Digest, Sha256};
        let mut hasher = Sha256::new();
        hasher.update(mir_bytes);
        BodyHash(hasher.finalize().into())
    }

    /// Convert to a `FunctionHash` for compatibility with the existing store API.
    pub fn to_function_hash(&self) -> FunctionHash {
        FunctionHash(self.0.iter().map(|b| format!("{b:02x}")).collect())
    }
}

/// Hash of a function's spec (annotations + signature), for change classification.
///
/// When the spec hash changes between versions, the change is classified as
/// [`ChangeKind::SpecChanged`], which triggers transitive invalidation of all
/// callers. When only the body hash changes, the change is [`ChangeKind::BodyOnly`],
/// invalidating only the changed function itself.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct SpecHash(pub [u8; 32]);

impl SpecHash {
    /// Compute from raw spec bytes (e.g., serialized annotations + signature).
    pub fn from_spec(spec_bytes: &[u8]) -> Self {
        use sha2::{Digest, Sha256};
        let mut hasher = Sha256::new();
        hasher.update(spec_bytes);
        SpecHash(hasher.finalize().into())
    }
}

/// A change to a function, classified by whether the spec or only the body changed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ClassifiedChange {
    /// The fully-qualified function name.
    pub function: String,
    /// Whether this is a body-only or spec-changing edit.
    pub kind: ChangeKind,
}

/// Tracks body and spec hashes for all functions, enabling change detection
/// with automatic [`ChangeKind`] classification.
#[derive(Debug, Clone, Default)]
pub(crate) struct BodyHashRegistry {
    /// Function FQN -> current body hash.
    hashes: FxHashMap<String, BodyHash>,
    /// Function FQN -> current spec hash (optional; enables auto-classification).
    spec_hashes: FxHashMap<String, SpecHash>,
}

impl BodyHashRegistry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        BodyHashRegistry {
            hashes: FxHashMap::default(),
            spec_hashes: FxHashMap::default(),
        }
    }

    /// Register or update the body hash for a function.
    pub fn set(&mut self, function: &str, hash: BodyHash) {
        self.hashes.insert(function.to_string(), hash);
    }

    /// Register or update the spec hash for a function.
    pub fn set_spec(&mut self, function: &str, hash: SpecHash) {
        self.spec_hashes.insert(function.to_string(), hash);
    }

    /// Register or update both body and spec hashes for a function.
    pub fn set_both(&mut self, function: &str, body: BodyHash, spec: SpecHash) {
        self.hashes.insert(function.to_string(), body);
        self.spec_hashes.insert(function.to_string(), spec);
    }

    /// Get the current body hash for a function.
    pub fn get(&self, function: &str) -> Option<&BodyHash> {
        self.hashes.get(function)
    }

    /// Get the current spec hash for a function.
    pub fn get_spec(&self, function: &str) -> Option<&SpecHash> {
        self.spec_hashes.get(function)
    }

    /// Convert to a `HashMap<String, FunctionHash>` for compatibility with store APIs.
    pub fn to_function_hashes(&self) -> FxHashMap<String, FunctionHash> {
        self.hashes
            .iter()
            .map(|(name, hash)| (name.clone(), hash.to_function_hash()))
            .collect()
    }

    /// Detect which functions changed between two registries.
    pub fn changed_functions(&self, previous: &BodyHashRegistry) -> Vec<String> {
        let mut changed = Vec::new();
        for (func, hash) in &self.hashes {
            match previous.hashes.get(func) {
                Some(prev_hash) if prev_hash == hash => {}
                _ => changed.push(func.clone()),
            }
        }
        // Also detect deleted functions.
        for func in previous.hashes.keys() {
            if !self.hashes.contains_key(func) {
                changed.push(func.clone());
            }
        }
        changed.sort();
        changed.dedup();
        changed
    }

    /// Detect changed functions with automatic [`ChangeKind`] classification.
    ///
    /// Compares body and spec hashes between `self` (current) and `previous`:
    /// - If spec hash changed (or unavailable): [`ChangeKind::SpecChanged`] (fail-closed).
    /// - If only body hash changed: [`ChangeKind::BodyOnly`].
    /// - Deleted/new functions: [`ChangeKind::SpecChanged`] (fail-closed).
    pub fn changed_functions_classified(
        &self,
        previous: &BodyHashRegistry,
    ) -> Vec<ClassifiedChange> {
        let mut changes = Vec::new();

        for (func, hash) in &self.hashes {
            let body_changed = match previous.hashes.get(func) {
                Some(prev_hash) => prev_hash != hash,
                None => true, // new function
            };
            if !body_changed {
                continue;
            }

            let kind = self.classify_change(func, previous);
            changes.push(ClassifiedChange {
                function: func.clone(),
                kind,
            });
        }

        // Deleted functions are always SpecChanged (signature removed entirely).
        for func in previous.hashes.keys() {
            if !self.hashes.contains_key(func) {
                changes.push(ClassifiedChange {
                    function: func.clone(),
                    kind: ChangeKind::SpecChanged,
                });
            }
        }

        changes.sort_by(|a, b| a.function.cmp(&b.function));
        changes.dedup_by(|a, b| a.function == b.function);
        changes
    }

    /// Classify a single function's change as `BodyOnly` or `SpecChanged`.
    ///
    /// Fail-closed: if spec hashes are not available for either version,
    /// defaults to `SpecChanged` to avoid under-invalidation.
    fn classify_change(&self, function: &str, previous: &BodyHashRegistry) -> ChangeKind {
        match (self.spec_hashes.get(function), previous.spec_hashes.get(function)) {
            (Some(curr_spec), Some(prev_spec)) if curr_spec == prev_spec => {
                // Spec unchanged, only body changed.
                ChangeKind::BodyOnly
            }
            (Some(_), Some(_)) => {
                // Spec changed.
                ChangeKind::SpecChanged
            }
            _ => {
                // Spec hash not available — fail-closed.
                ChangeKind::SpecChanged
            }
        }
    }
}

/// Result of a transitive invalidation operation.
#[derive(Debug, Clone)]
pub(crate) struct InvalidationResult {
    /// Functions whose bodies directly changed.
    pub directly_changed: Vec<String>,
    /// Functions whose proofs were transitively invalidated (depends on a changed function).
    pub transitively_invalidated: Vec<String>,
    /// Content IDs of certificates that were removed from the store.
    pub removed_certs: Vec<ContentId>,
    /// Total number of certificates removed.
    pub total_removed: usize,
}

/// Perform transitive invalidation: given changed functions, remove their
/// certificates AND all certificates that transitively depend on them.
///
/// Algorithm:
/// 1. Identify directly changed functions (body hash mismatch).
/// 2. For each changed function, find all transitive dependents via reverse BFS.
/// 3. Remove certificates for all affected functions from the store.
pub(crate) fn transitive_invalidation(
    store: &mut ContentStore,
    dep_graph: &DependencyGraph,
    changed_functions: &[String],
) -> InvalidationResult {
    // Compute the full set of affected functions via reverse BFS.
    let mut affected: FxHashSet<String> = FxHashSet::default();
    let mut queue: VecDeque<String> = VecDeque::new();

    for func in changed_functions {
        affected.insert(func.clone());
        queue.push_back(func.clone());
    }

    while let Some(current) = queue.pop_front() {
        // Find all functions whose proofs depend on `current`.
        let dependents = dep_graph.invalidated_by(&current);
        for dep in dependents {
            if affected.insert(dep.clone()) {
                queue.push_back(dep);
            }
        }
    }

    let transitively_invalidated: Vec<String> = affected
        .iter()
        .filter(|f| !changed_functions.contains(f))
        .cloned()
        .collect();

    // Remove certificates for all affected functions.
    let mut removed_certs = Vec::new();
    for func in &affected {
        let certs = store.find_by_function(func);
        let ids: Vec<ContentId> = certs
            .iter()
            .map(|c| ContentId::from_cert(c))
            .collect();
        for id in ids {
            if store.remove(&id).is_some() {
                removed_certs.push(id);
            }
        }
    }

    let total_removed = removed_certs.len();

    let mut directly_changed: Vec<String> = changed_functions.to_vec();
    directly_changed.sort();
    let mut trans_sorted = transitively_invalidated;
    trans_sorted.sort();

    InvalidationResult {
        directly_changed,
        transitively_invalidated: trans_sorted,
        removed_certs,
        total_removed,
    }
}

/// Perform fine-grained invalidation respecting [`ChangeKind`] distinctions.
///
/// Unlike [`transitive_invalidation`] which always invalidates all transitive
/// dependents, this function only propagates through the call graph for
/// [`ChangeKind::SpecChanged`] entries. [`ChangeKind::BodyOnly`] changes
/// invalidate only the changed function itself.
///
/// Algorithm:
/// 1. All directly changed functions are added to the affected set.
/// 2. For each `SpecChanged` function, reverse BFS finds all transitive dependents.
/// 3. `BodyOnly` functions are NOT seeds for BFS — their callers are not affected.
/// 4. Certificates for all affected functions are removed from the store.
pub(crate) fn transitive_invalidation_classified(
    store: &mut ContentStore,
    dep_graph: &DependencyGraph,
    changes: &[ClassifiedChange],
) -> InvalidationResult {
    let mut affected: FxHashSet<String> = FxHashSet::default();
    let mut queue: VecDeque<String> = VecDeque::new();
    let mut directly_changed: Vec<String> = Vec::new();

    for change in changes {
        affected.insert(change.function.clone());
        directly_changed.push(change.function.clone());

        // Only spec changes propagate through the dependency graph.
        if change.kind == ChangeKind::SpecChanged {
            queue.push_back(change.function.clone());
        }
    }

    // Reverse BFS: only seeded from SpecChanged functions.
    while let Some(current) = queue.pop_front() {
        let dependents = dep_graph.invalidated_by(&current);
        for dep in dependents {
            if affected.insert(dep.clone()) {
                queue.push_back(dep);
            }
        }
    }

    let transitively_invalidated: Vec<String> = affected
        .iter()
        .filter(|f| !directly_changed.contains(f))
        .cloned()
        .collect();

    // Remove certificates for all affected functions.
    let mut removed_certs = Vec::new();
    for func in &affected {
        let certs = store.find_by_function(func);
        let ids: Vec<ContentId> = certs
            .iter()
            .map(|c| ContentId::from_cert(c))
            .collect();
        for id in ids {
            if store.remove(&id).is_some() {
                removed_certs.push(id);
            }
        }
    }

    let total_removed = removed_certs.len();

    directly_changed.sort();
    let mut trans_sorted = transitively_invalidated;
    trans_sorted.sort();

    InvalidationResult {
        directly_changed,
        transitively_invalidated: trans_sorted,
        removed_certs,
        total_removed,
    }
}

/// Convenience: detect changes between two body hash registries and perform
/// transitive invalidation in one step.
///
/// If spec hashes are available in both registries, uses fine-grained
/// [`ChangeKind`] classification to avoid over-invalidation. Otherwise,
/// falls back to the conservative [`transitive_invalidation`] path.
pub(crate) fn invalidate_from_body_changes(
    store: &mut ContentStore,
    dep_graph: &DependencyGraph,
    previous: &BodyHashRegistry,
    current: &BodyHashRegistry,
) -> InvalidationResult {
    let classified = current.changed_functions_classified(previous);
    transitive_invalidation_classified(store, dep_graph, &classified)
}

#[cfg(test)]
mod tests {
    use trust_types::ProofStrength;

    use super::*;
    use crate::{
        CertificateChain, ChainStep, ChainStepType, ProofCertificate, SolverInfo,
        VcSnapshot,
    };
    use crate::dependency_tracker::DependencyKind;

    fn make_cert(function: &str, body: &[u8]) -> ProofCertificate {
        let vc_snapshot = VcSnapshot {
            kind: "Assertion".to_string(),
            formula_json: format!("{function}-vc"),
            location: None,
        };
        let solver = SolverInfo {
            name: "z4".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        };
        ProofCertificate::new_trusted(
            function.to_string(),
            FunctionHash::from_bytes(body),
            vc_snapshot,
            solver,
            vec![1, 2, 3],
            "2026-04-01T00:00:00Z".to_string(),
        )
    }

    fn make_chain() -> CertificateChain {
        let mut chain = CertificateChain::new();
        chain.push(ChainStep {
            step_type: ChainStepType::VcGeneration,
            tool: "trust-vcgen".to_string(),
            tool_version: "0.1.0".to_string(),
            input_hash: "mir".to_string(),
            output_hash: "vc".to_string(),
            time_ms: 1,
            timestamp: "2026-04-01T00:00:00Z".to_string(),
        });
        chain
    }

    #[test]
    fn test_body_hash_deterministic() {
        let h1 = BodyHash::from_mir(b"fn foo() -> bool { true }");
        let h2 = BodyHash::from_mir(b"fn foo() -> bool { true }");
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_body_hash_different() {
        let h1 = BodyHash::from_mir(b"fn foo() -> bool { true }");
        let h2 = BodyHash::from_mir(b"fn foo() -> bool { false }");
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_body_hash_registry_changed_functions() {
        let mut prev = BodyHashRegistry::new();
        prev.set("foo", BodyHash::from_mir(b"foo-v1"));
        prev.set("bar", BodyHash::from_mir(b"bar-v1"));

        let mut curr = BodyHashRegistry::new();
        curr.set("foo", BodyHash::from_mir(b"foo-v2")); // changed
        curr.set("bar", BodyHash::from_mir(b"bar-v1")); // unchanged

        let changed = curr.changed_functions(&prev);
        assert_eq!(changed, vec!["foo"]);
    }

    #[test]
    fn test_body_hash_registry_deleted_function() {
        let mut prev = BodyHashRegistry::new();
        prev.set("foo", BodyHash::from_mir(b"foo-v1"));
        prev.set("bar", BodyHash::from_mir(b"bar-v1"));

        let mut curr = BodyHashRegistry::new();
        curr.set("foo", BodyHash::from_mir(b"foo-v1"));
        // bar deleted

        let changed = curr.changed_functions(&prev);
        assert_eq!(changed, vec!["bar"]);
    }

    #[test]
    fn test_transitive_invalidation_direct() {
        let mut store = ContentStore::new("test");
        store.insert(make_cert("foo", b"foo-body"), make_chain());
        store.insert(make_cert("bar", b"bar-body"), make_chain());

        let graph = DependencyGraph::new();

        let result = transitive_invalidation(
            &mut store,
            &graph,
            &["foo".to_string()],
        );

        assert_eq!(result.directly_changed, vec!["foo"]);
        assert_eq!(result.total_removed, 1);
        assert_eq!(store.len(), 1);
        assert_eq!(store.find_by_function("bar").len(), 1);
        assert!(store.find_by_function("foo").is_empty());
    }

    #[test]
    fn test_transitive_invalidation_chain() {
        // a depends on b, b depends on c. If c changes, all should be invalidated.
        let mut store = ContentStore::new("test");
        store.insert(make_cert("a", b"a-body"), make_chain());
        store.insert(make_cert("b", b"b-body"), make_chain());
        store.insert(make_cert("c", b"c-body"), make_chain());
        store.insert(make_cert("d", b"d-body"), make_chain()); // independent

        let mut graph = DependencyGraph::new();
        graph.add_dependency("a", DependencyKind::CalleeSummary, "b");
        graph.add_dependency("b", DependencyKind::CalleeSummary, "c");

        let result = transitive_invalidation(
            &mut store,
            &graph,
            &["c".to_string()],
        );

        assert_eq!(result.directly_changed, vec!["c"]);
        assert_eq!(result.total_removed, 3); // a, b, c
        assert_eq!(store.len(), 1); // only d remains
        assert_eq!(store.find_by_function("d").len(), 1);
    }

    #[test]
    fn test_transitive_invalidation_diamond() {
        // top -> left, top -> right, left -> bottom, right -> bottom
        // Changing bottom should invalidate all.
        let mut store = ContentStore::new("test");
        store.insert(make_cert("top", b"top-body"), make_chain());
        store.insert(make_cert("left", b"left-body"), make_chain());
        store.insert(make_cert("right", b"right-body"), make_chain());
        store.insert(make_cert("bottom", b"bottom-body"), make_chain());

        let mut graph = DependencyGraph::new();
        graph.add_dependency("top", DependencyKind::CalleeSummary, "left");
        graph.add_dependency("top", DependencyKind::CalleeSummary, "right");
        graph.add_dependency("left", DependencyKind::CalleeSummary, "bottom");
        graph.add_dependency("right", DependencyKind::CalleeSummary, "bottom");

        let result = transitive_invalidation(
            &mut store,
            &graph,
            &["bottom".to_string()],
        );

        assert_eq!(result.total_removed, 4);
        assert!(store.is_empty());
    }

    #[test]
    fn test_invalidate_from_body_changes() {
        let mut store = ContentStore::new("test");
        store.insert(make_cert("foo", b"foo-v1"), make_chain());
        store.insert(make_cert("bar", b"bar-v1"), make_chain());

        let mut prev = BodyHashRegistry::new();
        prev.set("foo", BodyHash::from_mir(b"foo-v1"));
        prev.set("bar", BodyHash::from_mir(b"bar-v1"));

        let mut curr = BodyHashRegistry::new();
        curr.set("foo", BodyHash::from_mir(b"foo-v2")); // changed
        curr.set("bar", BodyHash::from_mir(b"bar-v1")); // same

        let graph = DependencyGraph::new();
        let result = invalidate_from_body_changes(&mut store, &graph, &prev, &curr);

        assert_eq!(result.directly_changed, vec!["foo"]);
        assert_eq!(result.total_removed, 1);
        assert_eq!(store.len(), 1);
    }

    #[test]
    fn test_body_hash_to_function_hash() {
        let bh = BodyHash::from_mir(b"some mir bytes");
        let fh = bh.to_function_hash();
        assert_eq!(fh.0.len(), 64);
        assert!(fh.0.chars().all(|c| c.is_ascii_hexdigit()));
    }

    // -------------------------------------------------------------------
    // SpecHash basics
    // -------------------------------------------------------------------

    #[test]
    fn test_spec_hash_deterministic() {
        let h1 = SpecHash::from_spec(b"fn foo() -> bool");
        let h2 = SpecHash::from_spec(b"fn foo() -> bool");
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_spec_hash_different() {
        let h1 = SpecHash::from_spec(b"fn foo() -> bool");
        let h2 = SpecHash::from_spec(b"fn foo() -> i32");
        assert_ne!(h1, h2);
    }

    // -------------------------------------------------------------------
    // Classified change detection
    // -------------------------------------------------------------------

    #[test]
    fn test_changed_functions_classified_body_only() {
        let mut prev = BodyHashRegistry::new();
        prev.set_both("foo", BodyHash::from_mir(b"foo-v1"), SpecHash::from_spec(b"foo-spec"));
        prev.set_both("bar", BodyHash::from_mir(b"bar-v1"), SpecHash::from_spec(b"bar-spec"));

        let mut curr = BodyHashRegistry::new();
        // foo: body changed, spec same => BodyOnly
        curr.set_both("foo", BodyHash::from_mir(b"foo-v2"), SpecHash::from_spec(b"foo-spec"));
        curr.set_both("bar", BodyHash::from_mir(b"bar-v1"), SpecHash::from_spec(b"bar-spec"));

        let changes = curr.changed_functions_classified(&prev);
        assert_eq!(changes.len(), 1);
        assert_eq!(changes[0].function, "foo");
        assert_eq!(changes[0].kind, ChangeKind::BodyOnly);
    }

    #[test]
    fn test_changed_functions_classified_spec_changed() {
        let mut prev = BodyHashRegistry::new();
        prev.set_both("foo", BodyHash::from_mir(b"foo-v1"), SpecHash::from_spec(b"foo-spec-v1"));

        let mut curr = BodyHashRegistry::new();
        // foo: both body and spec changed => SpecChanged
        curr.set_both("foo", BodyHash::from_mir(b"foo-v2"), SpecHash::from_spec(b"foo-spec-v2"));

        let changes = curr.changed_functions_classified(&prev);
        assert_eq!(changes.len(), 1);
        assert_eq!(changes[0].function, "foo");
        assert_eq!(changes[0].kind, ChangeKind::SpecChanged);
    }

    #[test]
    fn test_changed_functions_classified_no_spec_defaults_to_spec_changed() {
        // Without spec hashes, fail-closed: treat as SpecChanged.
        let mut prev = BodyHashRegistry::new();
        prev.set("foo", BodyHash::from_mir(b"foo-v1"));

        let mut curr = BodyHashRegistry::new();
        curr.set("foo", BodyHash::from_mir(b"foo-v2"));

        let changes = curr.changed_functions_classified(&prev);
        assert_eq!(changes.len(), 1);
        assert_eq!(changes[0].kind, ChangeKind::SpecChanged, "missing spec hashes should default to SpecChanged");
    }

    #[test]
    fn test_changed_functions_classified_deleted_is_spec_changed() {
        let mut prev = BodyHashRegistry::new();
        prev.set_both("foo", BodyHash::from_mir(b"foo-v1"), SpecHash::from_spec(b"foo-spec"));

        let curr = BodyHashRegistry::new();

        let changes = curr.changed_functions_classified(&prev);
        assert_eq!(changes.len(), 1);
        assert_eq!(changes[0].function, "foo");
        assert_eq!(changes[0].kind, ChangeKind::SpecChanged);
    }

    #[test]
    fn test_changed_functions_classified_new_function_is_spec_changed() {
        let prev = BodyHashRegistry::new();

        let mut curr = BodyHashRegistry::new();
        curr.set_both("foo", BodyHash::from_mir(b"foo-v1"), SpecHash::from_spec(b"foo-spec"));

        let changes = curr.changed_functions_classified(&prev);
        assert_eq!(changes.len(), 1);
        assert_eq!(changes[0].function, "foo");
        assert_eq!(changes[0].kind, ChangeKind::SpecChanged, "new function should be SpecChanged (fail-closed)");
    }

    // -------------------------------------------------------------------
    // Classified transitive invalidation
    // -------------------------------------------------------------------

    #[test]
    fn test_classified_body_only_does_not_invalidate_callers() {
        // a -> b -> c. If c changes body-only, only c is invalidated.
        let mut store = ContentStore::new("test");
        store.insert(make_cert("a", b"a-body"), make_chain());
        store.insert(make_cert("b", b"b-body"), make_chain());
        store.insert(make_cert("c", b"c-body"), make_chain());

        let mut graph = DependencyGraph::new();
        graph.add_dependency("a", DependencyKind::CalleeSummary, "b");
        graph.add_dependency("b", DependencyKind::CalleeSummary, "c");

        let changes = vec![ClassifiedChange {
            function: "c".to_string(),
            kind: ChangeKind::BodyOnly,
        }];

        let result = transitive_invalidation_classified(&mut store, &graph, &changes);

        assert_eq!(result.directly_changed, vec!["c"]);
        assert!(result.transitively_invalidated.is_empty(), "body-only should not invalidate callers");
        assert_eq!(result.total_removed, 1);
        assert_eq!(store.len(), 2);
        assert_eq!(store.find_by_function("a").len(), 1);
        assert_eq!(store.find_by_function("b").len(), 1);
    }

    #[test]
    fn test_classified_spec_changed_invalidates_callers() {
        // a -> b -> c. If c changes spec, all are invalidated.
        let mut store = ContentStore::new("test");
        store.insert(make_cert("a", b"a-body"), make_chain());
        store.insert(make_cert("b", b"b-body"), make_chain());
        store.insert(make_cert("c", b"c-body"), make_chain());
        store.insert(make_cert("d", b"d-body"), make_chain()); // independent

        let mut graph = DependencyGraph::new();
        graph.add_dependency("a", DependencyKind::CalleeSummary, "b");
        graph.add_dependency("b", DependencyKind::CalleeSummary, "c");

        let changes = vec![ClassifiedChange {
            function: "c".to_string(),
            kind: ChangeKind::SpecChanged,
        }];

        let result = transitive_invalidation_classified(&mut store, &graph, &changes);

        assert_eq!(result.directly_changed, vec!["c"]);
        assert!(result.transitively_invalidated.contains(&"a".to_string()));
        assert!(result.transitively_invalidated.contains(&"b".to_string()));
        assert_eq!(result.total_removed, 3); // a, b, c
        assert_eq!(store.len(), 1); // only d remains
    }

    #[test]
    fn test_classified_diamond_body_only() {
        // top -> left, top -> right, left -> bottom, right -> bottom
        // bottom changes body-only: only bottom is invalidated.
        let mut store = ContentStore::new("test");
        store.insert(make_cert("top", b"top-body"), make_chain());
        store.insert(make_cert("left", b"left-body"), make_chain());
        store.insert(make_cert("right", b"right-body"), make_chain());
        store.insert(make_cert("bottom", b"bottom-body"), make_chain());

        let mut graph = DependencyGraph::new();
        graph.add_dependency("top", DependencyKind::CalleeSummary, "left");
        graph.add_dependency("top", DependencyKind::CalleeSummary, "right");
        graph.add_dependency("left", DependencyKind::CalleeSummary, "bottom");
        graph.add_dependency("right", DependencyKind::CalleeSummary, "bottom");

        let changes = vec![ClassifiedChange {
            function: "bottom".to_string(),
            kind: ChangeKind::BodyOnly,
        }];

        let result = transitive_invalidation_classified(&mut store, &graph, &changes);

        assert_eq!(result.total_removed, 1); // only bottom
        assert_eq!(store.len(), 3);
        assert!(store.find_by_function("top").len() == 1);
        assert!(store.find_by_function("left").len() == 1);
        assert!(store.find_by_function("right").len() == 1);
    }

    #[test]
    fn test_classified_diamond_spec_changed() {
        // Same diamond as above but bottom changes spec: all 4 invalidated.
        let mut store = ContentStore::new("test");
        store.insert(make_cert("top", b"top-body"), make_chain());
        store.insert(make_cert("left", b"left-body"), make_chain());
        store.insert(make_cert("right", b"right-body"), make_chain());
        store.insert(make_cert("bottom", b"bottom-body"), make_chain());

        let mut graph = DependencyGraph::new();
        graph.add_dependency("top", DependencyKind::CalleeSummary, "left");
        graph.add_dependency("top", DependencyKind::CalleeSummary, "right");
        graph.add_dependency("left", DependencyKind::CalleeSummary, "bottom");
        graph.add_dependency("right", DependencyKind::CalleeSummary, "bottom");

        let changes = vec![ClassifiedChange {
            function: "bottom".to_string(),
            kind: ChangeKind::SpecChanged,
        }];

        let result = transitive_invalidation_classified(&mut store, &graph, &changes);

        assert_eq!(result.total_removed, 4);
        assert!(store.is_empty());
    }

    #[test]
    fn test_classified_mixed_changes() {
        // a -> b, c -> b. b changes spec (invalidates a, c), and d changes body-only.
        let mut store = ContentStore::new("test");
        store.insert(make_cert("a", b"a-body"), make_chain());
        store.insert(make_cert("b", b"b-body"), make_chain());
        store.insert(make_cert("c", b"c-body"), make_chain());
        store.insert(make_cert("d", b"d-body"), make_chain());
        store.insert(make_cert("e", b"e-body"), make_chain()); // independent

        let mut graph = DependencyGraph::new();
        graph.add_dependency("a", DependencyKind::CalleeSummary, "b");
        graph.add_dependency("c", DependencyKind::CalleeSummary, "b");

        let changes = vec![
            ClassifiedChange {
                function: "b".to_string(),
                kind: ChangeKind::SpecChanged,
            },
            ClassifiedChange {
                function: "d".to_string(),
                kind: ChangeKind::BodyOnly,
            },
        ];

        let result = transitive_invalidation_classified(&mut store, &graph, &changes);

        // b (spec changed) + a, c (transitive) + d (body only) = 4 removed
        assert_eq!(result.total_removed, 4);
        assert_eq!(store.len(), 1); // only e remains
        assert_eq!(store.find_by_function("e").len(), 1);
    }

    #[test]
    fn test_invalidate_from_body_changes_with_spec_hashes() {
        // Integration test: full pipeline with spec hash classification.
        let mut store = ContentStore::new("test");
        store.insert(make_cert("caller", b"caller-body"), make_chain());
        store.insert(make_cert("callee", b"callee-body"), make_chain());

        let mut graph = DependencyGraph::new();
        graph.add_dependency("caller", DependencyKind::CalleeSummary, "callee");

        let mut prev = BodyHashRegistry::new();
        prev.set_both("caller", BodyHash::from_mir(b"caller-v1"), SpecHash::from_spec(b"caller-spec"));
        prev.set_both("callee", BodyHash::from_mir(b"callee-v1"), SpecHash::from_spec(b"callee-spec"));

        // callee body changed, spec unchanged => BodyOnly => caller NOT invalidated
        let mut curr = BodyHashRegistry::new();
        curr.set_both("caller", BodyHash::from_mir(b"caller-v1"), SpecHash::from_spec(b"caller-spec"));
        curr.set_both("callee", BodyHash::from_mir(b"callee-v2"), SpecHash::from_spec(b"callee-spec"));

        let result = invalidate_from_body_changes(&mut store, &graph, &prev, &curr);

        assert_eq!(result.directly_changed, vec!["callee"]);
        assert!(result.transitively_invalidated.is_empty(), "body-only callee change should not invalidate caller");
        assert_eq!(result.total_removed, 1);
        assert_eq!(store.find_by_function("caller").len(), 1);
    }

    #[test]
    fn test_invalidate_from_body_changes_spec_changed_propagates() {
        // Integration test: spec change does propagate.
        let mut store = ContentStore::new("test");
        store.insert(make_cert("caller", b"caller-body"), make_chain());
        store.insert(make_cert("callee", b"callee-body"), make_chain());

        let mut graph = DependencyGraph::new();
        graph.add_dependency("caller", DependencyKind::CalleeSummary, "callee");

        let mut prev = BodyHashRegistry::new();
        prev.set_both("caller", BodyHash::from_mir(b"caller-v1"), SpecHash::from_spec(b"caller-spec"));
        prev.set_both("callee", BodyHash::from_mir(b"callee-v1"), SpecHash::from_spec(b"callee-spec-v1"));

        // callee spec changed => caller IS invalidated
        let mut curr = BodyHashRegistry::new();
        curr.set_both("caller", BodyHash::from_mir(b"caller-v1"), SpecHash::from_spec(b"caller-spec"));
        curr.set_both("callee", BodyHash::from_mir(b"callee-v2"), SpecHash::from_spec(b"callee-spec-v2"));

        let result = invalidate_from_body_changes(&mut store, &graph, &prev, &curr);

        assert_eq!(result.directly_changed, vec!["callee"]);
        assert_eq!(result.transitively_invalidated, vec!["caller"]);
        assert_eq!(result.total_removed, 2);
    }
}
