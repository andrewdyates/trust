// trust-cache/fingerprint.rs: Semantic fingerprinting for stable cache keys
//
// Computes content-based hashes that are stable across non-semantic changes
// (formatting, comments, reordering). Used as cache keys for incremental
// verification to avoid re-verifying functions whose semantics haven't changed.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use sha2::{Digest, Sha256};

/// A semantic fingerprint -- a stable hash that ignores non-semantic changes.
///
/// Uses SHA-256 for determinism across Rust versions (see #368).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SemanticFingerprint {
    /// Hex-encoded SHA-256 hash (64 chars).
    pub hash: String,
    pub components: Vec<FingerprintComponent>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FingerprintComponent {
    Body,
    TypeSignature,
    Specification,
    Dependencies,
}

#[derive(Debug, Clone)]
pub struct FingerprintConfig {
    pub include_body: bool,
    pub include_types: bool,
    pub include_specs: bool,
    pub include_deps: bool,
}

impl Default for FingerprintConfig {
    fn default() -> Self {
        Self { include_body: true, include_types: true, include_specs: true, include_deps: false }
    }
}

#[derive(Debug, Clone)]
pub struct FunctionDesc {
    pub name: String,
    pub body_tokens: Vec<String>,
    pub param_types: Vec<String>,
    pub return_type: String,
    pub preconditions: Vec<String>,
    pub postconditions: Vec<String>,
    pub dependencies: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct TypeDesc {
    pub name: String,
    pub fields: BTreeMap<String, String>,
    pub traits: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct SpecDesc {
    pub function_name: String,
    pub formulas: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FingerprintDelta {
    pub changed_components: Vec<FingerprintComponent>,
    pub is_changed: bool,
}

pub fn fingerprint_function(desc: &FunctionDesc, config: &FingerprintConfig) -> SemanticFingerprint {
    let mut hasher = Sha256::new();
    let mut components = Vec::new();
    if config.include_body {
        for token in &desc.body_tokens {
            hasher.update(token.as_bytes());
            hasher.update(b"\x00");
        }
        components.push(FingerprintComponent::Body);
    }
    if config.include_types {
        for param in &desc.param_types {
            hasher.update(param.as_bytes());
            hasher.update(b"\x00");
        }
        hasher.update(desc.return_type.as_bytes());
        hasher.update(b"\x00");
        components.push(FingerprintComponent::TypeSignature);
    }
    if config.include_specs {
        let mut sorted_pre = desc.preconditions.clone(); sorted_pre.sort();
        for pre in &sorted_pre {
            hasher.update(pre.as_bytes());
            hasher.update(b"\x00");
        }
        let mut sorted_post = desc.postconditions.clone(); sorted_post.sort();
        for post in &sorted_post {
            hasher.update(post.as_bytes());
            hasher.update(b"\x00");
        }
        components.push(FingerprintComponent::Specification);
    }
    if config.include_deps {
        let mut sorted_deps = desc.dependencies.clone(); sorted_deps.sort();
        for dep in &sorted_deps {
            hasher.update(dep.as_bytes());
            hasher.update(b"\x00");
        }
        components.push(FingerprintComponent::Dependencies);
    }
    SemanticFingerprint { hash: format!("{:x}", hasher.finalize()), components }
}

pub fn fingerprint_type(desc: &TypeDesc) -> SemanticFingerprint {
    let mut hasher = Sha256::new();
    hasher.update(desc.name.as_bytes());
    hasher.update(b"\x00");
    for (field_name, field_type) in &desc.fields {
        hasher.update(field_name.as_bytes());
        hasher.update(b"\x00");
        hasher.update(field_type.as_bytes());
        hasher.update(b"\x00");
    }
    let mut sorted_traits = desc.traits.clone(); sorted_traits.sort();
    for t in &sorted_traits {
        hasher.update(t.as_bytes());
        hasher.update(b"\x00");
    }
    SemanticFingerprint { hash: format!("{:x}", hasher.finalize()), components: vec![FingerprintComponent::TypeSignature] }
}

pub fn fingerprint_spec(desc: &SpecDesc) -> SemanticFingerprint {
    let mut hasher = Sha256::new();
    hasher.update(desc.function_name.as_bytes());
    hasher.update(b"\x00");
    let mut sorted = desc.formulas.clone(); sorted.sort();
    for formula in &sorted {
        hasher.update(formula.as_bytes());
        hasher.update(b"\x00");
    }
    SemanticFingerprint { hash: format!("{:x}", hasher.finalize()), components: vec![FingerprintComponent::Specification] }
}

pub fn is_semantically_equivalent(a: &SemanticFingerprint, b: &SemanticFingerprint) -> bool {
    a.hash == b.hash
}

pub fn compute_delta(old: &SemanticFingerprint, new: &SemanticFingerprint) -> FingerprintDelta {
    if old.hash == new.hash {
        return FingerprintDelta { changed_components: Vec::new(), is_changed: false };
    }
    FingerprintDelta { changed_components: new.components.clone(), is_changed: true }
}

/// Compute per-component SHA-256 fingerprints for detailed delta analysis.
pub fn fingerprint_function_components(desc: &FunctionDesc) -> BTreeMap<String, String> {
    let mut result = BTreeMap::new();

    let mut h = Sha256::new();
    for token in &desc.body_tokens {
        h.update(token.as_bytes());
        h.update(b"\x00");
    }
    result.insert("body".to_string(), format!("{:x}", h.finalize()));

    let mut h = Sha256::new();
    for param in &desc.param_types {
        h.update(param.as_bytes());
        h.update(b"\x00");
    }
    h.update(desc.return_type.as_bytes());
    h.update(b"\x00");
    result.insert("type_signature".to_string(), format!("{:x}", h.finalize()));

    let mut h = Sha256::new();
    let mut sp = desc.preconditions.clone(); sp.sort();
    for pre in &sp {
        h.update(pre.as_bytes());
        h.update(b"\x00");
    }
    let mut sq = desc.postconditions.clone(); sq.sort();
    for post in &sq {
        h.update(post.as_bytes());
        h.update(b"\x00");
    }
    result.insert("specification".to_string(), format!("{:x}", h.finalize()));

    result
}

pub fn detailed_delta(old: &BTreeMap<String, String>, new: &BTreeMap<String, String>) -> Vec<String> {
    let mut changed = Vec::new();
    for (key, new_hash) in new {
        match old.get(key) {
            Some(old_hash) if old_hash != new_hash => changed.push(key.clone()),
            None => changed.push(key.clone()),
            _ => {}
        }
    }
    for key in old.keys() {
        if !new.contains_key(key) { changed.push(key.clone()); }
    }
    changed.sort();
    changed
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_desc() -> FunctionDesc {
        FunctionDesc {
            name: "add".into(), body_tokens: vec!["a".into(), "+".into(), "b".into()],
            param_types: vec!["u64".into(), "u64".into()], return_type: "u64".into(),
            preconditions: vec!["a + b < u64::MAX".into()],
            postconditions: vec!["result == a + b".into()],
            dependencies: vec!["checked_add".into()],
        }
    }

    #[test]
    fn test_fingerprint_deterministic() {
        let d = make_desc(); let c = FingerprintConfig::default();
        assert_eq!(fingerprint_function(&d, &c).hash, fingerprint_function(&d, &c).hash);
    }

    #[test]
    fn test_body_change_changes_hash() {
        let mut d = make_desc(); let c = FingerprintConfig::default();
        let fp1 = fingerprint_function(&d, &c);
        d.body_tokens = vec!["a".into(), "-".into(), "b".into()];
        assert_ne!(fp1.hash, fingerprint_function(&d, &c).hash);
    }

    #[test]
    fn test_type_change_changes_hash() {
        let mut d = make_desc(); let c = FingerprintConfig::default();
        let fp1 = fingerprint_function(&d, &c);
        d.return_type = "i64".into();
        assert_ne!(fp1.hash, fingerprint_function(&d, &c).hash);
    }

    #[test]
    fn test_spec_order_invariant() {
        let mut d1 = make_desc(); d1.preconditions = vec!["a > 0".into(), "b > 0".into()];
        let mut d2 = make_desc(); d2.preconditions = vec!["b > 0".into(), "a > 0".into()];
        let c = FingerprintConfig::default();
        assert_eq!(fingerprint_function(&d1, &c).hash, fingerprint_function(&d2, &c).hash);
    }

    #[test]
    fn test_config_body_only() {
        let d = make_desc();
        let c = FingerprintConfig { include_body: true, include_types: false, include_specs: false, include_deps: false };
        assert_eq!(fingerprint_function(&d, &c).components, vec![FingerprintComponent::Body]);
    }

    #[test]
    fn test_type_fingerprint_deterministic() {
        let d = TypeDesc { name: "P".into(), fields: [("x".into(), "f64".into())].into_iter().collect(), traits: vec![] };
        assert_eq!(fingerprint_type(&d).hash, fingerprint_type(&d).hash);
    }

    #[test]
    fn test_type_field_change() {
        let d1 = TypeDesc { name: "P".into(), fields: [("x".into(), "f64".into())].into_iter().collect(), traits: vec![] };
        let d2 = TypeDesc { name: "P".into(), fields: [("x".into(), "f32".into())].into_iter().collect(), traits: vec![] };
        assert_ne!(fingerprint_type(&d1).hash, fingerprint_type(&d2).hash);
    }

    #[test]
    fn test_spec_fingerprint_order_invariant() {
        let d1 = SpecDesc { function_name: "f".into(), formulas: vec!["a".into(), "b".into()] };
        let d2 = SpecDesc { function_name: "f".into(), formulas: vec!["b".into(), "a".into()] };
        assert_eq!(fingerprint_spec(&d1).hash, fingerprint_spec(&d2).hash);
    }

    #[test]
    fn test_semantic_equivalence() {
        let d = make_desc(); let c = FingerprintConfig::default();
        let fp = fingerprint_function(&d, &c);
        assert!(is_semantically_equivalent(&fp, &fp));
    }

    #[test]
    fn test_delta_no_change() {
        let d = make_desc(); let c = FingerprintConfig::default();
        let fp = fingerprint_function(&d, &c);
        let delta = compute_delta(&fp, &fp);
        assert!(!delta.is_changed);
    }

    #[test]
    fn test_delta_with_change() {
        let mut d = make_desc(); let c = FingerprintConfig::default();
        let fp1 = fingerprint_function(&d, &c);
        d.body_tokens.push("x".into());
        let fp2 = fingerprint_function(&d, &c);
        assert!(compute_delta(&fp1, &fp2).is_changed);
    }

    #[test]
    fn test_detailed_delta_body_only() {
        let d1 = make_desc();
        let c1 = fingerprint_function_components(&d1);
        let mut d2 = d1.clone(); d2.body_tokens = vec!["changed".into()];
        let c2 = fingerprint_function_components(&d2);
        let changed = detailed_delta(&c1, &c2);
        assert!(changed.contains(&"body".to_string()));
        assert!(!changed.contains(&"type_signature".to_string()));
    }

    #[test]
    fn test_deps_order_invariant() {
        let mut d1 = make_desc(); d1.dependencies = vec!["foo".into(), "bar".into()];
        let mut d2 = make_desc(); d2.dependencies = vec!["bar".into(), "foo".into()];
        let c = FingerprintConfig { include_body: true, include_types: true, include_specs: true, include_deps: true };
        assert_eq!(fingerprint_function(&d1, &c).hash, fingerprint_function(&d2, &c).hash);
    }
}
