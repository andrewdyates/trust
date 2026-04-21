// trust-proof-cert/chain_checker.rs: Independent certificate chain checker (#249)
//
// Verifies a proof certificate chain independently from the prover.
// Checks hash integrity, dependency completeness, and cycle freedom.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};
use std::fmt::Write;

use crate::{
    CertificateId, ProofCertificate,
};

// ---------------------------------------------------------------------------
// Chain check result types
// ---------------------------------------------------------------------------

/// Result of checking a certificate chain.
#[derive(Debug, Clone)]
pub(crate) struct ChainCheckResult {
    /// Whether the chain is valid.
    pub is_valid: bool,
    /// Number of certificates checked.
    pub certs_checked: usize,
    /// Number of certificates that passed.
    pub certs_passed: usize,
    /// Individual step results.
    pub steps: Vec<StepCheckResult>,
    /// Detected issues.
    pub issues: Vec<ChainIssue>,
}

impl ChainCheckResult {
    /// Create a new empty result.
    pub fn new() -> Self {
        Self {
            is_valid: true,
            certs_checked: 0,
            certs_passed: 0,
            steps: Vec::new(),
            issues: Vec::new(),
        }
    }
}

impl Default for ChainCheckResult {
    fn default() -> Self {
        Self::new()
    }
}

/// Result of checking a single proof step.
#[derive(Debug, Clone)]
pub(crate) struct StepCheckResult {
    /// Certificate being checked.
    pub cert_id: CertificateId,
    /// Function name.
    pub function: String,
    /// Whether this step passed.
    pub passed: bool,
    /// Reason for failure (if any).
    pub failure_reason: Option<String>,
}

/// An issue detected during chain checking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ChainIssue {
    /// A certificate's vc_hash doesn't match recomputed hash.
    TamperedCertificate {
        cert_id: CertificateId,
        function: String,
    },
    /// The chain has a gap: a required function has no certificate.
    MissingCertificate {
        function: String,
    },
    /// Circular dependency in the certificate chain.
    CircularDependency {
        functions: Vec<String>,
    },
}

impl std::fmt::Display for ChainIssue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TamperedCertificate { cert_id, function } => {
                write!(f, "tampered certificate {} for function '{function}'", cert_id.0)
            }
            Self::MissingCertificate { function } => {
                write!(f, "missing certificate for function '{function}'")
            }
            Self::CircularDependency { functions } => {
                write!(f, "circular dependency: {}", functions.join(" -> "))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Chain checker
// ---------------------------------------------------------------------------

/// Independent verifier for proof certificate chains.
pub(crate) struct ChainChecker {
    /// Certificates in the chain, keyed by function name.
    certificates: FxHashMap<String, ProofCertificate>,
    /// Call graph: function -> functions it depends on.
    dependencies: FxHashMap<String, Vec<String>>,
}

impl ChainChecker {
    /// Create a new chain checker.
    pub fn new() -> Self {
        Self {
            certificates: FxHashMap::default(),
            dependencies: FxHashMap::default(),
        }
    }

    /// Add a certificate with its dependencies.
    pub fn add_certificate(&mut self, cert: ProofCertificate, deps: Vec<String>) {
        let func = cert.function.clone();
        self.dependencies.insert(func.clone(), deps);
        self.certificates.insert(func, cert);
    }

    /// Run all checks on the certificate chain.
    pub fn check(&self) -> ChainCheckResult {
        let mut result = ChainCheckResult::new();

        // Check each certificate individually.
        for cert in self.certificates.values() {
            result.certs_checked += 1;
            let step = self.check_certificate(cert);
            if step.passed {
                result.certs_passed += 1;
            } else {
                result.is_valid = false;
            }
            result.steps.push(step);
        }

        // Check completeness: all dependencies have certificates.
        for deps in self.dependencies.values() {
            for dep in deps {
                if !self.certificates.contains_key(dep) {
                    result.issues.push(ChainIssue::MissingCertificate {
                        function: dep.clone(),
                    });
                    result.is_valid = false;
                }
            }
        }

        // Check for circular dependencies.
        if let Some(cycle) = self.detect_cycle() {
            result.issues.push(ChainIssue::CircularDependency {
                functions: cycle,
            });
            result.is_valid = false;
        }

        result
    }

    /// Check a single certificate for integrity.
    fn check_certificate(&self, cert: &ProofCertificate) -> StepCheckResult {
        // Verify that the vc_hash matches recomputed hash from vc_snapshot.
        let recomputed = cert.vc_snapshot.vc_hash();
        if recomputed != cert.vc_hash {
            return StepCheckResult {
                cert_id: cert.id.clone(),
                function: cert.function.clone(),
                passed: false,
                failure_reason: Some("vc_hash mismatch: snapshot hash differs from stored hash".into()),
            };
        }

        StepCheckResult {
            cert_id: cert.id.clone(),
            function: cert.function.clone(),
            passed: true,
            failure_reason: None,
        }
    }

    /// Detect circular dependencies using DFS.
    fn detect_cycle(&self) -> Option<Vec<String>> {
        let mut visited = FxHashSet::default();
        let mut in_stack = FxHashSet::default();
        let mut path = Vec::new();

        for function in self.certificates.keys() {
            if !visited.contains(function.as_str())
                && let Some(cycle) = self.dfs_cycle(function, &mut visited, &mut in_stack, &mut path)
            {

                    return Some(cycle);

            }
        }
        None
    }

    fn dfs_cycle(
        &self,
        node: &str,
        visited: &mut FxHashSet<String>,
        in_stack: &mut FxHashSet<String>,
        path: &mut Vec<String>,
    ) -> Option<Vec<String>> {
        visited.insert(node.to_string());
        in_stack.insert(node.to_string());
        path.push(node.to_string());

        if let Some(deps) = self.dependencies.get(node) {
            for dep in deps {
                if !visited.contains(dep.as_str()) {
                    if let Some(cycle) = self.dfs_cycle(dep, visited, in_stack, path) {
                        return Some(cycle);
                    }
                } else if in_stack.contains(dep.as_str()) {
                    let start = path.iter().position(|f| f == dep).unwrap_or(0);
                    let mut cycle: Vec<_> = path[start..].to_vec();
                    cycle.push(dep.clone());
                    return Some(cycle);
                }
            }
        }

        in_stack.remove(node);
        path.pop();
        None
    }
}

impl Default for ChainChecker {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Batch checker
// ---------------------------------------------------------------------------

/// Check multiple certificate chains and aggregate results.
pub(crate) fn batch_check(chains: &[ChainChecker]) -> BatchCheckResult {
    let mut result = BatchCheckResult {
        chains_checked: chains.len(),
        chains_valid: 0,
        total_certs: 0,
        total_issues: 0,
        results: Vec::new(),
    };

    for chain in chains {
        let check = chain.check();
        result.total_certs += check.certs_checked;
        result.total_issues += check.issues.len();
        if check.is_valid {
            result.chains_valid += 1;
        }
        result.results.push(check);
    }

    result
}

/// Result of batch checking multiple chains.
#[derive(Debug)]
pub(crate) struct BatchCheckResult {
    pub chains_checked: usize,
    pub chains_valid: usize,
    pub total_certs: usize,
    pub total_issues: usize,
    pub results: Vec<ChainCheckResult>,
}

// ---------------------------------------------------------------------------
// Tamper report
// ---------------------------------------------------------------------------

/// Generate a human-readable tamper report.
pub(crate) fn tamper_report(result: &ChainCheckResult) -> String {
    let mut report = String::new();
    let _ = writeln!(report, 
        "Chain Check: {} certs, {} passed, {} issues",
        result.certs_checked, result.certs_passed, result.issues.len()
    );

    if result.is_valid {
        report.push_str("Status: VALID\n");
    } else {
        report.push_str("Status: INVALID\n");
        for issue in &result.issues {
            let _ = writeln!(report, "  - {issue}");
        }
    }

    for step in &result.steps {
        if !step.passed {
            let _ = writeln!(report, 
                "  FAIL: {} ({})",
                step.function,
                step.failure_reason.as_deref().unwrap_or("unknown")
            );
        }
    }

    report
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CertificationStatus, FunctionHash, SolverInfo, VcSnapshot};
    use trust_types::ProofStrength;

    fn sample_cert(function: &str) -> ProofCertificate {
        let vc_snapshot = VcSnapshot {
            kind: "DivisionByZero".to_string(),
            formula_json: r#"{"Bool":true}"#.to_string(),
            location: None,
        };
        let vc_hash = vc_snapshot.vc_hash();
        ProofCertificate {
            id: CertificateId::generate(function, "2026-03-30T00:00:00Z"),
            function: function.to_string(),
            function_hash: FunctionHash("abc123".to_string()),
            vc_hash,
            vc_snapshot,
            solver: SolverInfo {
                name: "z4".to_string(),
                version: "1.0".to_string(),
                time_ms: 10,
                strength: ProofStrength::smt_unsat(),
                evidence: None,
            },
            proof_steps: vec![],
            witness: None,
            chain: Default::default(),
            proof_trace: vec![],
            timestamp: "2026-03-30T00:00:00Z".to_string(),
            status: CertificationStatus::Trusted,
            version: 2,
            signature: None,
        }
    }

    #[test]
    fn test_empty_chain_is_valid() {
        let checker = ChainChecker::new();
        let result = checker.check();
        assert!(result.is_valid);
        assert_eq!(result.certs_checked, 0);
    }

    #[test]
    fn test_single_cert_valid() {
        let mut checker = ChainChecker::new();
        checker.add_certificate(sample_cert("main"), vec![]);
        let result = checker.check();
        assert!(result.is_valid);
        assert_eq!(result.certs_checked, 1);
        assert_eq!(result.certs_passed, 1);
    }

    #[test]
    fn test_chain_with_dependency() {
        let mut checker = ChainChecker::new();
        checker.add_certificate(sample_cert("main"), vec!["helper".to_string()]);
        checker.add_certificate(sample_cert("helper"), vec![]);
        let result = checker.check();
        assert!(result.is_valid);
        assert_eq!(result.certs_checked, 2);
    }

    #[test]
    fn test_missing_dependency() {
        let mut checker = ChainChecker::new();
        checker.add_certificate(sample_cert("main"), vec!["missing".to_string()]);
        let result = checker.check();
        assert!(!result.is_valid);
        assert!(result.issues.iter().any(|i|
            matches!(i, ChainIssue::MissingCertificate { function } if function == "missing")
        ));
    }

    #[test]
    fn test_circular_dependency() {
        let mut checker = ChainChecker::new();
        checker.add_certificate(sample_cert("a"), vec!["b".to_string()]);
        checker.add_certificate(sample_cert("b"), vec!["a".to_string()]);
        let result = checker.check();
        assert!(!result.is_valid);
        assert!(result.issues.iter().any(|i| matches!(i, ChainIssue::CircularDependency { .. })));
    }

    #[test]
    fn test_tampered_cert_detection() {
        let mut cert = sample_cert("main");
        // Corrupt the vc_hash.
        cert.vc_hash = [0xFF; 32];
        let mut checker = ChainChecker::new();
        checker.add_certificate(cert, vec![]);
        let result = checker.check();
        assert!(!result.is_valid);
        assert!(result.steps.iter().any(|s| !s.passed));
    }

    #[test]
    fn test_batch_check() {
        let mut c1 = ChainChecker::new();
        c1.add_certificate(sample_cert("f1"), vec![]);
        let mut c2 = ChainChecker::new();
        c2.add_certificate(sample_cert("f2"), vec!["missing".to_string()]);

        let result = batch_check(&[c1, c2]);
        assert_eq!(result.chains_checked, 2);
        assert_eq!(result.chains_valid, 1);
        assert_eq!(result.total_certs, 2);
    }

    #[test]
    fn test_tamper_report_valid() {
        let checker = ChainChecker::new();
        let result = checker.check();
        let report = tamper_report(&result);
        assert!(report.contains("VALID"));
    }

    #[test]
    fn test_tamper_report_invalid() {
        let mut checker = ChainChecker::new();
        checker.add_certificate(sample_cert("main"), vec!["missing".to_string()]);
        let result = checker.check();
        let report = tamper_report(&result);
        assert!(report.contains("INVALID"));
    }

    #[test]
    fn test_chain_issue_display() {
        let issue = ChainIssue::MissingCertificate { function: "foo".into() };
        assert!(issue.to_string().contains("foo"));
    }

    #[test]
    fn test_chain_check_result_default() {
        let result = ChainCheckResult::default();
        assert!(result.is_valid);
        assert_eq!(result.certs_checked, 0);
    }

    #[test]
    fn test_deep_chain() {
        let mut checker = ChainChecker::new();
        checker.add_certificate(sample_cert("a"), vec!["b".to_string()]);
        checker.add_certificate(sample_cert("b"), vec!["c".to_string()]);
        checker.add_certificate(sample_cert("c"), vec!["d".to_string()]);
        checker.add_certificate(sample_cert("d"), vec![]);
        let result = checker.check();
        assert!(result.is_valid);
        assert_eq!(result.certs_checked, 4);
    }
}
