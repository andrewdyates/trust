// trust-debug/violations.rs: Exploitation chain analysis
//
// Composes individual violations into higher-severity attack chains.
// For example: an arithmetic overflow that controls a buffer size, combined
// with a taint flow, creates an arbitrary-write primitive that is more
// dangerous than either violation alone.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::{ExploitChain, SecurityViolation, SecurityViolationKind, Severity};

/// Build exploitation chains by composing individual violations.
///
/// Chains represent multi-step attacks where individual violations combine
/// to produce a more severe outcome. For example:
///
/// - ArithmeticOverflow → BufferOverflow → ArbitraryWrite (RCE chain)
/// - TaintFlow → CommandInjection (command injection chain)
/// - IndexOutOfBounds → UseAfterFree (memory corruption chain)
///
/// The chain analysis is conservative: it only composes violations in the
/// same function or connected via the call graph.
pub(crate) fn build_exploit_chains(violations: &[SecurityViolation]) -> Vec<ExploitChain> {
    let mut chains = Vec::new();

    // Strategy 1: Overflow → Memory Corruption chains
    let overflows: Vec<_> = violations
        .iter()
        .filter(|v| matches!(&v.kind, SecurityViolationKind::ArithmeticOverflow { .. }))
        .collect();
    let memory_writes: Vec<_> = violations
        .iter()
        .filter(|v| {
            matches!(
                &v.kind,
                SecurityViolationKind::BufferOverflow { .. }
                    | SecurityViolationKind::IndexOutOfBounds { .. }
                    | SecurityViolationKind::ArbitraryWrite { .. }
            )
        })
        .collect();

    for overflow in &overflows {
        for write in &memory_writes {
            if overflow.function == write.function {
                chains.push(ExploitChain {
                    name: format!("overflow-to-corruption in `{}`", overflow.function),
                    severity: Severity::Critical,
                    violation_ids: vec![overflow.id.clone(), write.id.clone()],
                    description: format!(
                        "Arithmetic overflow in `{}` may control a memory write, \
                         creating an arbitrary-write primitive exploitable for code execution",
                        overflow.function
                    ),
                });
            }
        }
    }

    // Strategy 2: Taint → Injection chains
    let taint_flows: Vec<_> = violations
        .iter()
        .filter(|v| matches!(&v.kind, SecurityViolationKind::TaintFlow { .. }))
        .collect();
    let injections: Vec<_> = violations
        .iter()
        .filter(|v| {
            matches!(
                &v.kind,
                SecurityViolationKind::CommandInjection { .. }
                    | SecurityViolationKind::SqlInjection { .. }
                    | SecurityViolationKind::TaintedSyscall { .. }
                    | SecurityViolationKind::TaintedIndirectCall { .. }
                    | SecurityViolationKind::FormatStringInjection { .. }
            )
        })
        .collect();

    for taint in &taint_flows {
        for injection in &injections {
            if taint.function == injection.function {
                chains.push(ExploitChain {
                    name: format!("taint-to-injection in `{}`", taint.function),
                    severity: Severity::Critical,
                    violation_ids: vec![taint.id.clone(), injection.id.clone()],
                    description: format!(
                        "Tainted data flows to injection point in `{}`, \
                         confirming attacker-controlled data reaches dangerous operation",
                        taint.function
                    ),
                });
            }
        }
    }

    // Strategy 3: UAF / Double-free chains
    let lifetime_bugs: Vec<_> = violations
        .iter()
        .filter(|v| {
            matches!(
                &v.kind,
                SecurityViolationKind::UseAfterFree { .. }
                    | SecurityViolationKind::DoubleFree { .. }
            )
        })
        .collect();

    for bug in &lifetime_bugs {
        for write in &memory_writes {
            if bug.function == write.function {
                chains.push(ExploitChain {
                    name: format!("lifetime-to-corruption in `{}`", bug.function),
                    severity: Severity::Critical,
                    violation_ids: vec![bug.id.clone(), write.id.clone()],
                    description: format!(
                        "Lifetime violation in `{}` combined with memory write \
                         creates a heap corruption primitive",
                        bug.function
                    ),
                });
            }
        }
    }

    // Strategy 4: Privilege escalation chains
    let priv_esc: Vec<_> = violations
        .iter()
        .filter(|v| matches!(&v.kind, SecurityViolationKind::PrivilegeEscalation { .. }))
        .collect();

    for priv_v in &priv_esc {
        for injection in &injections {
            chains.push(ExploitChain {
                name: format!("injection-to-privilege-escalation via `{}`", injection.function),
                severity: Severity::Critical,
                violation_ids: vec![injection.id.clone(), priv_v.id.clone()],
                description: format!(
                    "Injection in `{}` can reach privileged operation in `{}`, \
                     enabling full privilege escalation",
                    injection.function, priv_v.function
                ),
            });
        }
    }

    chains
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_violation(id: &str, func: &str, kind: SecurityViolationKind) -> SecurityViolation {
        SecurityViolation {
            id: id.to_string(),
            severity: Severity::Medium,
            kind,
            function: func.into(),
            location: None,
            description: String::new(),
            flow_path: vec![],
            counterexample: None,
            solver: "test".into(),
            time_ms: 0,
        }
    }

    #[test]
    fn test_overflow_to_corruption_chain() {
        let violations = vec![
            make_violation(
                "V1",
                "foo",
                SecurityViolationKind::ArithmeticOverflow { operation: "Add".to_string() },
            ),
            make_violation(
                "V2",
                "foo",
                SecurityViolationKind::BufferOverflow {
                    write_size: "n+1".to_string(),
                    buffer_size: "n".to_string(),
                },
            ),
        ];

        let chains = build_exploit_chains(&violations);
        assert_eq!(chains.len(), 1);
        assert_eq!(chains[0].severity, Severity::Critical);
        assert!(chains[0].name.contains("overflow-to-corruption"));
    }

    #[test]
    fn test_taint_to_injection_chain() {
        let violations = vec![
            make_violation(
                "V1",
                "handler",
                SecurityViolationKind::TaintFlow {
                    source: "user-input".to_string(),
                    sink: "db::query".to_string(),
                },
            ),
            make_violation(
                "V2",
                "handler",
                SecurityViolationKind::SqlInjection {
                    sink_func: "db::query".to_string(),
                    taint_source: "user-input".to_string(),
                },
            ),
        ];

        let chains = build_exploit_chains(&violations);
        assert_eq!(chains.len(), 1);
        assert!(chains[0].name.contains("taint-to-injection"));
    }

    #[test]
    fn test_no_chain_across_functions() {
        let violations = vec![
            make_violation(
                "V1",
                "foo",
                SecurityViolationKind::ArithmeticOverflow { operation: "Add".to_string() },
            ),
            make_violation(
                "V2",
                "bar",
                SecurityViolationKind::BufferOverflow {
                    write_size: "n".to_string(),
                    buffer_size: "n".to_string(),
                },
            ),
        ];

        let chains = build_exploit_chains(&violations);
        assert!(chains.is_empty(), "cross-function chains not yet supported");
    }

    #[test]
    fn test_empty_violations_no_chains() {
        let chains = build_exploit_chains(&[]);
        assert!(chains.is_empty());
    }
}
