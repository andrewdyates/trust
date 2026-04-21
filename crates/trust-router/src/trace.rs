// trust-router execution trace generation
//
// Generates human-readable execution traces from replayed counterexamples.
// Shows variable values at each MIR statement for diagnostic output.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;

use trust_symex::adapter::{AdapterResult, TraceStep, ValueSnapshot};
use trust_types::Counterexample;

/// A formatted execution trace suitable for human consumption.
#[derive(Debug, Clone)]
pub struct ExecutionTrace {
    /// Function name being traced.
    pub function: String,
    /// The counterexample that triggered this trace.
    pub counterexample_summary: String,
    /// Formatted trace lines.
    pub lines: Vec<TraceLine>,
    /// Summary of the execution outcome.
    pub outcome: TraceOutcome,
}

/// A single formatted line in the execution trace.
#[derive(Debug, Clone)]
pub struct TraceLine {
    /// Step number (0-indexed).
    pub step: usize,
    /// Block index.
    pub block: usize,
    /// Statement index within the block, if applicable.
    pub stmt: Option<usize>,
    /// Human-readable description of the operation.
    pub operation: String,
    /// Variable values at this point (name -> formatted value).
    pub variables: Vec<(String, String)>,
}

/// Outcome of the traced execution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TraceOutcome {
    /// Execution completed normally (return).
    Completed,
    /// Execution hit an infeasible path (spurious counterexample).
    Spurious,
    /// Execution was cut short (depth limit, error).
    Truncated,
}

/// Generate a human-readable execution trace from an adapter result.
///
/// Takes the raw adapter result and formats it into a structured trace
/// with variable values shown at each step.
#[must_use]
pub fn generate_trace(
    function_name: &str,
    counterexample: &Counterexample,
    adapter_result: &AdapterResult,
) -> ExecutionTrace {
    let lines: Vec<TraceLine> = adapter_result
        .trace
        .iter()
        .enumerate()
        .map(|(step, trace_step)| format_trace_line(step, trace_step))
        .collect();

    let outcome = if adapter_result.terminated_normally {
        TraceOutcome::Completed
    } else {
        TraceOutcome::Spurious
    };

    ExecutionTrace {
        function: function_name.to_owned(),
        counterexample_summary: format!("{counterexample}"),
        lines,
        outcome,
    }
}

/// Format a single trace step into a human-readable trace line.
fn format_trace_line(step: usize, trace_step: &TraceStep) -> TraceLine {
    let mut variables: Vec<(String, String)> = trace_step
        .state_snapshot
        .iter()
        .map(|(name, snap)| (name.clone(), format_value_snapshot(snap)))
        .collect();

    // Sort variables by name for deterministic output.
    variables.sort_by(|a, b| a.0.cmp(&b.0));

    TraceLine {
        step,
        block: trace_step.block_idx,
        stmt: trace_step.stmt_idx,
        operation: trace_step.description.clone(),
        variables,
    }
}

/// Format a value snapshot as a human-readable string.
fn format_value_snapshot(snap: &ValueSnapshot) -> String {
    match snap.concrete {
        Some(val) => format!("{val}"),
        None => format!("<symbolic: {}>", snap.symbolic),
    }
}

impl fmt::Display for ExecutionTrace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Execution Trace: {} ===", self.function)?;
        writeln!(f, "Counterexample: {}", self.counterexample_summary)?;
        writeln!(f, "Outcome: {}", self.outcome)?;
        writeln!(f)?;

        for line in &self.lines {
            write!(f, "  [{:>3}] bb{}", line.step, line.block)?;
            if let Some(stmt) = line.stmt {
                write!(f, "[{stmt}]")?;
            } else {
                write!(f, "    ")?;
            }
            writeln!(f, "  {}", line.operation)?;

            if !line.variables.is_empty() {
                write!(f, "        vars: ")?;
                let var_strs: Vec<String> = line
                    .variables
                    .iter()
                    .map(|(name, val)| format!("{name}={val}"))
                    .collect();
                writeln!(f, "{}", var_strs.join(", "))?;
            }
        }

        Ok(())
    }
}

impl fmt::Display for TraceOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Completed => write!(f, "COMPLETED (real bug confirmed)"),
            Self::Spurious => write!(f, "SPURIOUS (infeasible path)"),
            Self::Truncated => write!(f, "TRUNCATED (execution cut short)"),
        }
    }
}

/// Render a compact single-line summary of the trace for log output.
#[must_use]
pub fn trace_summary(trace: &ExecutionTrace) -> String {
    let block_path: Vec<String> = trace
        .lines
        .iter()
        .filter(|l| l.stmt.is_none())
        .map(|l| format!("bb{}", l.block))
        .collect();

    format!(
        "{}: {} -> {} ({} steps, path: {})",
        trace.function,
        trace.counterexample_summary,
        trace.outcome,
        trace.lines.len(),
        block_path.join(" -> "),
    )
}

/// Extract the final variable values from the trace as a simple map.
///
/// Useful for diagnostic enrichment: returns the last known value of
/// each variable at the end of execution.
#[must_use]
pub fn final_variable_values(trace: &ExecutionTrace) -> Vec<(String, String)> {
    trace
        .lines
        .last()
        .map(|line| line.variables.clone())
        .unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use trust_types::fx::FxHashMap;

    use trust_types::CounterexampleValue;
    use trust_symex::adapter::AdapterResult;
    use trust_symex::state::SymbolicState;

    use super::*;

    fn make_adapter_result(terminated: bool) -> AdapterResult {
        let mut final_state = SymbolicState::new();
        final_state.set("x", trust_symex::state::SymbolicValue::Concrete(42));

        let mut snap = FxHashMap::default();
        snap.insert(
            "x".to_owned(),
            ValueSnapshot {
                symbolic: "Concrete(42)".into(),
                concrete: Some(42),
            },
        );

        AdapterResult {
            trace: vec![
                TraceStep {
                    block_idx: 0,
                    stmt_idx: None,
                    description: "entry: seed counterexample values".into(),
                    state_snapshot: FxHashMap::default(),
                },
                TraceStep {
                    block_idx: 0,
                    stmt_idx: Some(0),
                    description: "_local1 = Constant(42)".into(),
                    state_snapshot: snap.clone(),
                },
                TraceStep {
                    block_idx: 0,
                    stmt_idx: None,
                    description: "return".into(),
                    state_snapshot: snap,
                },
            ],
            final_state,
            block_trace: vec![0],
            terminated_normally: terminated,
            modified_vars: FxHashMap::default(),
        }
    }

    #[test]
    fn test_trace_generation_completed() {
        let cex = Counterexample::new(vec![(
            "x".into(),
            CounterexampleValue::Int(42),
        )]);

        let adapter_result = make_adapter_result(true);
        let trace = generate_trace("test_fn", &cex, &adapter_result);

        assert_eq!(trace.function, "test_fn");
        assert_eq!(trace.outcome, TraceOutcome::Completed);
        assert_eq!(trace.lines.len(), 3);
    }

    #[test]
    fn test_trace_generation_spurious() {
        let cex = Counterexample::new(vec![]);
        let adapter_result = make_adapter_result(false);
        let trace = generate_trace("spurious_fn", &cex, &adapter_result);

        assert_eq!(trace.outcome, TraceOutcome::Spurious);
    }

    #[test]
    fn test_trace_display_format() {
        let cex = Counterexample::new(vec![(
            "x".into(),
            CounterexampleValue::Int(42),
        )]);
        let adapter_result = make_adapter_result(true);
        let trace = generate_trace("test_fn", &cex, &adapter_result);

        let display = format!("{trace}");
        assert!(display.contains("Execution Trace: test_fn"));
        assert!(display.contains("COMPLETED"));
    }

    #[test]
    fn test_trace_summary_format() {
        let cex = Counterexample::new(vec![(
            "x".into(),
            CounterexampleValue::Int(42),
        )]);
        let adapter_result = make_adapter_result(true);
        let trace = generate_trace("test_fn", &cex, &adapter_result);

        let summary = trace_summary(&trace);
        assert!(summary.contains("test_fn"));
        assert!(summary.contains("COMPLETED"));
    }

    #[test]
    fn test_final_variable_values() {
        let cex = Counterexample::new(vec![]);
        let adapter_result = make_adapter_result(true);
        let trace = generate_trace("test_fn", &cex, &adapter_result);

        let finals = final_variable_values(&trace);
        assert!(!finals.is_empty());
        // Should contain "x" = "42".
        let x_entry = finals.iter().find(|(name, _)| name == "x");
        assert!(x_entry.is_some());
        assert_eq!(x_entry.unwrap().1, "42");
    }
}
