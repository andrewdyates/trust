// trust-runtime/monitor.rs: Runtime verification monitor
//
// Manages active runtime checks with adaptive overhead control, customizable
// violation handlers, and code generation for runtime monitoring.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::time::Instant;
use std::fmt::Write;

use serde::{Deserialize, Serialize};

use crate::{CheckStrategy, RuntimeCheck};

// ---------------------------------------------------------------------------
// CheckId
// ---------------------------------------------------------------------------

/// Opaque identifier for a registered runtime check.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) struct CheckId(u64);

impl CheckId {
    /// Underlying numeric value.
    #[must_use]
    pub(crate) fn as_u64(self) -> u64 {
        self.0
    }
}

impl std::fmt::Display for CheckId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CheckId({})", self.0)
    }
}

// ---------------------------------------------------------------------------
// MonitorConfig
// ---------------------------------------------------------------------------

/// Configuration for the runtime verification monitor.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct MonitorConfig {
    /// How often to evaluate checks (1 = every call, N = every Nth call).
    pub check_frequency: u64,
    /// Maximum acceptable overhead as a percentage of total execution (0.0..100.0).
    pub max_overhead_pct: f64,
    /// Whether to adaptively adjust check frequency based on overhead.
    pub adaptive_sampling: bool,
}

impl MonitorConfig {
    /// Create a config that checks every invocation with no overhead limit.
    #[must_use]
    pub(crate) fn always() -> Self {
        Self {
            check_frequency: 1,
            max_overhead_pct: 100.0,
            adaptive_sampling: false,
        }
    }

    /// Create a config with the given frequency and overhead limit.
    #[must_use]
    pub(crate) fn with_overhead_limit(check_frequency: u64, max_overhead_pct: f64) -> Self {
        Self {
            check_frequency: check_frequency.max(1),
            max_overhead_pct: max_overhead_pct.clamp(0.0, 100.0),
            adaptive_sampling: false,
        }
    }

    /// Enable adaptive sampling.
    #[must_use]
    pub(crate) fn with_adaptive(mut self) -> Self {
        self.adaptive_sampling = true;
        self
    }
}

impl Default for MonitorConfig {
    fn default() -> Self {
        Self::always()
    }
}

// ---------------------------------------------------------------------------
// CheckResult
// ---------------------------------------------------------------------------

/// Result of evaluating a single runtime check.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum CheckResult {
    /// Check passed -- the condition held.
    Pass {
        /// Time spent evaluating the check in microseconds.
        time_us: u64,
    },
    /// Check failed -- a violation was detected.
    Fail {
        /// Time spent evaluating the check in microseconds.
        time_us: u64,
        /// Description of the violation.
        message: String,
    },
    /// Check was skipped (overhead budget exhausted or frequency gate).
    Skip {
        /// Why the check was skipped.
        reason: SkipReason,
    },
}

/// Reason a check was skipped.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum SkipReason {
    /// The check frequency gate filtered this invocation.
    FrequencyGate,
    /// The overhead budget was exhausted.
    OverheadBudget,
}

// ---------------------------------------------------------------------------
// ViolationHandler trait
// ---------------------------------------------------------------------------

/// Customizable response to a runtime check violation.
pub(crate) trait ViolationHandler: std::fmt::Debug {
    /// Handle a violation detected by the given check.
    ///
    /// Returns `true` to continue execution, `false` to signal abort.
    fn handle_violation(&self, check: &RuntimeCheck, message: &str) -> bool;
}

/// Default handler: logs the violation and continues.
#[derive(Debug, Clone)]
pub(crate) struct DefaultHandler;

impl ViolationHandler for DefaultHandler {
    fn handle_violation(&self, check: &RuntimeCheck, message: &str) -> bool {
        eprintln!(
            "tRust runtime violation: {} in `{}` at {}:{} -- {}",
            check.description,
            check.function,
            check.location.file,
            check.location.line_start,
            message,
        );
        true // continue execution
    }
}

/// Panic handler: aborts on the first violation.
#[derive(Debug, Clone)]
pub(crate) struct PanicHandler;

impl ViolationHandler for PanicHandler {
    fn handle_violation(&self, check: &RuntimeCheck, message: &str) -> bool {
        panic!(
            "tRust runtime violation: {} in `{}` at {}:{} -- {}",
            check.description,
            check.function,
            check.location.file,
            check.location.line_start,
            message,
        );
    }
}

// ---------------------------------------------------------------------------
// MonitorStats
// ---------------------------------------------------------------------------

/// Aggregate statistics from the runtime monitor.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct MonitorStats {
    /// Total checks evaluated (excluding skips).
    pub checks_evaluated: u64,
    /// Total violations found.
    pub violations_found: u64,
    /// Total overhead in microseconds across all check evaluations.
    pub overhead_microseconds: u64,
    /// Total checks skipped.
    pub checks_skipped: u64,
}

// ---------------------------------------------------------------------------
// RuntimeMonitor
// ---------------------------------------------------------------------------

/// Entry for a registered check inside the monitor.
#[derive(Debug)]
struct CheckEntry {
    check: RuntimeCheck,
    invocation_count: u64,
    pass_count: u64,
    fail_count: u64,
    skip_count: u64,
    total_time_us: u64,
}

/// Runtime verification monitor managing active runtime checks and contracts.
#[derive(Debug)]
pub(crate) struct RuntimeMonitor {
    config: MonitorConfig,
    checks: FxHashMap<CheckId, CheckEntry>,
    next_id: u64,
    handler: Box<dyn ViolationHandler>,
    stats: MonitorStats,
    /// Active contracts keyed by function name.
    active_contracts: FxHashMap<String, ContractState>,
    /// Accumulated violation reports.
    violation_log: Vec<ViolationReport>,
    /// Accumulated monitor events.
    event_log: Vec<MonitorEvent>,
}

impl RuntimeMonitor {
    /// Create a new monitor with default configuration and the default handler.
    #[must_use]
    pub(crate) fn new(config: MonitorConfig) -> Self {
        Self {
            config,
            checks: FxHashMap::default(),
            next_id: 0,
            handler: Box::new(DefaultHandler),
            stats: MonitorStats::default(),
            active_contracts: FxHashMap::default(),
            violation_log: Vec::new(),
            event_log: Vec::new(),
        }
    }

    /// Create a monitor with a custom violation handler.
    #[must_use]
    pub(crate) fn with_handler(config: MonitorConfig, handler: Box<dyn ViolationHandler>) -> Self {
        Self {
            config,
            checks: FxHashMap::default(),
            next_id: 0,
            handler,
            stats: MonitorStats::default(),
            active_contracts: FxHashMap::default(),
            violation_log: Vec::new(),
            event_log: Vec::new(),
        }
    }

    /// Register a runtime check and return its unique identifier.
    pub(crate) fn register_check(&mut self, check: RuntimeCheck) -> CheckId {
        let id = CheckId(self.next_id);
        self.next_id += 1;
        self.checks.insert(
            id,
            CheckEntry {
                check,
                invocation_count: 0,
                pass_count: 0,
                fail_count: 0,
                skip_count: 0,
                total_time_us: 0,
            },
        );
        id
    }

    /// Evaluate a check against the provided runtime state (a key-value map of
    /// variable names to their runtime string representations).
    ///
    /// The check outcome is determined by comparing `runtime_state` entries
    /// against the check's strategy expectations.
    pub(crate) fn evaluate_check(
        &mut self,
        id: CheckId,
        runtime_state: &FxHashMap<String, String>,
    ) -> CheckResult {
        // Check existence first without holding a mutable borrow.
        if !self.checks.contains_key(&id) {
            return CheckResult::Skip {
                reason: SkipReason::FrequencyGate,
            };
        }

        // Increment invocation count and check frequency gate.
        {
            let entry = self.checks.get_mut(&id).expect("invariant: key exists");
            entry.invocation_count += 1;

            if self.config.check_frequency > 1
                && !entry.invocation_count.is_multiple_of(self.config.check_frequency)
            {
                entry.skip_count += 1;
                self.stats.checks_skipped += 1;
                return CheckResult::Skip {
                    reason: SkipReason::FrequencyGate,
                };
            }
        }
        // Mutable borrow dropped; now safe to call should_check (immutable).

        // Overhead budget check.
        let max_overhead = self.config.max_overhead_pct;
        if !self.should_check(id, max_overhead) {
            let entry = self.checks.get_mut(&id).expect("invariant: key exists");
            entry.skip_count += 1;
            self.stats.checks_skipped += 1;
            return CheckResult::Skip {
                reason: SkipReason::OverheadBudget,
            };
        }

        // Evaluate the check strategy.
        let entry = self.checks.get_mut(&id).expect("invariant: key exists");

        let start = Instant::now();
        let result = evaluate_strategy(&entry.check.strategy, runtime_state);
        let elapsed_us = start.elapsed().as_micros() as u64;

        entry.total_time_us += elapsed_us;
        self.stats.checks_evaluated += 1;
        self.stats.overhead_microseconds += elapsed_us;

        if result.is_pass() {
            entry.pass_count += 1;
            CheckResult::Pass { time_us: elapsed_us }
        } else {
            // Fail-closed: both Fail and Unknown are treated as violations.
            entry.fail_count += 1;
            self.stats.violations_found += 1;
            let reason = match result {
                StrategyResult::Fail => "condition violated",
                StrategyResult::Unknown => "could not be evaluated (fail-closed)",
                StrategyResult::Pass => unreachable!(),
            };
            let message = format!(
                "{}: {}",
                entry.check.strategy.description(),
                reason,
            );
            let continue_exec = self.handler.handle_violation(&entry.check, &message);
            if !continue_exec {
                // Handler signaled abort -- in practice this would terminate.
                // For the monitor API, we still return the Fail result.
            }
            CheckResult::Fail {
                time_us: elapsed_us,
                message,
            }
        }
    }

    /// Decide whether a check should be evaluated given the overhead budget.
    ///
    /// Returns `true` if the check is within budget, `false` if it would
    /// exceed the configured `max_overhead_pct`.
    #[must_use]
    pub(crate) fn should_check(&self, id: CheckId, overhead_budget: f64) -> bool {
        if overhead_budget >= 100.0 {
            return true;
        }

        let entry = match self.checks.get(&id) {
            Some(e) => e,
            None => return false,
        };

        // If we have no data yet, allow the check.
        if entry.invocation_count == 0 {
            return true;
        }

        // Estimate overhead as (total check time) / (total invocations * assumed_call_time).
        // Use 1us as baseline assumed per-call cost.
        let assumed_call_time_us = 1u64;
        let total_call_time_us = entry.invocation_count * assumed_call_time_us;
        if total_call_time_us == 0 {
            return true;
        }
        let overhead_pct =
            (entry.total_time_us as f64 / total_call_time_us as f64) * 100.0;

        overhead_pct <= overhead_budget
    }

    /// Get current aggregate statistics.
    #[must_use]
    pub(crate) fn stats(&self) -> &MonitorStats {
        &self.stats
    }

    /// Number of registered checks.
    #[must_use]
    pub(crate) fn check_count(&self) -> usize {
        self.checks.len()
    }

    /// Get the check associated with an id.
    #[must_use]
    pub(crate) fn get_check(&self, id: CheckId) -> Option<&RuntimeCheck> {
        self.checks.get(&id).map(|e| &e.check)
    }

    /// Record a monitor event and update state accordingly.
    pub(crate) fn record_event(&mut self, event: MonitorEvent) {
        match &event {
            MonitorEvent::FunctionEntry { function, contract } => {
                let state = ContractState {
                    function: function.clone(),
                    preconditions_checked: false,
                    postconditions_checked: false,
                    precondition_passed: false,
                    postcondition_passed: false,
                    args: FxHashMap::default(),
                    contract: contract.clone(),
                };
                self.active_contracts.insert(function.clone(), state);
            }
            MonitorEvent::FunctionExit { function } => {
                self.active_contracts.remove(function.as_str());
            }
            MonitorEvent::AssertionCheck { function, passed } => {
                self.stats.checks_evaluated += 1;
                if !passed {
                    self.stats.violations_found += 1;
                }
                // Update contract state if tracked.
                if let Some(cs) = self.active_contracts.get_mut(function.as_str())
                    && !passed {
                        cs.precondition_passed = false;
                    }
            }
            MonitorEvent::Violation { report } => {
                self.stats.violations_found += 1;
                self.violation_log.push(report.clone());
            }
        }
        self.event_log.push(event);
    }

    /// Evaluate requires clauses for a function at entry.
    ///
    /// Records results in the contract state and returns a `ViolationReport`
    /// on the first failing clause, or `None` if all pass.
    pub(crate) fn check_precondition(
        &mut self,
        function: &str,
        args: &FxHashMap<String, String>,
    ) -> Option<ViolationReport> {
        let contract = match self.active_contracts.get(function) {
            Some(cs) => cs.contract.clone(),
            None => return None,
        };

        // Store args in contract state.
        if let Some(cs) = self.active_contracts.get_mut(function) {
            cs.args = args.clone();
            cs.preconditions_checked = true;
        }

        let result =
            crate::contract::ContractEnforcer::check_precondition(&contract, args);

        match result {
            Ok(()) => {
                if let Some(cs) = self.active_contracts.get_mut(function) {
                    cs.precondition_passed = true;
                }
                self.stats.checks_evaluated += 1;
                None
            }
            Err(err) => {
                if let Some(cs) = self.active_contracts.get_mut(function) {
                    cs.precondition_passed = false;
                }
                self.stats.checks_evaluated += 1;
                self.stats.violations_found += 1;
                let report = ViolationReport {
                    function: function.to_string(),
                    kind: ViolationKind::PreconditionFailed,
                    message: format!("{err}"),
                    contract_description: format!(
                        "{} preconditions",
                        contract.preconditions.len()
                    ),
                    context: args.clone(),
                };
                self.violation_log.push(report.clone());
                self.event_log.push(MonitorEvent::Violation {
                    report: report.clone(),
                });
                Some(report)
            }
        }
    }

    /// Evaluate ensures clauses for a function at exit.
    ///
    /// Uses the args captured at function entry as `old_state`.
    /// Returns a `ViolationReport` on the first failing clause, or `None`.
    pub(crate) fn check_postcondition(
        &mut self,
        function: &str,
        result_state: &FxHashMap<String, String>,
    ) -> Option<ViolationReport> {
        let (contract, old_args) = match self.active_contracts.get(function) {
            Some(cs) => (cs.contract.clone(), cs.args.clone()),
            None => return None,
        };

        if let Some(cs) = self.active_contracts.get_mut(function) {
            cs.postconditions_checked = true;
        }

        let result = crate::contract::ContractEnforcer::check_postcondition(
            &contract,
            result_state,
            &old_args,
        );

        match result {
            Ok(()) => {
                if let Some(cs) = self.active_contracts.get_mut(function) {
                    cs.postcondition_passed = true;
                }
                self.stats.checks_evaluated += 1;
                None
            }
            Err(err) => {
                if let Some(cs) = self.active_contracts.get_mut(function) {
                    cs.postcondition_passed = false;
                }
                self.stats.checks_evaluated += 1;
                self.stats.violations_found += 1;
                let report = ViolationReport {
                    function: function.to_string(),
                    kind: ViolationKind::PostconditionFailed,
                    message: format!("{err}"),
                    contract_description: format!(
                        "{} postconditions",
                        contract.postconditions.len()
                    ),
                    context: result_state.clone(),
                };
                self.violation_log.push(report.clone());
                self.event_log.push(MonitorEvent::Violation {
                    report: report.clone(),
                });
                Some(report)
            }
        }
    }

    /// Get the contract state for a currently-active function.
    #[must_use]
    pub(crate) fn get_contract_state(&self, function: &str) -> Option<&ContractState> {
        self.active_contracts.get(function)
    }

    /// Get all recorded violation reports.
    #[must_use]
    pub(crate) fn violation_log(&self) -> &[ViolationReport] {
        &self.violation_log
    }

    /// Get all recorded events.
    #[must_use]
    pub(crate) fn event_log(&self) -> &[MonitorEvent] {
        &self.event_log
    }

    /// Number of active contracts being tracked.
    #[must_use]
    pub(crate) fn active_contract_count(&self) -> usize {
        self.active_contracts.len()
    }
}

// ---------------------------------------------------------------------------
// MonitorEvent
// ---------------------------------------------------------------------------

/// Events emitted by the runtime verification monitor.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum MonitorEvent {
    /// A monitored function was entered.
    FunctionEntry {
        function: String,
        contract: crate::contract::Contract,
    },
    /// A monitored function returned.
    FunctionExit {
        function: String,
    },
    /// A runtime assertion was checked.
    AssertionCheck {
        function: String,
        passed: bool,
    },
    /// A contract violation was detected.
    Violation {
        report: ViolationReport,
    },
}

// ---------------------------------------------------------------------------
// ContractState
// ---------------------------------------------------------------------------

/// Tracks the evaluation state of a contract during a monitored function call.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct ContractState {
    /// The function being monitored.
    pub function: String,
    /// Whether preconditions have been evaluated.
    pub preconditions_checked: bool,
    /// Whether postconditions have been evaluated.
    pub postconditions_checked: bool,
    /// Whether preconditions passed.
    pub precondition_passed: bool,
    /// Whether postconditions passed.
    pub postcondition_passed: bool,
    /// Arguments captured at function entry (for old-value postconditions).
    pub args: FxHashMap<String, String>,
    /// The contract being enforced.
    pub contract: crate::contract::Contract,
}

// ---------------------------------------------------------------------------
// ViolationReport
// ---------------------------------------------------------------------------

/// Detailed report of a contract violation detected at runtime.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct ViolationReport {
    /// The function where the violation occurred.
    pub function: String,
    /// What kind of violation was detected.
    pub kind: ViolationKind,
    /// Human-readable description of the violation.
    pub message: String,
    /// Description of the contract that was violated.
    pub contract_description: String,
    /// Runtime state at the time of the violation.
    pub context: FxHashMap<String, String>,
}

impl std::fmt::Display for ViolationReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{}] {} in `{}`: {}",
            self.kind, self.message, self.function, self.contract_description
        )
    }
}

// ---------------------------------------------------------------------------
// ViolationKind
// ---------------------------------------------------------------------------

/// Classification of contract violations.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum ViolationKind {
    /// A `requires` clause failed at function entry.
    PreconditionFailed,
    /// An `ensures` clause failed at function exit.
    PostconditionFailed,
    /// A runtime assertion failed.
    AssertionFailed,
    /// An invariant was violated.
    InvariantViolated,
}

impl std::fmt::Display for ViolationKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ViolationKind::PreconditionFailed => write!(f, "PRECONDITION"),
            ViolationKind::PostconditionFailed => write!(f, "POSTCONDITION"),
            ViolationKind::AssertionFailed => write!(f, "ASSERTION"),
            ViolationKind::InvariantViolated => write!(f, "INVARIANT"),
        }
    }
}

// ---------------------------------------------------------------------------
// Strategy evaluation result (tri-state)
// ---------------------------------------------------------------------------

/// Result of evaluating a check strategy.
///
/// Fail-closed: callers should treat `Unknown` as a violation unless
/// explicitly configured for fail-open behavior.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StrategyResult {
    /// The strategy condition held.
    Pass,
    /// The strategy condition was violated.
    Fail,
    /// The strategy could not be evaluated (deferred to compiler
    /// instrumentation, or missing runtime state).
    Unknown,
}

impl StrategyResult {
    /// Returns `true` only if the strategy definitively passed.
    fn is_pass(self) -> bool {
        self == StrategyResult::Pass
    }
}

// ---------------------------------------------------------------------------
// Strategy evaluation
// ---------------------------------------------------------------------------

/// Evaluate a check strategy against runtime state.
///
/// `runtime_state` maps variable names (e.g., "index", "len", "divisor") to
/// their string-encoded runtime values.
///
/// Returns `StrategyResult::Unknown` for deferred strategies or when required
/// state is missing (fail-closed: callers treat Unknown as a violation).
fn evaluate_strategy(
    strategy: &CheckStrategy,
    state: &FxHashMap<String, String>,
) -> StrategyResult {
    match strategy {
        CheckStrategy::BoundsCheck => {
            let index = parse_u64(state.get("index"));
            let len = parse_u64(state.get("len"));
            match (index, len) {
                (Some(i), Some(l)) => bool_to_result(i < l),
                // Cannot evaluate -- Unknown (fail-closed).
                _ => StrategyResult::Unknown,
            }
        }
        CheckStrategy::DivisorNonZero => {
            let divisor = parse_i64(state.get("divisor"));
            match divisor {
                Some(d) => bool_to_result(d != 0),
                // Missing divisor state -- Unknown (fail-closed).
                None => StrategyResult::Unknown,
            }
        }
        CheckStrategy::SliceRangeCheck => {
            let start = parse_u64(state.get("start"));
            let end = parse_u64(state.get("end"));
            let len = parse_u64(state.get("len"));
            match (start, end, len) {
                (Some(s), Some(e), Some(l)) => bool_to_result(s <= e && e <= l),
                _ => StrategyResult::Unknown,
            }
        }
        CheckStrategy::OverflowCheck { .. }
        | CheckStrategy::ShiftCheck
        | CheckStrategy::NegationCheck => {
            // These are compiler-emitted checks; runtime state evaluation
            // is deferred to the compiler's own instrumentation.
            // If instrumentation is absent (e.g., release builds), we cannot
            // confirm the check passed -- return Unknown (fail-closed).
            StrategyResult::Unknown
        }
        CheckStrategy::PreserveAssertion { .. } => {
            // Evaluate based on a "condition" key in state.
            match state.get("condition") {
                Some(v) => bool_to_result(v == "true" || v == "1"),
                // Missing condition state -- Unknown (fail-closed).
                None => StrategyResult::Unknown,
            }
        }
        CheckStrategy::UnreachablePanic => {
            // If we reach evaluation, the unreachable code was reached.
            // A "reached" key in state signals this.
            match state.get("reached") {
                Some(v) => bool_to_result(v != "true" && v != "1"),
                // Missing reached state -- Unknown (fail-closed).
                None => StrategyResult::Unknown,
            }
        }
    }
}

/// Convert a boolean check result to a `StrategyResult`.
fn bool_to_result(passed: bool) -> StrategyResult {
    if passed {
        StrategyResult::Pass
    } else {
        StrategyResult::Fail
    }
}

/// Parse a string value as u64.
fn parse_u64(value: Option<&String>) -> Option<u64> {
    value.and_then(|v| v.parse().ok())
}

/// Parse a string value as i64.
fn parse_i64(value: Option<&String>) -> Option<i64> {
    value.and_then(|v| v.parse().ok())
}

// ---------------------------------------------------------------------------
// Code generation
// ---------------------------------------------------------------------------

/// Generate Rust code for a runtime monitoring harness that evaluates
/// all provided checks.
#[must_use]
pub(crate) fn generate_monitor_code(checks: &[RuntimeCheck]) -> String {
    let mut code = String::new();
    code.push_str("// tRust: Generated runtime monitor\n");
    code.push_str("// This code evaluates runtime checks for unproved VCs.\n\n");
    code.push_str("#[cfg(trust_runtime)]\n");
    code.push_str("mod trust_monitor {\n");
    code.push_str("    use std::collections::HashMap;\n\n");

    for (i, check) in checks.iter().enumerate() {
        let _ = writeln!(code, 
            "    /// Check {}: {} in `{}`",
            i, check.description, check.function
        );
        let _ = writeln!(code, "    fn check_{}(state: &HashMap<String, String>) -> bool {{", i);
        code.push_str(&generate_strategy_check(&check.strategy, "        "));
        code.push_str("    }\n\n");
    }

    // Generate the dispatch function.
    code.push_str("    pub fn evaluate_all(state: &HashMap<String, String>) -> Vec<bool> {\n");
    code.push_str("        vec![\n");
    for i in 0..checks.len() {
        let _ = writeln!(code, "            check_{}(state),", i);
    }
    code.push_str("        ]\n");
    code.push_str("    }\n");

    code.push_str("}\n");
    code
}

/// Generate the body of a strategy check function.
///
/// Generated code is fail-closed: missing state causes the check to fail
/// rather than silently passing. Deferred strategies (compiler-emitted)
/// also fail when instrumentation cannot be confirmed.
fn generate_strategy_check(strategy: &CheckStrategy, indent: &str) -> String {
    match strategy {
        CheckStrategy::BoundsCheck => {
            // Fail-closed: missing index or len fails the check.
            format!(
                "{indent}let index: Option<usize> = state.get(\"index\").and_then(|v| v.parse().ok());\n\
                 {indent}let len: Option<usize> = state.get(\"len\").and_then(|v| v.parse().ok());\n\
                 {indent}match (index, len) {{ (Some(i), Some(l)) => i < l, _ => false }}\n"
            )
        }
        CheckStrategy::DivisorNonZero => {
            // Fail-closed: missing divisor fails the check (no unwrap_or(1)).
            format!(
                "{indent}let divisor: Option<i64> = state.get(\"divisor\").and_then(|v| v.parse().ok());\n\
                 {indent}match divisor {{ Some(d) => d != 0, None => false }}\n"
            )
        }
        CheckStrategy::SliceRangeCheck => {
            // Fail-closed: missing start/end/len fails the check.
            format!(
                "{indent}let start: Option<usize> = state.get(\"start\").and_then(|v| v.parse().ok());\n\
                 {indent}let end: Option<usize> = state.get(\"end\").and_then(|v| v.parse().ok());\n\
                 {indent}let len: Option<usize> = state.get(\"len\").and_then(|v| v.parse().ok());\n\
                 {indent}match (start, end, len) {{ (Some(s), Some(e), Some(l)) => s <= e && e <= l, _ => false }}\n"
            )
        }
        CheckStrategy::PreserveAssertion { message } => {
            // Fail-closed: missing condition fails the check.
            format!(
                "{indent}// Preserved assertion: {}\n\
                 {indent}let cond: bool = state.get(\"condition\").map(|v| v == \"true\" || v == \"1\").unwrap_or(false);\n\
                 {indent}cond\n",
                message.replace('"', "\\\"")
            )
        }
        CheckStrategy::UnreachablePanic => {
            // Fail-closed: missing reached state assumes unreachable was
            // reached (conservative).
            format!(
                "{indent}// If this code is reached, the unreachable was reached\n\
                 {indent}let reached: bool = state.get(\"reached\").map(|v| v == \"true\" || v == \"1\").unwrap_or(true);\n\
                 {indent}!reached\n"
            )
        }
        CheckStrategy::OverflowCheck { .. }
        | CheckStrategy::ShiftCheck
        | CheckStrategy::NegationCheck => {
            // Fail-closed: deferred to compiler instrumentation which may
            // be absent in release builds.
            format!("{indent}false // compiler-emitted check: fail-closed when instrumentation absent\n")
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CheckKind, CheckStrategy, RuntimeCheck};
    use trust_types::SourceSpan;

    fn span() -> SourceSpan {
        SourceSpan {
            file: "src/lib.rs".to_string(),
            line_start: 42,
            col_start: 5,
            line_end: 42,
            col_end: 30,
        }
    }

    fn make_check(kind: CheckKind, strategy: CheckStrategy) -> RuntimeCheck {
        RuntimeCheck {
            kind,
            location: span(),
            description: "test check".to_string(),
            strategy,
            function: "test_fn".to_string(),
        }
    }

    fn state(pairs: &[(&str, &str)]) -> FxHashMap<String, String> {
        pairs
            .iter()
            .map(|(k, v)| (k.to_string(), v.to_string()))
            .collect()
    }

    // -----------------------------------------------------------------------
    // CheckId
    // -----------------------------------------------------------------------

    #[test]
    fn test_check_id_display() {
        let id = CheckId(42);
        assert_eq!(format!("{id}"), "CheckId(42)");
        assert_eq!(id.as_u64(), 42);
    }

    // -----------------------------------------------------------------------
    // MonitorConfig
    // -----------------------------------------------------------------------

    #[test]
    fn test_config_always() {
        let config = MonitorConfig::always();
        assert_eq!(config.check_frequency, 1);
        assert!((config.max_overhead_pct - 100.0).abs() < f64::EPSILON);
        assert!(!config.adaptive_sampling);
    }

    #[test]
    fn test_config_with_overhead_limit() {
        let config = MonitorConfig::with_overhead_limit(10, 5.0);
        assert_eq!(config.check_frequency, 10);
        assert!((config.max_overhead_pct - 5.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_config_clamps_overhead() {
        let config = MonitorConfig::with_overhead_limit(1, 150.0);
        assert!((config.max_overhead_pct - 100.0).abs() < f64::EPSILON);

        let config = MonitorConfig::with_overhead_limit(1, -10.0);
        assert!(config.max_overhead_pct.abs() < f64::EPSILON);
    }

    #[test]
    fn test_config_clamps_frequency() {
        let config = MonitorConfig::with_overhead_limit(0, 50.0);
        assert_eq!(config.check_frequency, 1);
    }

    #[test]
    fn test_config_default() {
        let config = MonitorConfig::default();
        assert_eq!(config.check_frequency, 1);
    }

    #[test]
    fn test_config_with_adaptive() {
        let config = MonitorConfig::always().with_adaptive();
        assert!(config.adaptive_sampling);
    }

    // -----------------------------------------------------------------------
    // Check registration
    // -----------------------------------------------------------------------

    #[test]
    fn test_register_check() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let check = make_check(CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck);
        let id = monitor.register_check(check.clone());
        assert_eq!(id.as_u64(), 0);
        assert_eq!(monitor.check_count(), 1);
        assert!(monitor.get_check(id).is_some());
        assert_eq!(monitor.get_check(id).unwrap().function, "test_fn");
    }

    #[test]
    fn test_register_multiple_checks() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let id1 = monitor.register_check(make_check(
            CheckKind::IndexOutOfBounds,
            CheckStrategy::BoundsCheck,
        ));
        let id2 = monitor.register_check(make_check(
            CheckKind::DivisionByZero,
            CheckStrategy::DivisorNonZero,
        ));
        assert_ne!(id1, id2);
        assert_eq!(monitor.check_count(), 2);
    }

    // -----------------------------------------------------------------------
    // Check evaluation: BoundsCheck
    // -----------------------------------------------------------------------

    #[test]
    fn test_evaluate_bounds_check_pass() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let id = monitor.register_check(make_check(
            CheckKind::IndexOutOfBounds,
            CheckStrategy::BoundsCheck,
        ));

        let s = state(&[("index", "3"), ("len", "10")]);
        let result = monitor.evaluate_check(id, &s);
        assert!(matches!(result, CheckResult::Pass { .. }));
        assert_eq!(monitor.stats().checks_evaluated, 1);
        assert_eq!(monitor.stats().violations_found, 0);
    }

    #[test]
    fn test_evaluate_bounds_check_fail() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let id = monitor.register_check(make_check(
            CheckKind::IndexOutOfBounds,
            CheckStrategy::BoundsCheck,
        ));

        let s = state(&[("index", "10"), ("len", "5")]);
        let result = monitor.evaluate_check(id, &s);
        assert!(matches!(result, CheckResult::Fail { .. }));
        assert_eq!(monitor.stats().violations_found, 1);
    }

    #[test]
    fn test_evaluate_bounds_check_missing_state_fails_closed() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let id = monitor.register_check(make_check(
            CheckKind::IndexOutOfBounds,
            CheckStrategy::BoundsCheck,
        ));

        let s = state(&[]); // no index or len
        let result = monitor.evaluate_check(id, &s);
        // Missing state => Unknown => fail-closed (treated as violation).
        assert!(matches!(result, CheckResult::Fail { .. }));
        assert_eq!(monitor.stats().violations_found, 1);
    }

    // -----------------------------------------------------------------------
    // Check evaluation: DivisorNonZero
    // -----------------------------------------------------------------------

    #[test]
    fn test_evaluate_divisor_nonzero_pass() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let id = monitor.register_check(make_check(
            CheckKind::DivisionByZero,
            CheckStrategy::DivisorNonZero,
        ));

        let s = state(&[("divisor", "7")]);
        let result = monitor.evaluate_check(id, &s);
        assert!(matches!(result, CheckResult::Pass { .. }));
    }

    #[test]
    fn test_evaluate_divisor_nonzero_fail() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let id = monitor.register_check(make_check(
            CheckKind::DivisionByZero,
            CheckStrategy::DivisorNonZero,
        ));

        let s = state(&[("divisor", "0")]);
        let result = monitor.evaluate_check(id, &s);
        assert!(matches!(result, CheckResult::Fail { .. }));
    }

    // -----------------------------------------------------------------------
    // Check evaluation: SliceRangeCheck
    // -----------------------------------------------------------------------

    #[test]
    fn test_evaluate_slice_range_pass() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let id = monitor.register_check(make_check(
            CheckKind::SliceBoundsCheck,
            CheckStrategy::SliceRangeCheck,
        ));

        let s = state(&[("start", "2"), ("end", "5"), ("len", "10")]);
        let result = monitor.evaluate_check(id, &s);
        assert!(matches!(result, CheckResult::Pass { .. }));
    }

    #[test]
    fn test_evaluate_slice_range_fail_start_gt_end() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let id = monitor.register_check(make_check(
            CheckKind::SliceBoundsCheck,
            CheckStrategy::SliceRangeCheck,
        ));

        let s = state(&[("start", "6"), ("end", "3"), ("len", "10")]);
        let result = monitor.evaluate_check(id, &s);
        assert!(matches!(result, CheckResult::Fail { .. }));
    }

    #[test]
    fn test_evaluate_slice_range_fail_end_gt_len() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let id = monitor.register_check(make_check(
            CheckKind::SliceBoundsCheck,
            CheckStrategy::SliceRangeCheck,
        ));

        let s = state(&[("start", "0"), ("end", "15"), ("len", "10")]);
        let result = monitor.evaluate_check(id, &s);
        assert!(matches!(result, CheckResult::Fail { .. }));
    }

    // -----------------------------------------------------------------------
    // Frequency gating
    // -----------------------------------------------------------------------

    #[test]
    fn test_frequency_gate_skips_intermediate() {
        let config = MonitorConfig::with_overhead_limit(3, 100.0);
        let mut monitor = RuntimeMonitor::new(config);
        let id = monitor.register_check(make_check(
            CheckKind::IndexOutOfBounds,
            CheckStrategy::BoundsCheck,
        ));

        let s = state(&[("index", "0"), ("len", "10")]);

        // Invocation 1: skipped (1 % 3 != 0)
        let r1 = monitor.evaluate_check(id, &s);
        assert!(matches!(r1, CheckResult::Skip { reason: SkipReason::FrequencyGate }));

        // Invocation 2: skipped (2 % 3 != 0)
        let r2 = monitor.evaluate_check(id, &s);
        assert!(matches!(r2, CheckResult::Skip { reason: SkipReason::FrequencyGate }));

        // Invocation 3: evaluated (3 % 3 == 0)
        let r3 = monitor.evaluate_check(id, &s);
        assert!(matches!(r3, CheckResult::Pass { .. }));

        assert_eq!(monitor.stats().checks_evaluated, 1);
        assert_eq!(monitor.stats().checks_skipped, 2);
    }

    // -----------------------------------------------------------------------
    // Overhead control
    // -----------------------------------------------------------------------

    #[test]
    fn test_should_check_unregistered_with_limited_budget() {
        let monitor = RuntimeMonitor::new(MonitorConfig::always());
        let id = CheckId(999);
        // Nonexistent check with limited budget => false (no entry).
        assert!(!monitor.should_check(id, 50.0));
    }

    #[test]
    fn test_should_check_unlimited_budget_short_circuits() {
        let monitor = RuntimeMonitor::new(MonitorConfig::always());
        let id = CheckId(999);
        // With 100% budget, should_check returns true immediately.
        assert!(monitor.should_check(id, 100.0));
    }

    #[test]
    fn test_should_check_registered() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let id = monitor.register_check(make_check(
            CheckKind::IndexOutOfBounds,
            CheckStrategy::BoundsCheck,
        ));
        // No invocations yet => allow.
        assert!(monitor.should_check(id, 5.0));
    }

    // -----------------------------------------------------------------------
    // Violation handlers
    // -----------------------------------------------------------------------

    #[test]
    fn test_default_handler_continues() {
        let handler = DefaultHandler;
        let check = make_check(CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck);
        assert!(handler.handle_violation(&check, "test violation"));
    }

    #[test]
    #[should_panic(expected = "tRust runtime violation")]
    fn test_panic_handler_panics() {
        let handler = PanicHandler;
        let check = make_check(CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck);
        handler.handle_violation(&check, "test violation");
    }

    #[test]
    fn test_monitor_with_custom_handler() {
        let mut monitor = RuntimeMonitor::with_handler(
            MonitorConfig::always(),
            Box::new(DefaultHandler),
        );
        let id = monitor.register_check(make_check(
            CheckKind::DivisionByZero,
            CheckStrategy::DivisorNonZero,
        ));

        let s = state(&[("divisor", "0")]);
        let result = monitor.evaluate_check(id, &s);
        assert!(matches!(result, CheckResult::Fail { .. }));
    }

    // -----------------------------------------------------------------------
    // MonitorStats
    // -----------------------------------------------------------------------

    #[test]
    fn test_stats_accumulate() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let id = monitor.register_check(make_check(
            CheckKind::IndexOutOfBounds,
            CheckStrategy::BoundsCheck,
        ));

        let pass_state = state(&[("index", "0"), ("len", "10")]);
        let fail_state = state(&[("index", "10"), ("len", "5")]);

        monitor.evaluate_check(id, &pass_state);
        monitor.evaluate_check(id, &pass_state);
        monitor.evaluate_check(id, &fail_state);

        let stats = monitor.stats();
        assert_eq!(stats.checks_evaluated, 3);
        assert_eq!(stats.violations_found, 1);
    }

    // -----------------------------------------------------------------------
    // Unregistered check
    // -----------------------------------------------------------------------

    #[test]
    fn test_evaluate_unregistered_check() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let bogus_id = CheckId(999);
        let s = state(&[]);
        let result = monitor.evaluate_check(bogus_id, &s);
        assert!(matches!(
            result,
            CheckResult::Skip { reason: SkipReason::FrequencyGate }
        ));
    }

    // -----------------------------------------------------------------------
    // Code generation
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_monitor_code_empty() {
        let code = generate_monitor_code(&[]);
        assert!(code.contains("#[cfg(trust_runtime)]"));
        assert!(code.contains("mod trust_monitor"));
        assert!(code.contains("evaluate_all"));
    }

    #[test]
    fn test_generate_monitor_code_bounds_check() {
        let checks = vec![make_check(
            CheckKind::IndexOutOfBounds,
            CheckStrategy::BoundsCheck,
        )];
        let code = generate_monitor_code(&checks);
        assert!(code.contains("check_0"));
        assert!(code.contains("index"));
        assert!(code.contains("len"));
    }

    #[test]
    fn test_generate_monitor_code_multiple_checks() {
        let checks = vec![
            make_check(CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck),
            make_check(CheckKind::DivisionByZero, CheckStrategy::DivisorNonZero),
            make_check(CheckKind::SliceBoundsCheck, CheckStrategy::SliceRangeCheck),
        ];
        let code = generate_monitor_code(&checks);
        assert!(code.contains("check_0"));
        assert!(code.contains("check_1"));
        assert!(code.contains("check_2"));
        assert!(code.contains("divisor"));
        // SliceRangeCheck emits: (Some(s), Some(e), Some(l)) => s <= e && e <= l
        assert!(code.contains("s <= e"));
    }

    #[test]
    fn test_generate_monitor_code_overflow_fail_closed() {
        let checks = vec![make_check(
            CheckKind::ArithmeticOverflow,
            CheckStrategy::OverflowCheck { op: trust_types::BinOp::Add },
        )];
        let code = generate_monitor_code(&checks);
        // Deferred strategies now emit fail-closed code.
        assert!(code.contains("compiler-emitted check"));
        assert!(code.contains("false"));
    }

    // -----------------------------------------------------------------------
    // Serialization
    // -----------------------------------------------------------------------

    #[test]
    fn test_check_result_serialization() {
        let results = vec![
            CheckResult::Pass { time_us: 42 },
            CheckResult::Fail {
                time_us: 10,
                message: "oops".to_string(),
            },
            CheckResult::Skip {
                reason: SkipReason::OverheadBudget,
            },
        ];

        for result in &results {
            let json = serde_json::to_string(result).expect("serialize");
            let roundtrip: CheckResult = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(&roundtrip, result);
        }
    }

    #[test]
    fn test_monitor_stats_serialization() {
        let stats = MonitorStats {
            checks_evaluated: 100,
            violations_found: 3,
            overhead_microseconds: 5000,
            checks_skipped: 20,
        };
        let json = serde_json::to_string(&stats).expect("serialize");
        let roundtrip: MonitorStats = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip, stats);
    }

    #[test]
    fn test_config_serialization() {
        let config = MonitorConfig::with_overhead_limit(5, 10.0).with_adaptive();
        let json = serde_json::to_string(&config).expect("serialize");
        let roundtrip: MonitorConfig = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip, config);
    }

    #[test]
    fn test_check_id_serialization() {
        let id = CheckId(42);
        let json = serde_json::to_string(&id).expect("serialize");
        let roundtrip: CheckId = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip, id);
    }

    // -----------------------------------------------------------------------
    // Contract monitoring: helpers
    // -----------------------------------------------------------------------

    fn make_contract(name: &str) -> crate::contract::Contract {
        use crate::contract::{Contract, ContractClause};
        Contract::new(name)
            .with_precondition(ContractClause::new(
                "b must be nonzero",
                "b != 0",
                vec!["b".to_string()],
            ))
            .with_postcondition(ContractClause::new(
                "result <= a",
                "result <= a",
                vec!["result".to_string(), "a".to_string()],
            ))
    }

    // -----------------------------------------------------------------------
    // Contract monitoring: MonitorEvent + record_event
    // -----------------------------------------------------------------------

    #[test]
    fn test_record_function_entry_creates_contract_state() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let contract = make_contract("safe_div");

        monitor.record_event(MonitorEvent::FunctionEntry {
            function: "safe_div".to_string(),
            contract: contract.clone(),
        });

        assert_eq!(monitor.active_contract_count(), 1);
        let cs = monitor.get_contract_state("safe_div").unwrap();
        assert_eq!(cs.function, "safe_div");
        assert!(!cs.preconditions_checked);
        assert!(!cs.postconditions_checked);
        assert_eq!(cs.contract, contract);
    }

    #[test]
    fn test_record_function_exit_removes_contract_state() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        monitor.record_event(MonitorEvent::FunctionEntry {
            function: "f".to_string(),
            contract: make_contract("f"),
        });
        assert_eq!(monitor.active_contract_count(), 1);

        monitor.record_event(MonitorEvent::FunctionExit {
            function: "f".to_string(),
        });
        assert_eq!(monitor.active_contract_count(), 0);
    }

    #[test]
    fn test_record_assertion_check_updates_stats() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        monitor.record_event(MonitorEvent::AssertionCheck {
            function: "f".to_string(),
            passed: true,
        });
        assert_eq!(monitor.stats().checks_evaluated, 1);
        assert_eq!(monitor.stats().violations_found, 0);

        monitor.record_event(MonitorEvent::AssertionCheck {
            function: "f".to_string(),
            passed: false,
        });
        assert_eq!(monitor.stats().checks_evaluated, 2);
        assert_eq!(monitor.stats().violations_found, 1);
    }

    #[test]
    fn test_record_violation_event_logs_report() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let report = ViolationReport {
            function: "f".to_string(),
            kind: ViolationKind::PreconditionFailed,
            message: "b was zero".to_string(),
            contract_description: "1 preconditions".to_string(),
            context: state(&[("b", "0")]),
        };
        monitor.record_event(MonitorEvent::Violation {
            report: report.clone(),
        });
        assert_eq!(monitor.violation_log().len(), 1);
        assert_eq!(monitor.violation_log()[0], report);
        assert_eq!(monitor.stats().violations_found, 1);
    }

    #[test]
    fn test_event_log_records_all_events() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let contract = make_contract("f");

        monitor.record_event(MonitorEvent::FunctionEntry {
            function: "f".to_string(),
            contract,
        });
        monitor.record_event(MonitorEvent::AssertionCheck {
            function: "f".to_string(),
            passed: true,
        });
        monitor.record_event(MonitorEvent::FunctionExit {
            function: "f".to_string(),
        });

        assert_eq!(monitor.event_log().len(), 3);
    }

    // -----------------------------------------------------------------------
    // Contract monitoring: check_precondition
    // -----------------------------------------------------------------------

    #[test]
    fn test_check_precondition_pass() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let contract = make_contract("safe_div");

        monitor.record_event(MonitorEvent::FunctionEntry {
            function: "safe_div".to_string(),
            contract,
        });

        let args = state(&[("b", "5")]);
        let result = monitor.check_precondition("safe_div", &args);
        assert!(result.is_none());

        let cs = monitor.get_contract_state("safe_div").unwrap();
        assert!(cs.preconditions_checked);
        assert!(cs.precondition_passed);
        assert_eq!(monitor.stats().checks_evaluated, 1);
    }

    #[test]
    fn test_check_precondition_fail_returns_violation_report() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let contract = make_contract("safe_div");

        monitor.record_event(MonitorEvent::FunctionEntry {
            function: "safe_div".to_string(),
            contract,
        });

        let args = state(&[("b", "0")]);
        let report = monitor.check_precondition("safe_div", &args);
        assert!(report.is_some());

        let report = report.unwrap();
        assert_eq!(report.function, "safe_div");
        assert_eq!(report.kind, ViolationKind::PreconditionFailed);
        assert!(report.message.contains("precondition violated"));

        let cs = monitor.get_contract_state("safe_div").unwrap();
        assert!(cs.preconditions_checked);
        assert!(!cs.precondition_passed);
        assert_eq!(monitor.stats().violations_found, 1);
    }

    #[test]
    fn test_check_precondition_no_active_contract() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let args = state(&[("b", "0")]);
        // No function entry recorded => None.
        let result = monitor.check_precondition("nonexistent", &args);
        assert!(result.is_none());
    }

    // -----------------------------------------------------------------------
    // Contract monitoring: check_postcondition
    // -----------------------------------------------------------------------

    #[test]
    fn test_check_postcondition_pass() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let contract = make_contract("safe_div");

        monitor.record_event(MonitorEvent::FunctionEntry {
            function: "safe_div".to_string(),
            contract,
        });

        // Set args at precondition time.
        let args = state(&[("a", "10"), ("b", "2")]);
        monitor.check_precondition("safe_div", &args);

        // Check postcondition: result <= a => 5 <= 10 => pass.
        let result_state = state(&[("result", "5")]);
        let report = monitor.check_postcondition("safe_div", &result_state);
        assert!(report.is_none());

        let cs = monitor.get_contract_state("safe_div").unwrap();
        assert!(cs.postconditions_checked);
        assert!(cs.postcondition_passed);
    }

    #[test]
    fn test_check_postcondition_fail_returns_violation_report() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let contract = make_contract("safe_div");

        monitor.record_event(MonitorEvent::FunctionEntry {
            function: "safe_div".to_string(),
            contract,
        });

        let args = state(&[("a", "10"), ("b", "2")]);
        monitor.check_precondition("safe_div", &args);

        // Check postcondition: result <= a => 20 <= 10 => fail.
        let result_state = state(&[("result", "20")]);
        let report = monitor.check_postcondition("safe_div", &result_state);
        assert!(report.is_some());

        let report = report.unwrap();
        assert_eq!(report.kind, ViolationKind::PostconditionFailed);
        assert!(report.message.contains("postcondition violated"));
        assert_eq!(monitor.violation_log().len(), 1);
    }

    #[test]
    fn test_check_postcondition_no_active_contract() {
        let mut monitor = RuntimeMonitor::new(MonitorConfig::always());
        let result_state = state(&[("result", "5")]);
        let report = monitor.check_postcondition("nonexistent", &result_state);
        assert!(report.is_none());
    }

    // -----------------------------------------------------------------------
    // ViolationReport + ViolationKind
    // -----------------------------------------------------------------------

    #[test]
    fn test_violation_report_display() {
        let report = ViolationReport {
            function: "safe_div".to_string(),
            kind: ViolationKind::PreconditionFailed,
            message: "b was zero".to_string(),
            contract_description: "1 preconditions".to_string(),
            context: state(&[("b", "0")]),
        };
        let display = format!("{report}");
        assert!(display.contains("PRECONDITION"));
        assert!(display.contains("safe_div"));
        assert!(display.contains("b was zero"));
    }

    #[test]
    fn test_violation_kind_display() {
        assert_eq!(format!("{}", ViolationKind::PreconditionFailed), "PRECONDITION");
        assert_eq!(format!("{}", ViolationKind::PostconditionFailed), "POSTCONDITION");
        assert_eq!(format!("{}", ViolationKind::AssertionFailed), "ASSERTION");
        assert_eq!(format!("{}", ViolationKind::InvariantViolated), "INVARIANT");
    }

    // -----------------------------------------------------------------------
    // ContractState serialization
    // -----------------------------------------------------------------------

    #[test]
    fn test_contract_state_serialization() {
        let cs = ContractState {
            function: "f".to_string(),
            preconditions_checked: true,
            postconditions_checked: false,
            precondition_passed: true,
            postcondition_passed: false,
            args: state(&[("x", "1")]),
            contract: make_contract("f"),
        };
        let json = serde_json::to_string(&cs).expect("serialize");
        let roundtrip: ContractState = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip, cs);
    }

    #[test]
    fn test_violation_report_serialization() {
        let report = ViolationReport {
            function: "f".to_string(),
            kind: ViolationKind::PostconditionFailed,
            message: "result too large".to_string(),
            contract_description: "1 postconditions".to_string(),
            context: state(&[("result", "999")]),
        };
        let json = serde_json::to_string(&report).expect("serialize");
        let roundtrip: ViolationReport = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip, report);
    }
}
