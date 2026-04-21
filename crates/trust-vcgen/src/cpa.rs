// trust-vcgen/cpa.rs: Configurable Program Analysis framework
//
// Provides a lightweight CPAchecker-style framework over tRust's verification
// IR. Domains implement lattice-style state operations, transfer functions
// evolve states through statements, and a configurable worklist algorithm
// handles merge and stop policies at control-flow join points.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use trust_types::fx::FxHashMap;

use serde::{Deserialize, Serialize};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Formula, Operand, Place, Projection, Rvalue, Sort,
    Statement, Terminator, UnOp, VerifiableBody,
};

use crate::abstract_interp::{
    AbstractDomain, Interval, IntervalDomain, interval_add, interval_mul, interval_sub,
};

/// A single abstract state in a configurable program analysis.
pub trait CpaState: Clone + PartialEq {
    /// Join two states at a control-flow merge point.
    #[must_use]
    fn join(&self, other: &Self) -> Self;

    /// Returns true when the state is unreachable.
    #[must_use]
    fn is_bottom(&self) -> bool;

    /// Partial order over abstract states.
    #[must_use]
    fn leq(&self, other: &Self) -> bool;

    /// Convert the abstract state into a solver-level formula.
    #[must_use]
    fn to_formula(&self) -> Formula;
}

/// Statement-level transfer function for a CPA domain.
pub trait TransferFunction<S>
where
    S: CpaState,
{
    /// Apply one statement to an abstract state.
    #[must_use]
    fn transfer(&self, state: &S, stmt: &Statement) -> S;
}

/// Merge policy at join points.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum MergeOperator {
    /// Keep abstract states separate.
    Sep,
    /// Join abstract states into one summary state.
    Join,
}

/// Stop policy for reached states.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum StopOperator {
    /// Stop only on exact duplicates.
    Sep,
    /// Stop when the candidate is covered by the join of reached states.
    Join,
    /// Stop when a single reached state covers the candidate.
    Coverage,
}

/// Configuration for the CPA algorithm.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct CpaConfig {
    /// How states merge when they reach the same block.
    pub merge: MergeOperator,
    /// When exploration stops for a candidate successor state.
    pub stop: StopOperator,
    /// Hard limit on worklist iterations.
    pub max_iterations: usize,
}

impl CpaConfig {
    /// Construct a CPA configuration explicitly.
    #[must_use]
    pub fn new(merge: MergeOperator, stop: StopOperator, max_iterations: usize) -> Self {
        Self { merge, stop, max_iterations }
    }
}

impl Default for CpaConfig {
    fn default() -> Self {
        Self { merge: MergeOperator::Join, stop: StopOperator::Coverage, max_iterations: 10_000 }
    }
}

/// Errors produced by the CPA framework.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum CpaError {
    /// The body contains no entry block.
    #[error("cannot run CPA on an empty body")]
    EmptyBody,

    /// Control flow referenced a block that does not exist.
    #[error("block {block:?} does not exist in the verifiable body")]
    MissingBlock { block: BlockId },

    /// The configured iteration budget was exceeded.
    #[error("CPA exceeded the configured iteration limit of {limit}")]
    MaxIterationsReached { limit: usize },
}

/// Interval-domain wrapper that implements the CPA state interface.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpaDomain {
    /// Wrapped interval domain.
    pub intervals: IntervalDomain,
}

impl CpaDomain {
    /// Wrap an interval domain as a CPA state.
    #[must_use]
    pub fn new(intervals: IntervalDomain) -> Self {
        Self { intervals }
    }

    /// Create the top interval state.
    #[must_use]
    pub fn top() -> Self {
        Self::new(IntervalDomain::top())
    }

    /// Create the bottom interval state.
    #[must_use]
    pub fn bottom() -> Self {
        Self::new(IntervalDomain::bottom())
    }

    /// Read a variable's interval.
    #[must_use]
    pub fn get(&self, var: &str) -> Interval {
        self.intervals.get(var)
    }

    /// Update a variable's interval.
    pub fn set(&mut self, var: impl Into<String>, interval: Interval) {
        self.intervals.set(var.into(), interval);
    }

    /// Borrow the wrapped interval domain.
    #[must_use]
    pub fn as_interval_domain(&self) -> &IntervalDomain {
        &self.intervals
    }

    /// Consume the wrapper and return the wrapped interval domain.
    #[must_use]
    pub fn into_interval_domain(self) -> IntervalDomain {
        self.intervals
    }
}

impl From<IntervalDomain> for CpaDomain {
    fn from(intervals: IntervalDomain) -> Self {
        Self::new(intervals)
    }
}

impl CpaState for CpaDomain {
    fn join(&self, other: &Self) -> Self {
        Self::new(self.intervals.join(&other.intervals))
    }

    fn is_bottom(&self) -> bool {
        self.intervals.is_bottom()
    }

    fn leq(&self, other: &Self) -> bool {
        self.intervals.leq(&other.intervals)
    }

    fn to_formula(&self) -> Formula {
        if self.is_bottom() {
            return Formula::Bool(false);
        }

        let mut conjuncts = Vec::new();

        for (name, interval) in &self.intervals.vars {
            if interval.is_bottom() {
                return Formula::Bool(false);
            }

            let var = Formula::Var(name.clone(), Sort::Int);
            if interval.lo != i128::MIN {
                conjuncts
                    .push(Formula::Ge(Box::new(var.clone()), Box::new(Formula::Int(interval.lo))));
            }
            if interval.hi != i128::MAX {
                conjuncts.push(Formula::Le(Box::new(var), Box::new(Formula::Int(interval.hi))));
            }
        }

        conjoin(conjuncts)
    }
}

/// Product domain over two CPA states.
#[derive(Debug, Clone, PartialEq)]
pub struct CompositeDomain<L, R> {
    /// Left component.
    pub left: L,
    /// Right component.
    pub right: R,
}

impl<L, R> CompositeDomain<L, R> {
    /// Construct a product-domain state.
    #[must_use]
    pub fn new(left: L, right: R) -> Self {
        Self { left, right }
    }
}

impl<L, R> CpaState for CompositeDomain<L, R>
where
    L: CpaState,
    R: CpaState,
{
    fn join(&self, other: &Self) -> Self {
        Self::new(self.left.join(&other.left), self.right.join(&other.right))
    }

    fn is_bottom(&self) -> bool {
        self.left.is_bottom() || self.right.is_bottom()
    }

    fn leq(&self, other: &Self) -> bool {
        self.left.leq(&other.left) && self.right.leq(&other.right)
    }

    fn to_formula(&self) -> Formula {
        if self.is_bottom() {
            return Formula::Bool(false);
        }
        conjoin(vec![self.left.to_formula(), self.right.to_formula()])
    }
}

/// Interval-based transfer function for the CPA interval wrapper.
#[derive(Debug, Clone, Copy)]
pub struct IntervalTransfer<'a> {
    body: &'a VerifiableBody,
}

impl<'a> IntervalTransfer<'a> {
    /// Construct an interval transfer function for one body.
    #[must_use]
    pub fn new(body: &'a VerifiableBody) -> Self {
        Self { body }
    }
}

impl TransferFunction<CpaDomain> for IntervalTransfer<'_> {
    fn transfer(&self, state: &CpaDomain, stmt: &Statement) -> CpaDomain {
        let mut next = state.clone();
        if next.is_bottom() {
            return next;
        }

        match stmt {
            Statement::Assign { place, rvalue, .. } => {
                let target = place_to_var_name(self.body, place);
                let interval = eval_rvalue(self.body, state.as_interval_domain(), rvalue);
                next.set(target, interval);
            }
            Statement::Nop => {}
            _ => {},
        }

        next
    }
}

/// A generic worklist-based CPA algorithm over a verifiable body.
pub struct CpaAlgorithm<'a, S, T>
where
    S: CpaState,
    T: TransferFunction<S>,
{
    body: &'a VerifiableBody,
    transfer: T,
    initial_state: S,
    config: CpaConfig,
}

impl<'a, S, T> CpaAlgorithm<'a, S, T>
where
    S: CpaState,
    T: TransferFunction<S>,
{
    /// Construct a CPA algorithm instance.
    #[must_use]
    pub fn new(body: &'a VerifiableBody, transfer: T, initial_state: S, config: CpaConfig) -> Self {
        Self { body, transfer, initial_state, config }
    }

    /// Run the configured CPA to a block-state fixpoint.
    pub fn run(&self) -> Result<FxHashMap<BlockId, S>, CpaError> {
        let Some(entry_block) = self.body.blocks.first().map(|block| block.id) else {
            return Err(CpaError::EmptyBody);
        };

        let mut reached: FxHashMap<BlockId, Vec<S>> = FxHashMap::default();
        reached.insert(entry_block, vec![self.initial_state.clone()]);

        let mut worklist = VecDeque::from([(entry_block, self.initial_state.clone())]);
        let mut iterations = 0usize;

        while let Some((block_id, entry_state)) = worklist.pop_front() {
            if iterations >= self.config.max_iterations {
                return Err(CpaError::MaxIterationsReached { limit: self.config.max_iterations });
            }
            iterations += 1;

            if entry_state.is_bottom() {
                continue;
            }

            let block = self.block(block_id)?;
            let exit_state = block
                .stmts
                .iter()
                .fold(entry_state, |state, stmt| self.transfer.transfer(&state, stmt));

            if exit_state.is_bottom() {
                continue;
            }

            for successor in successor_blocks(&block.terminator) {
                let _ = self.block(successor)?;
                let reached_states = reached.entry(successor).or_default();

                if should_stop(reached_states, &exit_state, self.config.stop) {
                    continue;
                }

                if let Some(next_state) =
                    merge_candidate(reached_states, exit_state.clone(), self.config.merge)
                {
                    worklist.push_back((successor, next_state));
                }
            }
        }

        Ok(summarize_reached(reached))
    }

    fn block(&self, block_id: BlockId) -> Result<&BasicBlock, CpaError> {
        self.body
            .blocks
            .iter()
            .find(|block| block.id == block_id)
            .ok_or(CpaError::MissingBlock { block: block_id })
    }
}

fn successor_blocks(terminator: &Terminator) -> Vec<BlockId> {
    match terminator {
        Terminator::Goto(target) | Terminator::Drop { target, .. } => vec![*target],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut successors = targets.iter().map(|(_, block)| *block).collect::<Vec<_>>();
            successors.push(*otherwise);
            successors
        }
        Terminator::Assert { target, .. } => vec![*target],
        Terminator::Call { target, .. } => target.iter().copied().collect(),
        Terminator::Return | Terminator::Unreachable => Vec::new(),
        _ => vec![],
    }
}

fn should_stop<S>(reached: &[S], candidate: &S, stop: StopOperator) -> bool
where
    S: CpaState,
{
    if candidate.is_bottom() {
        return true;
    }

    match stop {
        StopOperator::Sep => reached.iter().any(|state| state == candidate),
        StopOperator::Join => joined_state(reached).is_some_and(|joined| candidate.leq(&joined)),
        StopOperator::Coverage => reached.iter().any(|state| candidate.leq(state)),
    }
}

fn merge_candidate<S>(reached: &mut Vec<S>, candidate: S, merge: MergeOperator) -> Option<S>
where
    S: CpaState,
{
    match merge {
        MergeOperator::Sep => {
            reached.push(candidate.clone());
            Some(candidate)
        }
        MergeOperator::Join => {
            let merged = match joined_state(reached) {
                Some(existing) => existing.join(&candidate),
                None => candidate.clone(),
            };

            let unchanged =
                reached.len() == 1 && reached.first().is_some_and(|state| *state == merged);
            if unchanged {
                return None;
            }

            reached.clear();
            reached.push(merged.clone());
            Some(merged)
        }
    }
}

fn joined_state<S>(states: &[S]) -> Option<S>
where
    S: CpaState,
{
    let mut iter = states.iter();
    let first = iter.next()?.clone();
    Some(iter.fold(first, |joined, state| joined.join(state)))
}

fn summarize_reached<S>(reached: FxHashMap<BlockId, Vec<S>>) -> FxHashMap<BlockId, S>
where
    S: CpaState,
{
    reached
        .into_iter()
        .filter_map(|(block_id, states)| joined_state(&states).map(|state| (block_id, state)))
        .collect()
}

fn conjoin(mut formulae: Vec<Formula>) -> Formula {
    formulae.retain(|formula| *formula != Formula::Bool(true));
    match formulae.len() {
        0 => Formula::Bool(true),
        1 => formulae.pop().unwrap_or(Formula::Bool(true)),
        _ => Formula::And(formulae),
    }
}

fn place_to_var_name(body: &VerifiableBody, place: &Place) -> String {
    let fallback = format!("_{}", place.local);
    let base =
        body.locals.get(place.local).and_then(|decl| decl.name.as_deref()).unwrap_or(&fallback);

    if place.projections.is_empty() {
        return base.to_string();
    }

    let projections = place
        .projections
        .iter()
        .map(|projection| match projection {
            Projection::Field(index) => format!(".{index}"),
            Projection::Index(index) => format!("[_{index}]"),
            Projection::Deref => "*".to_string(),
            Projection::Downcast(index) => format!("@{index}"),
            Projection::ConstantIndex { offset, from_end } => {
                if *from_end { format!("[-{offset}]") } else { format!("[{offset}]") }
            }
            Projection::Subslice { from, to, from_end } => {
                if *from_end { format!("[{from}..-{to}]") } else { format!("[{from}..{to}]") }
            }
            _ => "unknown".to_string(),
        })
        .collect::<Vec<_>>()
        .join("");
    format!("{base}{projections}")
}

fn operand_to_interval(op: &Operand, body: &VerifiableBody, state: &IntervalDomain) -> Interval {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            let name = place_to_var_name(body, place);
            state.get(&name)
        }
        Operand::Constant(constant) => match constant {
            ConstValue::Bool(value) => Interval::constant(i128::from(*value)),
            ConstValue::Int(value) => Interval::constant(*value),
            ConstValue::Uint(value, _) => {
                i128::try_from(*value).map_or(Interval::TOP, Interval::constant)
            }
            ConstValue::Float(_) | ConstValue::Unit => Interval::TOP,
            _ => Interval::TOP,
        },
        _ => Interval::TOP,
    }
}

fn eval_rvalue(body: &VerifiableBody, state: &IntervalDomain, rvalue: &Rvalue) -> Interval {
    match rvalue {
        Rvalue::Use(op) => operand_to_interval(op, body, state),
        Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            let left = operand_to_interval(lhs, body, state);
            let right = operand_to_interval(rhs, body, state);
            match op {
                BinOp::Add => interval_add(&left, &right),
                BinOp::Sub => interval_sub(&left, &right),
                BinOp::Mul => interval_mul(&left, &right),
                _ => Interval::TOP,
            }
        }
        Rvalue::UnaryOp(UnOp::Neg, op) => {
            let interval = operand_to_interval(op, body, state);
            if interval.is_bottom() {
                return Interval::BOTTOM;
            }

            match (interval.hi.checked_neg(), interval.lo.checked_neg()) {
                (Some(lo), Some(hi)) => Interval::new(lo, hi),
                _ => Interval::TOP,
            }
        }
        Rvalue::UnaryOp(UnOp::Not | UnOp::PtrMetadata, _) => Interval::TOP,
        Rvalue::Len(_) | Rvalue::Discriminant(_) => Interval::new(0, i128::MAX),
        Rvalue::Ref { .. }
        | Rvalue::AddressOf(_, _)
        | Rvalue::Cast(_, _)
        | Rvalue::Aggregate(_, _)
        | Rvalue::CopyForDeref(_) => Interval::TOP,
        Rvalue::Repeat(op, _) => operand_to_interval(op, body, state),
        _ => Interval::TOP,
    }
}

// ── Taint Analysis Domain ───────────────────────────────────────────────────
//
// A CPA domain that tracks taint propagation through variables. Tainted
// values originate from external inputs (function arguments, calls to
// taint sources) and flow through assignments and operations.
//
// Combined with CpaDomain via CompositeDomain, this enables the CPA
// framework to run safety (intervals) + taint analysis simultaneously
// on a single function.

/// Taint classification for a single variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TaintLevel {
    /// Not tainted (safe).
    Clean,
    /// Tainted — value may come from an untrusted source.
    Tainted,
    /// Sanitized — was tainted but passed through a sanitizer.
    Sanitized,
}

impl TaintLevel {
    /// Join two taint levels (upper bound in the taint lattice).
    ///
    /// `Tainted` dominates `Sanitized`, which dominates `Clean`.
    #[must_use]
    fn join(self, other: Self) -> Self {
        match (self, other) {
            (TaintLevel::Tainted, _) | (_, TaintLevel::Tainted) => TaintLevel::Tainted,
            (TaintLevel::Sanitized, _) | (_, TaintLevel::Sanitized) => TaintLevel::Sanitized,
            _ => TaintLevel::Clean,
        }
    }

    /// Partial order: Clean <= Sanitized <= Tainted.
    #[must_use]
    fn leq(self, other: Self) -> bool {
        matches!(
            (self, other),
            (TaintLevel::Clean, _)
                | (TaintLevel::Sanitized, TaintLevel::Sanitized)
                | (TaintLevel::Sanitized, TaintLevel::Tainted)
                | (TaintLevel::Tainted, TaintLevel::Tainted)
        )
    }
}

/// A taint-tracking CPA state: maps variable names to taint levels.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TaintDomain {
    /// Per-variable taint classification.
    pub vars: FxHashMap<String, TaintLevel>,
    /// Whether this state is bottom (unreachable).
    pub is_bottom: bool,
}

impl TaintDomain {
    /// Create a top state (all variables clean by default).
    #[must_use]
    pub fn top() -> Self {
        Self { vars: FxHashMap::default(), is_bottom: false }
    }

    /// Create a bottom state (unreachable).
    #[must_use]
    pub fn bottom() -> Self {
        Self { vars: FxHashMap::default(), is_bottom: true }
    }

    /// Get the taint level for a variable (default: Clean).
    #[must_use]
    pub fn get(&self, var: &str) -> TaintLevel {
        if self.is_bottom {
            return TaintLevel::Clean;
        }
        self.vars.get(var).copied().unwrap_or(TaintLevel::Clean)
    }

    /// Set the taint level for a variable.
    pub fn set(&mut self, var: impl Into<String>, level: TaintLevel) {
        if !self.is_bottom {
            self.vars.insert(var.into(), level);
        }
    }

    /// Mark a variable as tainted (e.g., from external input).
    pub fn taint(&mut self, var: impl Into<String>) {
        self.set(var, TaintLevel::Tainted);
    }

    /// Mark a variable as sanitized.
    pub fn sanitize(&mut self, var: impl Into<String>) {
        self.set(var, TaintLevel::Sanitized);
    }

    /// Check if any variable is tainted.
    #[must_use]
    pub fn has_tainted_vars(&self) -> bool {
        self.vars.values().any(|&level| level == TaintLevel::Tainted)
    }

    /// Return all tainted variable names.
    #[must_use]
    pub fn tainted_vars(&self) -> Vec<String> {
        self.vars
            .iter()
            .filter(|&(_, &level)| level == TaintLevel::Tainted)
            .map(|(name, _)| name.clone())
            .collect()
    }
}

impl CpaState for TaintDomain {
    fn join(&self, other: &Self) -> Self {
        if self.is_bottom {
            return other.clone();
        }
        if other.is_bottom {
            return self.clone();
        }

        let mut vars = FxHashMap::default();
        let all_keys: std::collections::BTreeSet<&String> =
            self.vars.keys().chain(other.vars.keys()).collect();
        for key in all_keys {
            let a = self.get(key);
            let b = other.get(key);
            let joined = a.join(b);
            if joined != TaintLevel::Clean {
                vars.insert(key.clone(), joined);
            }
        }
        Self { vars, is_bottom: false }
    }

    fn is_bottom(&self) -> bool {
        self.is_bottom
    }

    fn leq(&self, other: &Self) -> bool {
        if self.is_bottom {
            return true;
        }
        if other.is_bottom {
            return false;
        }
        // For each variable in self, its taint must be <= the taint in other.
        for (name, &level) in &self.vars {
            if !level.leq(other.get(name)) {
                return false;
            }
        }
        true
    }

    fn to_formula(&self) -> Formula {
        if self.is_bottom {
            return Formula::Bool(false);
        }
        // Encode taint as boolean variables: tainted(x) = true if x is tainted.
        let mut conjuncts = Vec::new();
        for (name, &level) in &self.vars {
            let taint_var = Formula::Var(format!("tainted_{name}"), Sort::Bool);
            match level {
                TaintLevel::Tainted => conjuncts.push(taint_var),
                TaintLevel::Clean => {
                    conjuncts.push(Formula::Not(Box::new(taint_var)));
                }
                TaintLevel::Sanitized => {
                    // Sanitized is clean for formula purposes.
                    conjuncts.push(Formula::Not(Box::new(taint_var)));
                }
            }
        }
        conjoin(conjuncts)
    }
}

/// Taint transfer function for the CPA taint domain.
///
/// Propagates taint through assignments: if any source operand is tainted,
/// the destination becomes tainted. Constants are always clean.
#[derive(Debug, Clone)]
pub struct TaintTransfer<'a> {
    body: &'a VerifiableBody,
    /// Function names considered as taint sources (e.g., "read", "recv").
    taint_sources: Vec<String>,
    /// Function names considered as sanitizers (e.g., "escape_html").
    sanitizers: Vec<String>,
}

impl<'a> TaintTransfer<'a> {
    /// Create a taint transfer function for one body.
    #[must_use]
    pub fn new(body: &'a VerifiableBody) -> Self {
        Self {
            body,
            taint_sources: vec![
                "read".into(),
                "recv".into(),
                "getenv".into(),
                "stdin".into(),
                "input".into(),
            ],
            sanitizers: vec![
                "escape".into(),
                "sanitize".into(),
                "validate".into(),
                "encode".into(),
            ],
        }
    }

    /// Create a taint transfer with custom sources and sanitizers.
    #[must_use]
    pub fn with_sources_and_sanitizers(
        body: &'a VerifiableBody,
        taint_sources: Vec<String>,
        sanitizers: Vec<String>,
    ) -> Self {
        Self { body, taint_sources, sanitizers }
    }
}

impl TransferFunction<TaintDomain> for TaintTransfer<'_> {
    fn transfer(&self, state: &TaintDomain, stmt: &Statement) -> TaintDomain {
        let mut next = state.clone();
        if next.is_bottom {
            return next;
        }

        match stmt {
            Statement::Assign { place, rvalue, .. } => {
                let target = place_to_var_name(self.body, place);
                let taint = rvalue_taint(self.body, state, rvalue);
                next.set(target, taint);
            }
            Statement::Nop => {}
            _ => {},
        }

        next
    }
}

/// Compute the taint level of an rvalue based on its operands.
fn rvalue_taint(body: &VerifiableBody, state: &TaintDomain, rvalue: &Rvalue) -> TaintLevel {
    match rvalue {
        Rvalue::Use(op) => operand_taint(body, state, op),
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            let l = operand_taint(body, state, lhs);
            let r = operand_taint(body, state, rhs);
            l.join(r)
        }
        Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) => operand_taint(body, state, op),
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::Len(place)
        | Rvalue::Discriminant(place)
        | Rvalue::CopyForDeref(place) => {
            let name = place_to_var_name(body, place);
            state.get(&name)
        }
        Rvalue::Aggregate(_, ops) => {
            let mut level = TaintLevel::Clean;
            for op in ops {
                level = level.join(operand_taint(body, state, op));
            }
            level
        }
        Rvalue::Repeat(op, _) => operand_taint(body, state, op),
        _ => TaintLevel::Tainted,
    }
}

/// Get the taint level for a single operand.
fn operand_taint(body: &VerifiableBody, state: &TaintDomain, op: &Operand) -> TaintLevel {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            let name = place_to_var_name(body, place);
            state.get(&name)
        }
        Operand::Constant(_) => TaintLevel::Clean,
        _ => TaintLevel::Tainted,
    }
}

/// Convenience: run interval + taint analysis simultaneously using CompositeDomain.
///
/// Returns per-block (interval, taint) state pairs.
pub fn run_composite_safety_taint(
    body: &VerifiableBody,
    tainted_args: &[usize],
) -> Result<FxHashMap<BlockId, CompositeDomain<CpaDomain, TaintDomain>>, CpaError> {
    let initial_intervals = CpaDomain::top();
    let mut initial_taint = TaintDomain::top();

    // Mark specified arguments as tainted.
    for &arg_idx in tainted_args {
        if let Some(decl) = body.locals.get(arg_idx) {
            let name = decl.name.clone().unwrap_or_else(|| format!("_{arg_idx}"));
            initial_taint.taint(name);
        }
    }

    let initial = CompositeDomain::new(initial_intervals, initial_taint);
    let interval_transfer = IntervalTransfer::new(body);
    let taint_transfer = TaintTransfer::new(body);
    let composite_transfer = CompositeTransfer::new(interval_transfer, taint_transfer);

    let algorithm = CpaAlgorithm::new(body, composite_transfer, initial, CpaConfig::default());
    algorithm.run()
}

/// Composite transfer function that applies two transfers in parallel.
#[derive(Debug, Clone)]
pub struct CompositeTransfer<L, R> {
    left: L,
    right: R,
}

impl<L, R> CompositeTransfer<L, R> {
    /// Create a composite transfer from two component transfers.
    #[must_use]
    pub fn new(left: L, right: R) -> Self {
        Self { left, right }
    }
}

impl<LS, RS, L, R> TransferFunction<CompositeDomain<LS, RS>> for CompositeTransfer<L, R>
where
    LS: CpaState,
    RS: CpaState,
    L: TransferFunction<LS>,
    R: TransferFunction<RS>,
{
    fn transfer(
        &self,
        state: &CompositeDomain<LS, RS>,
        stmt: &Statement,
    ) -> CompositeDomain<LS, RS> {
        let left = self.left.transfer(&state.left, stmt);
        let right = self.right.transfer(&state.right, stmt);
        CompositeDomain::new(left, right)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use trust_types::{BasicBlock, ConstValue, LocalDecl, SourceSpan, Ty};

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct CounterState(i32);

    impl CpaState for CounterState {
        fn join(&self, other: &Self) -> Self {
            Self(self.0.max(other.0))
        }

        fn is_bottom(&self) -> bool {
            self.0 < 0
        }

        fn leq(&self, other: &Self) -> bool {
            self.0 <= other.0
        }

        fn to_formula(&self) -> Formula {
            if self.is_bottom() {
                return Formula::Bool(false);
            }
            Formula::Eq(
                Box::new(Formula::Var("counter".into(), Sort::Int)),
                Box::new(Formula::Int(i128::from(self.0))),
            )
        }
    }

    #[derive(Debug, Clone, Copy)]
    struct CounterAssignTransfer;

    impl TransferFunction<CounterState> for CounterAssignTransfer {
        fn transfer(&self, state: &CounterState, stmt: &Statement) -> CounterState {
            match stmt {
                Statement::Assign {
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(value))),
                    ..
                } => CounterState(*value as i32),
                Statement::Nop => CounterState(state.0 + 1),
                _ => state.clone(),
            }
        }
    }

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    fn simple_straight_line_body() -> VerifiableBody {
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("y".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
                            span: span(),
                        },
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(2))),
                            span: span(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 0,
            return_ty: Ty::i32(),
        }
    }

    fn invalid_successor_body() -> VerifiableBody {
        VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: Some("ret".into()) }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Goto(BlockId(9)),
            }],
            arg_count: 0,
            return_ty: Ty::i32(),
        }
    }

    fn self_loop_body() -> VerifiableBody {
        VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: Some("ret".into()) }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Nop],
                terminator: Terminator::Goto(BlockId(0)),
            }],
            arg_count: 0,
            return_ty: Ty::i32(),
        }
    }

    fn interval_state(var: &str, interval: Interval) -> CpaDomain {
        let mut state = CpaDomain::top();
        state.set(var.to_string(), interval);
        state
    }

    #[test]
    fn test_cpa_domain_wraps_interval_domain() {
        let mut intervals = IntervalDomain::top();
        intervals.set("x".into(), Interval::new(0, 5));

        let state = CpaDomain::new(intervals.clone());
        assert_eq!(state.get("x"), Interval::new(0, 5));
        assert_eq!(state.into_interval_domain(), intervals);
    }

    #[test]
    fn test_cpa_domain_to_formula_emits_bounds() {
        let state = interval_state("x", Interval::new(1, 3));
        let formula = state.to_formula();

        assert_eq!(
            formula,
            Formula::And(vec![
                Formula::Ge(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(1)),
                ),
                Formula::Le(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(3)),
                ),
            ])
        );
    }

    #[test]
    fn test_composite_domain_join_is_pointwise() {
        let left_a = interval_state("x", Interval::new(0, 1));
        let left_b = interval_state("x", Interval::new(1, 4));
        let right_a = interval_state("y", Interval::new(5, 5));
        let right_b = interval_state("y", Interval::new(3, 9));

        let joined =
            CompositeDomain::new(left_a, right_a).join(&CompositeDomain::new(left_b, right_b));

        assert_eq!(joined.left.get("x"), Interval::new(0, 4));
        assert_eq!(joined.right.get("y"), Interval::new(3, 9));
    }

    #[test]
    fn test_composite_domain_leq_is_pointwise() {
        let smaller = CompositeDomain::new(
            interval_state("x", Interval::new(1, 2)),
            interval_state("y", Interval::new(4, 4)),
        );
        let larger = CompositeDomain::new(
            interval_state("x", Interval::new(0, 3)),
            interval_state("y", Interval::new(0, 10)),
        );

        assert!(smaller.leq(&larger));
        assert!(!larger.leq(&smaller));
    }

    #[test]
    fn test_cpa_algorithm_propagates_straight_line_state() {
        let body = simple_straight_line_body();
        let algorithm = CpaAlgorithm::new(
            &body,
            IntervalTransfer::new(&body),
            CpaDomain::top(),
            CpaConfig::default(),
        );

        let states = algorithm.run().expect("straight-line CPA should succeed");
        let block1 = states.get(&BlockId(1)).expect("block 1 should be reachable");

        assert_eq!(block1.get("x"), Interval::constant(1));
        assert_eq!(block1.get("y"), Interval::constant(2));
    }

    #[test]
    fn test_merge_sep_keeps_distinct_states() {
        let mut reached = vec![CounterState(1)];
        let merged = merge_candidate(&mut reached, CounterState(3), MergeOperator::Sep);

        assert_eq!(merged, Some(CounterState(3)));
        assert_eq!(reached, vec![CounterState(1), CounterState(3)]);
    }

    #[test]
    fn test_merge_join_collapses_reached_states() {
        let mut reached = vec![CounterState(1), CounterState(2)];
        let merged = merge_candidate(&mut reached, CounterState(3), MergeOperator::Join);

        assert_eq!(merged, Some(CounterState(3)));
        assert_eq!(reached, vec![CounterState(3)]);
    }

    #[test]
    fn test_stop_sep_only_stops_duplicates() {
        let reached = vec![CounterState(2)];

        assert!(should_stop(&reached, &CounterState(2), StopOperator::Sep));
        assert!(!should_stop(&reached, &CounterState(1), StopOperator::Sep));
    }

    #[test]
    fn test_stop_join_uses_joined_reached_state() {
        let reached = vec![
            interval_state("x", Interval::constant(0)),
            interval_state("x", Interval::constant(10)),
        ];
        let candidate = interval_state("x", Interval::new(0, 10));

        assert!(should_stop(&reached, &candidate, StopOperator::Join));
    }

    #[test]
    fn test_stop_coverage_requires_a_single_covering_state() {
        let reached = vec![
            interval_state("x", Interval::constant(0)),
            interval_state("x", Interval::constant(10)),
        ];
        let candidate = interval_state("x", Interval::new(0, 10));

        assert!(!should_stop(&reached, &candidate, StopOperator::Coverage));
    }

    #[test]
    fn test_cpa_algorithm_reports_missing_successor() {
        let body = invalid_successor_body();
        let algorithm = CpaAlgorithm::new(
            &body,
            IntervalTransfer::new(&body),
            CpaDomain::top(),
            CpaConfig::default(),
        );

        let error = algorithm.run().expect_err("invalid successor should fail");
        assert_eq!(error, CpaError::MissingBlock { block: BlockId(9) });
    }

    #[test]
    fn test_cpa_algorithm_respects_max_iterations() {
        let body = self_loop_body();
        let algorithm = CpaAlgorithm::new(
            &body,
            CounterAssignTransfer,
            CounterState(0),
            CpaConfig::new(MergeOperator::Sep, StopOperator::Sep, 3),
        );

        let error = algorithm.run().expect_err("self-loop should exhaust the iteration budget");
        assert_eq!(error, CpaError::MaxIterationsReached { limit: 3 });
    }

    // -- Taint domain tests --

    #[test]
    fn test_taint_level_join_lattice() {
        assert_eq!(TaintLevel::Clean.join(TaintLevel::Clean), TaintLevel::Clean);
        assert_eq!(TaintLevel::Clean.join(TaintLevel::Tainted), TaintLevel::Tainted);
        assert_eq!(TaintLevel::Tainted.join(TaintLevel::Clean), TaintLevel::Tainted);
        assert_eq!(TaintLevel::Clean.join(TaintLevel::Sanitized), TaintLevel::Sanitized);
        assert_eq!(TaintLevel::Sanitized.join(TaintLevel::Tainted), TaintLevel::Tainted);
        assert_eq!(TaintLevel::Sanitized.join(TaintLevel::Sanitized), TaintLevel::Sanitized);
    }

    #[test]
    fn test_taint_level_leq() {
        assert!(TaintLevel::Clean.leq(TaintLevel::Clean));
        assert!(TaintLevel::Clean.leq(TaintLevel::Sanitized));
        assert!(TaintLevel::Clean.leq(TaintLevel::Tainted));
        assert!(TaintLevel::Sanitized.leq(TaintLevel::Tainted));
        assert!(TaintLevel::Tainted.leq(TaintLevel::Tainted));
        assert!(!TaintLevel::Tainted.leq(TaintLevel::Clean));
        assert!(!TaintLevel::Tainted.leq(TaintLevel::Sanitized));
    }

    #[test]
    fn test_taint_domain_default_is_clean() {
        let state = TaintDomain::top();
        assert_eq!(state.get("x"), TaintLevel::Clean);
        assert!(!state.has_tainted_vars());
    }

    #[test]
    fn test_taint_domain_set_and_get() {
        let mut state = TaintDomain::top();
        state.taint("user_input");
        assert_eq!(state.get("user_input"), TaintLevel::Tainted);
        assert!(state.has_tainted_vars());

        state.sanitize("user_input");
        assert_eq!(state.get("user_input"), TaintLevel::Sanitized);
        assert!(!state.has_tainted_vars());
    }

    #[test]
    fn test_taint_domain_join() {
        let mut a = TaintDomain::top();
        a.taint("x");

        let mut b = TaintDomain::top();
        b.set("y", TaintLevel::Sanitized);

        let joined = a.join(&b);
        assert_eq!(joined.get("x"), TaintLevel::Tainted);
        assert_eq!(joined.get("y"), TaintLevel::Sanitized);
        assert_eq!(joined.get("z"), TaintLevel::Clean);
    }

    #[test]
    fn test_taint_domain_leq() {
        let mut smaller = TaintDomain::top();
        smaller.set("x", TaintLevel::Clean);

        let mut larger = TaintDomain::top();
        larger.set("x", TaintLevel::Tainted);

        assert!(smaller.leq(&larger));
        assert!(!larger.leq(&smaller));
    }

    #[test]
    fn test_taint_domain_bottom_is_leq_everything() {
        let bottom = TaintDomain::bottom();
        let top = TaintDomain::top();
        assert!(bottom.leq(&top));
        assert!(!top.leq(&bottom));
    }

    #[test]
    fn test_taint_domain_to_formula() {
        let mut state = TaintDomain::top();
        state.taint("x");
        state.set("y", TaintLevel::Clean);

        let formula = state.to_formula();
        // Should produce a conjunction with tainted_x = true and tainted_y = false.
        assert!(matches!(formula, Formula::And(_) | Formula::Var(..) | Formula::Not(_)));
    }

    #[test]
    fn test_taint_transfer_propagates_through_assignment() {
        let body = simple_straight_line_body();
        let transfer = TaintTransfer::new(&body);

        let mut state = TaintDomain::top();
        state.taint("x");

        // Assign: ret = x + y. x is tainted, so ret should be tainted.
        let stmt = Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        assert_eq!(next.get("ret"), TaintLevel::Tainted);
    }

    #[test]
    fn test_taint_transfer_constant_is_clean() {
        let body = simple_straight_line_body();
        let transfer = TaintTransfer::new(&body);

        let mut state = TaintDomain::top();
        state.taint("x");

        // Assign: ret = constant 42. Should be clean regardless of other vars.
        let stmt = Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        assert_eq!(next.get("ret"), TaintLevel::Clean);
    }

    #[test]
    fn test_composite_safety_taint_runs() {
        let body = simple_straight_line_body();
        // Mark argument x (local 1) as tainted.
        let result = run_composite_safety_taint(&body, &[1]);
        assert!(result.is_ok(), "composite analysis should succeed");

        let states = result.expect("should succeed");
        // Block 1 should have results.
        let block1 = states.get(&BlockId(1)).expect("block 1 reachable");

        // Interval: x = 1, y = 2.
        assert_eq!(block1.left.get("x"), Interval::constant(1));

        // Taint: x was initially tainted but Block 0 reassigns x = 1 (constant),
        // which kills the taint. So x is Clean at Block 1 entry.
        assert_eq!(block1.right.get("x"), TaintLevel::Clean);
    }

    #[test]
    fn test_tainted_vars_list() {
        let mut state = TaintDomain::top();
        state.taint("a");
        state.taint("b");
        state.set("c", TaintLevel::Sanitized);

        let mut tainted = state.tainted_vars();
        tainted.sort();
        assert_eq!(tainted, vec!["a", "b"]);
    }
}
