// trust-vcgen/interval_domain.rs: CPA-integrated interval abstract domain
//
// Wraps the IntervalDomain from abstract_interp into the CPA framework with
// proper widening at loop heads and arithmetic transfer functions.
//
// Reference: Cousot & Cousot, "Abstract Interpretation" (POPL 1977).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    BinOp, ConstValue, Formula, Operand, Place, Projection, Rvalue, Statement, UnOp,
    VerifiableBody,
};

use crate::abstract_interp::{
    AbstractDomain, Interval, IntervalDomain, interval_add, interval_mul, interval_sub,
};
use crate::cpa::{CpaState, TransferFunction};

// ── CPA Interval State ─────────────────────────────────────────────────────

/// A CPA state backed by an interval domain with widening support.
///
/// This extends the basic CpaDomain in cpa.rs with explicit widening
/// tracking for loop-head convergence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpaIntervalState {
    /// The underlying interval domain mapping variables to ranges.
    pub intervals: IntervalDomain,
    /// Number of times this state has been widened (for convergence tracking).
    pub widen_count: u32,
}

impl CpaIntervalState {
    /// Create a top state (all variables unconstrained).
    #[must_use]
    pub fn top() -> Self {
        Self { intervals: IntervalDomain::top(), widen_count: 0 }
    }

    /// Create a bottom state (unreachable).
    #[must_use]
    pub fn bottom() -> Self {
        Self { intervals: IntervalDomain::bottom(), widen_count: 0 }
    }

    /// Create from an existing interval domain.
    #[must_use]
    pub fn from_domain(intervals: IntervalDomain) -> Self {
        Self { intervals, widen_count: 0 }
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

    /// Widen this state against another, returning the widened result.
    ///
    /// At loop heads, if the upper bound increases we widen to +inf;
    /// if the lower bound decreases we widen to -inf.
    #[must_use]
    pub fn widen(&self, other: &Self) -> Self {
        Self {
            intervals: self.intervals.widen(&other.intervals),
            widen_count: self.widen_count + 1,
        }
    }

    /// Narrow this state with another to recover precision after widening.
    #[must_use]
    pub fn narrow(&self, other: &Self) -> Self {
        Self {
            intervals: self.intervals.narrow(&other.intervals),
            widen_count: self.widen_count,
        }
    }

    /// Meet (intersection) of two interval states.
    #[must_use]
    pub fn meet(&self, other: &Self) -> Self {
        Self {
            intervals: self.intervals.meet(&other.intervals),
            widen_count: self.widen_count.min(other.widen_count),
        }
    }

    /// Borrow the underlying interval domain.
    #[must_use]
    pub fn as_interval_domain(&self) -> &IntervalDomain {
        &self.intervals
    }
}

impl CpaState for CpaIntervalState {
    fn join(&self, other: &Self) -> Self {
        Self {
            intervals: self.intervals.join(&other.intervals),
            widen_count: self.widen_count.max(other.widen_count),
        }
    }

    fn is_bottom(&self) -> bool {
        self.intervals.is_bottom()
    }

    fn leq(&self, other: &Self) -> bool {
        self.intervals.leq(&other.intervals)
    }

    fn to_formula(&self) -> Formula {
        // tRust #451: Delegate to the shared interval-to-formula conversion.
        crate::abstract_interp::interval_domain_to_formula(&self.intervals)
    }
}

// ── Transfer Function ───────────────────────────────────────────────────────

/// Transfer function for the CPA interval domain.
///
/// Handles arithmetic operations (add, sub, mul), constants, copies,
/// and unary operations. Unknown operations produce Top intervals.
#[derive(Debug, Clone, Copy)]
pub struct IntervalCpaTransfer<'a> {
    body: &'a VerifiableBody,
}

impl<'a> IntervalCpaTransfer<'a> {
    /// Create an interval transfer function for a verifiable body.
    #[must_use]
    pub fn new(body: &'a VerifiableBody) -> Self {
        Self { body }
    }
}

impl TransferFunction<CpaIntervalState> for IntervalCpaTransfer<'_> {
    fn transfer(&self, state: &CpaIntervalState, stmt: &Statement) -> CpaIntervalState {
        let mut next = state.clone();
        if next.is_bottom() {
            return next;
        }

        match stmt {
            Statement::Assign { place, rvalue, .. } => {
                let target = place_to_var_name(self.body, place);
                let interval = eval_rvalue(self.body, &state.intervals, rvalue);
                next.set(target, interval);
            }
            Statement::Nop => {}
            _ => {},
        }

        next
    }
}

// ── Helpers ─────────────────────────────────────────────────────────────────

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
                BinOp::Div => {
                    if right.is_bottom() || left.is_bottom() {
                        return Interval::BOTTOM;
                    }
                    if right.contains(0) {
                        return Interval::TOP;
                    }
                    // Conservative: compute from corners
                    interval_div(&left, &right)
                }
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

/// Interval division with corner analysis. Divisor must not contain zero.
fn interval_div(a: &Interval, b: &Interval) -> Interval {
    if a.is_bottom() || b.is_bottom() {
        return Interval::BOTTOM;
    }
    let corners = [
        a.lo.checked_div(b.lo),
        a.lo.checked_div(b.hi),
        a.hi.checked_div(b.lo),
        a.hi.checked_div(b.hi),
    ];
    let mut lo = i128::MAX;
    let mut hi = i128::MIN;
    for c in &corners {
        match c {
            Some(v) => {
                lo = lo.min(*v);
                hi = hi.max(*v);
            }
            None => return Interval::TOP,
        }
    }
    Interval::new(lo, hi)
}

// ── Tests ───────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{BasicBlock, BlockId, LocalDecl, Sort, SourceSpan, Terminator, Ty};

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    fn simple_body() -> VerifiableBody {
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("y".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(10))),
                        span: span(),
                    },
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(20))),
                        span: span(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::i32(),
        }
    }

    #[test]
    fn test_cpa_interval_state_top_and_bottom() {
        let top = CpaIntervalState::top();
        assert!(!top.is_bottom());
        assert_eq!(top.get("x"), Interval::TOP);

        let bottom = CpaIntervalState::bottom();
        assert!(bottom.is_bottom());
    }

    #[test]
    fn test_cpa_interval_state_set_and_get() {
        let mut state = CpaIntervalState::top();
        state.set("x", Interval::new(0, 10));
        assert_eq!(state.get("x"), Interval::new(0, 10));
        assert_eq!(state.get("y"), Interval::TOP);
    }

    #[test]
    fn test_cpa_interval_state_join() {
        let mut a = CpaIntervalState::top();
        a.set("x", Interval::new(0, 5));

        let mut b = CpaIntervalState::top();
        b.set("x", Interval::new(3, 10));

        let joined = a.join(&b);
        assert_eq!(joined.get("x"), Interval::new(0, 10));
    }

    #[test]
    fn test_cpa_interval_state_leq() {
        let mut smaller = CpaIntervalState::top();
        smaller.set("x", Interval::new(2, 5));

        let mut larger = CpaIntervalState::top();
        larger.set("x", Interval::new(0, 10));

        assert!(smaller.leq(&larger));
        assert!(!larger.leq(&smaller));
    }

    #[test]
    fn test_cpa_interval_state_widen() {
        let mut prev = CpaIntervalState::top();
        prev.set("i", Interval::new(0, 5));

        let mut next = CpaIntervalState::top();
        next.set("i", Interval::new(0, 10));

        let widened = prev.widen(&next);
        // Upper bound increased, so widen to +inf
        assert_eq!(widened.get("i"), Interval::new(0, i128::MAX));
        assert_eq!(widened.widen_count, 1);
    }

    #[test]
    fn test_cpa_interval_state_widen_stable() {
        let mut prev = CpaIntervalState::top();
        prev.set("i", Interval::new(0, 10));

        let mut next = CpaIntervalState::top();
        next.set("i", Interval::new(0, 5));

        let widened = prev.widen(&next);
        // No increase, stays stable
        assert_eq!(widened.get("i"), Interval::new(0, 10));
    }

    #[test]
    fn test_cpa_interval_state_narrow() {
        let mut wide = CpaIntervalState::top();
        wide.set("i", Interval::new(0, i128::MAX));

        let mut precise = CpaIntervalState::top();
        precise.set("i", Interval::new(0, 100));

        let narrowed = wide.narrow(&precise);
        assert_eq!(narrowed.get("i"), Interval::new(0, 100));
    }

    #[test]
    fn test_cpa_interval_state_meet() {
        let mut a = CpaIntervalState::top();
        a.set("x", Interval::new(0, 10));

        let mut b = CpaIntervalState::top();
        b.set("x", Interval::new(5, 15));

        let met = a.meet(&b);
        assert_eq!(met.get("x"), Interval::new(5, 10));
    }

    #[test]
    fn test_cpa_interval_state_meet_empty() {
        let mut a = CpaIntervalState::top();
        a.set("x", Interval::new(0, 3));

        let mut b = CpaIntervalState::top();
        b.set("x", Interval::new(5, 10));

        let met = a.meet(&b);
        assert!(met.is_bottom());
    }

    #[test]
    fn test_cpa_interval_state_to_formula() {
        let mut state = CpaIntervalState::top();
        state.set("x", Interval::new(1, 5));

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
                    Box::new(Formula::Int(5)),
                ),
            ])
        );
    }

    #[test]
    fn test_cpa_interval_state_bottom_join_identity() {
        let mut a = CpaIntervalState::top();
        a.set("x", Interval::new(1, 5));

        let bottom = CpaIntervalState::bottom();
        assert_eq!(a.join(&bottom), a);
        assert_eq!(bottom.join(&a), a);
    }

    #[test]
    fn test_cpa_interval_state_bottom_leq_everything() {
        let bottom = CpaIntervalState::bottom();
        let top = CpaIntervalState::top();
        assert!(bottom.leq(&top));
        assert!(!top.leq(&bottom));
    }

    #[test]
    fn test_interval_transfer_constant_assignment() {
        let body = simple_body();
        let transfer = IntervalCpaTransfer::new(&body);
        let state = CpaIntervalState::top();

        let stmt = Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        assert_eq!(next.get("x"), Interval::constant(42));
    }

    #[test]
    fn test_interval_transfer_add() {
        let body = simple_body();
        let transfer = IntervalCpaTransfer::new(&body);

        let mut state = CpaIntervalState::top();
        state.set("x", Interval::new(0, 10));
        state.set("y", Interval::new(5, 20));

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
        assert_eq!(next.get("ret"), Interval::new(5, 30));
    }

    #[test]
    fn test_interval_transfer_sub() {
        let body = simple_body();
        let transfer = IntervalCpaTransfer::new(&body);

        let mut state = CpaIntervalState::top();
        state.set("x", Interval::new(10, 20));
        state.set("y", Interval::new(1, 5));

        let stmt = Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::BinaryOp(
                BinOp::Sub,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        assert_eq!(next.get("ret"), Interval::new(5, 19));
    }

    #[test]
    fn test_interval_transfer_mul() {
        let body = simple_body();
        let transfer = IntervalCpaTransfer::new(&body);

        let mut state = CpaIntervalState::top();
        state.set("x", Interval::new(2, 4));
        state.set("y", Interval::new(3, 5));

        let stmt = Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::BinaryOp(
                BinOp::Mul,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        assert_eq!(next.get("ret"), Interval::new(6, 20));
    }

    #[test]
    fn test_interval_transfer_nop_preserves_state() {
        let body = simple_body();
        let transfer = IntervalCpaTransfer::new(&body);

        let mut state = CpaIntervalState::top();
        state.set("x", Interval::new(1, 10));

        let next = transfer.transfer(&state, &Statement::Nop);
        assert_eq!(next.get("x"), Interval::new(1, 10));
    }

    #[test]
    fn test_interval_transfer_bottom_stays_bottom() {
        let body = simple_body();
        let transfer = IntervalCpaTransfer::new(&body);
        let state = CpaIntervalState::bottom();

        let stmt = Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        assert!(next.is_bottom());
    }

    #[test]
    fn test_interval_transfer_negation() {
        let body = simple_body();
        let transfer = IntervalCpaTransfer::new(&body);

        let mut state = CpaIntervalState::top();
        state.set("x", Interval::new(3, 7));

        let stmt = Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        assert_eq!(next.get("ret"), Interval::new(-7, -3));
    }

    #[test]
    fn test_interval_div_transfer() {
        let body = simple_body();
        let transfer = IntervalCpaTransfer::new(&body);

        let mut state = CpaIntervalState::top();
        state.set("x", Interval::new(10, 20));
        state.set("y", Interval::new(2, 5));

        let stmt = Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::BinaryOp(
                BinOp::Div,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        assert_eq!(next.get("ret"), Interval::new(2, 10));
    }

    #[test]
    fn test_interval_div_transfer_includes_zero_is_top() {
        let body = simple_body();
        let transfer = IntervalCpaTransfer::new(&body);

        let mut state = CpaIntervalState::top();
        state.set("x", Interval::new(10, 20));
        state.set("y", Interval::new(-1, 5));

        let stmt = Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::BinaryOp(
                BinOp::Div,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        assert_eq!(next.get("ret"), Interval::TOP);
    }
}
