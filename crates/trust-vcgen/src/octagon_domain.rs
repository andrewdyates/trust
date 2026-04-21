// trust-vcgen/octagon_domain.rs: CPA-integrated octagon abstract domain
//
// Wraps the OctagonDomain from abstract_domains.rs into the CPA framework,
// tracking relational constraints of the form +/-x +/-y <= c between pairs
// of variables. Supports transfer for assignments and comparisons.
//
// Reference: Mine, "The Octagon Abstract Domain" (Higher-Order and Symbolic
// Computation, 2006).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    BinOp, ConstValue, Formula, Operand, Place, Projection, Rvalue, Statement, VerifiableBody,
};

use crate::abstract_domains::{OctagonConstraint, OctagonDomain, Sign};
use crate::abstract_interp::AbstractDomain;
use crate::cpa::{CpaState, TransferFunction};

// ── CPA Octagon State ───────────────────────────────────────────────────────

/// A CPA state backed by an octagon domain for relational analysis.
///
/// Tracks constraints of the form `+/-x +/-y <= c` which can express
/// relationships like `x - y <= 5` (x is at most 5 more than y).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpaOctagonState {
    /// The underlying octagon domain.
    pub octagon: OctagonDomain,
}

impl CpaOctagonState {
    /// Create a top state (no relational constraints).
    #[must_use]
    pub fn top() -> Self {
        Self { octagon: OctagonDomain::top() }
    }

    /// Create a bottom state (unreachable).
    #[must_use]
    pub fn bottom() -> Self {
        Self { octagon: OctagonDomain::bottom() }
    }

    /// Create from an existing octagon domain.
    #[must_use]
    pub fn from_domain(octagon: OctagonDomain) -> Self {
        Self { octagon }
    }

    /// Create from a set of constraints.
    #[must_use]
    pub fn from_constraints(constraints: impl IntoIterator<Item = OctagonConstraint>) -> Self {
        Self { octagon: OctagonDomain::from_constraints(constraints) }
    }

    /// Add a unary bound: +/-var <= bound.
    #[must_use]
    pub fn with_unary_bound(self, var: &str, sign: Sign, bound: i128) -> Self {
        let mut constraints: Vec<OctagonConstraint> =
            self.octagon.constraints.into_iter().collect();
        constraints.push(OctagonConstraint::unary(var, sign, bound));
        Self::from_constraints(constraints)
    }

    /// Add a binary relational constraint: sign_i * x + sign_j * y <= bound.
    #[must_use]
    pub fn with_binary_bound(
        self,
        var_i: &str,
        sign_i: Sign,
        var_j: &str,
        sign_j: Sign,
        bound: i128,
    ) -> Self {
        let mut constraints: Vec<OctagonConstraint> =
            self.octagon.constraints.into_iter().collect();
        constraints.push(OctagonConstraint::binary(var_i, sign_i, var_j, sign_j, bound));
        Self::from_constraints(constraints)
    }

    /// Check if a specific variable has a positive upper bound.
    #[must_use]
    pub fn upper_bound(&self, var: &str) -> Option<i128> {
        self.octagon
            .constraints
            .iter()
            .filter(|c| c.var_i == var && c.sign_i == Sign::Pos && c.var_j.is_none())
            .map(|c| c.bound)
            .min()
    }

    /// Check if a specific variable has a negative upper bound (lower bound = -bound).
    #[must_use]
    pub fn lower_bound(&self, var: &str) -> Option<i128> {
        self.octagon
            .constraints
            .iter()
            .filter(|c| c.var_i == var && c.sign_i == Sign::Neg && c.var_j.is_none())
            .map(|c| -c.bound)
            .max()
    }

    /// Borrow the underlying octagon domain.
    #[must_use]
    pub fn as_octagon_domain(&self) -> &OctagonDomain {
        &self.octagon
    }
}

impl CpaState for CpaOctagonState {
    fn join(&self, other: &Self) -> Self {
        Self { octagon: self.octagon.join(&other.octagon) }
    }

    fn is_bottom(&self) -> bool {
        self.octagon.is_bottom()
    }

    fn leq(&self, other: &Self) -> bool {
        self.octagon.leq(&other.octagon)
    }

    fn to_formula(&self) -> Formula {
        self.octagon.to_formula()
    }
}

// ── Transfer Function ───────────────────────────────────────────────────────

/// Octagon transfer function for the CPA framework.
///
/// For assignments `x = y + c`, derives `x - y <= c` and `y - x <= -c`.
/// For assignments `x = c`, derives `x <= c` and `-x <= -c`.
/// For comparisons, adds the constraint if the comparison is an assignment
/// of a boolean result.
#[derive(Debug, Clone)]
pub struct OctagonTransfer<'a> {
    body: &'a VerifiableBody,
}

impl<'a> OctagonTransfer<'a> {
    /// Create an octagon transfer for a verifiable body.
    #[must_use]
    pub fn new(body: &'a VerifiableBody) -> Self {
        Self { body }
    }
}

impl TransferFunction<CpaOctagonState> for OctagonTransfer<'_> {
    fn transfer(&self, state: &CpaOctagonState, stmt: &Statement) -> CpaOctagonState {
        if state.is_bottom() {
            return state.clone();
        }

        match stmt {
            Statement::Assign { place, rvalue, .. } => {
                let target = place_to_var_name(self.body, place);
                transfer_assign(state, &target, self.body, rvalue)
            }
            Statement::Nop => state.clone(),
            _ => state.clone(),
        }
    }
}

/// Generate octagon constraints from an assignment.
fn transfer_assign(
    state: &CpaOctagonState,
    target: &str,
    body: &VerifiableBody,
    rvalue: &Rvalue,
) -> CpaOctagonState {
    // Remove existing constraints involving the target variable,
    // since the assignment overwrites it.
    let mut retained: Vec<OctagonConstraint> = state
        .octagon
        .constraints
        .iter()
        .filter(|c| c.var_i != target && c.var_j.as_deref() != Some(target))
        .cloned()
        .collect();

    match rvalue {
        // x = constant
        Rvalue::Use(Operand::Constant(ConstValue::Int(c))) => {
            // x <= c and -x <= -c
            retained.push(OctagonConstraint::unary(target, Sign::Pos, *c));
            retained.push(OctagonConstraint::unary(target, Sign::Neg, -*c));
        }
        Rvalue::Use(Operand::Constant(ConstValue::Uint(c, _))) => {
            if let Ok(v) = i128::try_from(*c) {
                retained.push(OctagonConstraint::unary(target, Sign::Pos, v));
                retained.push(OctagonConstraint::unary(target, Sign::Neg, -v));
            }
        }

        // x = y (copy/move)
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => {
            let source = place_to_var_name(body, place);
            if source != target {
                // x - y <= 0 and y - x <= 0
                retained.push(OctagonConstraint::binary(
                    target,
                    Sign::Pos,
                    &source,
                    Sign::Neg,
                    0,
                ));
                retained.push(OctagonConstraint::binary(
                    &source,
                    Sign::Pos,
                    target,
                    Sign::Neg,
                    0,
                ));
            }
        }

        // x = y + z or x = y - z (derive relational constraints)
        Rvalue::BinaryOp(BinOp::Add, lhs, rhs) | Rvalue::CheckedBinaryOp(BinOp::Add, lhs, rhs) => {
            if let Some(add_constraints) = binary_op_constraints(target, body, lhs, rhs, BinOp::Add)
            {
                retained.extend(add_constraints);
            }
        }
        Rvalue::BinaryOp(BinOp::Sub, lhs, rhs) | Rvalue::CheckedBinaryOp(BinOp::Sub, lhs, rhs) => {
            if let Some(sub_constraints) = binary_op_constraints(target, body, lhs, rhs, BinOp::Sub)
            {
                retained.extend(sub_constraints);
            }
        }

        _ => {
            // Unknown rvalue: no new constraints about target
        }
    }

    CpaOctagonState::from_constraints(retained)
}

/// Derive octagon constraints from a binary operation assignment.
///
/// For `target = var + const_c`, derives:
///   target - var <= c and var - target <= -c
///
/// For `target = var - const_c`, derives:
///   target - var <= -c and var - target <= c
fn binary_op_constraints(
    target: &str,
    body: &VerifiableBody,
    lhs: &Operand,
    rhs: &Operand,
    op: BinOp,
) -> Option<Vec<OctagonConstraint>> {
    let mut constraints = Vec::new();

    // Case: var op constant
    match (lhs, rhs) {
        (Operand::Copy(place) | Operand::Move(place), Operand::Constant(cv)) => {
            let source = place_to_var_name(body, place);
            let c = const_to_i128(cv)?;
            let offset = match op {
                BinOp::Add => c,
                BinOp::Sub => -c,
                _ => return None,
            };
            if source != target {
                // target - source <= offset, source - target <= -offset
                constraints.push(OctagonConstraint::binary(
                    target,
                    Sign::Pos,
                    &source,
                    Sign::Neg,
                    offset,
                ));
                constraints.push(OctagonConstraint::binary(
                    &source,
                    Sign::Pos,
                    target,
                    Sign::Neg,
                    -offset,
                ));
            }
        }
        (Operand::Constant(cv), Operand::Copy(place) | Operand::Move(place)) if op == BinOp::Add => {
            // constant + var
            let source = place_to_var_name(body, place);
            let c = const_to_i128(cv)?;
            if source != target {
                constraints.push(OctagonConstraint::binary(
                    target,
                    Sign::Pos,
                    &source,
                    Sign::Neg,
                    c,
                ));
                constraints.push(OctagonConstraint::binary(
                    &source,
                    Sign::Pos,
                    target,
                    Sign::Neg,
                    -c,
                ));
            }
        }
        (Operand::Copy(_p1) | Operand::Move(_p1), Operand::Copy(_p2) | Operand::Move(_p2)) => {
            // target = source1 op source2 (two variables)
            // Octagon constraints require constant offsets between variable pairs.
            // Variable-variable operations cannot produce tight octagon constraints
            // without additional context. Let the interval domain handle numerics.
        }
        _ => {}
    }

    if constraints.is_empty() { None } else { Some(constraints) }
}

fn const_to_i128(cv: &ConstValue) -> Option<i128> {
    match cv {
        ConstValue::Int(v) => Some(*v),
        ConstValue::Uint(v, _) => i128::try_from(*v).ok(),
        ConstValue::Bool(b) => Some(i128::from(*b)),
        _ => None,
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

// ── Tests ───────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{BasicBlock, BlockId, LocalDecl, SourceSpan, Terminator, Ty};

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
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::i32(),
        }
    }

    #[test]
    fn test_octagon_state_top_and_bottom() {
        let top = CpaOctagonState::top();
        assert!(!top.is_bottom());

        let bottom = CpaOctagonState::bottom();
        assert!(bottom.is_bottom());
    }

    #[test]
    fn test_octagon_state_with_unary_bound() {
        let state = CpaOctagonState::top()
            .with_unary_bound("x", Sign::Pos, 10);
        assert_eq!(state.upper_bound("x"), Some(10));
    }

    #[test]
    fn test_octagon_state_with_binary_bound() {
        let state = CpaOctagonState::top()
            .with_binary_bound("x", Sign::Pos, "y", Sign::Neg, 5);

        // x - y <= 5 should be in constraints
        assert!(state.octagon.constraints.contains(
            &OctagonConstraint::binary("x", Sign::Pos, "y", Sign::Neg, 5)
        ));
    }

    #[test]
    fn test_octagon_state_join() {
        let a = CpaOctagonState::from_constraints([
            OctagonConstraint::binary("x", Sign::Pos, "y", Sign::Neg, 3),
        ]);
        let b = CpaOctagonState::from_constraints([
            OctagonConstraint::binary("x", Sign::Pos, "y", Sign::Neg, 8),
        ]);

        let joined = a.join(&b);
        // Join takes the max bound: x - y <= 8
        assert!(joined.octagon.constraints.contains(
            &OctagonConstraint::binary("x", Sign::Pos, "y", Sign::Neg, 8)
        ));
    }

    #[test]
    fn test_octagon_state_leq() {
        let smaller = CpaOctagonState::from_constraints([
            OctagonConstraint::binary("x", Sign::Pos, "y", Sign::Neg, 3),
            OctagonConstraint::unary("x", Sign::Pos, 5),
        ]);

        let larger = CpaOctagonState::from_constraints([
            OctagonConstraint::binary("x", Sign::Pos, "y", Sign::Neg, 3),
        ]);

        // smaller has more constraints (tighter), so smaller <= larger
        assert!(smaller.leq(&larger));
    }

    #[test]
    fn test_octagon_state_bottom_leq_everything() {
        let bottom = CpaOctagonState::bottom();
        let top = CpaOctagonState::top();
        assert!(bottom.leq(&top));
        assert!(!top.leq(&bottom));
    }

    #[test]
    fn test_octagon_state_to_formula() {
        let state = CpaOctagonState::from_constraints([
            OctagonConstraint::binary("x", Sign::Pos, "y", Sign::Neg, 5),
        ]);
        let formula = state.to_formula();
        // Should produce Le(x + (-y), 5)
        assert!(matches!(formula, Formula::Le(..)));
    }

    #[test]
    fn test_octagon_transfer_constant_assignment() {
        let body = simple_body();
        let transfer = OctagonTransfer::new(&body);
        let state = CpaOctagonState::top();

        let stmt = Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        // x <= 42 and -x <= -42
        assert_eq!(next.upper_bound("x"), Some(42));
        assert_eq!(next.lower_bound("x"), Some(42));
    }

    #[test]
    fn test_octagon_transfer_copy_assignment() {
        let body = simple_body();
        let transfer = OctagonTransfer::new(&body);

        let state = CpaOctagonState::top()
            .with_unary_bound("y", Sign::Pos, 10);

        // ret = y (copy)
        let stmt = Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        // ret - y <= 0 and y - ret <= 0 should be derived
        assert!(next.octagon.constraints.contains(
            &OctagonConstraint::binary("ret", Sign::Pos, "y", Sign::Neg, 0)
        ));
    }

    #[test]
    fn test_octagon_transfer_add_constant() {
        let body = simple_body();
        let transfer = OctagonTransfer::new(&body);
        let state = CpaOctagonState::top();

        // ret = x + 5
        let stmt = Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Int(5)),
            ),
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        // ret - x <= 5 should be derived
        assert!(next.octagon.constraints.contains(
            &OctagonConstraint::binary("ret", Sign::Pos, "x", Sign::Neg, 5)
        ));
        // x - ret <= -5
        assert!(next.octagon.constraints.contains(
            &OctagonConstraint::binary("ret", Sign::Neg, "x", Sign::Pos, -5)
        ));
    }

    #[test]
    fn test_octagon_transfer_sub_constant() {
        let body = simple_body();
        let transfer = OctagonTransfer::new(&body);
        let state = CpaOctagonState::top();

        // ret = x - 3
        let stmt = Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::BinaryOp(
                BinOp::Sub,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Int(3)),
            ),
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        // ret - x <= -3 should be derived
        assert!(next.octagon.constraints.contains(
            &OctagonConstraint::binary("ret", Sign::Pos, "x", Sign::Neg, -3)
        ));
    }

    #[test]
    fn test_octagon_transfer_nop_preserves_state() {
        let state = CpaOctagonState::top()
            .with_unary_bound("x", Sign::Pos, 10);
        let body = simple_body();
        let transfer = OctagonTransfer::new(&body);

        let next = transfer.transfer(&state, &Statement::Nop);
        assert_eq!(next, state);
    }

    #[test]
    fn test_octagon_transfer_bottom_stays_bottom() {
        let state = CpaOctagonState::bottom();
        let body = simple_body();
        let transfer = OctagonTransfer::new(&body);

        let stmt = Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        assert!(next.is_bottom());
    }

    #[test]
    fn test_octagon_transfer_overwrites_old_constraints() {
        let body = simple_body();
        let transfer = OctagonTransfer::new(&body);

        // Start with x <= 10
        let state = CpaOctagonState::top()
            .with_unary_bound("x", Sign::Pos, 10);

        // x = 42 (should replace x <= 10 with x <= 42)
        let stmt = Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        assert_eq!(next.upper_bound("x"), Some(42));
    }

    #[test]
    fn test_octagon_closure_derives_transitive_constraints() {
        // x - y <= 3 and y - z <= 4 should derive x - z <= 7
        let state = CpaOctagonState::from_constraints([
            OctagonConstraint::binary("x", Sign::Pos, "y", Sign::Neg, 3),
            OctagonConstraint::binary("y", Sign::Pos, "z", Sign::Neg, 4),
        ]);

        assert!(state.octagon.constraints.contains(
            &OctagonConstraint::binary("x", Sign::Pos, "z", Sign::Neg, 7)
        ));
    }
}
