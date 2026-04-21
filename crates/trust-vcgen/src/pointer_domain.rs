// trust-vcgen/pointer_domain.rs: CPA-integrated pointer/alias abstract domain
//
// Tracks points-to sets for reference variables in the CPA framework.
// For each reference variable, maintains the set of memory locations it may
// point to. Supports transfer for reference creation, dereference, and move.
//
// Reference: Andersen, "Program Analysis and Specialization for the C
// Programming Language" (PhD thesis, DIKU, 1994).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use trust_types::{
    Formula, Operand, Place, Projection, Rvalue, Sort, Statement, VerifiableBody,
};

use crate::cpa::{CpaState, TransferFunction};

// ── Points-To Set ───────────────────────────────────────────────────────────

/// A single points-to entry: a variable name representing a memory location.
pub type Location = String;

/// The set of locations a pointer may reference.
pub type PointsToSet = BTreeSet<Location>;

// ── CPA Pointer State ───────────────────────────────────────────────────────

/// A CPA state tracking points-to sets for reference variables.
///
/// Each variable that holds a reference is mapped to the set of variables
/// it may point to. Variables not in the map are assumed to point to nothing
/// (they are not references).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpaPointerState {
    /// Variable name -> set of locations it may point to.
    pub points_to: BTreeMap<String, PointsToSet>,
    /// Whether this state is bottom (unreachable).
    pub is_unreachable: bool,
}

impl CpaPointerState {
    /// Create a top state (no alias information).
    #[must_use]
    pub fn top() -> Self {
        Self { points_to: BTreeMap::new(), is_unreachable: false }
    }

    /// Create a bottom state (unreachable).
    #[must_use]
    pub fn bottom() -> Self {
        Self { points_to: BTreeMap::new(), is_unreachable: true }
    }

    /// Get the points-to set for a variable (empty if not a reference).
    #[must_use]
    pub fn get_points_to(&self, var: &str) -> PointsToSet {
        if self.is_unreachable {
            return BTreeSet::new();
        }
        self.points_to.get(var).cloned().unwrap_or_default()
    }

    /// Set the points-to set for a variable.
    pub fn set_points_to(&mut self, var: impl Into<String>, targets: PointsToSet) {
        if !self.is_unreachable {
            let var = var.into();
            if targets.is_empty() {
                self.points_to.remove(&var);
            } else {
                self.points_to.insert(var, targets);
            }
        }
    }

    /// Check if two variables may alias (their points-to sets overlap).
    #[must_use]
    pub fn may_alias(&self, a: &str, b: &str) -> bool {
        if self.is_unreachable {
            return false;
        }
        let pts_a = self.get_points_to(a);
        let pts_b = self.get_points_to(b);
        pts_a.intersection(&pts_b).next().is_some()
    }

    /// Check if two variables must alias (both point to exactly one location
    /// and that location is the same).
    #[must_use]
    pub fn must_alias(&self, a: &str, b: &str) -> bool {
        if self.is_unreachable {
            return false;
        }
        let pts_a = self.get_points_to(a);
        let pts_b = self.get_points_to(b);
        pts_a.len() == 1 && pts_a == pts_b
    }

    /// Get all variables that are known references (have non-empty points-to sets).
    #[must_use]
    pub fn reference_vars(&self) -> Vec<String> {
        self.points_to.keys().cloned().collect()
    }

    /// Number of tracked reference variables.
    #[must_use]
    pub fn num_references(&self) -> usize {
        self.points_to.len()
    }
}

impl CpaState for CpaPointerState {
    fn join(&self, other: &Self) -> Self {
        if self.is_unreachable {
            return other.clone();
        }
        if other.is_unreachable {
            return self.clone();
        }

        let mut points_to = BTreeMap::new();
        let all_vars: BTreeSet<&String> =
            self.points_to.keys().chain(other.points_to.keys()).collect();

        for var in all_vars {
            let pts_self = self.get_points_to(var);
            let pts_other = other.get_points_to(var);
            let joined: PointsToSet = pts_self.union(&pts_other).cloned().collect();
            if !joined.is_empty() {
                points_to.insert(var.clone(), joined);
            }
        }

        Self { points_to, is_unreachable: false }
    }

    fn is_bottom(&self) -> bool {
        self.is_unreachable
    }

    fn leq(&self, other: &Self) -> bool {
        if self.is_unreachable {
            return true;
        }
        if other.is_unreachable {
            return false;
        }
        // self <= other iff for every var, self.pts(var) subset_of other.pts(var)
        for (var, pts) in &self.points_to {
            let other_pts = other.get_points_to(var);
            if !pts.is_subset(&other_pts) {
                return false;
            }
        }
        true
    }

    fn to_formula(&self) -> Formula {
        if self.is_unreachable {
            return Formula::Bool(false);
        }
        if self.points_to.is_empty() {
            return Formula::Bool(true);
        }

        // Encode points-to as disequality constraints:
        // For each pair of variables that cannot alias, assert ptr_a != ptr_b
        let mut conjuncts = Vec::new();
        let vars: Vec<&String> = self.points_to.keys().collect();

        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                if !self.may_alias(vars[i], vars[j]) {
                    // These two pointers definitely don't alias
                    let a = Formula::Var(format!("ptr_{}", vars[i]), Sort::Int);
                    let b = Formula::Var(format!("ptr_{}", vars[j]), Sort::Int);
                    conjuncts.push(Formula::Not(Box::new(Formula::Eq(
                        Box::new(a),
                        Box::new(b),
                    ))));
                }
            }

            // For variables with a singleton points-to set, assert equality
            let pts = self.get_points_to(vars[i]);
            if pts.len() == 1 {
                // SAFETY: len == 1 guarantees .next() returns Some.
                let target = pts.iter().next()
                    .unwrap_or_else(|| unreachable!("empty iter despite len == 1"));
                let ptr = Formula::Var(format!("ptr_{}", vars[i]), Sort::Int);
                let loc = Formula::Var(format!("loc_{target}"), Sort::Int);
                conjuncts.push(Formula::Eq(Box::new(ptr), Box::new(loc)));
            }
        }

        match conjuncts.len() {
            0 => Formula::Bool(true),
            1 => conjuncts.pop().unwrap_or(Formula::Bool(true)),
            _ => Formula::And(conjuncts),
        }
    }
}

// ── Transfer Function ───────────────────────────────────────────────────────

/// Pointer transfer function for the CPA framework.
///
/// Handles:
/// - `Ref { place }` -> creates a new points-to entry
/// - Copy/Move of a reference -> copies the points-to set
/// - Aggregates -> tracks reference components
#[derive(Debug, Clone)]
pub struct PointerTransfer<'a> {
    body: &'a VerifiableBody,
}

impl<'a> PointerTransfer<'a> {
    /// Create a pointer transfer for a verifiable body.
    #[must_use]
    pub fn new(body: &'a VerifiableBody) -> Self {
        Self { body }
    }
}

impl TransferFunction<CpaPointerState> for PointerTransfer<'_> {
    fn transfer(&self, state: &CpaPointerState, stmt: &Statement) -> CpaPointerState {
        if state.is_unreachable {
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

fn transfer_assign(
    state: &CpaPointerState,
    target: &str,
    body: &VerifiableBody,
    rvalue: &Rvalue,
) -> CpaPointerState {
    let mut next = state.clone();

    match rvalue {
        // &x or &mut x -> target points to x
        Rvalue::Ref { place, .. } => {
            let pointee = place_to_var_name(body, place);
            let mut pts = BTreeSet::new();
            pts.insert(pointee);
            next.set_points_to(target, pts);
        }

        // Copy/Move of a reference -> copy the points-to set
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => {
            let source = place_to_var_name(body, place);

            // Check if the source is a dereference (e.g., *ptr)
            if has_deref_projection(place) {
                // *ptr = ... is a write through a pointer.
                // The target gets the points-to set of what ptr points to.
                let base = base_var_name(body, place);
                let base_pts = state.get_points_to(&base);
                // When dereferencing, the result points to whatever the
                // pointed-to locations themselves point to.
                let mut result_pts = BTreeSet::new();
                for loc in &base_pts {
                    result_pts.extend(state.get_points_to(loc));
                }
                if result_pts.is_empty() {
                    // Non-reference value: clear points-to for target
                    next.points_to.remove(target);
                } else {
                    next.set_points_to(target, result_pts);
                }
            } else {
                // Simple copy/move: copy the points-to set
                let source_pts = state.get_points_to(&source);
                if source_pts.is_empty() {
                    next.points_to.remove(target);
                } else {
                    next.set_points_to(target, source_pts);
                }
            }
        }

        // Aggregate with reference components
        Rvalue::Aggregate(_, ops) => {
            // If any operand is a reference, the aggregate may contain references
            // For now, clear the target's points-to info
            next.points_to.remove(target);
            for (i, op) in ops.iter().enumerate() {
                if let Operand::Copy(place) | Operand::Move(place) = op {
                    let source = place_to_var_name(body, place);
                    let source_pts = state.get_points_to(&source);
                    if !source_pts.is_empty() {
                        let field_name = format!("{target}.{i}");
                        next.set_points_to(field_name, source_pts);
                    }
                }
            }
        }

        // Cast of a reference preserves alias info
        Rvalue::Cast(Operand::Copy(place) | Operand::Move(place), _) => {
            let source = place_to_var_name(body, place);
            let source_pts = state.get_points_to(&source);
            if source_pts.is_empty() {
                next.points_to.remove(target);
            } else {
                next.set_points_to(target, source_pts);
            }
        }

        // Everything else clears the points-to info for the target
        _ => {
            next.points_to.remove(target);
        }
    }

    next
}

fn has_deref_projection(place: &Place) -> bool {
    place.projections.iter().any(|p| matches!(p, Projection::Deref))
}

fn base_var_name(body: &VerifiableBody, place: &Place) -> String {
    let fallback = format!("_{}", place.local);
    body.locals
        .get(place.local)
        .and_then(|decl| decl.name.as_deref())
        .unwrap_or(&fallback)
        .to_string()
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
    use trust_types::{BasicBlock, BlockId, ConstValue, LocalDecl, SourceSpan, Terminator, Ty};

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    fn ref_body() -> VerifiableBody {
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("y".into()) },
                LocalDecl {
                    index: 3,
                    ty: Ty::Ref { inner: Box::new(Ty::i32()), mutable: false },
                    name: Some("r".into()),
                },
                LocalDecl {
                    index: 4,
                    ty: Ty::Ref { inner: Box::new(Ty::i32()), mutable: true },
                    name: Some("s".into()),
                },
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
    fn test_pointer_state_top_and_bottom() {
        let top = CpaPointerState::top();
        assert!(!top.is_bottom());
        assert!(top.get_points_to("x").is_empty());

        let bottom = CpaPointerState::bottom();
        assert!(bottom.is_bottom());
    }

    #[test]
    fn test_pointer_state_set_and_get() {
        let mut state = CpaPointerState::top();
        let mut pts = BTreeSet::new();
        pts.insert("x".to_string());
        state.set_points_to("r", pts);

        assert_eq!(state.get_points_to("r"), BTreeSet::from(["x".to_string()]));
        assert!(state.get_points_to("s").is_empty());
    }

    #[test]
    fn test_pointer_state_may_alias() {
        let mut state = CpaPointerState::top();
        state.set_points_to("r", BTreeSet::from(["x".to_string(), "y".to_string()]));
        state.set_points_to("s", BTreeSet::from(["y".to_string(), "z".to_string()]));

        assert!(state.may_alias("r", "s")); // both may point to y
    }

    #[test]
    fn test_pointer_state_no_alias() {
        let mut state = CpaPointerState::top();
        state.set_points_to("r", BTreeSet::from(["x".to_string()]));
        state.set_points_to("s", BTreeSet::from(["y".to_string()]));

        assert!(!state.may_alias("r", "s")); // disjoint points-to sets
    }

    #[test]
    fn test_pointer_state_must_alias() {
        let mut state = CpaPointerState::top();
        state.set_points_to("r", BTreeSet::from(["x".to_string()]));
        state.set_points_to("s", BTreeSet::from(["x".to_string()]));

        assert!(state.must_alias("r", "s"));
    }

    #[test]
    fn test_pointer_state_not_must_alias_when_multiple() {
        let mut state = CpaPointerState::top();
        state.set_points_to("r", BTreeSet::from(["x".to_string(), "y".to_string()]));
        state.set_points_to("s", BTreeSet::from(["x".to_string(), "y".to_string()]));

        assert!(!state.must_alias("r", "s")); // multiple possible targets
    }

    #[test]
    fn test_pointer_state_join() {
        let mut a = CpaPointerState::top();
        a.set_points_to("r", BTreeSet::from(["x".to_string()]));

        let mut b = CpaPointerState::top();
        b.set_points_to("r", BTreeSet::from(["y".to_string()]));

        let joined = a.join(&b);
        assert_eq!(
            joined.get_points_to("r"),
            BTreeSet::from(["x".to_string(), "y".to_string()])
        );
    }

    #[test]
    fn test_pointer_state_join_with_bottom() {
        let mut a = CpaPointerState::top();
        a.set_points_to("r", BTreeSet::from(["x".to_string()]));

        let bottom = CpaPointerState::bottom();
        assert_eq!(a.join(&bottom), a);
        assert_eq!(bottom.join(&a), a);
    }

    #[test]
    fn test_pointer_state_leq() {
        let mut smaller = CpaPointerState::top();
        smaller.set_points_to("r", BTreeSet::from(["x".to_string()]));

        let mut larger = CpaPointerState::top();
        larger.set_points_to("r", BTreeSet::from(["x".to_string(), "y".to_string()]));

        assert!(smaller.leq(&larger));
        assert!(!larger.leq(&smaller));
    }

    #[test]
    fn test_pointer_state_leq_bottom() {
        let bottom = CpaPointerState::bottom();
        let top = CpaPointerState::top();
        assert!(bottom.leq(&top));
        assert!(!top.leq(&bottom));
    }

    #[test]
    fn test_pointer_state_to_formula_singleton() {
        let mut state = CpaPointerState::top();
        state.set_points_to("r", BTreeSet::from(["x".to_string()]));

        let formula = state.to_formula();
        // Should produce: ptr_r == loc_x
        assert!(matches!(formula, Formula::Eq(..)));
    }

    #[test]
    fn test_pointer_state_to_formula_no_alias() {
        let mut state = CpaPointerState::top();
        state.set_points_to("r", BTreeSet::from(["x".to_string()]));
        state.set_points_to("s", BTreeSet::from(["y".to_string()]));

        let formula = state.to_formula();
        // Should produce conjunction with ptr_r != ptr_s and equalities
        assert!(matches!(formula, Formula::And(_)));
    }

    #[test]
    fn test_pointer_state_to_formula_bottom() {
        let state = CpaPointerState::bottom();
        assert_eq!(state.to_formula(), Formula::Bool(false));
    }

    #[test]
    fn test_pointer_state_to_formula_top() {
        let state = CpaPointerState::top();
        assert_eq!(state.to_formula(), Formula::Bool(true));
    }

    #[test]
    fn test_pointer_transfer_ref_creation() {
        let body = ref_body();
        let transfer = PointerTransfer::new(&body);
        let state = CpaPointerState::top();

        // r = &x
        let stmt = Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        assert_eq!(next.get_points_to("r"), BTreeSet::from(["x".to_string()]));
    }

    #[test]
    fn test_pointer_transfer_mut_ref_creation() {
        let body = ref_body();
        let transfer = PointerTransfer::new(&body);
        let state = CpaPointerState::top();

        // s = &mut y
        let stmt = Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Ref { mutable: true, place: Place::local(2) },
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        assert_eq!(next.get_points_to("s"), BTreeSet::from(["y".to_string()]));
    }

    #[test]
    fn test_pointer_transfer_copy_ref() {
        let body = ref_body();
        let transfer = PointerTransfer::new(&body);

        let mut state = CpaPointerState::top();
        state.set_points_to("r", BTreeSet::from(["x".to_string()]));

        // s = r (copy reference)
        let stmt = Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        assert_eq!(next.get_points_to("s"), BTreeSet::from(["x".to_string()]));
        // r should still point to x
        assert_eq!(next.get_points_to("r"), BTreeSet::from(["x".to_string()]));
    }

    #[test]
    fn test_pointer_transfer_move_ref() {
        let body = ref_body();
        let transfer = PointerTransfer::new(&body);

        let mut state = CpaPointerState::top();
        state.set_points_to("r", BTreeSet::from(["x".to_string()]));

        // s = move r
        let stmt = Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Use(Operand::Move(Place::local(3))),
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        assert_eq!(next.get_points_to("s"), BTreeSet::from(["x".to_string()]));
        // Move semantics: in MIR, move doesn't invalidate the source at the
        // points-to level (that's handled by borrow checking)
        assert_eq!(next.get_points_to("r"), BTreeSet::from(["x".to_string()]));
    }

    #[test]
    fn test_pointer_transfer_non_ref_assignment_clears() {
        let body = ref_body();
        let transfer = PointerTransfer::new(&body);

        let mut state = CpaPointerState::top();
        state.set_points_to("r", BTreeSet::from(["x".to_string()]));

        // r = 42 (non-reference assignment)
        let stmt = Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        assert!(next.get_points_to("r").is_empty());
    }

    #[test]
    fn test_pointer_transfer_nop_preserves() {
        let mut state = CpaPointerState::top();
        state.set_points_to("r", BTreeSet::from(["x".to_string()]));

        let body = ref_body();
        let transfer = PointerTransfer::new(&body);

        let next = transfer.transfer(&state, &Statement::Nop);
        assert_eq!(next, state);
    }

    #[test]
    fn test_pointer_transfer_bottom_stays_bottom() {
        let state = CpaPointerState::bottom();
        let body = ref_body();
        let transfer = PointerTransfer::new(&body);

        let stmt = Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
            span: span(),
        };

        let next = transfer.transfer(&state, &stmt);
        assert!(next.is_bottom());
    }

    #[test]
    fn test_pointer_state_reference_vars() {
        let mut state = CpaPointerState::top();
        state.set_points_to("r", BTreeSet::from(["x".to_string()]));
        state.set_points_to("s", BTreeSet::from(["y".to_string()]));

        let mut refs = state.reference_vars();
        refs.sort();
        assert_eq!(refs, vec!["r", "s"]);
        assert_eq!(state.num_references(), 2);
    }

    #[test]
    fn test_pointer_join_preserves_both_targets() {
        // After a branch, r might point to x or y
        let mut path_a = CpaPointerState::top();
        path_a.set_points_to("r", BTreeSet::from(["x".to_string()]));

        let mut path_b = CpaPointerState::top();
        path_b.set_points_to("r", BTreeSet::from(["y".to_string()]));

        let joined = path_a.join(&path_b);
        let pts = joined.get_points_to("r");
        assert!(pts.contains("x"));
        assert!(pts.contains("y"));
        assert_eq!(pts.len(), 2);
    }
}
