// trust-vcgen/frame_condition.rs: Frame condition generation for modifies clauses (#304)
//
// Generates frame conditions that assert unmodified state is preserved across
// function execution. A modifies clause declares which locations a function may
// change; the frame condition enforces that everything else stays the same.
//
// Key concepts:
// - ModifiesClause: set of locations a function is allowed to modify
// - FrameCondition: formula asserting all non-modified state is preserved
// - generate_frame(): compute frame from modifies clause and all locations
// - infer_modifies(): infer modifies set from function body assignments
// - check_frame_violation(): detect writes outside the modifies set
// - havoc_modified(): generate fresh symbolic values for modified locations
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;

use trust_types::{Formula, Place, Sort, Statement, VerifiableFunction};

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// A location that may be modified, identified by a canonical string name.
/// Derived from a MIR Place (local + projections).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Location {
    /// Canonical name (e.g. "x", "_3.1", "*p").
    pub name: String,
    /// SMT sort for generating symbolic values.
    pub sort: Sort,
}

/// Declares the set of locations a function is permitted to modify.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModifiesClause {
    /// The function this clause applies to.
    pub function: String,
    /// Locations the function may modify.
    pub locations: FxHashSet<Location>,
}

impl ModifiesClause {
    /// Create an empty modifies clause (function modifies nothing).
    #[must_use]
    pub fn empty(function: impl Into<String>) -> Self {
        Self {
            function: function.into(),
            locations: FxHashSet::default(),
        }
    }

    /// Create a modifies clause from a set of location names and sorts.
    #[must_use]
    pub fn new(function: impl Into<String>, locations: FxHashSet<Location>) -> Self {
        Self {
            function: function.into(),
            locations,
        }
    }

    /// Check whether a location name is in the modifies set.
    #[must_use]
    pub fn is_modified(&self, name: &str) -> bool {
        self.locations.iter().any(|loc| loc.name == name)
    }

    /// Number of locations in the modifies set.
    #[must_use]
    pub fn len(&self) -> usize {
        self.locations.len()
    }

    /// Whether the modifies set is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.locations.is_empty()
    }
}

/// A generated frame condition: a formula asserting that all locations outside
/// the modifies set are preserved (old value == new value).
#[derive(Debug, Clone, PartialEq)]
pub struct FrameCondition {
    /// The function this frame applies to.
    pub function: String,
    /// The formula: conjunction of (old_x == new_x) for all non-modified x.
    pub formula: Formula,
    /// Number of preserved (non-modified) locations.
    pub preserved_count: usize,
    /// Number of modified (havocked) locations.
    pub modified_count: usize,
}

/// A frame violation: a write to a location not in the modifies set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrameViolation {
    /// The location that was written but not declared as modified.
    pub location: String,
    /// The block index where the violation was detected.
    pub block_index: usize,
}

/// Result of havocking modified locations: fresh symbolic variables.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HavocResult {
    /// Map from location name to the fresh symbolic variable name.
    pub fresh_vars: Vec<(String, String)>,
}

// ---------------------------------------------------------------------------
// Frame condition generation
// ---------------------------------------------------------------------------

/// Generate a frame condition from a modifies clause and the set of all
/// locations in the function.
///
/// For each location NOT in the modifies set, generates `old_x == new_x`
/// (asserting preservation). Returns the conjunction of all such equalities.
#[must_use]
pub fn generate_frame(
    func: &VerifiableFunction,
    modifies: &ModifiesClause,
) -> FrameCondition {
    let all_locations = collect_all_locations(func);
    let mut preserved = Vec::new();
    let mut modified_count = 0;

    for loc in &all_locations {
        if modifies.is_modified(&loc.name) {
            modified_count += 1;
        } else {
            // old_x == new_x (frame preservation)
            let old_var = Formula::Var(
                format!("{}_old", loc.name),
                loc.sort.clone(),
            );
            let new_var = Formula::Var(
                format!("{}_new", loc.name),
                loc.sort.clone(),
            );
            preserved.push(Formula::Eq(Box::new(old_var), Box::new(new_var)));
        }
    }

    let preserved_count = preserved.len();
    let formula = if preserved.is_empty() {
        Formula::Bool(true)
    } else if preserved.len() == 1 {
        // SAFETY: len == 1 guarantees .next() returns Some.
        preserved.into_iter().next()
            .unwrap_or_else(|| unreachable!("empty iter despite len == 1"))
    } else {
        Formula::And(preserved)
    };

    FrameCondition {
        function: func.name.clone(),
        formula,
        preserved_count,
        modified_count,
    }
}

/// Infer which locations a function body modifies by scanning all assignments.
///
/// Walks every block and statement, collecting the target places of all
/// `Statement::Assign` nodes.
#[must_use]
pub fn infer_modifies(func: &VerifiableFunction) -> ModifiesClause {
    let mut locations = FxHashSet::default();

    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, .. } = stmt {
                let name = place_to_canonical_name(func, place);
                let sort = resolve_place_sort(func, place);
                locations.insert(Location { name, sort });
            }
        }
    }

    ModifiesClause::new(&func.name, locations)
}

/// Check for frame violations: writes to locations not in the modifies set.
///
/// Returns a list of violations (location name + block index) for each
/// assignment that targets a location outside the declared modifies clause.
#[must_use]
pub fn check_frame_violation(
    func: &VerifiableFunction,
    modifies: &ModifiesClause,
) -> Vec<FrameViolation> {
    let mut violations = Vec::new();

    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, .. } = stmt {
                let name = place_to_canonical_name(func, place);
                if !modifies.is_modified(&name) {
                    violations.push(FrameViolation {
                        location: name,
                        block_index: block.id.0,
                    });
                }
            }
        }
    }

    violations
}

/// Generate fresh symbolic values (havoc) for all modified locations.
///
/// For each location in the modifies set, creates a fresh variable name
/// (suffixed with `_havoc`) to represent an arbitrary post-state value.
/// This is used when abstracting a function call: modified locations get
/// unconstrained fresh values, while frame locations are preserved.
#[must_use]
pub fn havoc_modified(modifies: &ModifiesClause) -> HavocResult {
    let mut fresh_vars: Vec<(String, String)> = modifies
        .locations
        .iter()
        .map(|loc| {
            let fresh = format!("{}_havoc", loc.name);
            (loc.name.clone(), fresh)
        })
        .collect();

    // Sort for deterministic output in tests
    fresh_vars.sort_by(|a, b| a.0.cmp(&b.0));

    HavocResult { fresh_vars }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Collect all named locations in a function (locals + projected places from assignments).
fn collect_all_locations(func: &VerifiableFunction) -> Vec<Location> {
    let mut seen = FxHashSet::default();
    let mut result = Vec::new();

    // All declared locals
    for decl in &func.body.locals {
        let name = decl
            .name
            .clone()
            .unwrap_or_else(|| format!("_{}", decl.index));
        let sort = Sort::from_ty(&decl.ty);
        if seen.insert(name.clone()) {
            result.push(Location { name, sort });
        }
    }

    // Also include projected places from assignments (e.g. _3.1)
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, .. } = stmt
                && !place.projections.is_empty() {
                    let name = place_to_canonical_name(func, place);
                    let sort = resolve_place_sort(func, place);
                    if seen.insert(name.clone()) {
                        result.push(Location { name, sort });
                    }
                }
        }
    }

    result
}

/// Convert a Place to a canonical location name.
///
/// Uses the local's declared name if available, otherwise `_N`.
/// Projections are appended: `.N` for fields, `[_N]` for index,
/// `*` for deref, `@N` for downcast.
fn place_to_canonical_name(func: &VerifiableFunction, place: &Place) -> String {
    let fallback = format!("_{}", place.local);
    let base = func
        .body
        .locals
        .get(place.local)
        .and_then(|d| d.name.as_deref())
        .unwrap_or(&fallback);

    if place.projections.is_empty() {
        base.to_string()
    } else {
        use trust_types::Projection;
        let projs: Vec<String> = place
            .projections
            .iter()
            .map(|p| match p {
                Projection::Field(i) => format!(".{i}"),
                Projection::Index(i) => format!("[_{i}]"),
                Projection::Deref => "*".to_string(),
                Projection::Downcast(i) => format!("@{i}"),
                Projection::ConstantIndex { offset, from_end } => {
                    if *from_end { format!("[-{offset}]") } else { format!("[{offset}]") }
                }
                Projection::Subslice { from, to, from_end } => {
                    if *from_end { format!("[{from}..-{to}]") } else { format!("[{from}..{to}]") }
                }
                _ => "unknown".to_string(),
            })
            .collect();
        format!("{base}{}", projs.join(""))
    }
}

/// Resolve the SMT sort for a place, walking through projections.
fn resolve_place_sort(func: &VerifiableFunction, place: &Place) -> Sort {
    use trust_types::Ty;

    let Some(decl) = func.body.locals.get(place.local) else {
        return Sort::Int;
    };

    let mut ty = &decl.ty;
    for proj in &place.projections {
        ty = match (proj, ty) {
            (trust_types::Projection::Field(idx), Ty::Tuple(fields)) => {
                match fields.get(*idx) {
                    Some(t) => t,
                    None => return Sort::Int,
                }
            }
            (trust_types::Projection::Field(idx), Ty::Adt { fields, .. }) => {
                match fields.get(*idx) {
                    Some((_, t)) => t,
                    None => return Sort::Int,
                }
            }
            (trust_types::Projection::Deref, Ty::Ref { inner, .. }) => inner,
            // tRust #432: Deref through RawPtr yields the pointee type.
            (trust_types::Projection::Deref, Ty::RawPtr { pointee, .. }) => pointee,
            (trust_types::Projection::Index(_), Ty::Array { elem, .. })
            | (trust_types::Projection::Index(_), Ty::Slice { elem }) => elem,
            _ => return Sort::Int,
        };
    }
    Sort::from_ty(ty)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{
        BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place,
        Rvalue, SourceSpan, Terminator, Ty, VerifiableBody, VerifiableFunction,
    };

    /// Build a simple function: fn add(a: u32, b: u32) -> u32 { a + b }
    fn simple_add_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "add".to_string(),
            def_path: "test::add".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },        // return
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: Ty::u32(), name: Some("result".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a function with a tuple field assignment.
    fn tuple_assign_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "tuple_fn".to_string(),
            def_path: "test::tuple_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                        name: Some("pair".into()),
                    },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::field(1, 0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a function that modifies nothing (no assignments).
    fn readonly_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "readonly".to_string(),
            def_path: "test::readonly".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    // -----------------------------------------------------------------------
    // Test: infer_modifies
    // -----------------------------------------------------------------------

    #[test]
    fn test_infer_modifies_simple_add() {
        let func = simple_add_function();
        let modifies = infer_modifies(&func);

        assert_eq!(modifies.function, "add");
        // Assigns to local 3 (result) and local 0 (return slot)
        assert_eq!(modifies.len(), 2);
        assert!(modifies.is_modified("result"));
        assert!(modifies.is_modified("_0"));
        assert!(!modifies.is_modified("a"));
        assert!(!modifies.is_modified("b"));
    }

    #[test]
    fn test_infer_modifies_readonly() {
        let func = readonly_function();
        let modifies = infer_modifies(&func);

        assert!(modifies.is_empty(), "readonly function should have empty modifies");
    }

    #[test]
    fn test_infer_modifies_tuple_field() {
        let func = tuple_assign_function();
        let modifies = infer_modifies(&func);

        assert!(
            modifies.is_modified("pair.0"),
            "should detect tuple field assignment"
        );
        assert!(!modifies.is_modified("pair"));
        assert!(!modifies.is_modified("x"));
    }

    // -----------------------------------------------------------------------
    // Test: generate_frame
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_frame_preserves_unmodified() {
        let func = simple_add_function();
        let modifies = infer_modifies(&func);
        let frame = generate_frame(&func, &modifies);

        assert_eq!(frame.function, "add");
        assert_eq!(frame.modified_count, 2);
        // a and b are preserved (not modified)
        assert_eq!(frame.preserved_count, 2);
        // Formula should be And([a_old == a_new, b_old == b_new])
        match &frame.formula {
            Formula::And(clauses) => {
                assert_eq!(clauses.len(), 2);
                for clause in clauses {
                    assert!(
                        matches!(clause, Formula::Eq(_, _)),
                        "each frame clause should be an equality"
                    );
                }
            }
            _ => panic!("expected And formula for frame with 2 preserved locations"),
        }
    }

    #[test]
    fn test_generate_frame_all_modified() {
        let func = simple_add_function();
        // Create a modifies clause that covers ALL locations
        let all_locs = collect_all_locations(&func);
        let modifies = ModifiesClause::new(
            "add",
            all_locs.into_iter().collect(),
        );
        let frame = generate_frame(&func, &modifies);

        assert_eq!(frame.preserved_count, 0);
        assert_eq!(frame.formula, Formula::Bool(true));
    }

    #[test]
    fn test_generate_frame_nothing_modified() {
        let func = simple_add_function();
        let modifies = ModifiesClause::empty("add");
        let frame = generate_frame(&func, &modifies);

        // All 4 locals should be preserved
        assert_eq!(frame.preserved_count, 4);
        assert_eq!(frame.modified_count, 0);
    }

    #[test]
    fn test_generate_frame_single_preserved() {
        let func = readonly_function();
        // Modify _0 but not x -> single preserved location
        let mut locs = FxHashSet::default();
        locs.insert(Location {
            name: "_0".to_string(),
            sort: Sort::Int,
        });
        let modifies = ModifiesClause::new("readonly", locs);
        let frame = generate_frame(&func, &modifies);

        assert_eq!(frame.preserved_count, 1);
        // Single equality, not wrapped in And
        assert!(
            matches!(&frame.formula, Formula::Eq(_, _)),
            "single preserved location should produce bare Eq, not And"
        );
    }

    // -----------------------------------------------------------------------
    // Test: check_frame_violation
    // -----------------------------------------------------------------------

    #[test]
    fn test_check_frame_violation_no_violations() {
        let func = simple_add_function();
        let modifies = infer_modifies(&func);
        let violations = check_frame_violation(&func, &modifies);

        assert!(violations.is_empty(), "inferred modifies should have no violations");
    }

    #[test]
    fn test_check_frame_violation_detects_extra_write() {
        let func = simple_add_function();
        // Only allow modification of "result", not "_0"
        let mut locs = FxHashSet::default();
        locs.insert(Location {
            name: "result".to_string(),
            sort: Sort::BitVec(32),
        });
        let modifies = ModifiesClause::new("add", locs);
        let violations = check_frame_violation(&func, &modifies);

        assert_eq!(violations.len(), 1, "writing to _0 should be a violation");
        assert_eq!(violations[0].location, "_0");
        assert_eq!(violations[0].block_index, 0);
    }

    #[test]
    fn test_check_frame_violation_empty_modifies() {
        let func = simple_add_function();
        let modifies = ModifiesClause::empty("add");
        let violations = check_frame_violation(&func, &modifies);

        assert_eq!(violations.len(), 2, "all writes should be violations with empty modifies");
    }

    // -----------------------------------------------------------------------
    // Test: havoc_modified
    // -----------------------------------------------------------------------

    #[test]
    fn test_havoc_modified_generates_fresh_vars() {
        let func = simple_add_function();
        let modifies = infer_modifies(&func);
        let havoc = havoc_modified(&modifies);

        assert_eq!(havoc.fresh_vars.len(), 2);
        // Sorted by original name
        for (orig, fresh) in &havoc.fresh_vars {
            assert!(fresh.ends_with("_havoc"));
            assert!(fresh.starts_with(orig.as_str()));
        }
    }

    #[test]
    fn test_havoc_modified_empty() {
        let modifies = ModifiesClause::empty("test");
        let havoc = havoc_modified(&modifies);

        assert!(havoc.fresh_vars.is_empty());
    }

    // -----------------------------------------------------------------------
    // Test: ModifiesClause API
    // -----------------------------------------------------------------------

    #[test]
    fn test_modifies_clause_empty_constructor() {
        let mc = ModifiesClause::empty("foo");
        assert_eq!(mc.function, "foo");
        assert!(mc.is_empty());
        assert_eq!(mc.len(), 0);
        assert!(!mc.is_modified("x"));
    }

    #[test]
    fn test_modifies_clause_new_constructor() {
        let mut locs = FxHashSet::default();
        locs.insert(Location {
            name: "x".to_string(),
            sort: Sort::Int,
        });
        locs.insert(Location {
            name: "y".to_string(),
            sort: Sort::Bool,
        });
        let mc = ModifiesClause::new("bar", locs);

        assert_eq!(mc.function, "bar");
        assert_eq!(mc.len(), 2);
        assert!(mc.is_modified("x"));
        assert!(mc.is_modified("y"));
        assert!(!mc.is_modified("z"));
    }
}
