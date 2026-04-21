// trust-vcgen/pointer_analysis.rs: Abstract interpretation over pointer states
//
// Tracks pointer validity (null, valid, dangling, freed) through the MIR
// control flow graph and generates VCs for unsafe dereferences. This is a
// lightweight flow-sensitive analysis that catches common pointer bugs:
// - Dereferencing a possibly-null pointer
// - Dereferencing a freed pointer (use-after-free)
// - Dereferencing a dangling pointer
// - Misaligned pointer dereference
//
// Part of #132: Comprehensive unsafe code verification
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use serde::{Deserialize, Serialize};
use trust_types::*;
use trust_types::fx::FxHashSet;

// ────────────────────────────────────────────────────────────────────────────
// Pointer state lattice
// ────────────────────────────────────────────────────────────────────────────

/// Abstract state of a pointer at a given program point.
///
/// Forms a lattice:
/// ```text
///          Unknown
///         /  |  \  \
///      Null Valid Freed Dangling
///         \  |  /  /
///          Bottom
/// ```
///
/// Join merges states conservatively (if a pointer is Valid on one path
/// and Null on another, the join is Unknown).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PointerState {
    /// No information available -- must check before deref.
    Unknown,
    /// Known to be null (e.g., assigned from literal 0 or `ptr::null()`).
    Null,
    /// Known to be valid: non-null, within allocation, properly aligned.
    Valid,
    /// The underlying allocation has been freed (use-after-free risk).
    Freed,
    /// Points to stack memory that has gone out of scope.
    Dangling,
    /// Unreachable state (bottom of lattice).
    Bottom,
}

impl PointerState {
    /// Join two pointer states (least upper bound in the lattice).
    #[must_use]
    pub fn join(self, other: Self) -> Self {
        if self == other {
            return self;
        }
        match (self, other) {
            (Self::Bottom, s) | (s, Self::Bottom) => s,
            _ => Self::Unknown,
        }
    }

    /// Whether this state is safe to dereference.
    #[must_use]
    pub fn is_safe_to_deref(self) -> bool {
        self == Self::Valid
    }

    /// Whether dereferencing this pointer is definitely an error.
    #[must_use]
    pub fn is_definite_error(self) -> bool {
        matches!(self, Self::Null | Self::Freed | Self::Dangling)
    }

    /// Human-readable label for diagnostics.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::Unknown => "unknown",
            Self::Null => "null",
            Self::Valid => "valid",
            Self::Freed => "freed",
            Self::Dangling => "dangling",
            Self::Bottom => "bottom",
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Pointer analysis state
// ────────────────────────────────────────────────────────────────────────────

/// Pointer states for all tracked locals at a program point.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PointerAnalysisState {
    /// Map from local index to pointer state.
    states: FxHashMap<usize, PointerState>,
}

impl PointerAnalysisState {
    /// Create a new empty state.
    #[must_use]
    pub fn new() -> Self {
        Self {
            states: FxHashMap::default(),
        }
    }

    /// Get the state of a local. Returns Unknown if not tracked.
    #[must_use]
    pub fn get(&self, local: usize) -> PointerState {
        self.states.get(&local).copied().unwrap_or(PointerState::Unknown)
    }

    /// Set the state of a local.
    pub fn set(&mut self, local: usize, state: PointerState) {
        self.states.insert(local, state);
    }

    /// Number of tracked locals.
    #[must_use]
    pub fn tracked_count(&self) -> usize {
        self.states.len()
    }

    /// Join with another state (per-local join).
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        let mut result = Self::new();
        // Join all keys from both states
        let all_keys: FxHashSet<usize> = self
            .states
            .keys()
            .chain(other.states.keys())
            .copied()
            .collect();
        for key in all_keys {
            let s1 = self.get(key);
            let s2 = other.get(key);
            result.set(key, s1.join(s2));
        }
        result
    }
}

impl Default for PointerAnalysisState {
    fn default() -> Self {
        Self::new()
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Pointer analysis engine
// ────────────────────────────────────────────────────────────────────────────

/// Result of analyzing a single dereference.
#[derive(Debug, Clone)]
pub struct DerefCheckResult {
    /// Local index of the pointer being dereferenced.
    pub pointer_local: usize,
    /// State of the pointer at the dereference point.
    pub state: PointerState,
    /// Block where the deref occurs.
    pub block_id: BlockId,
    /// Source span of the deref.
    pub span: SourceSpan,
}

/// Run pointer analysis on a function and check all dereferences.
///
/// Returns results for each dereference found, indicating the pointer
/// state at that program point. The caller can use these to generate
/// targeted VCs or diagnostics.
#[must_use]
pub fn analyze_pointers(func: &VerifiableFunction) -> Vec<DerefCheckResult> {
    let pointer_locals = identify_pointer_locals(func);
    if pointer_locals.is_empty() {
        return Vec::new();
    }

    // Initialize states: arguments are Unknown (could be anything),
    // non-argument pointer locals start as Bottom (uninitialized).
    let mut block_states: FxHashMap<BlockId, PointerAnalysisState> = FxHashMap::default();

    let mut init_state = PointerAnalysisState::new();
    for &local in &pointer_locals {
        if local <= func.body.arg_count {
            init_state.set(local, PointerState::Unknown);
        } else {
            init_state.set(local, PointerState::Bottom);
        }
    }
    if let Some(first_block) = func.body.blocks.first() {
        block_states.insert(first_block.id, init_state);
    }

    // Simple forward pass (single-pass for acyclic CFGs, which covers
    // most MIR basic blocks from a single function).
    for block in &func.body.blocks {
        let mut state = block_states
            .get(&block.id)
            .cloned()
            .unwrap_or_default();

        // Transfer through statements
        for stmt in &block.stmts {
            transfer_statement(stmt, &pointer_locals, &mut state);
        }

        // Propagate to successors
        let successors = block.terminator.unguarded_successors();
        for clause in block.terminator.discovered_clauses(block.id) {
            if let ClauseTarget::Block(target) = clause.target {
                let existing = block_states
                    .get(&target)
                    .cloned()
                    .unwrap_or_default();
                block_states.insert(target, existing.join(&state));
            }
        }
        for succ in successors {
            let existing = block_states
                .get(&succ)
                .cloned()
                .unwrap_or_default();
            block_states.insert(succ, existing.join(&state));
        }

        // Store the final state for this block (after statements, before terminator)
        block_states.insert(block.id, state);
    }

    // Check all dereferences against computed states
    let mut results = Vec::new();
    for block in &func.body.blocks {
        let state = block_states
            .get(&block.id)
            .cloned()
            .unwrap_or_default();

        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, span, .. } = stmt
                && let Some(local) = deref_pointer_local(rvalue) {
                    results.push(DerefCheckResult {
                        pointer_local: local,
                        state: state.get(local),
                        block_id: block.id,
                        span: span.clone(),
                    });
                }
        }
    }

    results
}

/// Identify which locals have pointer/reference types.
fn identify_pointer_locals(func: &VerifiableFunction) -> Vec<usize> {
    func.body
        .locals
        .iter()
        // tRust #432: Include both Ref and RawPtr locals as pointer locals.
        .filter(|d| d.ty.is_pointer_like())
        .map(|d| d.index)
        .collect()
}

/// Transfer function: update pointer states after a statement.
fn transfer_statement(
    stmt: &Statement,
    pointer_locals: &[usize],
    state: &mut PointerAnalysisState,
) {
    if let Statement::Assign { place, rvalue, .. } = stmt {
        let dest = place.local;
        if !pointer_locals.contains(&dest) {
            return;
        }

        match rvalue {
            // Assigning a constant null
            Rvalue::Use(Operand::Constant(ConstValue::Int(0)))
            | Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))) => {
                state.set(dest, PointerState::Null);
            }
            // Copying/moving another pointer
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) => {
                if pointer_locals.contains(&src.local) && src.projections.is_empty() {
                    state.set(dest, state.get(src.local));
                }
            }
            // Taking a reference: the result is Valid
            Rvalue::Ref { .. } => {
                state.set(dest, PointerState::Valid);
            }
            // Unknown rvalue: pointer state becomes Unknown
            _ => {
                state.set(dest, PointerState::Unknown);
            }
        }
    }
}

/// If an rvalue dereferences a pointer, return the local index.
fn deref_pointer_local(rvalue: &Rvalue) -> Option<usize> {
    match rvalue {
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => {
            if place.projections.iter().any(|p| matches!(p, Projection::Deref)) {
                Some(place.local)
            } else {
                None
            }
        }
        Rvalue::Ref { place, .. } => {
            if place.projections.iter().any(|p| matches!(p, Projection::Deref)) {
                Some(place.local)
            } else {
                None
            }
        }
        _ => None,
    }
}

// ────────────────────────────────────────────────────────────────────────────
// VC generation from pointer analysis
// ────────────────────────────────────────────────────────────────────────────

/// Generate VCs for pointer safety based on analysis results.
///
/// Produces VCs for dereferences where the pointer state is not
/// definitively `Valid`. The formula encodes the specific concern:
/// - Unknown -> null check + dangling check
/// - Null -> definite null deref
/// - Freed -> definite use-after-free
/// - Dangling -> definite dangling deref
#[must_use]
pub fn check_deref_safety(
    func: &VerifiableFunction,
) -> Vec<VerificationCondition> {
    let results = analyze_pointers(func);
    let mut vcs = Vec::new();

    for result in &results {
        if result.state.is_safe_to_deref() {
            continue; // Proven safe, no VC needed
        }

        let ptr_name = func
            .body
            .locals
            .get(result.pointer_local)
            .and_then(|d| d.name.as_deref())
            .unwrap_or("unknown")
            .to_string();

        match result.state {
            PointerState::Null => {
                vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:ptr] definite null pointer dereference: *{ptr_name}"
                        ),
                    },
                    function: func.name.clone(),
                    location: result.span.clone(),
                    // Always SAT: we know it's null
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                });
            }
            PointerState::Freed => {
                vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:ptr] use-after-free: *{ptr_name}"
                        ),
                    },
                    function: func.name.clone(),
                    location: result.span.clone(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                });
            }
            PointerState::Dangling => {
                vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:ptr] dangling pointer dereference: *{ptr_name}"
                        ),
                    },
                    function: func.name.clone(),
                    location: result.span.clone(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                });
            }
            PointerState::Unknown | PointerState::Bottom => {
                // Could be null -- generate a null check VC
                let ptr_var = Formula::Var(
                    format!("ptr_{ptr_name}"),
                    Sort::Int,
                );
                vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:ptr] possible null dereference: *{ptr_name}"
                        ),
                    },
                    function: func.name.clone(),
                    location: result.span.clone(),
                    formula: Formula::Eq(
                        Box::new(ptr_var),
                        Box::new(Formula::Int(0)),
                    ),
                    contract_metadata: None,
                });
            }
            PointerState::Valid => unreachable!("filtered above"),
        }
    }

    vcs
}

/// Generate alignment check VCs for pointer dereferences.
///
/// For each dereference of a pointer-typed local, generates a VC
/// asserting that the pointer address is properly aligned for its
/// pointee type.
#[must_use]
pub fn check_alignment(
    func: &VerifiableFunction,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, span, .. } = stmt
                && let Some(local) = deref_pointer_local(rvalue) {
                    let ptr_name = func
                        .body
                        .locals
                        .get(local)
                        .and_then(|d| d.name.as_deref())
                        .unwrap_or("unknown");

                    // Determine alignment from the pointee type
                    // tRust #432: Extract alignment from both Ref and RawPtr via pointee_ty().
                    let align = func
                        .body
                        .locals
                        .get(local)
                        .and_then(|d| d.ty.pointee_ty()
                            .and_then(|p| p.int_width().map(|w| w / 8)))
                        .unwrap_or(1);

                    if align > 1 {
                        let ptr_var = Formula::Var(
                            format!("ptr_{ptr_name}"),
                            Sort::Int,
                        );
                        vcs.push(VerificationCondition {
                            kind: VcKind::Assertion {
                                message: format!(
                                    "[unsafe:ptr] alignment check for *{ptr_name} (align={align})"
                                ),
                            },
                            function: func.name.clone(),
                            location: span.clone(),
                            formula: Formula::Not(Box::new(Formula::Eq(
                                Box::new(Formula::Rem(
                                    Box::new(ptr_var),
                                    Box::new(Formula::Int(align as i128)),
                                )),
                                Box::new(Formula::Int(0)),
                            ))),
                            contract_metadata: None,
                        });
                    }
                }
        }
    }

    vcs
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── Test helpers ─────────────────────────────────────────────────────

    fn deref_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "deref_raw".to_string(),
            def_path: "test::deref_raw".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                        name: Some("raw_ptr".into()),
                    },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("value".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Deref],
                        })),
                        span: SourceSpan {
                            file: "test.rs".into(),
                            line_start: 5,
                            col_start: 4,
                            line_end: 5,
                            col_end: 15,
                        },
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn safe_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "safe_add".to_string(),
            def_path: "test::safe_add".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
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

    /// Function that takes a ref, creates a ref via &, then derefs it.
    /// The ref-created pointer should be Valid -> no VC needed.
    fn ref_then_deref_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "ref_deref".to_string(),
            def_path: "test::ref_deref".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                    LocalDecl {
                        index: 2,
                        ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                        name: Some("ptr".into()),
                    },
                    LocalDecl { index: 3, ty: Ty::u32(), name: Some("val".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        // ptr = &x -> state becomes Valid
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Ref {
                                mutable: false,
                                place: Place::local(1),
                            },
                            span: SourceSpan::default(),
                        },
                        // val = *ptr -> deref of Valid pointer
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 2,
                                projections: vec![Projection::Deref],
                            })),
                            span: SourceSpan {
                                file: "test.rs".into(),
                                line_start: 4,
                                col_start: 4,
                                line_end: 4,
                                col_end: 15,
                            },
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    // ── PointerState tests ──────────────────────────────────────────────

    #[test]
    fn test_pointer_state_join_same() {
        assert_eq!(PointerState::Valid.join(PointerState::Valid), PointerState::Valid);
        assert_eq!(PointerState::Null.join(PointerState::Null), PointerState::Null);
        assert_eq!(
            PointerState::Unknown.join(PointerState::Unknown),
            PointerState::Unknown
        );
    }

    #[test]
    fn test_pointer_state_join_bottom() {
        assert_eq!(PointerState::Bottom.join(PointerState::Valid), PointerState::Valid);
        assert_eq!(PointerState::Null.join(PointerState::Bottom), PointerState::Null);
        assert_eq!(
            PointerState::Bottom.join(PointerState::Bottom),
            PointerState::Bottom
        );
    }

    #[test]
    fn test_pointer_state_join_different_becomes_unknown() {
        assert_eq!(PointerState::Valid.join(PointerState::Null), PointerState::Unknown);
        assert_eq!(PointerState::Freed.join(PointerState::Valid), PointerState::Unknown);
        assert_eq!(
            PointerState::Dangling.join(PointerState::Null),
            PointerState::Unknown
        );
    }

    #[test]
    fn test_pointer_state_is_safe_to_deref() {
        assert!(PointerState::Valid.is_safe_to_deref());
        assert!(!PointerState::Null.is_safe_to_deref());
        assert!(!PointerState::Unknown.is_safe_to_deref());
        assert!(!PointerState::Freed.is_safe_to_deref());
        assert!(!PointerState::Dangling.is_safe_to_deref());
    }

    #[test]
    fn test_pointer_state_is_definite_error() {
        assert!(PointerState::Null.is_definite_error());
        assert!(PointerState::Freed.is_definite_error());
        assert!(PointerState::Dangling.is_definite_error());
        assert!(!PointerState::Valid.is_definite_error());
        assert!(!PointerState::Unknown.is_definite_error());
    }

    #[test]
    fn test_pointer_state_labels() {
        assert_eq!(PointerState::Unknown.label(), "unknown");
        assert_eq!(PointerState::Null.label(), "null");
        assert_eq!(PointerState::Valid.label(), "valid");
        assert_eq!(PointerState::Freed.label(), "freed");
        assert_eq!(PointerState::Dangling.label(), "dangling");
        assert_eq!(PointerState::Bottom.label(), "bottom");
    }

    #[test]
    fn test_pointer_state_serialization_roundtrip() {
        for state in [
            PointerState::Unknown,
            PointerState::Null,
            PointerState::Valid,
            PointerState::Freed,
            PointerState::Dangling,
            PointerState::Bottom,
        ] {
            let json = serde_json::to_string(&state).expect("serialize");
            let round: PointerState =
                serde_json::from_str(&json).expect("deserialize");
            assert_eq!(round, state);
        }
    }

    // ── PointerAnalysisState tests ──────────────────────────────────────

    #[test]
    fn test_analysis_state_default_is_unknown() {
        let state = PointerAnalysisState::new();
        assert_eq!(state.get(0), PointerState::Unknown);
        assert_eq!(state.get(42), PointerState::Unknown);
    }

    #[test]
    fn test_analysis_state_set_get() {
        let mut state = PointerAnalysisState::new();
        state.set(1, PointerState::Valid);
        state.set(2, PointerState::Null);
        assert_eq!(state.get(1), PointerState::Valid);
        assert_eq!(state.get(2), PointerState::Null);
        assert_eq!(state.tracked_count(), 2);
    }

    #[test]
    fn test_analysis_state_join() {
        let mut s1 = PointerAnalysisState::new();
        s1.set(1, PointerState::Valid);
        s1.set(2, PointerState::Null);

        let mut s2 = PointerAnalysisState::new();
        s2.set(1, PointerState::Null);
        s2.set(3, PointerState::Valid);

        let joined = s1.join(&s2);
        assert_eq!(joined.get(1), PointerState::Unknown); // Valid join Null
        assert_eq!(joined.get(2), PointerState::Unknown); // Null join Unknown (not tracked in s2)
        assert_eq!(joined.get(3), PointerState::Unknown); // Unknown (not tracked in s1) join Valid
    }

    // ── analyze_pointers tests ──────────────────────────────────────────

    #[test]
    fn test_analyze_pointers_deref_unknown_arg() {
        let func = deref_function();
        let results = analyze_pointers(&func);

        // Should find 1 deref of pointer local 1 (argument -> Unknown)
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].pointer_local, 1);
        assert_eq!(results[0].state, PointerState::Unknown);
    }

    #[test]
    fn test_analyze_pointers_safe_function() {
        let func = safe_function();
        let results = analyze_pointers(&func);
        assert!(results.is_empty(), "safe function has no pointer derefs");
    }

    #[test]
    fn test_analyze_pointers_ref_then_deref_is_valid() {
        let func = ref_then_deref_function();
        let results = analyze_pointers(&func);

        assert_eq!(results.len(), 1);
        assert_eq!(results[0].pointer_local, 2);
        // After `ptr = &x`, the pointer should be Valid
        assert_eq!(results[0].state, PointerState::Valid);
    }

    // ── check_deref_safety tests ────────────────────────────────────────

    #[test]
    fn test_check_deref_safety_unknown_generates_vc() {
        let func = deref_function();
        let vcs = check_deref_safety(&func);

        assert_eq!(vcs.len(), 1, "unknown pointer should generate 1 VC");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::Assertion { message } if message.contains("possible null dereference")
        ));
    }

    #[test]
    fn test_check_deref_safety_valid_no_vc() {
        let func = ref_then_deref_function();
        let vcs = check_deref_safety(&func);
        assert!(vcs.is_empty(), "valid pointer should generate no VCs");
    }

    #[test]
    fn test_check_deref_safety_safe_function_no_vc() {
        let func = safe_function();
        let vcs = check_deref_safety(&func);
        assert!(vcs.is_empty());
    }

    // ── check_alignment tests ───────────────────────────────────────────

    #[test]
    fn test_check_alignment_u32_deref() {
        let func = deref_function();
        let vcs = check_alignment(&func);

        // u32 has alignment 4 (32 bits / 8)
        assert_eq!(vcs.len(), 1);
        assert!(matches!(
            &vcs[0].kind,
            VcKind::Assertion { message } if message.contains("alignment check")
                && message.contains("align=4")
        ));
    }

    #[test]
    fn test_check_alignment_safe_function_no_vc() {
        let func = safe_function();
        let vcs = check_alignment(&func);
        assert!(vcs.is_empty());
    }

    #[test]
    fn test_check_alignment_ref_then_deref() {
        let func = ref_then_deref_function();
        let vcs = check_alignment(&func);

        // Still generates alignment VC regardless of validity
        // (alignment is structural, not flow-dependent)
        assert_eq!(vcs.len(), 1);
        assert!(matches!(
            &vcs[0].kind,
            VcKind::Assertion { message } if message.contains("alignment check")
        ));
    }

    // ── VC proof level tests ────────────────────────────────────────────

    #[test]
    fn test_deref_vcs_are_l0_safety() {
        let func = deref_function();
        let vcs = check_deref_safety(&func);
        for vc in &vcs {
            assert_eq!(vc.kind.proof_level(), ProofLevel::L0Safety);
        }
    }

    #[test]
    fn test_alignment_vcs_are_l0_safety() {
        let func = deref_function();
        let vcs = check_alignment(&func);
        for vc in &vcs {
            assert_eq!(vc.kind.proof_level(), ProofLevel::L0Safety);
        }
    }

    // ── Integration: combined analysis ──────────────────────────────────

    #[test]
    fn test_combined_deref_and_alignment() {
        let func = deref_function();
        let deref_vcs = check_deref_safety(&func);
        let align_vcs = check_alignment(&func);

        let total = deref_vcs.len() + align_vcs.len();
        assert_eq!(total, 2, "deref_function should produce 2 combined VCs");
    }
}
