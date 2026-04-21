// trust-vcgen/chc.rs: Constrained Horn Clause encoding for loop invariant inference
//
// Encodes MIR loops as CHC systems for z4's Spacer engine. Each loop header
// becomes an uninterpreted predicate, each path through the loop body becomes
// a Horn clause. Spacer solves for the predicate interpretations, yielding
// loop invariants.
//
// CHC system structure for a simple loop `while cond { body }`:
//   Entry:     pre(vars) => inv(vars_init)
//   Inductive: inv(vars) /\ cond /\ body_constraint => inv(vars')
//   Exit:      inv(vars) /\ !cond => post(vars)
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use crate::loop_analysis::{LoopInfo, detect_loops};
use crate::u128_to_formula;
use trust_types::fx::FxHashSet;

/// Errors arising from CHC encoding.
#[derive(Debug, Clone, thiserror::Error)]
pub enum ChcError {
    /// The function contains no loops to encode.
    #[error("no loops found in function `{function}`")]
    NoLoops { function: String },

    /// A loop has no induction variables, making CHC encoding impractical.
    #[error("loop at block {header} has no induction variables")]
    NoInductionVars { header: usize },

    /// The loop body could not be symbolically encoded.
    #[error("failed to encode loop body: {reason}")]
    EncodingFailed { reason: String },
}

/// A predicate symbol in a CHC system (e.g., the loop invariant).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChcPredicate {
    /// Name of the predicate (e.g., "inv_bb1").
    pub name: String,
    /// Parameter names with their sorts.
    pub params: Vec<(String, Sort)>,
}

impl ChcPredicate {
    /// Create a predicate application with the given argument formulas.
    #[must_use]
    pub fn apply(&self, args: &[Formula]) -> ChcAtom {
        ChcAtom {
            predicate: self.name.clone(),
            args: args.to_vec(),
        }
    }

    /// Create a predicate application using primed variable names (post-state).
    #[must_use]
    pub fn apply_primed(&self) -> ChcAtom {
        let args: Vec<Formula> = self
            .params
            .iter()
            .map(|(name, sort)| Formula::Var(format!("{name}'"), sort.clone()))
            .collect();
        ChcAtom {
            predicate: self.name.clone(),
            args,
        }
    }

    /// Create a predicate application using unprimed variable names (pre-state).
    #[must_use]
    pub fn apply_unprimed(&self) -> ChcAtom {
        let args: Vec<Formula> = self
            .params
            .iter()
            .map(|(name, sort)| Formula::Var(name.clone(), sort.clone()))
            .collect();
        ChcAtom {
            predicate: self.name.clone(),
            args,
        }
    }
}

/// An application of a predicate to arguments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChcAtom {
    /// Predicate name being applied.
    pub predicate: String,
    /// Arguments to the predicate.
    pub args: Vec<Formula>,
}

/// A single Constrained Horn Clause.
///
/// Semantics: `body_atoms /\ constraint => head`
///
/// In CHC format:
///   - head is a predicate application (or `false` for queries)
///   - body_atoms are predicate applications
///   - constraint is a first-order formula over theory sorts
#[derive(Debug, Clone)]
pub struct ChcClause {
    /// The head predicate (conclusion). None means the query clause (head = false).
    pub head: Option<ChcAtom>,
    /// Body predicate applications (premises).
    pub body_atoms: Vec<ChcAtom>,
    /// First-order constraint over variables.
    pub constraint: Formula,
    /// Human-readable label for diagnostics.
    pub label: String,
}

/// The role of a clause in the CHC system.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClauseRole {
    /// Entry clause: precondition => inv(init_vars)
    Entry,
    /// Inductive clause: inv(vars) /\ body => inv(vars')
    Inductive,
    /// Exit/query clause: inv(vars) /\ exit_cond => postcondition
    Exit,
}

/// A complete CHC system encoding one or more loops.
#[derive(Debug, Clone)]
pub struct ChcSystem {
    /// Predicates to solve for (one per loop).
    pub predicates: Vec<ChcPredicate>,
    /// Horn clauses defining the system.
    pub clauses: Vec<ChcClause>,
    /// Role annotations for each clause (parallel to `clauses`).
    pub roles: Vec<ClauseRole>,
    /// Source function name for diagnostics.
    pub function_name: String,
}

impl ChcSystem {
    /// Number of predicates to infer.
    #[must_use]
    pub fn predicate_count(&self) -> usize {
        self.predicates.len()
    }

    /// Number of clauses in the system.
    #[must_use]
    pub fn clause_count(&self) -> usize {
        self.clauses.len()
    }

    /// Get clauses by role.
    #[must_use]
    pub fn clauses_by_role(&self, role: ClauseRole) -> Vec<&ChcClause> {
        self.clauses
            .iter()
            .zip(self.roles.iter())
            .filter(|(_, r)| **r == role)
            .map(|(c, _)| c)
            .collect()
    }

    /// Get entry clauses.
    #[must_use]
    pub fn entry_clauses(&self) -> Vec<&ChcClause> {
        self.clauses_by_role(ClauseRole::Entry)
    }

    /// Get inductive clauses.
    #[must_use]
    pub fn inductive_clauses(&self) -> Vec<&ChcClause> {
        self.clauses_by_role(ClauseRole::Inductive)
    }

    /// Get exit/query clauses.
    #[must_use]
    pub fn exit_clauses(&self) -> Vec<&ChcClause> {
        self.clauses_by_role(ClauseRole::Exit)
    }
}

/// Encode all loops in a function as a CHC system.
///
/// For each detected loop:
///   1. Creates an invariant predicate over the loop's modified variables
///   2. Generates entry clause: precondition => inv(init_vars)
///   3. Generates inductive clause: inv(vars) /\ loop_body => inv(vars')
///   4. Generates exit clause: inv(vars) /\ exit_cond => post
///
/// The resulting system can be passed to Spacer via `spacer_bridge::to_smtlib2`.
pub fn encode_function_loops(func: &VerifiableFunction) -> Result<ChcSystem, ChcError> {
    let loops = detect_loops(func);
    if loops.is_empty() {
        return Err(ChcError::NoLoops { function: func.name.clone() });
    }

    let mut predicates = Vec::new();
    let mut clauses = Vec::new();
    let mut roles = Vec::new();

    for loop_info in &loops {
        let (pred, loop_clauses, loop_roles) = encode_single_loop(func, loop_info)?;
        predicates.push(pred);
        clauses.extend(loop_clauses);
        roles.extend(loop_roles);
    }

    Ok(ChcSystem {
        predicates,
        clauses,
        roles,
        function_name: func.name.clone(),
    })
}

/// Encode a single loop as CHC clauses.
///
/// Returns the predicate and the entry/inductive/exit clauses.
fn encode_single_loop(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
) -> Result<(ChcPredicate, Vec<ChcClause>, Vec<ClauseRole>), ChcError> {
    // Collect variables modified in the loop body
    let modified_vars = collect_modified_variables(func, loop_info);
    if modified_vars.is_empty() {
        return Err(ChcError::NoInductionVars { header: loop_info.header.0 });
    }

    // Create invariant predicate
    let pred_name = format!("inv_bb{}", loop_info.header.0);
    let predicate = ChcPredicate {
        name: pred_name,
        params: modified_vars.clone(),
    };

    let mut clauses = Vec::new();
    let mut roles = Vec::new();

    // --- Entry clause ---
    // precondition => inv(init_values)
    let init_args = build_init_args(func, loop_info, &modified_vars);
    let entry_head = predicate.apply(&init_args);
    let precondition = build_precondition(func);

    clauses.push(ChcClause {
        head: Some(entry_head),
        body_atoms: vec![],
        constraint: precondition,
        label: format!("entry_bb{}", loop_info.header.0),
    });
    roles.push(ClauseRole::Entry);

    // --- Inductive clause ---
    // inv(vars) /\ cond /\ body_transition => inv(vars')
    let body_pred = predicate.apply_unprimed();
    let primed_head = predicate.apply_primed();

    let loop_cond = extract_loop_condition(func, loop_info);
    let body_transition = build_body_transition(func, loop_info, &modified_vars);

    let inductive_constraint = Formula::And(vec![loop_cond, body_transition]);

    clauses.push(ChcClause {
        head: Some(primed_head),
        body_atoms: vec![body_pred],
        constraint: inductive_constraint,
        label: format!("inductive_bb{}", loop_info.header.0),
    });
    roles.push(ClauseRole::Inductive);

    // --- Exit clause (query) ---
    // inv(vars) /\ !cond => postcondition
    // Encoded as: inv(vars) /\ !cond /\ !post => false
    let exit_pred = predicate.apply_unprimed();
    let exit_cond = extract_exit_condition(func, loop_info);
    let postcondition = build_postcondition(func);

    let exit_constraint = Formula::And(vec![exit_cond, Formula::Not(Box::new(postcondition))]);

    clauses.push(ChcClause {
        head: None, // query: head = false
        body_atoms: vec![exit_pred],
        constraint: exit_constraint,
        label: format!("exit_bb{}", loop_info.header.0),
    });
    roles.push(ClauseRole::Exit);

    Ok((predicate, clauses, roles))
}

/// Collect variables modified inside the loop body.
///
/// These become the parameters of the invariant predicate.
pub(crate) fn collect_modified_variables(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
) -> Vec<(String, Sort)> {
    let mut modified = Vec::new();
    let mut seen_locals = FxHashSet::default();
    let body_set: FxHashSet<usize> =
        loop_info.body_blocks.iter().map(|b| b.0).collect();

    for &body_id in &body_set {
        let Some(block) = func.body.blocks.get(body_id) else {
            continue;
        };
        for stmt in &block.stmts {
            if let Statement::Assign { place, .. } = stmt
                && place.projections.is_empty() && !seen_locals.contains(&place.local) {
                    seen_locals.insert(place.local);
                    if let Some(decl) = func.body.locals.get(place.local) {
                        let name = decl
                            .name
                            .clone()
                            .unwrap_or_else(|| format!("_{}", place.local));
                        let sort = Sort::from_ty(&decl.ty);
                        modified.push((name, sort));
                    }
                }
        }
    }

    // Sort for deterministic output
    modified.sort_by(|a, b| a.0.cmp(&b.0));
    modified
}

/// Build initial values for the invariant predicate arguments.
///
/// Uses induction variable init values where available, falls back to
/// uninterpreted variable references.
fn build_init_args(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    params: &[(String, Sort)],
) -> Vec<Formula> {
    params
        .iter()
        .map(|(name, sort)| {
            // Try to find an induction variable with a known init
            if let Some(ivar) = loop_info.induction_vars.iter().find(|iv| {
                let iv_name = func
                    .body
                    .locals
                    .get(iv.local_idx)
                    .and_then(|d| d.name.clone())
                    .unwrap_or_else(|| format!("_{}", iv.local_idx));
                iv_name == *name
            })
                && let Some(init) = &ivar.init {
                    return init.clone();
                }
            // Fallback: use an initial-state variable
            Formula::Var(format!("{name}_init"), sort.clone())
        })
        .collect()
}

/// Extract the loop continuation condition from the header block.
///
/// Looks for a SwitchInt terminator in the header and extracts the
/// condition under which the loop body is entered.
pub(crate) fn extract_loop_condition(func: &VerifiableFunction, loop_info: &LoopInfo) -> Formula {
    let Some(header) = func.body.blocks.get(loop_info.header.0) else {
        return Formula::Bool(true);
    };

    match &header.terminator {
        Terminator::SwitchInt { discr, targets, .. } => {
            // The loop body is entered when the discriminant matches a target
            // that leads to a body block
            let body_set: FxHashSet<usize> =
                loop_info.body_blocks.iter().map(|b| b.0).collect();

            let discr_formula = crate::operand_to_formula(func, discr);

            for (value, target) in targets {
                if body_set.contains(&target.0) && *target != loop_info.header {
                    // This target enters the loop body
                    return Formula::Eq(
                        Box::new(discr_formula),
                        Box::new(u128_to_formula(*value)),
                    );
                }
            }
            Formula::Bool(true)
        }
        _ => Formula::Bool(true),
    }
}

/// Extract the loop exit condition (negation of the continuation condition).
pub(crate) fn extract_exit_condition(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
) -> Formula {
    let cond = extract_loop_condition(func, loop_info);
    Formula::Not(Box::new(cond))
}

/// Build the body transition relation: how variables change in one iteration.
///
/// For each modified variable, generates `var' = update_expr(var, ...)`.
fn build_body_transition(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    params: &[(String, Sort)],
) -> Formula {
    let mut constraints = Vec::new();
    let body_set: FxHashSet<usize> =
        loop_info.body_blocks.iter().map(|b| b.0).collect();

    for (name, sort) in params {
        let primed = Formula::Var(format!("{name}'"), sort.clone());

        // Try to find the update expression from the loop body
        let update = find_variable_update(func, &body_set, name);

        match update {
            Some(update_formula) => {
                constraints.push(Formula::Eq(Box::new(primed), Box::new(update_formula)));
            }
            None => {
                // Variable not updated in this path -- stays the same
                let unprimed = Formula::Var(name.clone(), sort.clone());
                constraints.push(Formula::Eq(Box::new(primed), Box::new(unprimed)));
            }
        }
    }

    if constraints.is_empty() {
        Formula::Bool(true)
    } else if constraints.len() == 1 {
        // SAFETY: len == 1 arm of the match guarantees .next() returns Some.
        constraints.into_iter().next()
            .unwrap_or_else(|| unreachable!("empty iter despite len == 1"))
    } else {
        Formula::And(constraints)
    }
}

/// Find the update expression for a variable in the loop body.
fn find_variable_update(
    func: &VerifiableFunction,
    body_set: &FxHashSet<usize>,
    var_name: &str,
) -> Option<Formula> {
    for &body_id in body_set {
        let Some(block) = func.body.blocks.get(body_id) else {
            continue;
        };
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt
                && place.projections.is_empty()
                    && let Some(decl) = func.body.locals.get(place.local) {
                        let name = decl
                            .name
                            .clone()
                            .unwrap_or_else(|| format!("_{}", place.local));
                        if name == var_name {
                            return Some(rvalue_to_formula(func, rvalue));
                        }
                    }
        }
    }
    None
}

/// Convert an Rvalue to a Formula.
pub(crate) fn rvalue_to_formula(func: &VerifiableFunction, rvalue: &Rvalue) -> Formula {
    match rvalue {
        Rvalue::Use(op) => crate::operand_to_formula(func, op),
        Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            let l = crate::operand_to_formula(func, lhs);
            let r = crate::operand_to_formula(func, rhs);
            // tRust #390: Pass operand width for proper bitwise formula generation.
            // tRust #782: Pass signedness for correct right-shift selection.
            let ty = crate::operand_ty(func, lhs);
            let width = ty.as_ref().and_then(|t| t.int_width());
            let signed = ty.as_ref().is_some_and(|t| t.is_signed());
            binop_to_formula(*op, l, r, width, signed)
        }
        Rvalue::UnaryOp(UnOp::Neg, op) => {
            Formula::Neg(Box::new(crate::operand_to_formula(func, op)))
        }
        Rvalue::UnaryOp(UnOp::Not, op) => {
            Formula::Not(Box::new(crate::operand_to_formula(func, op)))
        }
        // tRust: #386 — PtrMetadata extracts metadata from a fat pointer.
        // Model as identity (pass-through) for verification purposes.
        Rvalue::UnaryOp(UnOp::PtrMetadata, op) => crate::operand_to_formula(func, op),
        Rvalue::Cast(op, _ty) => {
            // Cast preserves the operand value at the logical level.
            // Bit-width truncation/extension is handled by the overflow pass.
            crate::operand_to_formula(func, op)
        }
        Rvalue::Ref { place, .. } => {
            // Model a reference as a fresh symbolic variable representing the
            // address/pointer.  The variable name encodes the place so that
            // two references to the same place unify.
            let place_name = crate::place_to_var_name(func, place);
            Formula::Var(format!("ref_{place_name}"), Sort::Int)
        }
        Rvalue::Aggregate(kind, operands) => {
            // For single-element aggregates (common: newtype wrappers, single-variant
            // enums), propagate the inner value.  Multi-element aggregates get a
            // fresh symbolic variable — full tuple/struct modeling is deferred.
            if operands.len() == 1 {
                crate::operand_to_formula(func, &operands[0])
            } else {
                let tag = match kind {
                    AggregateKind::Tuple => "tuple",
                    AggregateKind::Array => "array",
                    AggregateKind::Adt { name, .. } => name.as_str(),
                    _ => "unknown",
                };
                Formula::Var(format!("agg_{tag}_{}", operands.len()), Sort::Int)
            }
        }
        Rvalue::Discriminant(place) => {
            // The discriminant is an integer tag for the enum variant.
            let place_name = crate::place_to_var_name(func, place);
            Formula::Var(format!("discr_{place_name}"), Sort::Int)
        }
        Rvalue::Len(place) => {
            // Length is a non-negative integer property of the place.
            let place_name = crate::place_to_var_name(func, place);
            Formula::Var(format!("len_{place_name}"), Sort::Int)
        }
        Rvalue::Repeat(op, _) => crate::operand_to_formula(func, op),
        Rvalue::AddressOf(_, place) => {
            let place_name = crate::place_to_var_name(func, place);
            Formula::Var(format!("addr_{place_name}"), Sort::Int)
        }
        Rvalue::CopyForDeref(place) => {
            let place_name = crate::place_to_var_name(func, place);
            Formula::Var(place_name, Sort::Int)
        }
        _ => Formula::Var("__unknown".to_string(), Sort::Int),
    }
}

/// Convert a binary operation to a Formula.
///
/// `width` is the bit width of the integer operands (from `Ty::int_width()`).
/// When provided, bitwise operations (BitAnd, BitOr, BitXor, Shl, Shr) are
/// translated to proper bitvector formulas (BvAnd, BvOr, BvXor, BvShl, BvLShr)
/// with IntToBv/BvToInt bridges. When `None`, defaults to 64 bits.
// tRust #390: Emit proper bitvector formulas instead of uninterpreted approximations.
// tRust #458: Promoted to `pub` for use by trust-transval vc_core.
pub fn binop_to_formula(op: BinOp, lhs: Formula, rhs: Formula, width: Option<u32>, signed: bool) -> Formula {
    match op {
        BinOp::Add => Formula::Add(Box::new(lhs), Box::new(rhs)),
        BinOp::Sub => Formula::Sub(Box::new(lhs), Box::new(rhs)),
        BinOp::Mul => Formula::Mul(Box::new(lhs), Box::new(rhs)),
        BinOp::Div => Formula::Div(Box::new(lhs), Box::new(rhs)),
        BinOp::Rem => Formula::Rem(Box::new(lhs), Box::new(rhs)),
        BinOp::Eq => Formula::Eq(Box::new(lhs), Box::new(rhs)),
        BinOp::Ne => Formula::Not(Box::new(Formula::Eq(Box::new(lhs), Box::new(rhs)))),
        BinOp::Lt => Formula::Lt(Box::new(lhs), Box::new(rhs)),
        BinOp::Le => Formula::Le(Box::new(lhs), Box::new(rhs)),
        BinOp::Gt => Formula::Gt(Box::new(lhs), Box::new(rhs)),
        BinOp::Ge => Formula::Ge(Box::new(lhs), Box::new(rhs)),
        // tRust #383: Three-way comparison: ITE(a < b, -1, ITE(a == b, 0, 1))
        BinOp::Cmp => Formula::Ite(
            Box::new(Formula::Lt(Box::new(lhs.clone()), Box::new(rhs.clone()))),
            Box::new(Formula::Int(-1)),
            Box::new(Formula::Ite(
                Box::new(Formula::Eq(Box::new(lhs), Box::new(rhs))),
                Box::new(Formula::Int(0)),
                Box::new(Formula::Int(1)),
            )),
        ),
        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
            // tRust #390: Translate bitwise ops to bitvector formulas.
            // Operands are in integer domain (Sort::Int), so we bridge via
            // IntToBv/BvToInt to maintain sort compatibility with the rest of
            // the formula tree.
            let w = width.unwrap_or(64);
            let lhs_bv = Box::new(Formula::IntToBv(Box::new(lhs), w));
            let rhs_bv = Box::new(Formula::IntToBv(Box::new(rhs), w));
            let bv_result = match op {
                BinOp::BitAnd => Formula::BvAnd(lhs_bv, rhs_bv, w),
                BinOp::BitOr => Formula::BvOr(lhs_bv, rhs_bv, w),
                BinOp::BitXor => Formula::BvXor(lhs_bv, rhs_bv, w),
                BinOp::Shl => Formula::BvShl(lhs_bv, rhs_bv, w),
                // tRust #782: Use arithmetic right shift for signed types,
                // logical right shift for unsigned.
                BinOp::Shr if signed => Formula::BvAShr(lhs_bv, rhs_bv, w),
                BinOp::Shr => Formula::BvLShr(lhs_bv, rhs_bv, w),
                _ => unreachable!(
                    "bitvector lowering only handles bitwise and shift BinOp variants selected by the outer match"
                ),
            };
            // Bridge back to integer domain for compatibility with overflow/range checks.
            Formula::BvToInt(Box::new(bv_result), w, false)
        }
        _ => Formula::Var("__unknown_binop".to_string(), Sort::Int),
    }
}

/// Build a precondition formula from function contracts and parameter constraints.
fn build_precondition(func: &VerifiableFunction) -> Formula {
    if func.preconditions.is_empty() {
        Formula::Bool(true)
    } else if func.preconditions.len() == 1 {
        func.preconditions[0].clone()
    } else {
        Formula::And(func.preconditions.clone())
    }
}

/// Build a postcondition formula from function contracts.
fn build_postcondition(func: &VerifiableFunction) -> Formula {
    if func.postconditions.is_empty() {
        Formula::Bool(true)
    } else if func.postconditions.len() == 1 {
        func.postconditions[0].clone()
    } else {
        Formula::And(func.postconditions.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a simple counting loop: while i < n { i += 1; }
    fn counting_loop_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "count_to_n".to_string(),
            def_path: "test::count_to_n".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("i".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("cond".into()) },
                ],
                blocks: vec![
                    // bb0: i = 0; goto bb1
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    // bb1 (header): cond = i < n; SwitchInt -> [1: bb2, else: bb3]
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(2)),
                                Operand::Copy(Place::local(1)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(3)),
                            targets: vec![(1, BlockId(2))],
                            otherwise: BlockId(3),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb2 (body): i += 1; goto bb1
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    // bb3 (exit): return
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a sum loop: while i < n { sum += i; i += 1; }
    fn sum_loop_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "sum_to_n".to_string(),
            def_path: "test::sum_to_n".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("i".into()) },
                    LocalDecl { index: 3, ty: Ty::u32(), name: Some("sum".into()) },
                    LocalDecl { index: 4, ty: Ty::Bool, name: Some("cond".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(2),
                                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(3),
                                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(2)),
                                Operand::Copy(Place::local(1)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(4)),
                            targets: vec![(1, BlockId(2))],
                            otherwise: BlockId(3),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(3),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Add,
                                    Operand::Copy(Place::local(3)),
                                    Operand::Copy(Place::local(2)),
                                ),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(2),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Add,
                                    Operand::Copy(Place::local(2)),
                                    Operand::Constant(ConstValue::Uint(1, 64)),
                                ),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn no_loop_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "identity".to_string(),
            def_path: "test::identity".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
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

    fn loop_with_contracts() -> VerifiableFunction {
        let mut func = counting_loop_function();
        func.preconditions = vec![Formula::Ge(
            Box::new(Formula::Var("n".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )];
        func.postconditions = vec![Formula::Eq(
            Box::new(Formula::Var("i".into(), Sort::Int)),
            Box::new(Formula::Var("n".into(), Sort::Int)),
        )];
        func
    }

    #[test]
    fn test_encode_no_loops_returns_error() {
        let func = no_loop_function();
        let result = encode_function_loops(&func);
        assert!(result.is_err());
        match result.unwrap_err() {
            ChcError::NoLoops { function } => assert_eq!(function, "identity"),
            other => panic!("expected NoLoops error, got: {other:?}"),
        }
    }

    #[test]
    fn test_encode_counting_loop_produces_system() {
        let func = counting_loop_function();
        let system = encode_function_loops(&func).expect("should encode counting loop");
        assert_eq!(system.predicate_count(), 1);
        assert_eq!(system.clause_count(), 3);
        assert_eq!(system.function_name, "count_to_n");
    }

    #[test]
    fn test_predicate_has_correct_name() {
        let func = counting_loop_function();
        let system = encode_function_loops(&func).expect("should encode");
        assert_eq!(system.predicates[0].name, "inv_bb1");
    }

    #[test]
    fn test_predicate_params_are_modified_vars() {
        let func = counting_loop_function();
        let system = encode_function_loops(&func).expect("should encode");
        let params = &system.predicates[0].params;
        assert!(
            params.iter().any(|(name, _)| name == "i"),
            "i should be a predicate parameter, got: {params:?}"
        );
    }

    #[test]
    fn test_clause_roles_are_correct() {
        let func = counting_loop_function();
        let system = encode_function_loops(&func).expect("should encode");
        assert_eq!(system.entry_clauses().len(), 1);
        assert_eq!(system.inductive_clauses().len(), 1);
        assert_eq!(system.exit_clauses().len(), 1);
    }

    #[test]
    fn test_entry_clause_has_no_body_atoms() {
        let func = counting_loop_function();
        let system = encode_function_loops(&func).expect("should encode");
        let entry = &system.entry_clauses()[0];
        assert!(entry.body_atoms.is_empty());
        assert!(entry.head.is_some());
    }

    #[test]
    fn test_inductive_clause_has_body_atom() {
        let func = counting_loop_function();
        let system = encode_function_loops(&func).expect("should encode");
        let inductive = &system.inductive_clauses()[0];
        assert_eq!(inductive.body_atoms.len(), 1);
        assert_eq!(inductive.body_atoms[0].predicate, "inv_bb1");
        assert!(inductive.head.is_some());
    }

    #[test]
    fn test_exit_clause_is_query() {
        let func = counting_loop_function();
        let system = encode_function_loops(&func).expect("should encode");
        let exit = &system.exit_clauses()[0];
        assert!(exit.head.is_none());
        assert_eq!(exit.body_atoms.len(), 1);
    }

    #[test]
    fn test_sum_loop_has_multiple_modified_vars() {
        let func = sum_loop_function();
        let system = encode_function_loops(&func).expect("should encode sum loop");
        let param_names: Vec<&str> = system.predicates[0].params.iter().map(|(n, _)| n.as_str()).collect();
        assert!(param_names.contains(&"i"));
        assert!(param_names.contains(&"sum"));
    }

    #[test]
    fn test_predicate_apply_creates_correct_atom() {
        let pred = ChcPredicate {
            name: "inv".to_string(),
            params: vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
        };
        let atom = pred.apply(&[Formula::Int(0), Formula::Int(1)]);
        assert_eq!(atom.predicate, "inv");
        assert_eq!(atom.args.len(), 2);
    }

    #[test]
    fn test_predicate_apply_primed() {
        let pred = ChcPredicate {
            name: "inv".to_string(),
            params: vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Bool)],
        };
        let atom = pred.apply_primed();
        assert_eq!(atom.args.len(), 2);
        assert!(matches!(&atom.args[0], Formula::Var(name, Sort::Int) if name == "x'"));
        assert!(matches!(&atom.args[1], Formula::Var(name, Sort::Bool) if name == "y'"));
    }

    #[test]
    fn test_predicate_apply_unprimed() {
        let pred = ChcPredicate {
            name: "inv".to_string(),
            params: vec![("x".to_string(), Sort::Int)],
        };
        let atom = pred.apply_unprimed();
        assert!(matches!(&atom.args[0], Formula::Var(name, Sort::Int) if name == "x"));
    }

    #[test]
    fn test_loop_condition_extraction() {
        let func = counting_loop_function();
        let loops = detect_loops(&func);
        let cond = extract_loop_condition(&func, &loops[0]);
        assert!(
            matches!(&cond, Formula::Eq(_, rhs) if matches!(rhs.as_ref(), Formula::Int(1))),
            "loop condition should be cond == 1, got: {cond:?}"
        );
    }

    #[test]
    fn test_exit_condition_is_negated() {
        let func = counting_loop_function();
        let loops = detect_loops(&func);
        let exit_cond = extract_exit_condition(&func, &loops[0]);
        assert!(matches!(&exit_cond, Formula::Not(_)));
    }

    #[test]
    fn test_body_transition_captures_increment() {
        let func = counting_loop_function();
        let loops = detect_loops(&func);
        let modified = collect_modified_variables(&func, &loops[0]);
        let transition = build_body_transition(&func, &loops[0], &modified);
        match &transition {
            Formula::Eq(lhs, _) => {
                assert!(matches!(lhs.as_ref(), Formula::Var(name, _) if name == "i'"));
            }
            Formula::And(clauses) => {
                let has_i_prime = clauses.iter().any(|c| {
                    matches!(c, Formula::Eq(lhs, _) if matches!(lhs.as_ref(), Formula::Var(name, _) if name == "i'"))
                });
                assert!(has_i_prime);
            }
            other => panic!("expected Eq or And, got: {other:?}"),
        }
    }

    #[test]
    fn test_precondition_from_contracts() {
        let func = loop_with_contracts();
        let system = encode_function_loops(&func).expect("should encode");
        let entry = &system.entry_clauses()[0];
        assert!(matches!(&entry.constraint, Formula::Ge(_, _)));
    }

    #[test]
    fn test_postcondition_in_exit_clause() {
        let func = loop_with_contracts();
        let system = encode_function_loops(&func).expect("should encode");
        let exit = &system.exit_clauses()[0];
        match &exit.constraint {
            Formula::And(clauses) => {
                let has_negated_post = clauses.iter().any(|c| matches!(c, Formula::Not(_)));
                assert!(has_negated_post);
            }
            other => panic!("expected And, got: {other:?}"),
        }
    }

    #[test]
    fn test_clause_labels_contain_block_id() {
        let func = counting_loop_function();
        let system = encode_function_loops(&func).expect("should encode");
        for clause in &system.clauses {
            assert!(clause.label.contains("bb1"), "label: {}", clause.label);
        }
    }

    #[test]
    fn test_chc_error_display() {
        let e = ChcError::NoLoops { function: "foo".to_string() };
        assert_eq!(e.to_string(), "no loops found in function `foo`");
        let e = ChcError::NoInductionVars { header: 3 };
        assert_eq!(e.to_string(), "loop at block 3 has no induction variables");
        let e = ChcError::EncodingFailed { reason: "bad loop".to_string() };
        assert_eq!(e.to_string(), "failed to encode loop body: bad loop");
    }

    #[test]
    fn test_collect_modified_variables_sorted() {
        let func = sum_loop_function();
        let loops = detect_loops(&func);
        let modified = collect_modified_variables(&func, &loops[0]);
        for i in 1..modified.len() {
            assert!(modified[i - 1].0 <= modified[i].0, "not sorted: {modified:?}");
        }
    }

    #[test]
    fn test_binop_to_formula_arithmetic() {
        let x = Formula::Var("x".into(), Sort::Int);
        let y = Formula::Var("y".into(), Sort::Int);
        assert!(matches!(binop_to_formula(BinOp::Add, x.clone(), y.clone(), None, false), Formula::Add(_, _)));
        assert!(matches!(binop_to_formula(BinOp::Sub, x.clone(), y.clone(), None, false), Formula::Sub(_, _)));
        assert!(matches!(binop_to_formula(BinOp::Mul, x, y, None, false), Formula::Mul(_, _)));
    }

    #[test]
    fn test_binop_to_formula_comparison() {
        let x = Formula::Var("x".into(), Sort::Int);
        let y = Formula::Var("y".into(), Sort::Int);
        assert!(matches!(binop_to_formula(BinOp::Lt, x.clone(), y.clone(), None, false), Formula::Lt(_, _)));
        assert!(matches!(binop_to_formula(BinOp::Eq, x.clone(), y.clone(), None, false), Formula::Eq(_, _)));
        assert!(matches!(binop_to_formula(BinOp::Ne, x, y, None, false), Formula::Not(_)));
    }

    // tRust #390: Bitwise ops now emit proper bitvector formulas.
    #[test]
    fn test_binop_to_formula_bitwise_emits_bv() {
        let x = Formula::Var("x".into(), Sort::Int);
        let y = Formula::Var("y".into(), Sort::Int);
        let result = binop_to_formula(BinOp::BitAnd, x.clone(), y.clone(), Some(32), false);
        // Should be BvToInt(BvAnd(IntToBv(x, 32), IntToBv(y, 32), 32), 32, false)
        assert!(matches!(result, Formula::BvToInt(_, 32, false)));

        let result = binop_to_formula(BinOp::BitOr, x.clone(), y.clone(), Some(64), false);
        assert!(matches!(result, Formula::BvToInt(_, 64, false)));

        let result = binop_to_formula(BinOp::BitXor, x.clone(), y.clone(), Some(8), false);
        assert!(matches!(result, Formula::BvToInt(_, 8, false)));

        let result = binop_to_formula(BinOp::Shl, x.clone(), y.clone(), Some(32), false);
        assert!(matches!(result, Formula::BvToInt(_, 32, false)));

        // tRust #782: Unsigned Shr uses BvLShr.
        let result = binop_to_formula(BinOp::Shr, x.clone(), y.clone(), Some(32), false);
        assert!(matches!(result, Formula::BvToInt(_, 32, false)));

        // tRust #782: Signed Shr uses BvAShr.
        let result = binop_to_formula(BinOp::Shr, x, y, Some(32), true);
        assert!(matches!(result, Formula::BvToInt(_, 32, false)));
    }

    #[test]
    fn test_binop_to_formula_bitwise_default_width() {
        let x = Formula::Var("x".into(), Sort::Int);
        let y = Formula::Var("y".into(), Sort::Int);
        // When width is None, should default to 64 bits.
        let result = binop_to_formula(BinOp::BitAnd, x, y, None, false);
        assert!(matches!(result, Formula::BvToInt(_, 64, false)));
    }

    #[test]
    fn test_rvalue_to_formula_use() {
        let func = counting_loop_function();
        let rvalue = Rvalue::Use(Operand::Constant(ConstValue::Int(42)));
        let formula = rvalue_to_formula(&func, &rvalue);
        assert!(matches!(formula, Formula::Int(42)));
    }

    #[test]
    fn test_rvalue_to_formula_binary_op() {
        let func = counting_loop_function();
        let rvalue = Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Constant(ConstValue::Int(1)),
            Operand::Constant(ConstValue::Int(2)),
        );
        let formula = rvalue_to_formula(&func, &rvalue);
        assert!(matches!(formula, Formula::Add(_, _)));
    }
}
