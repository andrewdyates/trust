// trust-vcgen/ssa_transform.rs: SSA (Static Single Assignment) form transformation
//
// Transforms sequences of MIR-level assignments into SSA form where each
// variable is assigned exactly once. This simplifies reasoning about
// assignments in verification condition generation because:
// - No need for substitution chains
// - Each definition has a unique name (base_v0, base_v1, ...)
// - Phi nodes explicitly represent merge points in control flow
//
// Reference: Cytron et al., "Efficiently Computing Static Single Assignment
// Form and the Control Dependence Graph", TOPLAS 1991.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use trust_types::{BlockId, Formula, Sort};

// ---------------------------------------------------------------------------
// Core SSA types
// ---------------------------------------------------------------------------

/// An SSA variable: a base name with a version number.
///
/// In SSA form, each assignment to variable `x` produces a new version:
/// `x_v0`, `x_v1`, `x_v2`, etc.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SsaVariable {
    /// The original variable name (e.g., "x", "a").
    pub base: String,
    /// The SSA version number. Version 0 is the initial (parameter) version.
    pub version: u32,
}

impl SsaVariable {
    /// Create a new SSA variable with the given base name and version.
    #[must_use]
    pub fn new(base: impl Into<String>, version: u32) -> Self {
        Self { base: base.into(), version }
    }

    /// Return the SSA-qualified name: `{base}_v{version}`.
    #[must_use]
    pub fn ssa_name(&self) -> String {
        format!("{}_v{}", self.base, self.version)
    }
}

/// A phi node at a control flow merge point.
///
/// `result = phi(operands)` means `result` takes the value of whichever
/// operand corresponds to the incoming control flow edge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PhiNode {
    /// The result variable (the newly defined SSA variable).
    pub result: SsaVariable,
    /// The operands from each incoming block.
    pub operands: Vec<(BlockId, SsaVariable)>,
    /// The SMT sort of this variable.
    pub sort: Sort,
}

/// A single SSA statement: either an assignment or a phi node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SsaStatement {
    /// An assignment: `result = rhs_formula` where variables in rhs_formula
    /// have already been renamed to their SSA versions.
    Assign {
        result: SsaVariable,
        rhs: Formula,
        sort: Sort,
    },
    /// A phi node at a merge point.
    Phi(PhiNode),
}

// ---------------------------------------------------------------------------
// SsaContext: tracks versioning state during SSA construction
// ---------------------------------------------------------------------------

/// Context for SSA transformation, tracking current variable versions.
#[derive(Debug, Clone)]
pub struct SsaContext {
    /// Current version for each base variable name.
    current_versions: FxHashMap<String, u32>,
    /// All definitions: maps SSA variable to the sort.
    definitions: FxHashMap<SsaVariable, Sort>,
    /// The SSA statements produced so far.
    pub(crate) statements: Vec<SsaStatement>,
}

impl SsaContext {
    /// Create a new SSA context.
    #[must_use]
    pub fn new() -> Self {
        Self {
            current_versions: FxHashMap::default(),
            definitions: FxHashMap::default(),
            statements: Vec::new(),
        }
    }

    /// Get the current version of a variable, or 0 if not yet defined.
    #[must_use]
    pub fn current_version(&self, base: &str) -> u32 {
        self.current_versions.get(base).copied().unwrap_or(0)
    }

    /// Get the current SSA variable for a base name.
    #[must_use]
    pub fn current_var(&self, base: &str) -> SsaVariable {
        SsaVariable::new(base, self.current_version(base))
    }

    /// Allocate a fresh version for the given base variable, returning the
    /// new SSA variable.
    pub fn fresh_version(&mut self, base: &str, sort: Sort) -> SsaVariable {
        let next = self.current_version(base) + 1;
        self.current_versions.insert(base.to_string(), next);
        let var = SsaVariable::new(base, next);
        self.definitions.insert(var.clone(), sort);
        var
    }

    /// Register an initial (parameter) variable at version 0.
    pub fn register_initial(&mut self, base: &str, sort: Sort) {
        self.current_versions.entry(base.to_string()).or_insert(0);
        let var = SsaVariable::new(base, 0);
        self.definitions.insert(var, sort);
    }

    /// Get all defined SSA variables and their sorts.
    #[must_use]
    pub fn all_definitions(&self) -> &FxHashMap<SsaVariable, Sort> {
        &self.definitions
    }

    /// Get the current version map (base name -> version number).
    #[must_use]
    pub fn version_map(&self) -> &FxHashMap<String, u32> {
        &self.current_versions
    }

    /// Snapshot the current version state (for use before a branch).
    #[must_use]
    pub fn snapshot(&self) -> FxHashMap<String, u32> {
        self.current_versions.clone()
    }

    /// Restore version state from a snapshot.
    pub fn restore(&mut self, snapshot: FxHashMap<String, u32>) {
        self.current_versions = snapshot;
    }
}

impl Default for SsaContext {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// SSA transformation functions
// ---------------------------------------------------------------------------

/// A simple assignment representation for SSA input.
///
/// Represents `target = rhs` where rhs is a formula that may reference
/// variables by their base names.
#[derive(Debug, Clone)]
pub struct SimpleAssign {
    /// The target variable base name.
    pub target: String,
    /// The right-hand side formula (using base variable names).
    pub rhs: Formula,
    /// The sort of the target variable.
    pub sort: Sort,
}

/// Transform a sequence of assignments into SSA form.
///
/// Each assignment `x = expr` is transformed so that:
/// 1. Variable references in `expr` use the current SSA version
/// 2. The target `x` gets a fresh SSA version
///
/// Returns the list of SSA statements and the final context.
#[must_use]
pub fn to_ssa(
    params: &[(&str, Sort)],
    assignments: &[SimpleAssign],
) -> (Vec<SsaStatement>, SsaContext) {
    let mut ctx = SsaContext::new();

    // Register parameters at version 0
    for &(name, ref sort) in params {
        ctx.register_initial(name, sort.clone());
    }

    // Process each assignment
    for assign in assignments {
        // Rename variables in the RHS to their current SSA versions
        let renamed_rhs = rename_variables(&assign.rhs, &ctx);

        // Allocate a fresh version for the target
        let result = ctx.fresh_version(&assign.target, assign.sort.clone());

        let stmt = SsaStatement::Assign {
            result,
            rhs: renamed_rhs,
            sort: assign.sort.clone(),
        };
        ctx.statements.push(stmt.clone());
    }

    let stmts = ctx.statements.clone();
    (stmts, ctx)
}

/// Rename all variable references in a formula to their current SSA versions.
///
/// Traverses the formula tree and replaces each `Var(name, sort)` with
/// `Var(name_vN, sort)` where N is the current version of `name` in the
/// context.
#[must_use]
pub fn rename_variables(formula: &Formula, ctx: &SsaContext) -> Formula {
    match formula {
        Formula::Var(name, sort) => {
            let ver = ctx.current_version(name);
            let ssa_name = format!("{name}_v{ver}");
            Formula::Var(ssa_name, sort.clone())
        }
        Formula::Not(inner) => {
            Formula::Not(Box::new(rename_variables(inner, ctx)))
        }
        Formula::And(children) => {
            Formula::And(children.iter().map(|c| rename_variables(c, ctx)).collect())
        }
        Formula::Or(children) => {
            Formula::Or(children.iter().map(|c| rename_variables(c, ctx)).collect())
        }
        Formula::Implies(lhs, rhs) => Formula::Implies(
            Box::new(rename_variables(lhs, ctx)),
            Box::new(rename_variables(rhs, ctx)),
        ),
        Formula::Eq(lhs, rhs) => Formula::Eq(
            Box::new(rename_variables(lhs, ctx)),
            Box::new(rename_variables(rhs, ctx)),
        ),
        Formula::Lt(lhs, rhs) => Formula::Lt(
            Box::new(rename_variables(lhs, ctx)),
            Box::new(rename_variables(rhs, ctx)),
        ),
        Formula::Le(lhs, rhs) => Formula::Le(
            Box::new(rename_variables(lhs, ctx)),
            Box::new(rename_variables(rhs, ctx)),
        ),
        Formula::Gt(lhs, rhs) => Formula::Gt(
            Box::new(rename_variables(lhs, ctx)),
            Box::new(rename_variables(rhs, ctx)),
        ),
        Formula::Ge(lhs, rhs) => Formula::Ge(
            Box::new(rename_variables(lhs, ctx)),
            Box::new(rename_variables(rhs, ctx)),
        ),
        Formula::Add(lhs, rhs) => Formula::Add(
            Box::new(rename_variables(lhs, ctx)),
            Box::new(rename_variables(rhs, ctx)),
        ),
        Formula::Sub(lhs, rhs) => Formula::Sub(
            Box::new(rename_variables(lhs, ctx)),
            Box::new(rename_variables(rhs, ctx)),
        ),
        Formula::Mul(lhs, rhs) => Formula::Mul(
            Box::new(rename_variables(lhs, ctx)),
            Box::new(rename_variables(rhs, ctx)),
        ),
        Formula::Div(lhs, rhs) => Formula::Div(
            Box::new(rename_variables(lhs, ctx)),
            Box::new(rename_variables(rhs, ctx)),
        ),
        Formula::Rem(lhs, rhs) => Formula::Rem(
            Box::new(rename_variables(lhs, ctx)),
            Box::new(rename_variables(rhs, ctx)),
        ),
        Formula::Neg(inner) => {
            Formula::Neg(Box::new(rename_variables(inner, ctx)))
        }
        // Literals pass through unchanged
        Formula::Bool(_)
        | Formula::Int(_)
        | Formula::UInt(_)
        | Formula::BitVec { .. } => formula.clone(),
        // For any other formula variant, use children() for traversal.
        // Since we cannot reconstruct arbitrary variants generically,
        // we clone them as-is. This is conservative: bitvector ops and
        // quantifiers keep their original variable names.
        _other => formula.clone(),
    }
}

/// Insert phi nodes at control flow join points.
///
/// Given two branch contexts (e.g., from if-then-else), inserts phi nodes
/// for any variable that was defined differently in each branch.
///
/// Returns the phi nodes and updates the context to reflect the merged state.
pub fn insert_phi_nodes(
    ctx: &mut SsaContext,
    then_versions: &FxHashMap<String, u32>,
    else_versions: &FxHashMap<String, u32>,
    then_block: BlockId,
    else_block: BlockId,
) -> Vec<PhiNode> {
    let mut phis = Vec::new();

    // Collect all variable names from both branches
    let all_vars: FxHashSet<&String> = then_versions.keys().chain(else_versions.keys()).collect();

    for base in all_vars {
        let then_ver = then_versions.get(base).copied().unwrap_or(0);
        let else_ver = else_versions.get(base).copied().unwrap_or(0);

        // Only insert a phi node if the versions differ
        if then_ver != else_ver {
            let sort = ctx
                .all_definitions()
                .iter()
                .find(|(k, _)| k.base == *base)
                .map(|(_, s)| s.clone())
                .unwrap_or(Sort::Int);

            let result = ctx.fresh_version(base, sort.clone());

            let phi = PhiNode {
                result,
                operands: vec![
                    (then_block, SsaVariable::new(base.clone(), then_ver)),
                    (else_block, SsaVariable::new(base.clone(), else_ver)),
                ],
                sort,
            };
            phis.push(phi.clone());
            ctx.statements.push(SsaStatement::Phi(phi));
        }
    }

    phis
}

/// Convert SSA form back to non-SSA by generating equalities for phi nodes
/// and substituting versioned names back to base names in the final version.
///
/// Returns a list of formulas representing the constraints:
/// - For assignments: `result_ssa_name = renamed_rhs`
/// - For phi nodes: `result_ssa_name = ite(from_block == then_block, then_var, else_var)`
///   (simplified to equality constraints)
#[must_use]
pub fn from_ssa(statements: &[SsaStatement]) -> Vec<Formula> {
    let mut constraints = Vec::new();

    for stmt in statements {
        match stmt {
            SsaStatement::Assign { result, rhs, sort } => {
                let lhs = Formula::Var(result.ssa_name(), sort.clone());
                constraints.push(Formula::Eq(Box::new(lhs), Box::new(rhs.clone())));
            }
            SsaStatement::Phi(phi) => {
                // Each phi operand implies an equality.
                // phi(x_v1 from bb0, x_v2 from bb1) = x_v3
                // Encode as: (x_v3 = x_v1) \/ (x_v3 = x_v2)
                let lhs = Formula::Var(phi.result.ssa_name(), phi.sort.clone());
                let options: Vec<Formula> = phi
                    .operands
                    .iter()
                    .map(|(_, var)| {
                        Formula::Eq(
                            Box::new(lhs.clone()),
                            Box::new(Formula::Var(var.ssa_name(), phi.sort.clone())),
                        )
                    })
                    .collect();
                if options.len() == 1 {
                    // SAFETY: len == 1 guarantees .next() returns Some.
                    constraints.push(options.into_iter().next()
                        .unwrap_or_else(|| unreachable!("empty iter despite len == 1")));
                } else {
                    constraints.push(Formula::Or(options));
                }
            }
        }
    }

    constraints
}

/// Recover a map from SSA variable names back to their base names.
///
/// Useful for translating counterexamples back from SSA form.
#[must_use]
pub fn ssa_to_base_map(ctx: &SsaContext) -> FxHashMap<String, String> {
    ctx.all_definitions()
        .keys()
        .map(|var| (var.ssa_name(), var.base.clone()))
        .collect()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ssa_variable_new_and_name() {
        let v = SsaVariable::new("x", 0);
        assert_eq!(v.base, "x");
        assert_eq!(v.version, 0);
        assert_eq!(v.ssa_name(), "x_v0");

        let v3 = SsaVariable::new("y", 3);
        assert_eq!(v3.ssa_name(), "y_v3");
    }

    #[test]
    fn test_ssa_context_fresh_version() {
        let mut ctx = SsaContext::new();
        ctx.register_initial("x", Sort::Int);

        assert_eq!(ctx.current_version("x"), 0);

        let v1 = ctx.fresh_version("x", Sort::Int);
        assert_eq!(v1.version, 1);
        assert_eq!(ctx.current_version("x"), 1);

        let v2 = ctx.fresh_version("x", Sort::Int);
        assert_eq!(v2.version, 2);
        assert_eq!(ctx.current_version("x"), 2);
    }

    #[test]
    fn test_ssa_context_snapshot_restore() {
        let mut ctx = SsaContext::new();
        ctx.register_initial("x", Sort::Int);
        ctx.fresh_version("x", Sort::Int); // x_v1

        let snap = ctx.snapshot();
        assert_eq!(ctx.current_version("x"), 1);

        ctx.fresh_version("x", Sort::Int); // x_v2
        assert_eq!(ctx.current_version("x"), 2);

        ctx.restore(snap);
        assert_eq!(ctx.current_version("x"), 1);
    }

    #[test]
    fn test_to_ssa_simple_sequence() {
        // x = x + 1; x = x * 2
        let params = vec![("x", Sort::Int)];
        let assignments = vec![
            SimpleAssign {
                target: "x".to_string(),
                rhs: Formula::Add(
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                    Box::new(Formula::Int(1)),
                ),
                sort: Sort::Int,
            },
            SimpleAssign {
                target: "x".to_string(),
                rhs: Formula::Mul(
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                    Box::new(Formula::Int(2)),
                ),
                sort: Sort::Int,
            },
        ];

        let (stmts, ctx) = to_ssa(&params, &assignments);
        assert_eq!(stmts.len(), 2);

        // First: x_v1 = x_v0 + 1
        match &stmts[0] {
            SsaStatement::Assign { result, rhs, .. } => {
                assert_eq!(result.ssa_name(), "x_v1");
                match rhs {
                    Formula::Add(lhs, rhs_inner) => {
                        assert!(matches!(lhs.as_ref(), Formula::Var(n, _) if n == "x_v0"));
                        assert!(matches!(rhs_inner.as_ref(), Formula::Int(1)));
                    }
                    other => panic!("expected Add, got {other:?}"),
                }
            }
            other => panic!("expected Assign, got {other:?}"),
        }

        // Second: x_v2 = x_v1 * 2
        match &stmts[1] {
            SsaStatement::Assign { result, rhs, .. } => {
                assert_eq!(result.ssa_name(), "x_v2");
                match rhs {
                    Formula::Mul(lhs, _) => {
                        assert!(matches!(lhs.as_ref(), Formula::Var(n, _) if n == "x_v1"));
                    }
                    other => panic!("expected Mul, got {other:?}"),
                }
            }
            other => panic!("expected Assign, got {other:?}"),
        }

        assert_eq!(ctx.current_version("x"), 2);
    }

    #[test]
    fn test_to_ssa_multiple_variables() {
        // a = b + c; b = a - 1
        let params = vec![("a", Sort::Int), ("b", Sort::Int), ("c", Sort::Int)];
        let assignments = vec![
            SimpleAssign {
                target: "a".to_string(),
                rhs: Formula::Add(
                    Box::new(Formula::Var("b".to_string(), Sort::Int)),
                    Box::new(Formula::Var("c".to_string(), Sort::Int)),
                ),
                sort: Sort::Int,
            },
            SimpleAssign {
                target: "b".to_string(),
                rhs: Formula::Sub(
                    Box::new(Formula::Var("a".to_string(), Sort::Int)),
                    Box::new(Formula::Int(1)),
                ),
                sort: Sort::Int,
            },
        ];

        let (stmts, ctx) = to_ssa(&params, &assignments);
        assert_eq!(stmts.len(), 2);

        // a_v1 = b_v0 + c_v0
        match &stmts[0] {
            SsaStatement::Assign { result, rhs, .. } => {
                assert_eq!(result.ssa_name(), "a_v1");
                match rhs {
                    Formula::Add(lhs, rhs_inner) => {
                        assert!(matches!(lhs.as_ref(), Formula::Var(n, _) if n == "b_v0"));
                        assert!(matches!(rhs_inner.as_ref(), Formula::Var(n, _) if n == "c_v0"));
                    }
                    other => panic!("expected Add, got {other:?}"),
                }
            }
            other => panic!("expected Assign, got {other:?}"),
        }

        // b_v1 = a_v1 - 1  (uses the newly defined a_v1)
        match &stmts[1] {
            SsaStatement::Assign { result, rhs, .. } => {
                assert_eq!(result.ssa_name(), "b_v1");
                match rhs {
                    Formula::Sub(lhs, _) => {
                        assert!(matches!(lhs.as_ref(), Formula::Var(n, _) if n == "a_v1"));
                    }
                    other => panic!("expected Sub, got {other:?}"),
                }
            }
            other => panic!("expected Assign, got {other:?}"),
        }

        assert_eq!(ctx.current_version("a"), 1);
        assert_eq!(ctx.current_version("b"), 1);
        assert_eq!(ctx.current_version("c"), 0);
    }

    #[test]
    fn test_rename_variables_preserves_literals() {
        let ctx = SsaContext::new();
        let f = Formula::Int(42);
        assert_eq!(rename_variables(&f, &ctx), Formula::Int(42));

        let f = Formula::Bool(true);
        assert_eq!(rename_variables(&f, &ctx), Formula::Bool(true));
    }

    #[test]
    fn test_rename_variables_renames_vars() {
        let mut ctx = SsaContext::new();
        ctx.register_initial("x", Sort::Int);
        ctx.fresh_version("x", Sort::Int); // now x -> v1

        let f = Formula::Var("x".to_string(), Sort::Int);
        let renamed = rename_variables(&f, &ctx);
        assert!(matches!(&renamed, Formula::Var(name, _) if name == "x_v1"));
    }

    #[test]
    fn test_rename_variables_nested_formula() {
        let mut ctx = SsaContext::new();
        ctx.register_initial("a", Sort::Int);
        ctx.register_initial("b", Sort::Bool);

        let f = Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("a".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Var("b".to_string(), Sort::Bool),
        ]);

        let renamed = rename_variables(&f, &ctx);
        match &renamed {
            Formula::And(children) => {
                assert_eq!(children.len(), 2);
                match &children[0] {
                    Formula::Gt(lhs, _) => {
                        assert!(matches!(lhs.as_ref(), Formula::Var(n, _) if n == "a_v0"));
                    }
                    other => panic!("expected Gt, got {other:?}"),
                }
                assert!(matches!(&children[1], Formula::Var(n, _) if n == "b_v0"));
            }
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn test_insert_phi_nodes_different_versions() {
        let mut ctx = SsaContext::new();
        ctx.register_initial("x", Sort::Int);
        ctx.register_initial("y", Sort::Int);

        // then-branch: x -> v1, y -> v0
        let mut then_versions = FxHashMap::default();
        then_versions.insert("x".to_string(), 1u32);
        then_versions.insert("y".to_string(), 0u32);

        // else-branch: x -> v2, y -> v0
        let mut else_versions = FxHashMap::default();
        else_versions.insert("x".to_string(), 2u32);
        else_versions.insert("y".to_string(), 0u32);

        // Register definitions so they exist
        ctx.fresh_version("x", Sort::Int); // x_v1
        ctx.fresh_version("x", Sort::Int); // x_v2

        let phis = insert_phi_nodes(
            &mut ctx,
            &then_versions,
            &else_versions,
            BlockId(1),
            BlockId(2),
        );

        // Only x should get a phi node (y has same version in both)
        assert_eq!(phis.len(), 1);
        assert_eq!(phis[0].result.base, "x");
        assert_eq!(phis[0].operands.len(), 2);
        assert_eq!(phis[0].operands[0].0, BlockId(1));
        assert_eq!(phis[0].operands[0].1.version, 1);
        assert_eq!(phis[0].operands[1].0, BlockId(2));
        assert_eq!(phis[0].operands[1].1.version, 2);
    }

    #[test]
    fn test_insert_phi_nodes_same_versions_no_phi() {
        let mut ctx = SsaContext::new();
        ctx.register_initial("x", Sort::Int);

        let mut then_versions = FxHashMap::default();
        then_versions.insert("x".to_string(), 0u32);

        let mut else_versions = FxHashMap::default();
        else_versions.insert("x".to_string(), 0u32);

        let phis = insert_phi_nodes(
            &mut ctx,
            &then_versions,
            &else_versions,
            BlockId(1),
            BlockId(2),
        );

        assert!(phis.is_empty(), "same versions should produce no phi nodes");
    }

    #[test]
    fn test_from_ssa_assignments() {
        let stmts = vec![
            SsaStatement::Assign {
                result: SsaVariable::new("x", 1),
                rhs: Formula::Add(
                    Box::new(Formula::Var("x_v0".to_string(), Sort::Int)),
                    Box::new(Formula::Int(1)),
                ),
                sort: Sort::Int,
            },
        ];

        let constraints = from_ssa(&stmts);
        assert_eq!(constraints.len(), 1);

        match &constraints[0] {
            Formula::Eq(lhs, rhs) => {
                assert!(matches!(lhs.as_ref(), Formula::Var(n, _) if n == "x_v1"));
                assert!(matches!(rhs.as_ref(), Formula::Add(..)));
            }
            other => panic!("expected Eq, got {other:?}"),
        }
    }

    #[test]
    fn test_from_ssa_phi_nodes() {
        let stmts = vec![SsaStatement::Phi(PhiNode {
            result: SsaVariable::new("x", 3),
            operands: vec![
                (BlockId(1), SsaVariable::new("x", 1)),
                (BlockId(2), SsaVariable::new("x", 2)),
            ],
            sort: Sort::Int,
        })];

        let constraints = from_ssa(&stmts);
        assert_eq!(constraints.len(), 1);

        match &constraints[0] {
            Formula::Or(options) => {
                assert_eq!(options.len(), 2);
                // x_v3 = x_v1
                match &options[0] {
                    Formula::Eq(lhs, rhs) => {
                        assert!(matches!(lhs.as_ref(), Formula::Var(n, _) if n == "x_v3"));
                        assert!(matches!(rhs.as_ref(), Formula::Var(n, _) if n == "x_v1"));
                    }
                    other => panic!("expected Eq, got {other:?}"),
                }
                // x_v3 = x_v2
                match &options[1] {
                    Formula::Eq(lhs, rhs) => {
                        assert!(matches!(lhs.as_ref(), Formula::Var(n, _) if n == "x_v3"));
                        assert!(matches!(rhs.as_ref(), Formula::Var(n, _) if n == "x_v2"));
                    }
                    other => panic!("expected Eq, got {other:?}"),
                }
            }
            other => panic!("expected Or, got {other:?}"),
        }
    }

    #[test]
    fn test_ssa_to_base_map() {
        let mut ctx = SsaContext::new();
        ctx.register_initial("x", Sort::Int);
        ctx.register_initial("y", Sort::Bool);
        ctx.fresh_version("x", Sort::Int);

        let map = ssa_to_base_map(&ctx);
        assert_eq!(map.get("x_v0"), Some(&"x".to_string()));
        assert_eq!(map.get("x_v1"), Some(&"x".to_string()));
        assert_eq!(map.get("y_v0"), Some(&"y".to_string()));
    }

    #[test]
    fn test_to_ssa_empty_input() {
        let params: Vec<(&str, Sort)> = vec![("x", Sort::Int)];
        let assignments: Vec<SimpleAssign> = vec![];

        let (stmts, ctx) = to_ssa(&params, &assignments);
        assert!(stmts.is_empty());
        assert_eq!(ctx.current_version("x"), 0);
    }

    #[test]
    fn test_round_trip_ssa_and_back() {
        // x = x + y; y = x - 1
        let params = vec![("x", Sort::Int), ("y", Sort::Int)];
        let assignments = vec![
            SimpleAssign {
                target: "x".to_string(),
                rhs: Formula::Add(
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                    Box::new(Formula::Var("y".to_string(), Sort::Int)),
                ),
                sort: Sort::Int,
            },
            SimpleAssign {
                target: "y".to_string(),
                rhs: Formula::Sub(
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                    Box::new(Formula::Int(1)),
                ),
                sort: Sort::Int,
            },
        ];

        let (stmts, _ctx) = to_ssa(&params, &assignments);
        assert_eq!(stmts.len(), 2);

        // Convert back: should produce 2 equality constraints
        let constraints = from_ssa(&stmts);
        assert_eq!(constraints.len(), 2);

        // All constraints should be equalities
        for c in &constraints {
            assert!(matches!(c, Formula::Eq(..)), "expected Eq constraint");
        }
    }

    #[test]
    fn test_phi_node_struct_fields() {
        let phi = PhiNode {
            result: SsaVariable::new("x", 5),
            operands: vec![
                (BlockId(0), SsaVariable::new("x", 3)),
                (BlockId(1), SsaVariable::new("x", 4)),
                (BlockId(2), SsaVariable::new("x", 2)),
            ],
            sort: Sort::Bool,
        };

        assert_eq!(phi.result.ssa_name(), "x_v5");
        assert_eq!(phi.operands.len(), 3);
        assert_eq!(phi.sort, Sort::Bool);
    }

    #[test]
    fn test_context_current_var_unregistered_defaults_v0() {
        let ctx = SsaContext::new();
        let var = ctx.current_var("unknown");
        assert_eq!(var.base, "unknown");
        assert_eq!(var.version, 0);
        assert_eq!(var.ssa_name(), "unknown_v0");
    }
}
