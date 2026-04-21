// trust-router/independence.rs: Constraint independence optimization
//
// KLEE-inspired: split a conjunction into independent subproblems by
// analyzing shared variables. Each independent partition can be solved
// separately, often much faster than the monolithic query.
//
// Reference: Cadar, Dunbar, Engler. "KLEE: Unassisted and Automatic Generation
// of High-Coverage Tests for Complex Systems Programs." OSDI 2008, Section 4.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;
use trust_types::fx::{FxHashMap, FxHashSet};

use trust_types::Formula;

/// A partition of conjuncts that share variables.
///
/// Each partition is an independent subproblem: its conjuncts share no
/// variables with conjuncts in other partitions.
#[derive(Debug, Clone)]
pub struct IndependentPartition {
    /// The conjuncts in this partition.
    pub conjuncts: Vec<Formula>,
    /// The variables referenced by this partition.
    pub variables: BTreeSet<String>,
}

/// Result of partitioning a formula.
#[derive(Debug)]
pub struct PartitionResult {
    /// The independent partitions. If the formula was not a conjunction or
    /// could not be split, this contains a single partition with the original
    /// formula.
    pub partitions: Vec<IndependentPartition>,
    /// Whether the formula was actually split (partitions.len() > 1).
    pub was_split: bool,
}

/// Partition a formula into independent subproblems.
///
/// Only top-level And conjuncts are split. Nested Ands are not flattened.
/// Returns a single partition containing the original formula if it cannot
/// be split.
#[must_use]
pub fn partition(formula: &Formula) -> PartitionResult {
    let conjuncts = match formula {
        Formula::And(children) if children.len() > 1 => children.clone(),
        _ => {
            let mut vars = BTreeSet::new();
            collect_free_variables(formula, &mut vars);
            return PartitionResult {
                partitions: vec![IndependentPartition {
                    conjuncts: vec![formula.clone()],
                    variables: vars,
                }],
                was_split: false,
            };
        }
    };

    // Collect variables for each conjunct.
    let conjunct_vars: Vec<BTreeSet<String>> = conjuncts
        .iter()
        .map(|c| {
            let mut vars = BTreeSet::new();
            collect_free_variables(c, &mut vars);
            vars
        })
        .collect();

    // Union-Find to group conjuncts sharing variables.
    let n = conjuncts.len();
    let mut parent: Vec<usize> = (0..n).collect();

    // For each variable, track which conjuncts reference it.
    let mut var_to_conjuncts: FxHashMap<String, Vec<usize>> = FxHashMap::default();
    for (i, vars) in conjunct_vars.iter().enumerate() {
        for var in vars {
            var_to_conjuncts
                .entry(var.clone())
                .or_default()
                .push(i);
        }
    }

    // Union conjuncts that share a variable.
    for indices in var_to_conjuncts.values() {
        if indices.len() > 1 {
            let first = indices[0];
            for &other in &indices[1..] {
                union(&mut parent, first, other);
            }
        }
    }

    // Group conjuncts by their root.
    let mut groups: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
    for i in 0..n {
        let root = find(&mut parent, i);
        groups.entry(root).or_default().push(i);
    }

    let mut partitions: Vec<IndependentPartition> = groups
        .into_values()
        .map(|indices| {
            let mut all_vars = BTreeSet::new();
            let group_conjuncts: Vec<Formula> = indices
                .iter()
                .map(|&i| {
                    all_vars.append(&mut conjunct_vars[i].clone());
                    conjuncts[i].clone()
                })
                .collect();
            IndependentPartition {
                conjuncts: group_conjuncts,
                variables: all_vars,
            }
        })
        .collect();

    // Sort partitions by variable count (smallest first) for faster solving.
    partitions.sort_by_key(|p| p.variables.len());

    let was_split = partitions.len() > 1;
    PartitionResult {
        partitions,
        was_split,
    }
}

/// Reconstruct a formula from partitions.
///
/// If there is only one partition, returns its conjuncts wrapped in And
/// (or the single conjunct if only one). Multiple partitions are wrapped
/// in a top-level And.
#[must_use]
pub fn reconstruct(partitions: &[IndependentPartition]) -> Formula {
    let all_conjuncts: Vec<Formula> = partitions
        .iter()
        .flat_map(|p| p.conjuncts.iter().cloned())
        .collect();

    match all_conjuncts.len() {
        0 => Formula::Bool(true),
        // SAFETY: match arm guarantees len == 1.
        1 => all_conjuncts.into_iter().next()
            .unwrap_or_else(|| unreachable!("empty iter despite len == 1")),
        _ => Formula::And(all_conjuncts),
    }
}

/// Partition a slice of formulas into groups of mutually independent formulas.
///
/// Two formulas are independent if they share no free variables. Transitivity
/// applies: if formula A shares a variable with B, and B shares with C, then
/// A, B, and C are all in the same partition.
///
/// Uses union-find internally. Each returned `Vec<Formula>` is an independent
/// group whose variables are disjoint from all other groups.
///
/// # Examples
///
/// ```
/// # use trust_types::{Formula, Sort};
/// # use trust_router::independence::partition_independent;
/// let f1 = Formula::Gt(
///     Box::new(Formula::Var("x".into(), Sort::Int)),
///     Box::new(Formula::Int(0)),
/// );
/// let f2 = Formula::Lt(
///     Box::new(Formula::Var("y".into(), Sort::Int)),
///     Box::new(Formula::Int(10)),
/// );
/// let groups = partition_independent(&[f1, f2]);
/// assert_eq!(groups.len(), 2); // x and y are independent
/// ```
#[must_use]
pub fn partition_independent(formulas: &[Formula]) -> Vec<Vec<Formula>> {
    if formulas.is_empty() {
        return vec![];
    }
    if formulas.len() == 1 {
        return vec![formulas.to_vec()];
    }

    // Collect free variables for each formula.
    let formula_vars: Vec<FxHashSet<String>> = formulas
        .iter()
        .map(|f| f.free_variables())
        .collect();

    // Union-Find to group formulas sharing variables.
    let n = formulas.len();
    let mut parent: Vec<usize> = (0..n).collect();

    // For each variable, track which formulas reference it.
    let mut var_to_formulas: FxHashMap<String, Vec<usize>> = FxHashMap::default();
    for (i, vars) in formula_vars.iter().enumerate() {
        for var in vars {
            var_to_formulas
                .entry(var.clone())
                .or_default()
                .push(i);
        }
    }

    // Union formulas that share a variable.
    for indices in var_to_formulas.values() {
        if indices.len() > 1 {
            let first = indices[0];
            for &other in &indices[1..] {
                union(&mut parent, first, other);
            }
        }
    }

    // Group formulas by their root.
    let mut groups: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
    for i in 0..n {
        let root = find(&mut parent, i);
        groups.entry(root).or_default().push(i);
    }

    // Build the result, sorted by group size (smallest first) for faster solving.
    let mut result: Vec<Vec<Formula>> = groups
        .into_values()
        .map(|indices| {
            indices
                .into_iter()
                .map(|i| formulas[i].clone())
                .collect()
        })
        .collect();

    result.sort_by_key(|group| group.len());
    result
}

/// Collect free variable names from a formula.
///
/// Delegates to `Formula::free_variables()` and inserts into the provided set.
pub(crate) fn collect_free_variables(formula: &Formula, vars: &mut BTreeSet<String>) {
    vars.extend(formula.free_variables());
}

// Union-Find helpers.

fn find(parent: &mut [usize], mut i: usize) -> usize {
    while parent[i] != i {
        parent[i] = parent[parent[i]]; // path compression
        i = parent[i];
    }
    i
}

fn union(parent: &mut [usize], a: usize, b: usize) {
    let ra = find(parent, a);
    let rb = find(parent, b);
    if ra != rb {
        parent[rb] = ra;
    }
}

#[cfg(test)]
mod tests {
    use trust_types::Sort;

    use super::*;

    #[test]
    fn test_partition_independent_conjuncts() {
        // (x > 0) AND (y < 10) — independent, no shared variables
        let formula = Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Lt(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Int(10)),
            ),
        ]);

        let result = partition(&formula);
        assert!(result.was_split);
        assert_eq!(result.partitions.len(), 2);

        // Check that each partition has exactly one variable
        for p in &result.partitions {
            assert_eq!(p.variables.len(), 1);
            assert_eq!(p.conjuncts.len(), 1);
        }
    }

    #[test]
    fn test_partition_dependent_conjuncts() {
        // (x > 0) AND (x < 10) — share variable x, cannot split
        let formula = Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Lt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(10)),
            ),
        ]);

        let result = partition(&formula);
        assert!(!result.was_split);
        assert_eq!(result.partitions.len(), 1);
        assert_eq!(result.partitions[0].conjuncts.len(), 2);
    }

    #[test]
    fn test_partition_mixed_independence() {
        // (x > 0) AND (y < 10) AND (x < 5) — x-group and y-group
        let formula = Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Lt(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Int(10)),
            ),
            Formula::Lt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(5)),
            ),
        ]);

        let result = partition(&formula);
        assert!(result.was_split);
        assert_eq!(result.partitions.len(), 2);

        // One partition should have {x} with 2 conjuncts, the other {y} with 1
        let x_partition = result
            .partitions
            .iter()
            .find(|p| p.variables.contains("x"))
            .expect("should have x partition");
        assert_eq!(x_partition.conjuncts.len(), 2);

        let y_partition = result
            .partitions
            .iter()
            .find(|p| p.variables.contains("y"))
            .expect("should have y partition");
        assert_eq!(y_partition.conjuncts.len(), 1);
    }

    #[test]
    fn test_partition_non_conjunction() {
        // Single formula, not And — should return one partition
        let formula = Formula::Gt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );

        let result = partition(&formula);
        assert!(!result.was_split);
        assert_eq!(result.partitions.len(), 1);
    }

    #[test]
    fn test_partition_single_conjunct() {
        let formula = Formula::And(vec![Formula::Bool(true)]);

        let result = partition(&formula);
        assert!(!result.was_split);
        assert_eq!(result.partitions.len(), 1);
    }

    #[test]
    fn test_partition_three_independent_groups() {
        // (x > 0) AND (y > 0) AND (z > 0) — three independent groups
        let formula = Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Gt(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Gt(
                Box::new(Formula::Var("z".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        ]);

        let result = partition(&formula);
        assert!(result.was_split);
        assert_eq!(result.partitions.len(), 3);
    }

    #[test]
    fn test_partition_transitive_dependency() {
        // (x > y) AND (y > z) AND (a > 0) — {x,y,z} are transitively connected
        let formula = Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Var("y".into(), Sort::Int)),
            ),
            Formula::Gt(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Var("z".into(), Sort::Int)),
            ),
            Formula::Gt(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        ]);

        let result = partition(&formula);
        assert!(result.was_split);
        assert_eq!(result.partitions.len(), 2);

        let big = result
            .partitions
            .iter()
            .find(|p| p.variables.len() == 3)
            .expect("should have 3-var partition");
        assert!(big.variables.contains("x"));
        assert!(big.variables.contains("y"));
        assert!(big.variables.contains("z"));
        assert_eq!(big.conjuncts.len(), 2);
    }

    #[test]
    fn test_reconstruct_single_partition() {
        let p = vec![IndependentPartition {
            conjuncts: vec![Formula::Bool(true)],
            variables: BTreeSet::new(),
        }];
        let result = reconstruct(&p);
        assert_eq!(result, Formula::Bool(true));
    }

    #[test]
    fn test_reconstruct_multiple_partitions() {
        let p = vec![
            IndependentPartition {
                conjuncts: vec![Formula::Var("x".into(), Sort::Int)],
                variables: ["x".into()].into_iter().collect(),
            },
            IndependentPartition {
                conjuncts: vec![Formula::Var("y".into(), Sort::Int)],
                variables: ["y".into()].into_iter().collect(),
            },
        ];
        let result = reconstruct(&p);
        assert!(matches!(result, Formula::And(ref children) if children.len() == 2));
    }

    #[test]
    fn test_reconstruct_empty() {
        let p: Vec<IndependentPartition> = vec![];
        let result = reconstruct(&p);
        assert_eq!(result, Formula::Bool(true));
    }

    #[test]
    fn test_collect_free_variables_quantifier() {
        // forall x. (x > y) — free variable is y, not x
        let formula = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Var("y".into(), Sort::Int)),
            )),
        );
        let mut vars = BTreeSet::new();
        collect_free_variables(&formula, &mut vars);
        assert!(!vars.contains("x"));
        assert!(vars.contains("y"));
    }

    #[test]
    fn test_sorted_by_variable_count() {
        // Partitions should be sorted smallest-first
        let formula = Formula::And(vec![
            // Group with 2 vars
            Formula::Gt(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Var("b".into(), Sort::Int)),
            ),
            // Group with 1 var
            Formula::Gt(
                Box::new(Formula::Var("z".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        ]);

        let result = partition(&formula);
        assert!(result.was_split);
        assert!(result.partitions[0].variables.len() <= result.partitions[1].variables.len());
    }

    // -----------------------------------------------------------------------
    // partition_independent tests (#441)
    // -----------------------------------------------------------------------

    fn var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    #[test]
    fn test_partition_independent_no_shared_vars_two_partitions() {
        // f1 uses {x}, f2 uses {y} — no shared variables → two partitions.
        let f1 = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)));
        let f2 = Formula::Lt(Box::new(var("y")), Box::new(Formula::Int(10)));

        let groups = partition_independent(&[f1.clone(), f2.clone()]);
        assert_eq!(groups.len(), 2, "disjoint variables should yield two partitions");

        // Each group should contain exactly one formula.
        assert_eq!(groups[0].len(), 1);
        assert_eq!(groups[1].len(), 1);
    }

    #[test]
    fn test_partition_independent_shared_var_one_partition() {
        // Both formulas reference x → one partition.
        let f1 = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)));
        let f2 = Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(10)));

        let groups = partition_independent(&[f1, f2]);
        assert_eq!(groups.len(), 1, "shared variable x should yield one partition");
        assert_eq!(groups[0].len(), 2);
    }

    #[test]
    fn test_partition_independent_transitivity() {
        // f1 uses {a, b}, f2 uses {b, c} → transitivity merges all three.
        // a-b links f1 to f2; b-c links f2 to the c variable.
        // All three formulas share variables transitively → one partition.
        let f1 = Formula::Gt(Box::new(var("a")), Box::new(var("b")));
        let f2 = Formula::Gt(Box::new(var("b")), Box::new(var("c")));

        let groups = partition_independent(&[f1, f2]);
        assert_eq!(
            groups.len(),
            1,
            "transitive variable sharing (a-b, b-c) should yield one partition"
        );
        assert_eq!(groups[0].len(), 2);
    }

    #[test]
    fn test_partition_independent_transitivity_three_formulas() {
        // f1={a,b}, f2={b,c}, f3={d} → two partitions: {f1,f2} and {f3}.
        let f1 = Formula::Gt(Box::new(var("a")), Box::new(var("b")));
        let f2 = Formula::Gt(Box::new(var("b")), Box::new(var("c")));
        let f3 = Formula::Gt(Box::new(var("d")), Box::new(Formula::Int(0)));

        let groups = partition_independent(&[f1, f2, f3]);
        assert_eq!(groups.len(), 2, "a-b-c group and d group → two partitions");

        // The smaller group (d alone) should sort first.
        let d_group = groups.iter().find(|g| g.len() == 1);
        assert!(d_group.is_some());
        let abc_group = groups.iter().find(|g| g.len() == 2);
        assert!(abc_group.is_some());
    }

    #[test]
    fn test_partition_independent_empty_input() {
        let groups = partition_independent(&[]);
        assert!(groups.is_empty());
    }

    #[test]
    fn test_partition_independent_single_formula() {
        let f1 = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)));
        let groups = partition_independent(&[f1]);
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].len(), 1);
    }

    #[test]
    fn test_partition_independent_no_variables() {
        // Formulas with no variables (constants) are trivially independent.
        let f1 = Formula::Bool(true);
        let f2 = Formula::Bool(false);

        let groups = partition_independent(&[f1, f2]);
        // Both formulas share no variables, so they could each be their own group.
        // However, since they both have empty variable sets, the union-find
        // never merges them — they remain separate.
        assert_eq!(groups.len(), 2);
    }

    #[test]
    fn test_partition_independent_all_share_one_variable() {
        // All three formulas share x → one partition.
        let f1 = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)));
        let f2 = Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(10)));
        let f3 = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(5)));

        let groups = partition_independent(&[f1, f2, f3]);
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].len(), 3);
    }
}
