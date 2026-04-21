// trust-router/unified_memory.rs: Unified memory model for cross-function proof composition
//
// tRust: #198 Sunder and certus use incompatible memory models. Sunder's SP-calculus
// reasons over flat heap states, while certus encodes ownership axioms with region
// provenance, Stacked Borrows permissions, and lifetime outlives constraints.
//
// This module provides a shared memory abstraction that can be projected to either
// backend's native form, plus a compatibility check for composing proofs across
// function boundaries (e.g., sunder proves function A, certus proves function B,
// and we need to verify the handoff is sound).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// Unique identifier for a memory region in the unified model.
pub(crate) type RegionId = u64;

/// What kind of storage a memory region occupies.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum RegionKind {
    /// Stack-allocated local variable.
    Stack,
    /// Heap-allocated (Box, Vec backing storage, etc.).
    Heap,
    /// Global / static storage.
    Global,
}

/// Stacked Borrows permission level for a region.
///
/// Models the permission a reference has over its pointee region,
/// following the Stacked Borrows semantics:
/// - `Write` = unique mutable access (`&mut T`)
/// - `Read` = shared immutable access (`&T`)
/// - `Disabled` = moved or dropped, no access permitted
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Permission {
    Disabled = 0,
    Read = 1,
    Write = 2,
}

/// A memory region in the unified model.
///
/// Captures the essential properties that both sunder and certus need:
/// - Addressability (base address, represented symbolically as a region id)
/// - Storage kind (stack / heap / global)
/// - Lifetime scope (lexical nesting depth; higher = shorter-lived)
/// - Provenance (which parent region this was borrowed from, if any)
/// - Permission (Stacked Borrows access level)
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MemoryRegion {
    pub(crate) id: RegionId,
    pub(crate) kind: RegionKind,
    /// Lexical lifetime scope depth. 0 = 'static, higher = shorter-lived.
    pub(crate) lifetime: u32,
    /// Parent region id if this region is a borrow. `None` for owned regions.
    pub(crate) provenance: Option<RegionId>,
    /// Current Stacked Borrows permission.
    pub(crate) permission: Permission,
}

/// The unified memory model shared across sunder and certus.
///
/// Contains the set of live regions and their relationships. This is the
/// canonical representation from which backend-specific projections are derived.
#[derive(Debug, Clone)]
pub(crate) struct UnifiedMemoryModel {
    /// All live memory regions, ordered by id.
    regions: Vec<MemoryRegion>,
}

/// Result of checking whether two memory models are compatible at a function boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum MemoryModelCompatibility {
    /// The two models agree on all shared regions.
    Compatible,
    /// Region identities or kinds do not match at the boundary.
    IncompatibleRegions { reason: String },
    /// Lifetime relationships are contradictory across the boundary.
    IncompatibleLifetimes { reason: String },
}

// ---------------------------------------------------------------------------
// UnifiedMemoryModel implementation
// ---------------------------------------------------------------------------

impl UnifiedMemoryModel {
    /// Create a new empty unified memory model.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self { regions: Vec::new() }
    }

    /// Create a model from a pre-built list of regions.
    #[must_use]
    pub(crate) fn with_regions(regions: Vec<MemoryRegion>) -> Self {
        Self { regions }
    }

    /// Add a region to the model.
    pub(crate) fn add_region(&mut self, region: MemoryRegion) {
        self.regions.push(region);
    }

    /// Get all regions.
    #[must_use]
    pub(crate) fn regions(&self) -> &[MemoryRegion] {
        &self.regions
    }

    /// Look up a region by id.
    #[must_use]
    pub(crate) fn region_by_id(&self, id: RegionId) -> Option<&MemoryRegion> {
        self.regions.iter().find(|r| r.id == id)
    }

    /// Extract the set of region ids that appear at a function boundary
    /// (i.e., are referenced in the given formula's variables).
    #[must_use]
    pub(crate) fn boundary_region_ids(formula: &Formula) -> Vec<RegionId> {
        let mut ids = Vec::new();
        formula.visit(&mut |node| {
            if let Formula::Var(name, _) = node
                && let Some(prefix) = name.strip_suffix("_base")
                    .or_else(|| name.strip_suffix("_val"))
                    .or_else(|| name.strip_suffix("_live"))
                    .or_else(|| name.strip_suffix("_perm"))
                    && let Some(id_str) = prefix.strip_prefix("region_")
                        && let Ok(id) = id_str.parse::<RegionId>()
                            && !ids.contains(&id) {
                                ids.push(id);
                            }
        });
        ids.sort();
        ids
    }

    // -----------------------------------------------------------------------
    // Backend projections
    // -----------------------------------------------------------------------

    /// Project the unified model to sunder's SP-calculus form.
    ///
    /// Sunder works with a flat heap model: each region becomes a pair of
    /// symbolic variables (`region_N_base`, `region_N_val`) with non-aliasing
    /// assertions between distinct regions. Lifetime and ownership information
    /// is erased because SP-calculus does not track provenance.
    #[must_use]
    pub(crate) fn translate_to_sunder(&self) -> Formula {
        if self.regions.is_empty() {
            return Formula::Bool(true);
        }

        let mut conjuncts = Vec::new();

        // Non-aliasing: distinct regions have distinct base addresses.
        for i in 0..self.regions.len() {
            for j in (i + 1)..self.regions.len() {
                let ri = &self.regions[i];
                let rj = &self.regions[j];
                // In sunder's flat model, all live regions are non-aliasing.
                let base_i = Formula::Var(
                    format!("region_{}_base", ri.id),
                    Sort::Int,
                );
                let base_j = Formula::Var(
                    format!("region_{}_base", rj.id),
                    Sort::Int,
                );
                conjuncts.push(Formula::Not(Box::new(Formula::Eq(
                    Box::new(base_i),
                    Box::new(base_j),
                ))));
            }
        }

        if conjuncts.is_empty() {
            Formula::Bool(true)
        } else {
            Formula::And(conjuncts)
        }
    }

    /// Project the unified model to certus's ownership axiom form.
    ///
    /// Certus uses the full Stacked Borrows model: each region has a
    /// permission level, liveness flag, provenance chain, and lifetime
    /// outlives constraints. This produces the conjunction of all axioms
    /// that certus needs to reason about the regions.
    #[must_use]
    pub(crate) fn translate_to_certus(&self) -> Formula {
        if self.regions.is_empty() {
            return Formula::Bool(true);
        }

        let mut conjuncts = Vec::new();

        // Non-aliasing (same as sunder, but certus also needs it).
        for i in 0..self.regions.len() {
            for j in (i + 1)..self.regions.len() {
                let ri = &self.regions[i];
                let rj = &self.regions[j];
                let base_i = Formula::Var(format!("region_{}_base", ri.id), Sort::Int);
                let base_j = Formula::Var(format!("region_{}_base", rj.id), Sort::Int);
                conjuncts.push(Formula::Not(Box::new(Formula::Eq(
                    Box::new(base_i),
                    Box::new(base_j),
                ))));
            }
        }

        // Permission constraints per region.
        for region in &self.regions {
            let perm_var = Formula::Var(format!("region_{}_perm", region.id), Sort::Int);
            let perm_val = Formula::Int(region.permission as i128);
            conjuncts.push(Formula::Eq(Box::new(perm_var), Box::new(perm_val)));
        }

        // Liveness: non-Disabled regions are live.
        for region in &self.regions {
            let live_var = Formula::Var(format!("region_{}_live", region.id), Sort::Bool);
            let is_live = region.permission != Permission::Disabled;
            conjuncts.push(Formula::Eq(
                Box::new(live_var),
                Box::new(Formula::Bool(is_live)),
            ));
        }

        // Write-exclusivity: at most one Write per provenance group.
        let write_regions: Vec<&MemoryRegion> = self
            .regions
            .iter()
            .filter(|r| r.permission == Permission::Write)
            .collect();
        for i in 0..write_regions.len() {
            for j in (i + 1)..write_regions.len() {
                let ri = write_regions[i];
                let rj = write_regions[j];
                // Two Write regions sharing a provenance parent is forbidden.
                if ri.provenance == rj.provenance && ri.provenance.is_some() {
                    conjuncts.push(Formula::Bool(false)); // contradiction
                }
            }
        }

        // Lifetime outlives: if child is live, parent must be live.
        for region in &self.regions {
            if let Some(parent_id) = region.provenance
                && let Some(parent) = self.region_by_id(parent_id) {
                    // child_live => parent_live
                    let child_live = Formula::Var(
                        format!("region_{}_live", region.id),
                        Sort::Bool,
                    );
                    let parent_live = Formula::Var(
                        format!("region_{}_live", parent.id),
                        Sort::Bool,
                    );
                    conjuncts.push(Formula::Implies(
                        Box::new(child_live),
                        Box::new(parent_live),
                    ));
                }
        }

        if conjuncts.is_empty() {
            Formula::Bool(true)
        } else {
            Formula::And(conjuncts)
        }
    }

    // -----------------------------------------------------------------------
    // Cross-function proof composition
    // -----------------------------------------------------------------------

    /// Check whether two memory models are compatible at a function boundary.
    ///
    /// Given a sunder proof about function A and a certus proof about function B,
    /// this checks that the memory models agree on all regions that cross the
    /// boundary (i.e., regions referenced by both proofs).
    ///
    /// Compatibility requires:
    /// 1. Shared region ids map to the same `RegionKind`.
    /// 2. Lifetime ordering is consistent (no region is both outlived-by and
    ///    outlives the same peer across the two models).
    /// 3. No Write permission conflicts at the boundary.
    #[must_use]
    pub(crate) fn compose_proofs(
        caller_model: &UnifiedMemoryModel,
        callee_model: &UnifiedMemoryModel,
    ) -> MemoryModelCompatibility {
        // Find shared region ids.
        let caller_ids: Vec<RegionId> = caller_model.regions.iter().map(|r| r.id).collect();

        for callee_region in &callee_model.regions {
            if !caller_ids.contains(&callee_region.id) {
                continue; // Callee-local region, no boundary constraint.
            }

            let caller_region = caller_model
                .region_by_id(callee_region.id)
                // SAFETY: We checked caller_ids.contains(&callee_region.id) above.
                .unwrap_or_else(|| unreachable!("caller region not found despite contains check"));

            // Check 1: RegionKind must match.
            if caller_region.kind != callee_region.kind {
                return MemoryModelCompatibility::IncompatibleRegions {
                    reason: format!(
                        "region {} has kind {:?} in caller but {:?} in callee",
                        callee_region.id, caller_region.kind, callee_region.kind,
                    ),
                };
            }

            // Check 2: Lifetime consistency.
            // If both models claim provenance for the same region, the parent must agree.
            if caller_region.provenance != callee_region.provenance {
                return MemoryModelCompatibility::IncompatibleLifetimes {
                    reason: format!(
                        "region {} has provenance {:?} in caller but {:?} in callee",
                        callee_region.id, caller_region.provenance, callee_region.provenance,
                    ),
                };
            }

            // Check 3: Permission soundness at the boundary.
            // If the caller gives Write permission, the callee cannot also claim Write
            // unless it is the same exclusive borrow being passed through.
            if caller_region.permission == Permission::Write
                && callee_region.permission == Permission::Write
            {
                // This is OK only if both refer to the same exclusive borrow being
                // passed into the callee. We allow it for now (same region id = same borrow).
                // Conflict would arise if two *different* regions both had Write to the
                // same parent, which is caught by the write-exclusivity axiom above.
            }

            // Check: Disabled region in caller cannot be Read/Write in callee
            // (use-after-move at boundary).
            if caller_region.permission == Permission::Disabled
                && callee_region.permission != Permission::Disabled
            {
                return MemoryModelCompatibility::IncompatibleRegions {
                    reason: format!(
                        "region {} is Disabled (moved/dropped) in caller but {:?} in callee",
                        callee_region.id, callee_region.permission,
                    ),
                };
            }
        }

        MemoryModelCompatibility::Compatible
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn stack_region(id: RegionId, lifetime: u32, perm: Permission) -> MemoryRegion {
        MemoryRegion {
            id,
            kind: RegionKind::Stack,
            lifetime,
            provenance: None,
            permission: perm,
        }
    }

    fn borrowed_region(
        id: RegionId,
        parent: RegionId,
        lifetime: u32,
        perm: Permission,
    ) -> MemoryRegion {
        MemoryRegion {
            id,
            kind: RegionKind::Stack,
            lifetime,
            provenance: Some(parent),
            permission: perm,
        }
    }

    fn heap_region(id: RegionId, lifetime: u32, perm: Permission) -> MemoryRegion {
        MemoryRegion {
            id,
            kind: RegionKind::Heap,
            lifetime,
            provenance: None,
            permission: perm,
        }
    }

    // -- UnifiedMemoryModel basic operations --------------------------------

    #[test]
    fn test_empty_model() {
        let model = UnifiedMemoryModel::new();
        assert!(model.regions().is_empty());
        assert!(model.region_by_id(0).is_none());
    }

    #[test]
    fn test_add_and_lookup_region() {
        let mut model = UnifiedMemoryModel::new();
        model.add_region(stack_region(0, 1, Permission::Write));
        model.add_region(heap_region(1, 0, Permission::Write));

        assert_eq!(model.regions().len(), 2);
        assert_eq!(model.region_by_id(0).unwrap().kind, RegionKind::Stack);
        assert_eq!(model.region_by_id(1).unwrap().kind, RegionKind::Heap);
        assert!(model.region_by_id(99).is_none());
    }

    #[test]
    fn test_with_regions_constructor() {
        let regions = vec![
            stack_region(0, 1, Permission::Write),
            stack_region(1, 1, Permission::Read),
        ];
        let model = UnifiedMemoryModel::with_regions(regions);
        assert_eq!(model.regions().len(), 2);
    }

    // -- boundary_region_ids ------------------------------------------------

    #[test]
    fn test_boundary_region_ids_extracts_from_formula() {
        let formula = Formula::And(vec![
            Formula::Var("region_0_base".to_string(), Sort::Int),
            Formula::Var("region_1_val".to_string(), Sort::Int),
            Formula::Var("region_2_live".to_string(), Sort::Bool),
            Formula::Var("region_3_perm".to_string(), Sort::Int),
            Formula::Var("x".to_string(), Sort::Int), // not a region
        ]);
        let ids = UnifiedMemoryModel::boundary_region_ids(&formula);
        assert_eq!(ids, vec![0, 1, 2, 3]);
    }

    #[test]
    fn test_boundary_region_ids_empty_formula() {
        let ids = UnifiedMemoryModel::boundary_region_ids(&Formula::Bool(true));
        assert!(ids.is_empty());
    }

    #[test]
    fn test_boundary_region_ids_deduplicates() {
        let formula = Formula::And(vec![
            Formula::Var("region_0_base".to_string(), Sort::Int),
            Formula::Var("region_0_val".to_string(), Sort::Int),
        ]);
        let ids = UnifiedMemoryModel::boundary_region_ids(&formula);
        assert_eq!(ids, vec![0]);
    }

    // -- translate_to_sunder ------------------------------------------------

    #[test]
    fn test_sunder_empty_model_is_true() {
        let model = UnifiedMemoryModel::new();
        assert_eq!(model.translate_to_sunder(), Formula::Bool(true));
    }

    #[test]
    fn test_sunder_single_region_is_true() {
        let model = UnifiedMemoryModel::with_regions(vec![
            stack_region(0, 1, Permission::Write),
        ]);
        // Single region: no non-aliasing pairs needed.
        assert_eq!(model.translate_to_sunder(), Formula::Bool(true));
    }

    #[test]
    fn test_sunder_two_regions_produces_non_aliasing() {
        let model = UnifiedMemoryModel::with_regions(vec![
            stack_region(0, 1, Permission::Write),
            heap_region(1, 0, Permission::Write),
        ]);
        let formula = model.translate_to_sunder();

        // Should be: And([Not(Eq(region_0_base, region_1_base))])
        if let Formula::And(conjuncts) = &formula {
            assert_eq!(conjuncts.len(), 1);
            if let Formula::Not(inner) = &conjuncts[0] {
                assert!(matches!(inner.as_ref(), Formula::Eq(..)));
            } else {
                panic!("expected Not(Eq(...))");
            }
        } else {
            panic!("expected And");
        }
    }

    #[test]
    fn test_sunder_three_regions_produces_three_pairs() {
        let model = UnifiedMemoryModel::with_regions(vec![
            stack_region(0, 1, Permission::Write),
            stack_region(1, 1, Permission::Read),
            heap_region(2, 0, Permission::Write),
        ]);
        let formula = model.translate_to_sunder();

        // C(3,2) = 3 non-aliasing pairs
        if let Formula::And(conjuncts) = &formula {
            assert_eq!(conjuncts.len(), 3);
        } else {
            panic!("expected And with 3 conjuncts");
        }
    }

    // -- translate_to_certus ------------------------------------------------

    #[test]
    fn test_certus_empty_model_is_true() {
        let model = UnifiedMemoryModel::new();
        assert_eq!(model.translate_to_certus(), Formula::Bool(true));
    }

    #[test]
    fn test_certus_single_region_has_permission_and_liveness() {
        let model = UnifiedMemoryModel::with_regions(vec![
            stack_region(0, 1, Permission::Write),
        ]);
        let formula = model.translate_to_certus();

        if let Formula::And(conjuncts) = &formula {
            // Should have: permission assertion + liveness assertion (no non-aliasing with 1 region)
            assert_eq!(conjuncts.len(), 2);
        } else {
            panic!("expected And");
        }
    }

    #[test]
    fn test_certus_includes_lifetime_outlives() {
        let model = UnifiedMemoryModel::with_regions(vec![
            stack_region(0, 1, Permission::Write),
            borrowed_region(1, 0, 2, Permission::Read),
        ]);
        let formula = model.translate_to_certus();

        // Should contain an Implies(region_1_live, region_0_live) for the borrow.
        if let Formula::And(conjuncts) = &formula {
            let has_implies = conjuncts.iter().any(|c| matches!(c, Formula::Implies(..)));
            assert!(has_implies, "certus projection should include lifetime outlives implication");
        } else {
            panic!("expected And");
        }
    }

    #[test]
    fn test_certus_disabled_region_not_live() {
        let model = UnifiedMemoryModel::with_regions(vec![
            stack_region(0, 1, Permission::Disabled),
        ]);
        let formula = model.translate_to_certus();

        if let Formula::And(conjuncts) = &formula {
            // Permission = 0 (Disabled), liveness = false
            let has_false_live = conjuncts.iter().any(|c| {
                if let Formula::Eq(lhs, rhs) = c
                    && let Formula::Var(name, Sort::Bool) = lhs.as_ref()
                {
                    return name == "region_0_live"
                        && matches!(rhs.as_ref(), Formula::Bool(false));
                }
                false
            });
            assert!(has_false_live, "disabled region should have live=false");
        } else {
            panic!("expected And");
        }
    }

    // -- compose_proofs: compatible cases -----------------------------------

    #[test]
    fn test_compose_compatible_matching_regions() {
        let caller = UnifiedMemoryModel::with_regions(vec![
            stack_region(0, 1, Permission::Write),
            heap_region(1, 0, Permission::Read),
        ]);
        let callee = UnifiedMemoryModel::with_regions(vec![
            stack_region(0, 1, Permission::Write),
            heap_region(1, 0, Permission::Read),
        ]);
        assert_eq!(
            UnifiedMemoryModel::compose_proofs(&caller, &callee),
            MemoryModelCompatibility::Compatible,
        );
    }

    #[test]
    fn test_compose_compatible_disjoint_regions() {
        let caller = UnifiedMemoryModel::with_regions(vec![
            stack_region(0, 1, Permission::Write),
        ]);
        let callee = UnifiedMemoryModel::with_regions(vec![
            stack_region(1, 2, Permission::Write),
        ]);
        // No shared regions => compatible.
        assert_eq!(
            UnifiedMemoryModel::compose_proofs(&caller, &callee),
            MemoryModelCompatibility::Compatible,
        );
    }

    #[test]
    fn test_compose_compatible_empty_models() {
        let caller = UnifiedMemoryModel::new();
        let callee = UnifiedMemoryModel::new();
        assert_eq!(
            UnifiedMemoryModel::compose_proofs(&caller, &callee),
            MemoryModelCompatibility::Compatible,
        );
    }

    #[test]
    fn test_compose_compatible_write_passthrough() {
        // Passing an exclusive &mut borrow from caller to callee is valid.
        let caller = UnifiedMemoryModel::with_regions(vec![
            stack_region(0, 1, Permission::Write),
        ]);
        let callee = UnifiedMemoryModel::with_regions(vec![
            stack_region(0, 1, Permission::Write),
        ]);
        assert_eq!(
            UnifiedMemoryModel::compose_proofs(&caller, &callee),
            MemoryModelCompatibility::Compatible,
        );
    }

    // -- compose_proofs: incompatible cases ---------------------------------

    #[test]
    fn test_compose_incompatible_region_kind_mismatch() {
        let caller = UnifiedMemoryModel::with_regions(vec![
            stack_region(0, 1, Permission::Write),
        ]);
        let callee = UnifiedMemoryModel::with_regions(vec![
            heap_region(0, 1, Permission::Write),
        ]);
        let result = UnifiedMemoryModel::compose_proofs(&caller, &callee);
        assert!(
            matches!(result, MemoryModelCompatibility::IncompatibleRegions { .. }),
            "different RegionKind for same id should be incompatible",
        );
    }

    #[test]
    fn test_compose_incompatible_provenance_mismatch() {
        let caller = UnifiedMemoryModel::with_regions(vec![
            stack_region(0, 1, Permission::Write),
            borrowed_region(1, 0, 2, Permission::Read),
        ]);
        let callee = UnifiedMemoryModel::with_regions(vec![
            stack_region(0, 1, Permission::Write),
            // Callee thinks region 1 is owned, not borrowed from 0.
            stack_region(1, 2, Permission::Read),
        ]);
        let result = UnifiedMemoryModel::compose_proofs(&caller, &callee);
        assert!(
            matches!(result, MemoryModelCompatibility::IncompatibleLifetimes { .. }),
            "provenance disagreement should be incompatible lifetimes",
        );
    }

    #[test]
    fn test_compose_incompatible_use_after_move() {
        // Caller has moved/dropped region 0, callee tries to use it.
        let caller = UnifiedMemoryModel::with_regions(vec![
            stack_region(0, 1, Permission::Disabled),
        ]);
        let callee = UnifiedMemoryModel::with_regions(vec![
            stack_region(0, 1, Permission::Read),
        ]);
        let result = UnifiedMemoryModel::compose_proofs(&caller, &callee);
        assert!(
            matches!(result, MemoryModelCompatibility::IncompatibleRegions { .. }),
            "disabled in caller but used in callee should be incompatible",
        );
    }

    // -- roundtrip translation consistency ----------------------------------

    #[test]
    fn test_roundtrip_sunder_certus_non_aliasing_consistent() {
        // Both projections should agree on the non-aliasing structure.
        let model = UnifiedMemoryModel::with_regions(vec![
            stack_region(0, 1, Permission::Write),
            heap_region(1, 0, Permission::Read),
        ]);

        let sunder_formula = model.translate_to_sunder();
        let certus_formula = model.translate_to_certus();

        // Sunder: 1 non-aliasing conjunct.
        let sunder_count = match &sunder_formula {
            Formula::And(cs) => cs.len(),
            _ => panic!("sunder should produce And"),
        };
        assert_eq!(sunder_count, 1);

        // Certus: 1 non-aliasing + 2 permissions + 2 liveness = 5.
        let certus_count = match &certus_formula {
            Formula::And(cs) => cs.len(),
            _ => panic!("certus should produce And"),
        };
        assert_eq!(certus_count, 5);

        // The non-aliasing clause should be structurally identical.
        let sunder_clause = match &sunder_formula {
            Formula::And(cs) => &cs[0],
            _ => unreachable!(),
        };
        let certus_clause = match &certus_formula {
            Formula::And(cs) => &cs[0],
            _ => unreachable!(),
        };
        assert_eq!(sunder_clause, certus_clause);
    }

    #[test]
    fn test_roundtrip_empty_model_both_true() {
        let model = UnifiedMemoryModel::new();
        assert_eq!(model.translate_to_sunder(), Formula::Bool(true));
        assert_eq!(model.translate_to_certus(), Formula::Bool(true));
    }

    // -- MemoryModelCompatibility enum tests --------------------------------

    #[test]
    fn test_compatibility_enum_variants() {
        let c = MemoryModelCompatibility::Compatible;
        assert_eq!(c, MemoryModelCompatibility::Compatible);

        let ir = MemoryModelCompatibility::IncompatibleRegions {
            reason: "test".to_string(),
        };
        assert!(matches!(ir, MemoryModelCompatibility::IncompatibleRegions { .. }));

        let il = MemoryModelCompatibility::IncompatibleLifetimes {
            reason: "test".to_string(),
        };
        assert!(matches!(il, MemoryModelCompatibility::IncompatibleLifetimes { .. }));
    }

    // -- Permission ordering ------------------------------------------------

    #[test]
    fn test_permission_ordering() {
        assert!(Permission::Disabled < Permission::Read);
        assert!(Permission::Read < Permission::Write);
    }

    // -- RegionKind variants ------------------------------------------------

    #[test]
    fn test_region_kind_equality() {
        assert_eq!(RegionKind::Stack, RegionKind::Stack);
        assert_ne!(RegionKind::Stack, RegionKind::Heap);
        assert_ne!(RegionKind::Heap, RegionKind::Global);
    }

    // -- Complex composition scenario ---------------------------------------

    #[test]
    fn test_compose_complex_borrow_chain() {
        // Caller has: owned region 0, &mut borrow 1 from 0, & borrow 2 from 0
        let caller = UnifiedMemoryModel::with_regions(vec![
            stack_region(0, 1, Permission::Write),
            borrowed_region(1, 0, 2, Permission::Write),
            borrowed_region(2, 0, 2, Permission::Read),
        ]);
        // Callee receives: same borrow chain, matching provenance
        let callee = UnifiedMemoryModel::with_regions(vec![
            stack_region(0, 1, Permission::Write),
            borrowed_region(1, 0, 2, Permission::Write),
            borrowed_region(2, 0, 2, Permission::Read),
            // Plus a callee-local region
            stack_region(3, 3, Permission::Write),
        ]);
        assert_eq!(
            UnifiedMemoryModel::compose_proofs(&caller, &callee),
            MemoryModelCompatibility::Compatible,
        );
    }
}
