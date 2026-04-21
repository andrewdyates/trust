#![allow(dead_code)]
//! trust-symex: Symbolic/concolic execution engine over MIR
//!
//! Provides symbolic state tracking, path constraint collection, and
//! exploration strategies for MIR-level verification. Converts path
//! constraints to trust-types Formula for z4 dispatch.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub mod adapter;
pub(crate) mod alias_analysis;
// tRust #792: bmc.rs removed — BMC now handled by trust-zani-lib.
pub(crate) mod byte_encoding;
pub(crate) mod concolic;
pub(crate) mod concolic_fuzzing;
pub(crate) mod concrete;
pub(crate) mod constraint;
pub(crate) mod constraint_cache;
pub(crate) mod constraint_independence;
// tRust #792: constraint_solver.rs removed — constraint solving now via z4 directly.
pub(crate) mod constraints;
pub(crate) mod coverage;
pub mod engine;
pub(crate) mod error;
pub(crate) mod heap;
pub(crate) mod function_summary;
pub(crate) mod memory;
pub(crate) mod merge_heuristic;
pub(crate) mod merging;
pub(crate) mod ownership;
pub mod path;
pub(crate) mod path_prioritization;
pub(crate) mod provenance;
pub(crate) mod recursion;
pub(crate) mod region;
pub(crate) mod search;
pub mod state;
pub(crate) mod statistics;
// tRust #792: symbolic_array.rs, symbolic_heap.rs removed — unused, no callers.
pub(crate) mod symbolic_memory_model;
pub(crate) mod trace;

pub use constraint::{
    ConstraintSet, FeasibilityResult, check_feasibility, independence_splitting,
    simplify_constraints,
};
pub use coverage::{
    BranchPoint, CoverageMap, PathCoverage, coverage_percentage, suggest_next_path,
    uncovered_branches,
};
pub use engine::{BlockResult, ExecutionFork, SymbolicExecutor};
pub use function_summary::{
    AppliedSummary, FunctionSummary, Postcondition, Precondition, SideEffect, SummaryCache,
    apply_summary, compose_summaries, is_pure, substitute,
};
pub use memory::{
    MemoryAddress, MemoryError, MemoryRegion, MemorySnapshot, SymbolicMemory, diff_memories,
};
pub use error::SymexError;
pub use merging::{
    Interval, IteMerger, MergePolicy, MergeStrategy, MergedState, MergingExplorer, PathMerger,
    SplitResult, StateMerger, StateSplitter, WideningMerger, can_merge, merge_paths, merge_states,
    merge_states_with_pre_branch,
};
pub use path::{PathConstraint, symbolic_to_formula, symbolic_to_formula_with_signedness};
pub use search::{
    BfsStrategy, CoverageGuidedStrategy, DfsStrategy, HeuristicStrategy, PathPrioritizer,
    RandomPathStrategy, SearchConfig, SearchStrategy, SearchStrategyKind, SymbolicPath,
    make_strategy,
};
pub use ownership::{
    OwnershipChecker, OwnershipConstraint, OwnershipConstraintKind, OwnershipCounterexample,
    OwnershipError, check_static_ownership, generate_ownership_vcs,
};
pub use provenance::{
    AllocationInfo, BorrowStackItem, Permission, ProvenanceError, ProvenanceTag,
    ProvenanceTracker, ProvenanceVC, ProvenanceVCKind,
};
pub use byte_encoding::{
    ByteMemory, ByteMemoryError, ByteMemoryRegion, Endian, SymbolicByte,
};
pub use region::{
    OwnershipKind, Region, RegionError, RegionMap, RegionState,
};
pub use state::{SymbolicState, SymbolicValue, eval};
pub use statistics::{ExecutionStats, StatsCollector, format_stats_report};
pub use trace::{
    ConsistencyError, ConsistencyErrorKind, CounterexampleTrace, ExecutionTrace, TraceFormatter,
    TraceRecorder, TraceReplayer, TraceStep,
};
pub use symbolic_memory_model::{
    AccessKind, MemoryAccess, MemoryCell, MemoryModel, MemoryModelConfig, MemoryModelError,
    MemoryRegionModel, SymbolicPointer,
};
pub use alias_analysis::{
    AliasAnalyzer, AliasQuery, AliasResult, AliasSet, PointsToEntry,
};
pub use concolic::{
    ConcolicConfig, ConcolicEngine, ConcolicResult, ConcolicState, ConstraintSolver,
    ExplorationResult, MockSolver, concolic_search, execute_concrete, explore,
    explore_with_solver, generate_test_input, negate_branch,
};
pub use constraint_independence::{
    ConstraintPartition, ConstraintPartitioner, IndependenceGraph, PartitionConfig,
    PartitionResult,
};
pub use concolic_fuzzing::{
    BugKind, BugOracle, BugReport, ConcolicFuzzConfig, ConcolicFuzzExecutor, ConcolicFuzzResult,
    ConcolicFuzzTarget, ConcolicStrategy, CoverageTracker, FuzzParam,
};
