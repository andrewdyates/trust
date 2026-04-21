// trust-vcgen/memory_ordering: Memory ordering verification for concurrent programs
//
// Provides a structured model for reasoning about the C11/Rust memory model:
// - HappensBefore: partial order representing the happens-before relation
// - DataRaceDetector: checks if two memory accesses can race
// - AtomicAccessLog: records atomic operations with their orderings
// - RaceCondition: describes a detected race with conflicting accesses
// - MemoryModelChecker: verifies memory ordering constraints are sufficient
//
// Builds on the low-level primitives in data_race.rs (MemoryOrdering,
// AccessKind, SharedAccess) and provides higher-level analysis.
//
// Part of #203: Data race / atomics / memory ordering verification
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod happens_before;
mod race_condition;
mod atomic_access;
mod detector;
mod checker;
mod hb_graph;

#[cfg(test)]
mod tests;

pub use happens_before::HappensBefore;
pub use race_condition::RaceCondition;
pub use atomic_access::{AtomicAccessEntry, AtomicAccessLog};
pub use detector::DataRaceDetector;
pub use checker::{
    MemoryModelChecker, MemoryModelCheckResult, OrderingRequirement, OrderingViolation,
};
pub use hb_graph::HappensBeforeGraph;
