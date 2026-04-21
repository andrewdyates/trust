// trust-testgen/mutation/types.rs: Core mutation types and enums
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::Statement;

/// The type of mutation applied to source code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum MutationType {
    /// Replace arithmetic operator: `+` <-> `-`, `*` <-> `/`.
    ArithOp,
    /// Replace comparison operator: `>` <-> `>=`, `<` <-> `<=`, `==` <-> `!=`.
    CompOp,
    /// Replace boolean operator: `&&` <-> `||`, negate conditions.
    BoolOp,
    /// Shift boundary constants: `n` -> `n+1` or `n-1`.
    BoundaryShift,
    /// Replace return value with a default (0, false, empty).
    ReturnValue,
    /// Negate an `if` condition.
    ConditionNegation,
}

impl MutationType {
    /// Human-readable description of this mutation type.
    #[must_use]
    pub fn description(&self) -> &'static str {
        match self {
            MutationType::ArithOp => "arithmetic operator replacement",
            MutationType::CompOp => "comparison operator replacement",
            MutationType::BoolOp => "boolean operator replacement",
            MutationType::BoundaryShift => "boundary constant shift",
            MutationType::ReturnValue => "return value replacement",
            MutationType::ConditionNegation => "condition negation",
        }
    }
}

/// A single code mutation (mutant).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Mutant {
    /// Location in the original source (byte offset from start).
    pub(crate) offset: usize,
    /// Line number in the original source (1-indexed).
    pub(crate) line: usize,
    /// The type of mutation applied.
    pub(crate) mutation_type: MutationType,
    /// The original code fragment that was mutated.
    pub(crate) original: String,
    /// The mutated code fragment.
    pub(crate) mutated: String,
}

impl Mutant {
    /// Format this mutant as a human-readable diff-like description.
    #[must_use]
    pub fn describe(&self) -> String {
        format!(
            "line {}: {} ({}) -- `{}` -> `{}`",
            self.line,
            self.mutation_type.description(),
            match self.mutation_type {
                MutationType::ArithOp => "AOR",
                MutationType::CompOp => "ROR",
                MutationType::BoolOp => "LOR",
                MutationType::BoundaryShift => "BVR",
                MutationType::ReturnValue => "RVR",
                MutationType::ConditionNegation => "CNR",
            },
            self.original,
            self.mutated,
        )
    }
}

/// The result of testing a mutant against a test suite.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MutationResult {
    /// The mutant was detected (killed) by a test.
    Killed { test_name: String },
    /// The mutant survived (not detected by any test).
    Survived,
    /// The mutant is equivalent to the original (cannot be killed).
    Equivalent,
}

impl MutationResult {
    /// Returns true if the mutant was killed.
    #[must_use]
    pub fn is_killed(&self) -> bool {
        matches!(self, MutationResult::Killed { .. })
    }

    /// Returns true if the mutant survived.
    #[must_use]
    pub fn is_survived(&self) -> bool {
        matches!(self, MutationResult::Survived)
    }
}

/// A MIR-level mutation of a `VerifiableFunction` body.
#[derive(Debug, Clone)]
pub struct MirMutant {
    /// Block index in the function body.
    pub(crate) block_idx: usize,
    /// Statement index within the block.
    pub(crate) stmt_idx: usize,
    /// Type of mutation applied.
    pub(crate) mutation_type: MutationType,
    /// Description of the original construct.
    pub(crate) original_desc: String,
    /// Description of the mutated construct.
    pub(crate) mutated_desc: String,
    /// The mutated statement (replacing the original).
    pub(crate) mutated_stmt: Statement,
    /// Result of testing this mutant (initially Survived).
    pub(crate) result: MutationResult,
}

impl MirMutant {
    /// Format as a human-readable description.
    #[must_use]
    pub fn describe(&self) -> String {
        format!(
            "block[{}] stmt[{}]: {} -- `{}` -> `{}`",
            self.block_idx,
            self.stmt_idx,
            self.mutation_type.description(),
            self.original_desc,
            self.mutated_desc,
        )
    }
}
