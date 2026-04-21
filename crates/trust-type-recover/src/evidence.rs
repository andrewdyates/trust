// trust-type-recover: type evidence tracking
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::types::RecoveredType;

/// Source of evidence for a type recovery decision.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum EvidenceSource {
    /// DWARF debug information entry (DIE) at a given offset.
    Dwarf {
        /// Offset within the `.debug_info` section.
        die_offset: u64,
    },

    /// Memory access pattern analysis.
    AccessPattern {
        /// Address of the instruction performing the access.
        instruction_addr: u64,
        /// Byte offset being accessed.
        access_offset: u64,
        /// Size of the access in bytes.
        access_size: u64,
    },

    /// Value-set analysis (VSA) result constraining a value's range.
    ValueRange {
        /// Minimum observed or inferred value.
        min: i128,
        /// Maximum observed or inferred value.
        max: i128,
    },

    /// Signature matching against a known function database (libc, etc.).
    SignatureMatch {
        /// Name of the matched function (e.g., `malloc`, `strlen`).
        function_name: String,
        /// Which parameter or return value this evidence applies to.
        position: SignaturePosition,
    },

    /// Struct field access pattern (base+offset).
    StructAccess {
        /// Identifier for the base register/variable.
        base_id: u64,
        /// Address of the first observed struct access instruction.
        instruction_addr: u64,
    },

    /// Indexed (array) access pattern (base + index * stride).
    IndexedAccess {
        /// Identifier for the base register/variable.
        base_id: u64,
        /// Stride (element size) in bytes.
        stride: u64,
        /// Address of the first observed indexed access instruction.
        instruction_addr: u64,
    },

    /// Pointer dereference pattern (load-then-use-as-address).
    Dereference {
        /// Address of the instruction that loads the pointer.
        load_addr: u64,
        /// Address of the instruction that dereferences the pointer.
        deref_addr: u64,
    },

    /// Return register usage analysis at a call site.
    ReturnRegisterAnalysis {
        /// Address of the call instruction.
        call_addr: u64,
        /// Name of the called function, if known.
        callee_name: Option<String>,
    },

    /// Callee-side return register analysis across function exits.
    CalleeReturnAnalysis {
        /// Start address of the analyzed function.
        function_addr: u64,
        /// Name of the analyzed function, if known.
        function_name: Option<String>,
        /// Number of exit points analyzed for the function.
        exit_count: usize,
    },

    /// Combined evidence from multiple sources.
    Combined {
        /// The individual evidence sources that were merged.
        sources: Vec<EvidenceSource>,
    },
}

/// Position within a function signature that evidence applies to.
#[derive(Debug, Clone, PartialEq)]
pub enum SignaturePosition {
    /// A function parameter at the given index.
    Parameter(usize),
    /// The function return value.
    ReturnValue,
}

/// Evidence supporting a recovered type, with a confidence score.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeEvidence {
    /// The recovered type this evidence supports.
    pub recovered_type: RecoveredType,
    /// Confidence in the recovery, from 0.0 (guess) to 1.0 (certain).
    pub confidence: f64,
    /// Where this evidence came from.
    pub source: EvidenceSource,
}

impl TypeEvidence {
    /// Create new type evidence.
    #[must_use]
    pub fn new(recovered_type: RecoveredType, confidence: f64, source: EvidenceSource) -> Self {
        Self { recovered_type, confidence: confidence.clamp(0.0, 1.0), source }
    }
}
