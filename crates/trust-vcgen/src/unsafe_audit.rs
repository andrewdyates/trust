// trust-vcgen/unsafe_audit.rs: Unsafe code audit tracking and reporting
//
// Tracks all unsafe blocks across a crate, categorizes usage patterns,
// and produces audit reports showing verification coverage.
//
// Part of #137: Comprehensive unsafe code verification
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::*;

use crate::unsafe_verify::{UnsafeBlock, UnsafeVc, UnsafeVcKind, detect_unsafe_blocks, generate_unsafe_vcs};
use trust_types::fx::FxHashMap;

// ────────────────────────────────────────────────────────────────────────────
// Usage pattern classification
// ────────────────────────────────────────────────────────────────────────────

/// Categorized usage pattern for an unsafe block.
///
/// Classifying *why* unsafe is used determines what kind of audit attention
/// the block deserves and what verification strategy is most effective.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum UnsafeUsagePattern {
    /// Safe abstraction: unsafe internals exposed through a safe public API.
    /// Example: `Vec::push` uses unsafe internally but the API is safe.
    /// Verification: prove the safe API contract is upheld.
    SafeAbstraction,
    /// Raw performance: unsafe used to bypass bounds checks or avoid overhead.
    /// Example: `get_unchecked` instead of indexing.
    /// Verification: prove the skipped check would have passed.
    RawPerformance,
    /// FFI bridge: unsafe used to call foreign functions.
    /// Example: calling libc or a C library.
    /// Verification: pre/post conditions on the extern call.
    FfiBridge,
    /// Transmute / type punning: reinterpreting bits as a different type.
    /// Example: `mem::transmute`, union field access.
    /// Verification: layout compatibility and validity invariants.
    TypePunning,
    /// Hardware / low-level access: inline assembly, MMIO, volatile operations.
    /// Verification: limited — rely on SAFETY comments and manual audit.
    HardwareAccess,
    /// Global mutable state: accessing mutable statics.
    /// Verification: data-race freedom (requires concurrency model).
    GlobalMutableState,
    /// Unclassified: does not match any known pattern.
    Unclassified,
}

impl UnsafeUsagePattern {
    /// Human-readable label.
    #[must_use]
    pub fn label(&self) -> &str {
        match self {
            Self::SafeAbstraction => "safe abstraction",
            Self::RawPerformance => "raw performance",
            Self::FfiBridge => "FFI bridge",
            Self::TypePunning => "type punning",
            Self::HardwareAccess => "hardware access",
            Self::GlobalMutableState => "global mutable state",
            Self::Unclassified => "unclassified",
        }
    }

    /// Risk level: higher means more audit attention needed.
    #[must_use]
    pub fn risk_level(&self) -> u8 {
        match self {
            Self::SafeAbstraction => 1,
            Self::RawPerformance => 2,
            Self::FfiBridge => 3,
            Self::TypePunning => 4,
            Self::HardwareAccess => 5,
            Self::GlobalMutableState => 4,
            Self::Unclassified => 3,
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Audit entry and report
// ────────────────────────────────────────────────────────────────────────────

/// A single audited unsafe block with its classification and verification status.
#[derive(Debug, Clone)]
pub struct AuditEntry {
    /// The function containing this unsafe block.
    pub function_name: String,
    /// Source location.
    pub span: SourceSpan,
    /// MIR block ID.
    pub block_id: BlockId,
    /// Classified usage pattern.
    pub pattern: UnsafeUsagePattern,
    /// Whether a SAFETY comment was present.
    pub has_safety_comment: bool,
    /// Number of VCs generated for this block.
    pub vc_count: usize,
    /// The categorized VC kinds generated.
    pub vc_kinds: Vec<UnsafeVcKind>,
}

/// Aggregate audit report for all unsafe blocks in a set of functions.
#[derive(Debug, Clone)]
pub struct AuditReport {
    /// Individual audit entries.
    pub entries: Vec<AuditEntry>,
    /// Total number of functions audited.
    pub functions_audited: usize,
    /// Total number of unsafe blocks found.
    pub total_unsafe_blocks: usize,
    /// Number of blocks with SAFETY comments.
    pub blocks_with_comments: usize,
    /// Total VCs generated across all blocks.
    pub total_vcs: usize,
    /// Breakdown of blocks by usage pattern.
    pub pattern_counts: Vec<(UnsafeUsagePattern, usize)>,
}

impl AuditReport {
    /// Fraction of unsafe blocks that have SAFETY comments (0.0 to 1.0).
    #[must_use]
    pub fn comment_coverage(&self) -> f64 {
        if self.total_unsafe_blocks == 0 {
            1.0 // No unsafe blocks = perfect coverage
        } else {
            self.blocks_with_comments as f64 / self.total_unsafe_blocks as f64
        }
    }

    /// Fraction of unsafe blocks that have at least one VC (0.0 to 1.0).
    #[must_use]
    pub fn verification_coverage(&self) -> f64 {
        if self.total_unsafe_blocks == 0 {
            1.0
        } else {
            let covered = self.entries.iter().filter(|e| e.vc_count > 0).count();
            covered as f64 / self.total_unsafe_blocks as f64
        }
    }

    /// Maximum risk level across all entries.
    #[must_use]
    pub fn max_risk_level(&self) -> u8 {
        self.entries.iter().map(|e| e.pattern.risk_level()).max().unwrap_or(0)
    }

    /// Format a human-readable summary.
    #[must_use]
    pub fn summary(&self) -> String {
        let mut lines = Vec::new();
        lines.push("Unsafe Audit Report".to_string());
        lines.push("==================".to_string());
        lines.push(format!(
            "Functions audited: {}",
            self.functions_audited
        ));
        lines.push(format!(
            "Unsafe blocks: {}",
            self.total_unsafe_blocks
        ));
        lines.push(format!(
            "SAFETY comments: {} ({:.0}%)",
            self.blocks_with_comments,
            self.comment_coverage() * 100.0,
        ));
        lines.push(format!(
            "Verification conditions: {}",
            self.total_vcs
        ));
        lines.push(format!(
            "Verification coverage: {:.0}%",
            self.verification_coverage() * 100.0,
        ));
        lines.push(format!(
            "Max risk level: {}",
            self.max_risk_level()
        ));

        if !self.pattern_counts.is_empty() {
            lines.push(String::new());
            lines.push("Pattern breakdown:".to_string());
            for (pattern, count) in &self.pattern_counts {
                lines.push(format!(
                    "  {}: {} (risk {})",
                    pattern.label(),
                    count,
                    pattern.risk_level()
                ));
            }
        }

        lines.join("\n")
    }
}

// ────────────────────────────────────────────────────────────────────────────
// UnsafeAudit: crate-level audit tracker
// ────────────────────────────────────────────────────────────────────────────

/// Tracks all unsafe blocks across a crate and produces audit reports.
pub struct UnsafeAudit {
    entries: Vec<AuditEntry>,
    functions_audited: usize,
}

impl UnsafeAudit {
    /// Create a new empty audit.
    #[must_use]
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
            functions_audited: 0,
        }
    }

    /// Audit a single function, detecting unsafe blocks and generating VCs.
    pub fn audit_function(
        &mut self,
        func: &VerifiableFunction,
        comments: &[(SourceSpan, String)],
    ) {
        self.functions_audited += 1;

        let blocks = detect_unsafe_blocks(func);
        if blocks.is_empty() {
            return;
        }

        let unsafe_vcs = generate_unsafe_vcs(func, comments);

        for block in &blocks {
            let pattern = classify_pattern(func, block);
            let has_comment = block.safety_comment.is_some()
                || comments.iter().any(|(span, text)| {
                    span.file == block.span.file
                        && span.line_end <= block.span.line_start
                        && block.span.line_start - span.line_end <= 2
                        && text.contains("SAFETY:")
                });

            // Collect VCs that correspond to this block
            let block_vcs: Vec<&UnsafeVc> = unsafe_vcs
                .iter()
                .filter(|uvc| uvc.vc.location == block.span)
                .collect();

            let vc_kinds: Vec<UnsafeVcKind> = block_vcs
                .iter()
                .map(|uvc| uvc.unsafe_kind.clone())
                .collect();

            self.entries.push(AuditEntry {
                function_name: func.name.clone(),
                span: block.span.clone(),
                block_id: block.block_id,
                pattern,
                has_safety_comment: has_comment,
                vc_count: block_vcs.len(),
                vc_kinds,
            });
        }
    }

    /// Produce the final audit report.
    #[must_use]
    pub fn audit_report(&self) -> AuditReport {
        let total_unsafe_blocks = self.entries.len();
        let blocks_with_comments = self.entries.iter().filter(|e| e.has_safety_comment).count();
        let total_vcs: usize = self.entries.iter().map(|e| e.vc_count).sum();

        // Count patterns
        let mut pattern_map = FxHashMap::default();
        for entry in &self.entries {
            *pattern_map.entry(entry.pattern.clone()).or_insert(0usize) += 1;
        }
        let mut pattern_counts: Vec<(UnsafeUsagePattern, usize)> =
            pattern_map.into_iter().collect();
        // Sort by risk level descending for report readability
        pattern_counts.sort_by(|a, b| b.0.risk_level().cmp(&a.0.risk_level()));

        AuditReport {
            entries: self.entries.clone(),
            functions_audited: self.functions_audited,
            total_unsafe_blocks,
            blocks_with_comments,
            total_vcs,
            pattern_counts,
        }
    }
}

impl Default for UnsafeAudit {
    fn default() -> Self {
        Self::new()
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Pattern classification heuristics
// ────────────────────────────────────────────────────────────────────────────

/// Classify the usage pattern of an unsafe block based on its MIR context.
fn classify_pattern(
    func: &VerifiableFunction,
    block: &UnsafeBlock,
) -> UnsafeUsagePattern {
    let mir_block = func.body.blocks.iter().find(|b| b.id == block.block_id);
    let Some(mir_block) = mir_block else {
        return UnsafeUsagePattern::Unclassified;
    };

    // Check terminator for call patterns
    if let Terminator::Call { func: callee, .. } = &mir_block.terminator {
        let lower = callee.to_lowercase();

        // FFI bridge
        if lower.contains("::ffi::") || lower.contains("extern") {
            return UnsafeUsagePattern::FfiBridge;
        }

        // Type punning
        if lower.contains("mem::transmute") || lower.contains("mem::transmute_copy") {
            return UnsafeUsagePattern::TypePunning;
        }

        // Raw performance
        if lower.contains("get_unchecked")
            || lower.contains("ptr::read_unaligned")
            || lower.contains("ptr::write_unaligned")
        {
            return UnsafeUsagePattern::RawPerformance;
        }

        // Hardware / volatile
        if lower.contains("read_volatile") || lower.contains("write_volatile") {
            return UnsafeUsagePattern::HardwareAccess;
        }

        // Safe abstraction patterns: ptr::read/write in internal functions
        if lower.contains("ptr::read")
            || lower.contains("ptr::write")
            || lower.contains("slice::from_raw_parts")
            || lower.contains("from_utf8_unchecked")
        {
            return UnsafeUsagePattern::SafeAbstraction;
        }
    }

    // Check statements for deref patterns (usually safe abstraction or perf)
    for stmt in &mir_block.stmts {
        if let Statement::Assign { rvalue, .. } = stmt
            && has_raw_deref(rvalue) {
                return UnsafeUsagePattern::SafeAbstraction;
            }
    }

    UnsafeUsagePattern::Unclassified
}

/// Check whether an rvalue contains a raw pointer dereference.
/// (Duplicated from unsafe_verify to keep this module self-contained.)
fn has_raw_deref(rvalue: &Rvalue) -> bool {
    match rvalue {
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => {
            place.projections.iter().any(|p| matches!(p, Projection::Deref))
        }
        Rvalue::Ref { place, .. } => {
            place.projections.iter().any(|p| matches!(p, Projection::Deref))
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── Test helpers ─────────────────────────────────────────────────────

    fn unsafe_ptr_read_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "read_raw".to_string(),
            def_path: "test::read_raw".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                        name: Some("ptr".into()),
                    },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("val".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "core::ptr::read".to_string(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(2),
                            target: Some(BlockId(1)),
                            span: SourceSpan {
                                file: "test.rs".into(),
                                line_start: 10,
                                col_start: 8,
                                line_end: 10,
                                col_end: 30,
                            },
                            atomic: None,
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
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

    fn ffi_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "call_ffi".to_string(),
            def_path: "test::call_ffi".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref { mutable: false, inner: Box::new(Ty::Int { width: 8, signed: false }) },
                        name: Some("buf".into()),
                    },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("result".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "libc::ffi::write".to_string(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(2),
                            target: Some(BlockId(1)),
                            span: SourceSpan {
                                file: "ffi.rs".into(),
                                line_start: 12,
                                col_start: 4,
                                line_end: 12,
                                col_end: 30,
                            },
                            atomic: None,
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn transmute_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "transmute_fn".to_string(),
            def_path: "test::transmute_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("input".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("output".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "core::mem::transmute".to_string(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(2),
                            target: Some(BlockId(1)),
                            span: SourceSpan {
                                file: "test.rs".into(),
                                line_start: 8,
                                col_start: 4,
                                line_end: 8,
                                col_end: 40,
                            },
                            atomic: None,
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
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

    // ── UnsafeUsagePattern tests ─────────────────────────────────────────

    #[test]
    fn test_usage_pattern_labels() {
        assert_eq!(UnsafeUsagePattern::SafeAbstraction.label(), "safe abstraction");
        assert_eq!(UnsafeUsagePattern::RawPerformance.label(), "raw performance");
        assert_eq!(UnsafeUsagePattern::FfiBridge.label(), "FFI bridge");
        assert_eq!(UnsafeUsagePattern::TypePunning.label(), "type punning");
        assert_eq!(UnsafeUsagePattern::HardwareAccess.label(), "hardware access");
        assert_eq!(UnsafeUsagePattern::GlobalMutableState.label(), "global mutable state");
        assert_eq!(UnsafeUsagePattern::Unclassified.label(), "unclassified");
    }

    #[test]
    fn test_usage_pattern_risk_levels() {
        assert_eq!(UnsafeUsagePattern::SafeAbstraction.risk_level(), 1);
        assert_eq!(UnsafeUsagePattern::RawPerformance.risk_level(), 2);
        assert_eq!(UnsafeUsagePattern::FfiBridge.risk_level(), 3);
        assert_eq!(UnsafeUsagePattern::TypePunning.risk_level(), 4);
        assert_eq!(UnsafeUsagePattern::HardwareAccess.risk_level(), 5);
        assert_eq!(UnsafeUsagePattern::GlobalMutableState.risk_level(), 4);
        assert_eq!(UnsafeUsagePattern::Unclassified.risk_level(), 3);
    }

    #[test]
    fn test_usage_pattern_serialization_roundtrip() {
        let patterns = vec![
            UnsafeUsagePattern::SafeAbstraction,
            UnsafeUsagePattern::RawPerformance,
            UnsafeUsagePattern::FfiBridge,
            UnsafeUsagePattern::TypePunning,
            UnsafeUsagePattern::HardwareAccess,
            UnsafeUsagePattern::GlobalMutableState,
            UnsafeUsagePattern::Unclassified,
        ];
        for p in &patterns {
            let json = serde_json::to_string(p).expect("serialize");
            let round: UnsafeUsagePattern = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(&round, p);
        }
    }

    // ── Pattern classification tests ─────────────────────────────────────

    #[test]
    fn test_classify_pattern_ptr_read_is_safe_abstraction() {
        let func = unsafe_ptr_read_function();
        let blocks = detect_unsafe_blocks(&func);
        assert_eq!(blocks.len(), 1);
        let pattern = classify_pattern(&func, &blocks[0]);
        assert_eq!(pattern, UnsafeUsagePattern::SafeAbstraction);
    }

    #[test]
    fn test_classify_pattern_ffi_is_ffi_bridge() {
        let func = ffi_function();
        let blocks = detect_unsafe_blocks(&func);
        assert_eq!(blocks.len(), 1);
        let pattern = classify_pattern(&func, &blocks[0]);
        assert_eq!(pattern, UnsafeUsagePattern::FfiBridge);
    }

    #[test]
    fn test_classify_pattern_transmute_is_type_punning() {
        let func = transmute_function();
        let blocks = detect_unsafe_blocks(&func);
        assert_eq!(blocks.len(), 1);
        let pattern = classify_pattern(&func, &blocks[0]);
        assert_eq!(pattern, UnsafeUsagePattern::TypePunning);
    }

    #[test]
    fn test_classify_pattern_deref_is_safe_abstraction() {
        let func = deref_function();
        let blocks = detect_unsafe_blocks(&func);
        assert_eq!(blocks.len(), 1);
        let pattern = classify_pattern(&func, &blocks[0]);
        assert_eq!(pattern, UnsafeUsagePattern::SafeAbstraction);
    }

    // ── UnsafeAudit tests ────────────────────────────────────────────────

    #[test]
    fn test_audit_empty() {
        let audit = UnsafeAudit::new();
        let report = audit.audit_report();
        assert_eq!(report.functions_audited, 0);
        assert_eq!(report.total_unsafe_blocks, 0);
        assert_eq!(report.total_vcs, 0);
        assert!((report.comment_coverage() - 1.0).abs() < f64::EPSILON);
        assert!((report.verification_coverage() - 1.0).abs() < f64::EPSILON);
        assert_eq!(report.max_risk_level(), 0);
    }

    #[test]
    fn test_audit_safe_function() {
        let mut audit = UnsafeAudit::new();
        audit.audit_function(&safe_function(), &[]);
        let report = audit.audit_report();
        assert_eq!(report.functions_audited, 1);
        assert_eq!(report.total_unsafe_blocks, 0);
    }

    #[test]
    fn test_audit_single_unsafe_function() {
        let mut audit = UnsafeAudit::new();
        audit.audit_function(&unsafe_ptr_read_function(), &[]);
        let report = audit.audit_report();

        assert_eq!(report.functions_audited, 1);
        assert_eq!(report.total_unsafe_blocks, 1);
        assert_eq!(report.blocks_with_comments, 0);
        assert!((report.comment_coverage() - 0.0).abs() < f64::EPSILON);
        assert!(report.total_vcs > 0, "should generate VCs even without comments");
    }

    #[test]
    fn test_audit_multiple_functions() {
        let mut audit = UnsafeAudit::new();
        audit.audit_function(&unsafe_ptr_read_function(), &[]);
        audit.audit_function(&ffi_function(), &[]);
        audit.audit_function(&safe_function(), &[]);
        audit.audit_function(&transmute_function(), &[]);

        let report = audit.audit_report();
        assert_eq!(report.functions_audited, 4);
        assert_eq!(report.total_unsafe_blocks, 3);
        assert!(report.total_vcs > 0);

        // Check pattern breakdown
        assert!(
            report.pattern_counts.iter().any(|(p, _)| *p == UnsafeUsagePattern::FfiBridge),
            "should have FFI bridge pattern"
        );
        assert!(
            report.pattern_counts.iter().any(|(p, _)| *p == UnsafeUsagePattern::TypePunning),
            "should have type punning pattern"
        );
    }

    #[test]
    fn test_audit_with_comments() {
        let mut audit = UnsafeAudit::new();
        let comments = vec![(
            SourceSpan {
                file: "test.rs".into(),
                line_start: 9,
                col_start: 4,
                line_end: 9,
                col_end: 60,
            },
            "// SAFETY: pointer is non-null because allocated on heap".to_string(),
        )];
        audit.audit_function(&unsafe_ptr_read_function(), &comments);

        let report = audit.audit_report();
        assert_eq!(report.blocks_with_comments, 1);
        assert!((report.comment_coverage() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_audit_report_summary_format() {
        let mut audit = UnsafeAudit::new();
        audit.audit_function(&unsafe_ptr_read_function(), &[]);
        audit.audit_function(&ffi_function(), &[]);

        let report = audit.audit_report();
        let summary = report.summary();

        assert!(summary.contains("Unsafe Audit Report"));
        assert!(summary.contains("Functions audited: 2"));
        assert!(summary.contains("Unsafe blocks: 2"));
        assert!(summary.contains("Pattern breakdown:"));
    }

    #[test]
    fn test_audit_verification_coverage() {
        let mut audit = UnsafeAudit::new();
        audit.audit_function(&unsafe_ptr_read_function(), &[]);

        let report = audit.audit_report();
        // All unsafe blocks should have at least the missing-comment VC
        assert!(
            report.verification_coverage() > 0.0,
            "verification coverage should be > 0"
        );
    }

    #[test]
    fn test_audit_max_risk_level() {
        let mut audit = UnsafeAudit::new();
        audit.audit_function(&unsafe_ptr_read_function(), &[]);
        let report = audit.audit_report();
        assert_eq!(report.max_risk_level(), 1, "ptr::read = safe abstraction = risk 1");

        let mut audit2 = UnsafeAudit::new();
        audit2.audit_function(&ffi_function(), &[]);
        let report2 = audit2.audit_report();
        assert_eq!(report2.max_risk_level(), 3, "FFI = risk 3");

        let mut audit3 = UnsafeAudit::new();
        audit3.audit_function(&unsafe_ptr_read_function(), &[]);
        audit3.audit_function(&ffi_function(), &[]);
        audit3.audit_function(&transmute_function(), &[]);
        let report3 = audit3.audit_report();
        assert_eq!(report3.max_risk_level(), 4, "transmute = type punning = risk 4");
    }

    #[test]
    fn test_audit_default_trait() {
        let audit = UnsafeAudit::default();
        let report = audit.audit_report();
        assert_eq!(report.functions_audited, 0);
    }

    #[test]
    fn test_audit_entry_has_vc_kinds() {
        let mut audit = UnsafeAudit::new();
        audit.audit_function(&ffi_function(), &[]);

        let report = audit.audit_report();
        assert_eq!(report.entries.len(), 1);

        let entry = &report.entries[0];
        assert_eq!(entry.function_name, "call_ffi");
        assert_eq!(entry.pattern, UnsafeUsagePattern::FfiBridge);
        // The FFI block should have some VCs (at minimum the missing-comment VC)
        assert!(entry.vc_count > 0);
    }
}
