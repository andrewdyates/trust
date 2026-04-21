// trust-vcgen/unsafe_verify.rs: Unsafe code verification with SAFETY comment extraction
//
// Detects unsafe blocks in MIR, extracts // SAFETY: comments from source spans,
// parses structured safety claims, and generates Assertion VCs that encode the
// claimed invariants. This lets the solver check whether the safety justification
// is consistent with the surrounding code.
//
// Extended in #137 with:
// - UnsafeVcKind enum for typed unsafe VC categorization
// - UnsafeVerifier struct for stateful VC generation across a function
// - Memory safety VCs: pointer alignment, provenance, bounds checking
// - Transmute VCs: layout compatibility, validity invariant preservation
// - FFI VCs: pre/post conditions on extern calls, null pointer checks
//
// Part of #79, #137: Unsafe code verification
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::*;

// ────────────────────────────────────────────────────────────────────────────
// Core types (existing)
// ────────────────────────────────────────────────────────────────────────────

/// An unsafe block discovered in MIR, with its optional safety claim.
#[derive(Debug, Clone)]
pub struct UnsafeBlock {
    /// Source location of the unsafe block.
    pub span: SourceSpan,
    /// The raw `// SAFETY:` comment text, if found.
    pub safety_comment: Option<String>,
    /// Parsed safety claim, if the comment was successfully parsed.
    pub safety_claim: Option<SafetyClaim>,
    /// The block index in MIR where the unsafe code lives.
    pub block_id: BlockId,
}

/// A structured safety claim extracted from a `// SAFETY:` comment.
///
/// Convention: Rust's `// SAFETY:` comments should state:
/// 1. The invariant that makes this unsafe code sound.
/// 2. The justification for why that invariant holds at this call site.
///
/// We parse these into structured form so the solver can attempt to verify
/// the claimed invariant against the surrounding code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafetyClaim {
    /// The invariant being claimed (e.g., "pointer is non-null and aligned").
    pub invariant: String,
    /// The justification for why the invariant holds (e.g., "checked above on line 42").
    pub justification: String,
}

// ────────────────────────────────────────────────────────────────────────────
// New types (#137): UnsafeVcKind, UnsafeVc, UnsafeVerifier
// ────────────────────────────────────────────────────────────────────────────

/// Categorized kinds of unsafe verification conditions.
///
/// Each variant corresponds to a specific unsafe operation that requires
/// verification. This is orthogonal to `VcKind` (which is solver-facing);
/// `UnsafeVcKind` captures the *reason* the VC was generated from an unsafe
/// context so reporters and audit tools can provide targeted guidance.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum UnsafeVcKind {
    /// Raw pointer dereference: pointer must be non-null, aligned, and point
    /// to a valid allocation with sufficient size.
    RawPointerDeref {
        /// Human-readable pointer expression (e.g., "`*ptr`").
        pointer_expr: String,
    },
    /// `mem::transmute` or `mem::transmute_copy`: source and target layouts
    /// must be compatible, and the bit pattern must satisfy the target type's
    /// validity invariant.
    Transmute {
        from_ty: String,
        to_ty: String,
    },
    /// Union field access: reading a union field reinterprets the bits, so
    /// the active variant must match the accessed field.
    UnionAccess {
        union_name: String,
        field_name: String,
    },
    /// FFI call: extern function has no Rust-side safety guarantees. Pre/post
    /// conditions must be stated and verified.
    FfiCall {
        callee: String,
    },
    /// Inline assembly: opaque to the compiler, safety cannot be inferred.
    InlineAsm {
        /// A diagnostic label for the asm block.
        label: String,
    },
    /// Access to a mutable static variable: data races and aliasing are
    /// the caller's responsibility.
    MutableStaticAccess {
        static_name: String,
    },
}

impl UnsafeVcKind {
    /// Human-readable description for reports.
    #[must_use]
    pub fn description(&self) -> String {
        match self {
            Self::RawPointerDeref { pointer_expr } => {
                format!("raw pointer dereference: {pointer_expr}")
            }
            Self::Transmute { from_ty, to_ty } => {
                format!("transmute from {from_ty} to {to_ty}")
            }
            Self::UnionAccess { union_name, field_name } => {
                format!("union field access: {union_name}.{field_name}")
            }
            Self::FfiCall { callee } => {
                format!("FFI call to {callee}")
            }
            Self::InlineAsm { label } => {
                format!("inline assembly: {label}")
            }
            Self::MutableStaticAccess { static_name } => {
                format!("mutable static access: {static_name}")
            }
        }
    }
}

/// A tagged unsafe verification condition, pairing the solver-facing VC with
/// the unsafe-specific categorization.
#[derive(Debug, Clone)]
pub struct UnsafeVc {
    /// The solver-facing verification condition.
    pub vc: VerificationCondition,
    /// The categorized unsafe operation that produced this VC.
    pub unsafe_kind: UnsafeVcKind,
}

/// Stateful verifier that generates VCs for all unsafe blocks in a function.
///
/// Accumulates context (detected blocks, safety comments, type info) and
/// produces a comprehensive set of VCs covering all unsafe operations.
pub struct UnsafeVerifier<'a> {
    func: &'a VerifiableFunction,
    blocks: Vec<UnsafeBlock>,
    comments: Vec<(SourceSpan, String)>,
}

impl<'a> UnsafeVerifier<'a> {
    /// Create a new verifier for the given function.
    #[must_use]
    pub fn new(func: &'a VerifiableFunction) -> Self {
        Self {
            func,
            blocks: detect_unsafe_blocks(func),
            comments: Vec::new(),
        }
    }

    /// Attach source comments for SAFETY claim extraction.
    #[must_use]
    pub fn with_comments(mut self, comments: Vec<(SourceSpan, String)>) -> Self {
        self.comments = comments;
        self
    }

    /// Number of detected unsafe blocks.
    #[must_use]
    pub fn block_count(&self) -> usize {
        self.blocks.len()
    }

    /// Generate all unsafe VCs, returning both the solver-facing VCs and their
    /// categorized unsafe kinds.
    #[must_use]
    pub fn generate(&mut self) -> Vec<UnsafeVc> {
        attach_safety_comments(&mut self.blocks, &self.comments);

        let mut result = Vec::new();

        // Existing safety-claim VCs
        let claim_vcs = generate_safety_vcs(self.func, &self.blocks);
        for vc in claim_vcs {
            let unsafe_kind = classify_vc_from_assertion(&vc);
            result.push(UnsafeVc { vc, unsafe_kind });
        }

        // Additional typed VCs from block analysis
        for block in &self.blocks {
            self.generate_block_vcs(block, &mut result);
        }

        result
    }

    /// Generate typed VCs for a single unsafe block.
    fn generate_block_vcs(&self, block: &UnsafeBlock, out: &mut Vec<UnsafeVc>) {
        let mir_block = self.func.body.blocks.iter().find(|b| b.id == block.block_id);
        let Some(mir_block) = mir_block else { return };

        // Check terminator for specific unsafe patterns
        if let Terminator::Call { func: callee, span, .. } = &mir_block.terminator {
            let lower = callee.to_lowercase();

            // Transmute detection
            if lower.contains("mem::transmute") {
                Self::emit_transmute_vcs(&self.func.name, callee, span, out);
            }

            // FFI call detection
            if lower.contains("::ffi::") || lower.contains("extern") {
                Self::emit_ffi_vcs(&self.func.name, callee, span, out);
            }
        }

        // Check statements for raw pointer derefs
        for stmt in &mir_block.stmts {
            if let Statement::Assign { rvalue, span, .. } = stmt
                && has_raw_deref(rvalue) {
                    Self::emit_raw_deref_vcs(&self.func.name, rvalue, span, out);
                }
        }
    }

    /// Emit VCs for a raw pointer dereference.
    fn emit_raw_deref_vcs(
        func_name: &str,
        rvalue: &Rvalue,
        span: &SourceSpan,
        out: &mut Vec<UnsafeVc>,
    ) {
        let ptr_expr = deref_operand_name(rvalue);
        let ptr_var = Formula::Var(format!("ptr_{ptr_expr}"), Sort::Int);

        // VC 1: Non-null check
        out.push(UnsafeVc {
            vc: VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!("[unsafe:deref] null check for *{ptr_expr}"),
                },
                function: func_name.to_string(),
                location: span.clone(),
                formula: Formula::Eq(
                    Box::new(ptr_var.clone()),
                    Box::new(Formula::Int(0)),
                ),
                contract_metadata: None,
            },
            unsafe_kind: UnsafeVcKind::RawPointerDeref {
                pointer_expr: format!("*{ptr_expr}"),
            },
        });

        // VC 2: Alignment check (ptr % align == 0)
        //
        // SOUNDNESS FIX (#165): The old code used an unconstrained `align_*`
        // variable. The solver could set align to 1 (everything is 1-aligned),
        // making `ptr % 1 == 0` trivially true, discharging the check
        // vacuously. Without actual type alignment info, we conservatively
        // report "cannot verify alignment".
        out.push(UnsafeVc {
            vc: VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!("[unsafe:deref] alignment check (unverified) for *{ptr_expr}"),
                },
                function: func_name.to_string(),
                location: span.clone(),
                // Always SAT = conservatively "cannot verify alignment"
                formula: Formula::Bool(true),
                contract_metadata: None,
            },
            unsafe_kind: UnsafeVcKind::RawPointerDeref {
                pointer_expr: format!("*{ptr_expr}"),
            },
        });

        // VC 3: Provenance/bounds check — pointer must be within allocation
        out.push(UnsafeVc {
            vc: VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!("[unsafe:deref] bounds check (unverified) for *{ptr_expr}"),
                },
                function: func_name.to_string(),
                location: span.clone(),
                // Always SAT = conservatively "cannot verify bounds"
                formula: Formula::Bool(true),
                contract_metadata: None,
            },
            unsafe_kind: UnsafeVcKind::RawPointerDeref {
                pointer_expr: format!("*{ptr_expr}"),
            },
        });
    }

    /// Emit VCs for a transmute call.
    fn emit_transmute_vcs(
        func_name: &str,
        _callee: &str,
        span: &SourceSpan,
        out: &mut Vec<UnsafeVc>,
    ) {
        let from_ty = "T_src".to_string();
        let to_ty = "T_dst".to_string();

        // VC 1: Layout compatibility — size_of::<Src>() == size_of::<Dst>()
        out.push(UnsafeVc {
            vc: VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "[unsafe:transmute] layout compatibility (unverified): size_of({from_ty}) == size_of({to_ty})"
                    ),
                },
                function: func_name.to_string(),
                location: span.clone(),
                // Always SAT = conservatively "cannot verify layout compatibility"
                formula: Formula::Bool(true),
                contract_metadata: None,
            },
            unsafe_kind: UnsafeVcKind::Transmute {
                from_ty: from_ty.clone(),
                to_ty: to_ty.clone(),
            },
        });

        // VC 2: Validity invariant — the bit pattern must be valid for the target type
        //
        // SOUNDNESS FIX (#165): The old code used an unconstrained boolean
        // `transmute_valid_*` wrapped in Not(). Solver trivially discharged
        // it by setting the var to true. Now conservatively always SAT.
        out.push(UnsafeVc {
            vc: VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "[unsafe:transmute] validity invariant (unverified): bit pattern valid for {to_ty}"
                    ),
                },
                function: func_name.to_string(),
                location: span.clone(),
                // Always SAT = conservatively "cannot verify validity"
                formula: Formula::Bool(true),
                contract_metadata: None,
            },
            unsafe_kind: UnsafeVcKind::Transmute { from_ty, to_ty },
        });
    }

    /// Emit VCs for an FFI call.
    fn emit_ffi_vcs(
        func_name: &str,
        callee: &str,
        span: &SourceSpan,
        out: &mut Vec<UnsafeVc>,
    ) {
        // VC 1: FFI precondition check
        //
        // SOUNDNESS FIX (#165): The old code used an unconstrained boolean
        // `ffi_precond_*` wrapped in Not(). Solver trivially discharged it.
        // Now conservatively always SAT = "cannot verify FFI precondition".
        out.push(UnsafeVc {
            vc: VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!("[unsafe:ffi] precondition (unverified) for {callee}"),
                },
                function: func_name.to_string(),
                location: span.clone(),
                formula: Formula::Bool(true),
                contract_metadata: None,
            },
            unsafe_kind: UnsafeVcKind::FfiCall {
                callee: callee.to_string(),
            },
        });

        // VC 2: FFI postcondition — return value satisfies expected invariant
        //
        // SOUNDNESS FIX (#165): Same unconstrained boolean pattern.
        // Conservatively always SAT = "cannot verify FFI postcondition".
        out.push(UnsafeVc {
            vc: VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!("[unsafe:ffi] postcondition (unverified) for {callee}"),
                },
                function: func_name.to_string(),
                location: span.clone(),
                formula: Formula::Bool(true),
                contract_metadata: None,
            },
            unsafe_kind: UnsafeVcKind::FfiCall {
                callee: callee.to_string(),
            },
        });

        // VC 3: FFI null pointer check on pointer-type arguments
        let null_var = Formula::Var(
            format!("ffi_ptr_arg_{}", callee.replace("::", "_")),
            Sort::Int,
        );
        out.push(UnsafeVc {
            vc: VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "[unsafe:ffi] null pointer argument check for {callee}"
                    ),
                },
                function: func_name.to_string(),
                location: span.clone(),
                formula: Formula::Eq(
                    Box::new(null_var),
                    Box::new(Formula::Int(0)),
                ),
                contract_metadata: None,
            },
            unsafe_kind: UnsafeVcKind::FfiCall {
                callee: callee.to_string(),
            },
        });
    }
}

/// Top-level entry point for comprehensive unsafe VC generation.
///
/// Returns categorized `UnsafeVc` items that include both the solver VC
/// and the `UnsafeVcKind` classification. This is the preferred API for
/// tools that need rich diagnostics; for the simple `Vec<VerificationCondition>`
/// path, use `check_unsafe()` instead.
#[must_use]
pub fn generate_unsafe_vcs(
    func: &VerifiableFunction,
    comments: &[(SourceSpan, String)],
) -> Vec<UnsafeVc> {
    let mut verifier = UnsafeVerifier::new(func)
        .with_comments(comments.to_vec());
    verifier.generate()
}

/// Classify a VC generated from a safety-claim assertion into an `UnsafeVcKind`.
fn classify_vc_from_assertion(vc: &VerificationCondition) -> UnsafeVcKind {
    let msg = match &vc.kind {
        VcKind::Assertion { message } => message.as_str(),
        _ => "",
    };
    let lower = msg.to_lowercase();

    if lower.contains("transmute") {
        UnsafeVcKind::Transmute {
            from_ty: "unknown".into(),
            to_ty: "unknown".into(),
        }
    } else if lower.contains("ffi") || lower.contains("extern") {
        UnsafeVcKind::FfiCall {
            callee: "unknown".into(),
        }
    } else {
        // Default: raw pointer deref (most common unsafe pattern)
        UnsafeVcKind::RawPointerDeref {
            pointer_expr: "unknown".into(),
        }
    }
}

/// Extract a human-readable operand name from a deref rvalue.
fn deref_operand_name(rvalue: &Rvalue) -> String {
    match rvalue {
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => {
            format!("_{}", place.local)
        }
        Rvalue::Ref { place, .. } => {
            format!("_{}", place.local)
        }
        _ => "unknown".to_string(),
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Existing functions (preserved from #79)
// ────────────────────────────────────────────────────────────────────────────

/// Detect unsafe blocks in a verifiable function.
///
/// In MIR, unsafe blocks manifest as Call terminators to functions that require
/// unsafe (e.g., `ptr::read`, `ptr::write`, `slice::from_raw_parts`), or
/// as blocks containing raw pointer dereferences (Deref projections on raw ptrs).
///
/// We also detect explicit unsafe annotations via the function's contracts
/// and trust annotations.
#[must_use]
pub fn detect_unsafe_blocks(func: &VerifiableFunction) -> Vec<UnsafeBlock> {
    let mut blocks = Vec::new();

    for block in &func.body.blocks {
        // Check for unsafe call patterns in the terminator
        if let Terminator::Call { func: callee, span, .. } = &block.terminator
            && is_unsafe_fn_call(callee) {
                blocks.push(UnsafeBlock {
                    span: span.clone(),
                    safety_comment: None,
                    safety_claim: None,
                    block_id: block.id,
                });
            }

        // Check for raw pointer dereferences in statements
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, span, .. } = stmt
                && has_raw_deref(rvalue) {
                    blocks.push(UnsafeBlock {
                        span: span.clone(),
                        safety_comment: None,
                        safety_claim: None,
                        block_id: block.id,
                    });
                }
        }
    }

    blocks
}

/// Attach safety comments to detected unsafe blocks.
///
/// In a full compiler integration, comments would come from the source map.
/// This function accepts pre-extracted comment text and matches them to blocks
/// by source span proximity.
pub fn attach_safety_comments(
    blocks: &mut [UnsafeBlock],
    comments: &[(SourceSpan, String)],
) {
    for block in blocks.iter_mut() {
        // Find the closest preceding SAFETY comment
        for (comment_span, text) in comments {
            if comment_span.file == block.span.file
                && comment_span.line_end <= block.span.line_start
                && block.span.line_start - comment_span.line_end <= 2
                && text.contains("SAFETY:")
            {
                block.safety_comment = Some(text.clone());
                block.safety_claim = Some(parse_safety_comment(text));
            }
        }
    }
}

/// Parse a `// SAFETY:` comment into a structured safety claim.
///
/// Expected format:
/// ```text
/// // SAFETY: <invariant>
/// // <justification>
/// ```
///
/// Or single-line:
/// ```text
/// // SAFETY: <invariant> because <justification>
/// ```
///
/// If only the invariant line is present, justification defaults to
/// "no justification provided".
#[must_use]
pub fn parse_safety_comment(comment: &str) -> SafetyClaim {
    // Strip comment markers and find the SAFETY: prefix
    let lines: Vec<&str> = comment
        .lines()
        .map(|line| line.trim().trim_start_matches("//").trim())
        .filter(|line| !line.is_empty())
        .collect();

    if lines.is_empty() {
        return SafetyClaim {
            invariant: String::new(),
            justification: "no justification provided".to_string(),
        };
    }

    // Find the line with SAFETY:
    let safety_idx = lines.iter().position(|line| {
        line.starts_with("SAFETY:") || line.starts_with("SAFETY :")
    });

    let safety_line = match safety_idx {
        Some(idx) => lines[idx],
        None => {
            // No SAFETY: prefix found, treat entire comment as invariant
            return SafetyClaim {
                invariant: lines.join(" "),
                justification: "no justification provided".to_string(),
            };
        }
    };

    // Extract the invariant (text after "SAFETY:")
    let after_safety = safety_line
        .trim_start_matches("SAFETY:")
        .trim_start_matches("SAFETY :")
        .trim();

    // Check for "because" separator in single-line format
    if let Some(because_idx) = after_safety.to_lowercase().find(" because ") {
        let invariant = after_safety[..because_idx].trim().to_string();
        let justification = after_safety[because_idx + 9..].trim().to_string();
        return SafetyClaim { invariant, justification };
    }

    let invariant = after_safety.to_string();

    // Justification is the remaining lines after the SAFETY: line
    let justification_lines: Vec<&str> = match safety_idx {
        Some(idx) => lines[idx + 1..].to_vec(),
        None => vec![],
    };

    let justification = if justification_lines.is_empty() {
        "no justification provided".to_string()
    } else {
        justification_lines.join(" ")
    };

    SafetyClaim { invariant, justification }
}

/// Generate verification conditions for unsafe blocks.
///
/// For each unsafe block with a parsed safety claim, we generate an Assertion
/// VC encoding the invariant. Unsafe blocks without safety comments get a
/// "missing SAFETY comment" assertion that is trivially satisfiable (always
/// a finding).
///
/// The convention is: Assertion VCs with `message` prefixed by `[unsafe]`
/// are from unsafe verification. This lets reporters distinguish them.
pub fn generate_safety_vcs(
    func: &VerifiableFunction,
    blocks: &[UnsafeBlock],
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    for block in blocks {
        match &block.safety_claim {
            Some(claim) if !claim.invariant.is_empty() => {
                // Generate a conservative VC for the claimed invariant.
                //
                // SOUNDNESS FIX (#165): The old code used an unconstrained
                // boolean variable `safety_invariant_N` wrapped in Not().
                // The solver could set it to true, making Not(true) = UNSAT,
                // which vacuously "proved" every safety claim without checking
                // anything. We now use Formula::Bool(true) as the violation
                // formula — always SAT — meaning this VC conservatively
                // reports "cannot mechanically verify this claim" unless
                // downstream analysis constrains it further.
                vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe] SAFETY claim (unverified): {}",
                            claim.invariant,
                        ),
                    },
                    function: func.name.clone(),
                    location: block.span.clone(),
                    // Always SAT = conservatively "cannot verify".
                    // A downstream pass with actual program constraints can
                    // strengthen this into a real check.
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                });

                // If the justification references nullability, generate
                // a non-null check VC.
                if claim.invariant.to_lowercase().contains("non-null")
                    || claim.invariant.to_lowercase().contains("not null")
                    || claim.invariant.to_lowercase().contains("nonnull")
                {
                    vcs.push(VerificationCondition {
                        kind: VcKind::Assertion {
                            message: format!(
                                "[unsafe] null pointer check for: {}",
                                claim.invariant,
                            ),
                        },
                        function: func.name.clone(),
                        location: block.span.clone(),
                        formula: Formula::Eq(
                            Box::new(Formula::Var(
                                format!("ptr_{}", block.block_id.0),
                                Sort::Int,
                            )),
                            Box::new(Formula::Int(0)),
                        ),
                        contract_metadata: None,
                    });
                }

                // If the justification references alignment, generate
                // an alignment check VC.
                if claim.invariant.to_lowercase().contains("align") {
                    vcs.push(VerificationCondition {
                        kind: VcKind::Assertion {
                            message: format!(
                                "[unsafe] alignment check (unverified) for: {}",
                                claim.invariant,
                            ),
                        },
                        function: func.name.clone(),
                        location: block.span.clone(),
                        formula: Formula::Bool(true),
                        contract_metadata: None,
                    });
                }
            }
            _ => {
                // No safety claim: generate a "missing comment" assertion.
                // This is always SAT (Bool(true)) = always a finding.
                vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: "[unsafe] missing SAFETY comment on unsafe block".to_string(),
                    },
                    function: func.name.clone(),
                    location: block.span.clone(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                });
            }
        }
    }

    vcs
}

/// Check whether a function call name refers to an inherently unsafe function.
fn is_unsafe_fn_call(callee: &str) -> bool {
    const UNSAFE_PATTERNS: &[&str] = &[
        // Core pointer operations
        "ptr::read",
        "ptr::write",
        "ptr::read_volatile",
        "ptr::write_volatile",
        "ptr::copy",
        "ptr::copy_nonoverlapping",
        "ptr::swap",
        "ptr::replace",
        "ptr::drop_in_place",
        "ptr::read_unaligned",
        "ptr::write_unaligned",
        // Slice from raw parts
        "slice::from_raw_parts",
        "slice::from_raw_parts_mut",
        // String from raw
        "str::from_utf8_unchecked",
        "String::from_raw_parts",
        // Transmute
        "mem::transmute",
        "mem::transmute_copy",
        "mem::zeroed",
        "mem::uninitialized",
        // Alloc
        "alloc::alloc",
        "alloc::dealloc",
        "alloc::realloc",
        // Intrinsics
        "intrinsics::",
        // FFI / extern calls (heuristic: contains "extern" or "ffi")
        "::ffi::",
    ];

    let lower = callee.to_lowercase();
    UNSAFE_PATTERNS.iter().any(|p| lower.contains(&p.to_lowercase()))
}

/// Check whether an rvalue contains a raw pointer dereference.
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

/// Top-level entry point: check a function for unsafe code and generate VCs.
///
/// Called from `generate_vcs` in lib.rs. Detects unsafe blocks, attaches
/// safety comments (when available), and generates assertion VCs.
pub(crate) fn check_unsafe(
    func: &VerifiableFunction,
    comments: &[(SourceSpan, String)],
    vcs: &mut Vec<VerificationCondition>,
) {
    let mut blocks = detect_unsafe_blocks(func);
    if blocks.is_empty() {
        return;
    }

    attach_safety_comments(&mut blocks, comments);
    let safety_vcs = generate_safety_vcs(func, &blocks);
    vcs.extend(safety_vcs);
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::fx::FxHashSet;

    fn collect_free_vars(formula: &Formula) -> FxHashSet<String> {
        let mut vars = FxHashSet::default();
        collect_vars_recursive(formula, &mut vars);
        vars
    }

    fn collect_vars_recursive(formula: &Formula, vars: &mut FxHashSet<String>) {
        match formula {
            Formula::Var(name, _) => {
                vars.insert(name.clone());
            }
            _ => {
                for child in formula.children() {
                    collect_vars_recursive(child, vars);
                }
            }
        }
    }

    fn is_conservative_or_concrete_check(formula: &Formula) -> bool {
        match formula {
            Formula::Bool(true) | Formula::Bool(false) => true,
            Formula::Eq(lhs, rhs) => {
                !matches!(lhs.as_ref(), Formula::Var(_, _))
                    || !matches!(rhs.as_ref(), Formula::Var(_, _))
            }
            _ => false,
        }
    }

    /// Build a function with an unsafe ptr::read call.
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

    /// Build a function with a raw pointer deref in a statement.
    fn unsafe_deref_function() -> VerifiableFunction {
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

    /// Build a safe function with no unsafe blocks.
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

    /// Build a function with a transmute call.
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

    /// Build a function with an FFI call.
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
                                file: "test.rs".into(),
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

    // ── Existing tests (preserved) ──────────────────────────────────────

    #[test]
    fn test_detect_unsafe_blocks_ptr_read() {
        let func = unsafe_ptr_read_function();
        let blocks = detect_unsafe_blocks(&func);
        assert_eq!(blocks.len(), 1, "should detect 1 unsafe block for ptr::read");
        assert_eq!(blocks[0].block_id, BlockId(0));
        assert_eq!(blocks[0].span.line_start, 10);
    }

    #[test]
    fn test_detect_unsafe_blocks_deref() {
        let func = unsafe_deref_function();
        let blocks = detect_unsafe_blocks(&func);
        assert_eq!(blocks.len(), 1, "should detect 1 unsafe block for raw deref");
        assert_eq!(blocks[0].block_id, BlockId(0));
    }

    #[test]
    fn test_detect_unsafe_blocks_safe_function() {
        let func = safe_function();
        let blocks = detect_unsafe_blocks(&func);
        assert!(blocks.is_empty(), "safe function should have no unsafe blocks");
    }

    #[test]
    fn test_parse_safety_comment_single_line_because() {
        let comment = "// SAFETY: pointer is non-null because we checked it above";
        let claim = parse_safety_comment(comment);
        assert_eq!(claim.invariant, "pointer is non-null");
        assert_eq!(claim.justification, "we checked it above");
    }

    #[test]
    fn test_parse_safety_comment_multiline() {
        let comment = "// SAFETY: pointer is valid and aligned\n// the caller guarantees this via the function contract";
        let claim = parse_safety_comment(comment);
        assert_eq!(claim.invariant, "pointer is valid and aligned");
        assert_eq!(
            claim.justification,
            "the caller guarantees this via the function contract"
        );
    }

    #[test]
    fn test_parse_safety_comment_invariant_only() {
        let comment = "// SAFETY: pointer is non-null";
        let claim = parse_safety_comment(comment);
        assert_eq!(claim.invariant, "pointer is non-null");
        assert_eq!(claim.justification, "no justification provided");
    }

    #[test]
    fn test_parse_safety_comment_empty() {
        let claim = parse_safety_comment("");
        assert!(claim.invariant.is_empty());
        assert_eq!(claim.justification, "no justification provided");
    }

    #[test]
    fn test_parse_safety_comment_no_prefix() {
        let comment = "// this is just a regular comment";
        let claim = parse_safety_comment(comment);
        // No SAFETY: prefix, so the whole comment becomes invariant
        assert_eq!(claim.invariant, "this is just a regular comment");
        assert_eq!(claim.justification, "no justification provided");
    }

    #[test]
    fn test_generate_safety_vcs_with_claim() {
        let func = unsafe_ptr_read_function();
        let blocks = vec![UnsafeBlock {
            span: SourceSpan {
                file: "test.rs".into(),
                line_start: 10,
                col_start: 8,
                line_end: 10,
                col_end: 30,
            },
            safety_comment: Some("// SAFETY: pointer is non-null and aligned".into()),
            safety_claim: Some(SafetyClaim {
                invariant: "pointer is non-null and aligned".to_string(),
                justification: "no justification provided".to_string(),
            }),
            block_id: BlockId(0),
        }];

        let vcs = generate_safety_vcs(&func, &blocks);

        // Should produce: invariant VC + null check VC + alignment check VC
        assert_eq!(vcs.len(), 3, "claim with non-null + aligned = 3 VCs");

        // First VC: the invariant assertion
        assert!(matches!(&vcs[0].kind, VcKind::Assertion { message } if message.contains("[unsafe]")));
        assert!(matches!(&vcs[0].kind, VcKind::Assertion { message } if message.contains("SAFETY claim")));

        // Second VC: null pointer check
        assert!(matches!(&vcs[1].kind, VcKind::Assertion { message } if message.contains("null pointer check")));

        // Third VC: alignment check
        assert!(matches!(&vcs[2].kind, VcKind::Assertion { message } if message.contains("alignment check")));

        // All should be L0Safety level
        for vc in &vcs {
            assert_eq!(vc.kind.proof_level(), ProofLevel::L0Safety);
        }
    }

    #[test]
    fn test_safety_claim_vc_not_vacuously_true() {
        let func = unsafe_ptr_read_function();
        let blocks = vec![UnsafeBlock {
            span: SourceSpan {
                file: "test.rs".into(),
                line_start: 10,
                col_start: 8,
                line_end: 10,
                col_end: 30,
            },
            safety_comment: Some("// SAFETY: pointer is aligned".into()),
            safety_claim: Some(SafetyClaim {
                invariant: "pointer is aligned".to_string(),
                justification: "caller guarantees it".to_string(),
            }),
            block_id: BlockId(0),
        }];

        let vcs = generate_safety_vcs(&func, &blocks);
        assert_eq!(vcs.len(), 2, "claim + alignment check = 2 VCs");

        let alignment_vc = vcs
            .iter()
            .find(|vc| {
                matches!(
                    &vc.kind,
                    VcKind::Assertion { message } if message.contains("alignment check")
                )
            })
            .expect("alignment VC present");
        assert!(matches!(alignment_vc.formula, Formula::Bool(true)));
        assert!(matches!(
            &alignment_vc.kind,
            VcKind::Assertion { message } if message.contains("(unverified)")
        ));

        for vc in &vcs {
            let vars = collect_free_vars(&vc.formula);
            assert!(
                matches!(vc.formula, Formula::Bool(true) | Formula::Bool(false)) || vars.is_empty(),
                "safety claim VC should not leave free vars in a trivially dischargeable formula: {:?}",
                vc.formula
            );
        }
    }

    #[test]
    fn test_generate_safety_vcs_without_claim() {
        let func = unsafe_ptr_read_function();
        let blocks = vec![UnsafeBlock {
            span: SourceSpan::default(),
            safety_comment: None,
            safety_claim: None,
            block_id: BlockId(0),
        }];

        let vcs = generate_safety_vcs(&func, &blocks);

        assert_eq!(vcs.len(), 1, "missing claim should produce 1 VC");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::Assertion { message } if message.contains("missing SAFETY comment")
        ));
        // Missing SAFETY comment VC is always SAT (finding)
        assert!(matches!(vcs[0].formula, Formula::Bool(true)));
    }

    #[test]
    fn test_generate_safety_vcs_empty() {
        let func = safe_function();
        let blocks: Vec<UnsafeBlock> = vec![];
        let vcs = generate_safety_vcs(&func, &blocks);
        assert!(vcs.is_empty(), "no unsafe blocks = no VCs");
    }

    #[test]
    fn test_attach_safety_comments_matches_by_span() {
        let mut blocks = vec![UnsafeBlock {
            span: SourceSpan {
                file: "test.rs".into(),
                line_start: 10,
                col_start: 8,
                line_end: 10,
                col_end: 30,
            },
            safety_comment: None,
            safety_claim: None,
            block_id: BlockId(0),
        }];

        let comments = vec![(
            SourceSpan {
                file: "test.rs".into(),
                line_start: 8,
                col_start: 4,
                line_end: 9,
                col_end: 50,
            },
            "// SAFETY: pointer is valid because caller guarantees it".to_string(),
        )];

        attach_safety_comments(&mut blocks, &comments);

        assert!(blocks[0].safety_comment.is_some());
        assert!(blocks[0].safety_claim.is_some());
        let claim = blocks[0].safety_claim.as_ref().unwrap();
        assert_eq!(claim.invariant, "pointer is valid");
        assert_eq!(claim.justification, "caller guarantees it");
    }

    #[test]
    fn test_attach_safety_comments_no_match_wrong_file() {
        let mut blocks = vec![UnsafeBlock {
            span: SourceSpan {
                file: "test.rs".into(),
                line_start: 10,
                col_start: 0,
                line_end: 10,
                col_end: 30,
            },
            safety_comment: None,
            safety_claim: None,
            block_id: BlockId(0),
        }];

        let comments = vec![(
            SourceSpan {
                file: "other.rs".into(),
                line_start: 9,
                col_start: 0,
                line_end: 9,
                col_end: 50,
            },
            "// SAFETY: this is in another file".to_string(),
        )];

        attach_safety_comments(&mut blocks, &comments);
        assert!(blocks[0].safety_comment.is_none(), "wrong file should not match");
    }

    #[test]
    fn test_attach_safety_comments_no_match_too_far() {
        let mut blocks = vec![UnsafeBlock {
            span: SourceSpan {
                file: "test.rs".into(),
                line_start: 20,
                col_start: 0,
                line_end: 20,
                col_end: 30,
            },
            safety_comment: None,
            safety_claim: None,
            block_id: BlockId(0),
        }];

        let comments = vec![(
            SourceSpan {
                file: "test.rs".into(),
                line_start: 5,
                col_start: 0,
                line_end: 5,
                col_end: 50,
            },
            "// SAFETY: too far away".to_string(),
        )];

        attach_safety_comments(&mut blocks, &comments);
        assert!(blocks[0].safety_comment.is_none(), "comment too far should not match");
    }

    #[test]
    fn test_is_unsafe_fn_call() {
        assert!(is_unsafe_fn_call("core::ptr::read"));
        assert!(is_unsafe_fn_call("std::ptr::write"));
        assert!(is_unsafe_fn_call("core::slice::from_raw_parts"));
        assert!(is_unsafe_fn_call("std::mem::transmute"));
        assert!(is_unsafe_fn_call("core::intrinsics::copy"));
        assert!(is_unsafe_fn_call("some::ffi::extern_call"));
        assert!(is_unsafe_fn_call("alloc::alloc::alloc"));
        assert!(is_unsafe_fn_call("std::str::from_utf8_unchecked"));
        assert!(!is_unsafe_fn_call("std::vec::Vec::push"));
        assert!(!is_unsafe_fn_call("core::result::Result::unwrap"));
    }

    #[test]
    fn test_has_raw_deref() {
        assert!(has_raw_deref(&Rvalue::Use(Operand::Copy(Place {
            local: 1,
            projections: vec![Projection::Deref],
        }))));

        assert!(!has_raw_deref(&Rvalue::Use(Operand::Copy(Place::local(1)))));

        assert!(has_raw_deref(&Rvalue::Ref {
            mutable: false,
            place: Place {
                local: 1,
                projections: vec![Projection::Deref],
            },
        }));
    }

    #[test]
    fn test_check_unsafe_integration() {
        let func = unsafe_ptr_read_function();
        let comments = vec![(
            SourceSpan {
                file: "test.rs".into(),
                line_start: 9,
                col_start: 4,
                line_end: 9,
                col_end: 60,
            },
            "// SAFETY: pointer is non-null because allocated on the heap".to_string(),
        )];

        let mut vcs = Vec::new();
        check_unsafe(&func, &comments, &mut vcs);

        // Should have VCs from the unsafe block with the attached comment
        assert!(!vcs.is_empty(), "should generate VCs for unsafe block");
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::Assertion { message } if message.contains("[unsafe]")
            )),
            "should have [unsafe] tagged assertions"
        );
    }

    #[test]
    fn test_check_unsafe_safe_function_no_vcs() {
        let func = safe_function();
        let mut vcs = Vec::new();
        check_unsafe(&func, &[], &mut vcs);
        assert!(vcs.is_empty(), "safe function should produce no unsafe VCs");
    }

    #[test]
    fn test_check_unsafe_no_comments_produces_missing_vc() {
        let func = unsafe_ptr_read_function();
        let mut vcs = Vec::new();
        check_unsafe(&func, &[], &mut vcs);

        assert_eq!(vcs.len(), 1, "unsafe block without comment = 1 missing-comment VC");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::Assertion { message } if message.contains("missing SAFETY comment")
        ));
    }

    // ── New tests (#137): UnsafeVcKind, UnsafeVerifier, generate_unsafe_vcs ──

    #[test]
    fn test_unsafe_vc_kind_descriptions() {
        let deref = UnsafeVcKind::RawPointerDeref {
            pointer_expr: "*ptr".into(),
        };
        assert_eq!(deref.description(), "raw pointer dereference: *ptr");

        let transmute = UnsafeVcKind::Transmute {
            from_ty: "u32".into(),
            to_ty: "i32".into(),
        };
        assert_eq!(transmute.description(), "transmute from u32 to i32");

        let union_access = UnsafeVcKind::UnionAccess {
            union_name: "MyUnion".into(),
            field_name: "value".into(),
        };
        assert_eq!(union_access.description(), "union field access: MyUnion.value");

        let ffi = UnsafeVcKind::FfiCall {
            callee: "libc::write".into(),
        };
        assert_eq!(ffi.description(), "FFI call to libc::write");

        let asm = UnsafeVcKind::InlineAsm {
            label: "cpuid".into(),
        };
        assert_eq!(asm.description(), "inline assembly: cpuid");

        let mutable_static = UnsafeVcKind::MutableStaticAccess {
            static_name: "GLOBAL_STATE".into(),
        };
        assert_eq!(
            mutable_static.description(),
            "mutable static access: GLOBAL_STATE"
        );
    }

    #[test]
    fn test_unsafe_vc_kind_serialization_roundtrip() {
        let kinds = vec![
            UnsafeVcKind::RawPointerDeref { pointer_expr: "*p".into() },
            UnsafeVcKind::Transmute { from_ty: "u32".into(), to_ty: "f32".into() },
            UnsafeVcKind::UnionAccess { union_name: "U".into(), field_name: "f".into() },
            UnsafeVcKind::FfiCall { callee: "libc::read".into() },
            UnsafeVcKind::InlineAsm { label: "nop".into() },
            UnsafeVcKind::MutableStaticAccess { static_name: "G".into() },
        ];

        for kind in &kinds {
            let json = serde_json::to_string(kind).expect("serialize UnsafeVcKind");
            let round: UnsafeVcKind = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(&round, kind);
        }
    }

    #[test]
    fn test_unsafe_verifier_safe_function_empty() {
        let func = safe_function();
        let mut verifier = UnsafeVerifier::new(&func);
        assert_eq!(verifier.block_count(), 0);
        let vcs = verifier.generate();
        assert!(vcs.is_empty(), "safe function produces no unsafe VCs");
    }

    #[test]
    fn test_unsafe_verifier_ptr_read_no_comments() {
        let func = unsafe_ptr_read_function();
        let mut verifier = UnsafeVerifier::new(&func);
        assert_eq!(verifier.block_count(), 1);
        let vcs = verifier.generate();

        // Should have: 1 missing-comment VC (from claim pass)
        // No typed VCs for ptr::read call (not a deref in stmts, it's a Call terminator)
        assert!(
            vcs.iter().any(|uvc| matches!(
                &uvc.vc.kind,
                VcKind::Assertion { message } if message.contains("missing SAFETY comment")
            )),
            "should have missing-comment VC"
        );
    }

    #[test]
    fn test_unsafe_verifier_deref_generates_typed_vcs() {
        let func = unsafe_deref_function();
        let mut verifier = UnsafeVerifier::new(&func);
        assert_eq!(verifier.block_count(), 1);
        let vcs = verifier.generate();

        // Claim pass: 1 missing-comment VC
        // Typed pass: 3 VCs (null, alignment, bounds) for the deref
        assert_eq!(vcs.len(), 4, "1 missing-comment + 3 deref VCs = 4 total");

        // Check typed VCs
        let deref_vcs: Vec<_> = vcs
            .iter()
            .filter(|uvc| matches!(&uvc.unsafe_kind, UnsafeVcKind::RawPointerDeref { .. }))
            .collect();
        assert_eq!(deref_vcs.len(), 4, "all 4 VCs should be RawPointerDeref");

        // Check VC messages
        let messages: Vec<_> = vcs.iter().map(|uvc| {
            match &uvc.vc.kind {
                VcKind::Assertion { message } => message.clone(),
                _ => String::new(),
            }
        }).collect();

        assert!(messages.iter().any(|m| m.contains("null check")));
        assert!(messages.iter().any(|m| m.contains("alignment check")));
        assert!(messages.iter().any(|m| m.contains("bounds check")));
    }

    #[test]
    fn test_no_unconstrained_vars_in_deref_vcs() {
        let func = unsafe_deref_function();
        let mut verifier = UnsafeVerifier::new(&func);
        let vcs = verifier.generate();

        let deref_vcs: Vec<_> = vcs
            .iter()
            .filter(|unsafe_vc| {
                matches!(&unsafe_vc.unsafe_kind, UnsafeVcKind::RawPointerDeref { .. })
            })
            .collect();
        assert!(!deref_vcs.is_empty(), "expected raw deref VCs");

        let bounds_vc = deref_vcs
            .iter()
            .find(|unsafe_vc| {
                matches!(
                    &unsafe_vc.vc.kind,
                    VcKind::Assertion { message } if message.contains("bounds check")
                )
            })
            .expect("bounds VC present");
        assert!(matches!(bounds_vc.vc.formula, Formula::Bool(true)));
        assert!(matches!(
            &bounds_vc.vc.kind,
            VcKind::Assertion { message } if message.contains("(unverified)")
        ));

        for unsafe_vc in &deref_vcs {
            let vars = collect_free_vars(&unsafe_vc.vc.formula);
            if !vars.is_empty() {
                assert!(
                    is_conservative_or_concrete_check(&unsafe_vc.vc.formula),
                    "deref VC contains unconstrained vars in unsafe shape: {:?}",
                    unsafe_vc.vc.formula
                );
            }
        }
    }

    #[test]
    fn test_unsafe_verifier_transmute_generates_layout_and_validity_vcs() {
        let func = transmute_function();
        let mut verifier = UnsafeVerifier::new(&func);
        assert_eq!(verifier.block_count(), 1);
        let vcs = verifier.generate();

        // Should have:
        // 1 missing-comment VC (from claim pass)
        // 2 transmute VCs (layout + validity)
        let transmute_vcs: Vec<_> = vcs
            .iter()
            .filter(|uvc| matches!(&uvc.unsafe_kind, UnsafeVcKind::Transmute { .. }))
            .collect();
        assert!(transmute_vcs.len() >= 2, "should have at least 2 transmute VCs");

        let messages: Vec<_> = transmute_vcs.iter().map(|uvc| {
            match &uvc.vc.kind {
                VcKind::Assertion { message } => message.clone(),
                _ => String::new(),
            }
        }).collect();
        assert!(messages.iter().any(|m| m.contains("layout compatibility")));
        assert!(messages.iter().any(|m| m.contains("validity invariant")));
    }

    #[test]
    fn test_no_unconstrained_vars_in_transmute_vcs() {
        let func = transmute_function();
        let mut verifier = UnsafeVerifier::new(&func);
        let vcs = verifier.generate();

        let transmute_vcs: Vec<_> = vcs
            .iter()
            .filter(|unsafe_vc| matches!(&unsafe_vc.unsafe_kind, UnsafeVcKind::Transmute { .. }))
            .collect();
        assert!(!transmute_vcs.is_empty(), "expected transmute VCs");

        let layout_vc = transmute_vcs
            .iter()
            .find(|unsafe_vc| {
                matches!(
                    &unsafe_vc.vc.kind,
                    VcKind::Assertion { message } if message.contains("layout compatibility")
                )
            })
            .expect("layout VC present");
        assert!(matches!(layout_vc.vc.formula, Formula::Bool(true)));
        assert!(matches!(
            &layout_vc.vc.kind,
            VcKind::Assertion { message } if message.contains("(unverified)")
        ));

        for unsafe_vc in &transmute_vcs {
            let vars = collect_free_vars(&unsafe_vc.vc.formula);
            if !vars.is_empty() {
                assert!(
                    is_conservative_or_concrete_check(&unsafe_vc.vc.formula),
                    "transmute VC contains unconstrained vars in unsafe shape: {:?}",
                    unsafe_vc.vc.formula
                );
            }
        }
    }

    #[test]
    fn test_unsafe_verifier_ffi_generates_pre_post_null_vcs() {
        let func = ffi_function();
        let mut verifier = UnsafeVerifier::new(&func);
        assert_eq!(verifier.block_count(), 1);
        let vcs = verifier.generate();

        let ffi_vcs: Vec<_> = vcs
            .iter()
            .filter(|uvc| matches!(&uvc.unsafe_kind, UnsafeVcKind::FfiCall { .. }))
            .collect();
        assert!(ffi_vcs.len() >= 3, "should have at least 3 FFI VCs");

        let messages: Vec<_> = ffi_vcs.iter().map(|uvc| {
            match &uvc.vc.kind {
                VcKind::Assertion { message } => message.clone(),
                _ => String::new(),
            }
        }).collect();
        assert!(messages.iter().any(|m| m.contains("precondition")));
        assert!(messages.iter().any(|m| m.contains("postcondition")));
        assert!(messages.iter().any(|m| m.contains("null pointer argument")));
    }

    #[test]
    fn test_no_unconstrained_vars_in_ffi_vcs() {
        let func = ffi_function();
        let mut verifier = UnsafeVerifier::new(&func);
        let vcs = verifier.generate();

        let ffi_vcs: Vec<_> = vcs
            .iter()
            .filter(|unsafe_vc| matches!(&unsafe_vc.unsafe_kind, UnsafeVcKind::FfiCall { .. }))
            .collect();
        assert!(!ffi_vcs.is_empty(), "expected FFI VCs");

        for unsafe_vc in &ffi_vcs {
            let vars = collect_free_vars(&unsafe_vc.vc.formula);
            if !vars.is_empty() {
                assert!(
                    is_conservative_or_concrete_check(&unsafe_vc.vc.formula),
                    "FFI VC contains unconstrained vars in unsafe shape: {:?}",
                    unsafe_vc.vc.formula
                );
            }
        }
    }

    #[test]
    fn test_generate_unsafe_vcs_entry_point() {
        let func = unsafe_deref_function();
        let vcs = generate_unsafe_vcs(&func, &[]);

        assert!(!vcs.is_empty(), "should produce VCs for unsafe function");
        // All VCs should have an unsafe_kind
        for uvc in &vcs {
            let _ = uvc.unsafe_kind.description();
        }
    }

    #[test]
    fn test_generate_unsafe_vcs_with_comments() {
        let func = unsafe_ptr_read_function();
        let comments = vec![(
            SourceSpan {
                file: "test.rs".into(),
                line_start: 9,
                col_start: 4,
                line_end: 9,
                col_end: 60,
            },
            "// SAFETY: pointer is non-null because allocated on the heap".to_string(),
        )];

        let vcs = generate_unsafe_vcs(&func, &comments);

        // With a matching comment, we should get claim VCs (not missing-comment)
        assert!(
            vcs.iter().any(|uvc| matches!(
                &uvc.vc.kind,
                VcKind::Assertion { message } if message.contains("SAFETY claim")
            )),
            "should have SAFETY claim VC"
        );
        assert!(
            !vcs.iter().any(|uvc| matches!(
                &uvc.vc.kind,
                VcKind::Assertion { message } if message.contains("missing SAFETY comment")
            )),
            "should NOT have missing-comment VC when comment is present"
        );
    }

    #[test]
    fn test_unsafe_verifier_with_comments_builder() {
        let func = unsafe_ptr_read_function();
        let comments = vec![(
            SourceSpan {
                file: "test.rs".into(),
                line_start: 9,
                col_start: 4,
                line_end: 9,
                col_end: 60,
            },
            "// SAFETY: pointer is non-null because allocated on the heap".to_string(),
        )];

        let mut verifier = UnsafeVerifier::new(&func).with_comments(comments);
        assert_eq!(verifier.block_count(), 1);
        let vcs = verifier.generate();
        assert!(!vcs.is_empty());
    }

    #[test]
    fn test_classify_vc_from_assertion_transmute() {
        let vc = VerificationCondition {
            kind: VcKind::Assertion {
                message: "[unsafe:transmute] layout check".into(),
            },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let kind = classify_vc_from_assertion(&vc);
        assert!(matches!(kind, UnsafeVcKind::Transmute { .. }));
    }

    #[test]
    fn test_classify_vc_from_assertion_ffi() {
        let vc = VerificationCondition {
            kind: VcKind::Assertion {
                message: "[unsafe] FFI precondition".into(),
            },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let kind = classify_vc_from_assertion(&vc);
        assert!(matches!(kind, UnsafeVcKind::FfiCall { .. }));
    }

    #[test]
    fn test_classify_vc_from_assertion_default() {
        let vc = VerificationCondition {
            kind: VcKind::Assertion {
                message: "[unsafe] something generic".into(),
            },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let kind = classify_vc_from_assertion(&vc);
        assert!(matches!(kind, UnsafeVcKind::RawPointerDeref { .. }));
    }

    #[test]
    fn test_deref_operand_name() {
        let rvalue = Rvalue::Use(Operand::Copy(Place {
            local: 5,
            projections: vec![Projection::Deref],
        }));
        assert_eq!(deref_operand_name(&rvalue), "_5");

        let rvalue_ref = Rvalue::Ref {
            mutable: false,
            place: Place { local: 3, projections: vec![Projection::Deref] },
        };
        assert_eq!(deref_operand_name(&rvalue_ref), "_3");

        let rvalue_other = Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
        );
        assert_eq!(deref_operand_name(&rvalue_other), "unknown");
    }
}
