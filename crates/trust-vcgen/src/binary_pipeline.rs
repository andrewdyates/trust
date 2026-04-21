// trust-vcgen/binary_pipeline.rs: Unified binary analysis pipeline
//
// Combines binary lifting, type recovery, pattern detection, and security VC
// generation into a single pipeline. This is the main entry point for
// analyzing binary code through the verification pipeline.
//
// Pipeline stages:
//   1. Lift binary to abstract MIR (lifter.rs)
//   2. Recover types from usage patterns (type_recovery.rs + patterns.rs)
//   3. Detect security-relevant patterns (patterns.rs)
//   4. Generate security VCs (security_vcs.rs)
//
// tRust #565: Canonical binary verification pipeline:
//   trust-binary-parse -> trust-disasm -> trust-machine-sem -> trust-lift
//   -> trust-type-recover -> trust-decompile
//
// Entry point: analyze_lifted_binary() accepts a LiftedFunction from trust-lift
// and runs both security analysis (buffer overflow, UAF, format string, etc.)
// and memory model analysis (OOB, stack discipline).
//
// Legacy entry points (analyze_binary, analyze_binary_default) accept the
// older LiftedProgram format and will be removed in a future version.
//
// Part of #148: Binary analysis pipeline
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::*;

use crate::binary_analysis::lifter::{LiftError, LiftedProgram, lift_to_mir};
use crate::binary_analysis::patterns::{
    BinaryPattern, RecoveredType, detect_binary_patterns, recover_types,
};
use crate::binary_analysis::type_recovery::{
    RecoveredSignature, StructLayout, recover_signature, recover_struct_layouts,
};
use crate::security_vcs::{SecurityVc, generate_security_vcs};

// ────────────────────────────────────────────────────────────────────────────
// Pipeline result
// ────────────────────────────────────────────────────────────────────────────

/// Complete result of the binary analysis pipeline.
#[derive(Debug, Clone)]
pub struct BinaryAnalysisResult {
    /// The lifted MIR function.
    pub function: VerifiableFunction,
    /// Recovered function signature.
    pub signature: RecoveredSignature,
    /// Recovered struct layouts from memory access patterns.
    pub struct_layouts: Vec<StructLayout>,
    /// Detected security-relevant patterns.
    pub patterns: Vec<BinaryPattern>,
    /// Recovered types from usage analysis.
    pub recovered_types: Vec<RecoveredType>,
    /// Generated security VCs.
    pub security_vcs: Vec<SecurityVc>,
    /// Standard VCs from the lifted MIR.
    pub standard_vcs: Vec<VerificationCondition>,
}

impl BinaryAnalysisResult {
    /// Total number of VCs (security + standard).
    #[must_use]
    pub fn total_vc_count(&self) -> usize {
        self.security_vcs.len() + self.standard_vcs.len()
    }

    /// All VCs combined (security VCs unwrapped + standard VCs).
    #[must_use]
    pub fn all_vcs(&self) -> Vec<VerificationCondition> {
        let mut vcs: Vec<VerificationCondition> = self
            .security_vcs
            .iter()
            .map(|svc| svc.vc.clone())
            .collect();
        vcs.extend(self.standard_vcs.iter().cloned());
        vcs
    }

    /// Whether any security patterns were detected.
    #[must_use]
    pub fn has_security_findings(&self) -> bool {
        !self.security_vcs.is_empty()
    }
}

/// Errors from the binary analysis pipeline.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum BinaryPipelineError {
    /// Lifting failed.
    #[error("binary lifting failed: {0}")]
    LiftError(#[from] LiftError),
}

// ────────────────────────────────────────────────────────────────────────────
// Pipeline configuration
// ────────────────────────────────────────────────────────────────────────────

/// Configuration for the binary analysis pipeline.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BinaryPipelineConfig {
    /// Whether to generate standard MIR-level VCs (overflow, divzero, etc.).
    pub generate_standard_vcs: bool,
    /// Whether to run type recovery on the lifted program.
    pub enable_type_recovery: bool,
    /// Whether to generate security-focused VCs.
    pub enable_security_vcs: bool,
    /// Minimum severity threshold for security VCs (1-10).
    pub min_severity: u8,
}

impl Default for BinaryPipelineConfig {
    fn default() -> Self {
        Self {
            generate_standard_vcs: true,
            enable_type_recovery: true,
            enable_security_vcs: true,
            min_severity: 1,
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Pipeline entry points
// ────────────────────────────────────────────────────────────────────────────

/// Run the full binary analysis pipeline on a lifted program.
///
/// This is the main entry point. It lifts the binary to MIR, recovers types,
/// detects patterns, and generates both standard and security VCs.
pub fn analyze_binary(
    program: &LiftedProgram,
    config: &BinaryPipelineConfig,
) -> Result<BinaryAnalysisResult, BinaryPipelineError> {
    // Stage 1: Lift to MIR
    let function = lift_to_mir(program)?;

    // Stage 2: Recover types
    let signature = if config.enable_type_recovery {
        recover_signature(program)
    } else {
        RecoveredSignature {
            name: function.name.clone(),
            params: vec![],
            return_ty: crate::binary_analysis::type_recovery::RecoveredTy::Void,
            calling_convention: crate::binary_analysis::type_recovery::CallingConvention::Unknown,
        }
    };

    let struct_layouts = if config.enable_type_recovery {
        recover_struct_layouts(program)
    } else {
        vec![]
    };

    // Stage 3: Detect patterns and recover types from MIR
    let patterns = detect_binary_patterns(&function);
    let recovered_types = recover_types(&function);

    // Stage 4: Generate security VCs
    let mut security_vcs = if config.enable_security_vcs {
        generate_security_vcs(&function, &patterns, &recovered_types)
    } else {
        vec![]
    };

    // Apply severity filter
    if config.min_severity > 1 {
        security_vcs.retain(|svc| svc.property.severity() >= config.min_severity);
    }

    // Stage 5: Generate standard VCs
    let standard_vcs = if config.generate_standard_vcs {
        crate::generate_vcs(&function)
    } else {
        vec![]
    };

    Ok(BinaryAnalysisResult {
        function,
        signature,
        struct_layouts,
        patterns,
        recovered_types,
        security_vcs,
        standard_vcs,
    })
}

/// Quick analysis: run pipeline with default config.
#[deprecated(
    since = "0.1.0",
    note = "Use analyze_lifted_binary_default() for the canonical pipeline"
)]
pub fn analyze_binary_default(
    program: &LiftedProgram,
) -> Result<BinaryAnalysisResult, BinaryPipelineError> {
    analyze_binary(program, &BinaryPipelineConfig::default())
}

/// Security-only analysis: skip standard VCs, focus on security patterns.
#[deprecated(
    since = "0.1.0",
    note = "Use analyze_lifted_binary() with appropriate config for the canonical pipeline"
)]
pub fn analyze_binary_security_only(
    program: &LiftedProgram,
) -> Result<BinaryAnalysisResult, BinaryPipelineError> {
    analyze_binary(
        program,
        &BinaryPipelineConfig {
            generate_standard_vcs: false,
            enable_type_recovery: true,
            enable_security_vcs: true,
            min_severity: 1,
        },
    )
}

// ────────────────────────────────────────────────────────────────────────────
// tRust #565: Unified pipeline — canonical entry points
// ────────────────────────────────────────────────────────────────────────────

/// Unified binary analysis: runs BOTH the security analysis pipeline AND
/// the memory model pipeline on a `LiftedFunction` from the canonical
/// disassembler chain (trust-binary-parse -> trust-disasm -> trust-machine-sem
/// -> trust-lift -> trust-type-recover -> trust-decompile).
///
/// This is the single canonical entry point for binary verification.
/// It replaces the need to call `analyze_binary()` and `generate_binary_vcs()`
/// separately.
pub fn analyze_lifted_binary(
    lifted: &trust_lift::LiftedFunction,
    config: &BinaryPipelineConfig,
) -> Result<BinaryAnalysisResult, BinaryPipelineError> {
    // Convert to legacy format so security analysis can consume it
    let legacy = crate::lift_adapter::lifted_to_legacy(lifted);
    let mut result = analyze_binary(&legacy, config)?;

    // Also generate memory model VCs from the canonical pipeline
    let mem_vcs = crate::lift_adapter::generate_memory_model_vcs(lifted);
    result.standard_vcs.extend(mem_vcs);

    Ok(result)
}

/// Quick unified analysis with default config.
pub fn analyze_lifted_binary_default(
    lifted: &trust_lift::LiftedFunction,
) -> Result<BinaryAnalysisResult, BinaryPipelineError> {
    analyze_lifted_binary(lifted, &BinaryPipelineConfig::default())
}

#[cfg(test)]
#[allow(deprecated)]
mod tests {
    use super::*;
    use crate::binary_analysis::lifter::{
        AbstractInsn, AbstractOp, AbstractRegister, AbstractValue, MemoryAccess,
    };

    fn reg(id: u16, width: u32) -> AbstractRegister {
        AbstractRegister { id, name: format!("r{id}"), width }
    }

    fn insn(address: u64, op: AbstractOp) -> AbstractInsn {
        AbstractInsn { address, op, size: 4 }
    }

    fn simple_add_program() -> LiftedProgram {
        LiftedProgram {
            instructions: vec![
                insn(
                    0x100,
                    AbstractOp::BinArith {
                        dst: 2,
                        op: BinOp::Add,
                        lhs: AbstractValue::Register(0),
                        rhs: AbstractValue::Register(1),
                    },
                ),
                insn(0x104, AbstractOp::Return { value: Some(AbstractValue::Register(2)) }),
            ],
            entry_point: 0x100,
            registers: vec![reg(0, 64), reg(1, 64), reg(2, 64)],
        }
    }

    fn buffer_copy_program() -> LiftedProgram {
        LiftedProgram {
            instructions: vec![
                insn(
                    0x100,
                    AbstractOp::Call {
                        func: "memcpy".to_string(),
                        args: vec![
                            AbstractValue::Register(0),
                            AbstractValue::Register(1),
                            AbstractValue::Register(2),
                        ],
                        dest: None,
                        next: Some(0x108),
                    },
                ),
                insn(0x108, AbstractOp::Return { value: None }),
            ],
            entry_point: 0x100,
            registers: vec![reg(0, 64), reg(1, 64), reg(2, 64)],
        }
    }

    #[test]
    fn test_analyze_binary_simple() {
        let program = simple_add_program();
        let result = analyze_binary_default(&program).expect("pipeline should succeed");

        assert_eq!(result.function.name, "lifted_100");
        assert_eq!(result.signature.params.len(), 2);
        assert!(result.patterns.is_empty(), "simple add has no security patterns");
        assert!(result.security_vcs.is_empty(), "no security VCs for simple add");
        // Standard VCs: may produce overflow VC for the add
        let _ = result.total_vc_count();
    }

    #[test]
    fn test_analyze_binary_with_memcpy() {
        let program = buffer_copy_program();
        let result = analyze_binary_default(&program).expect("pipeline should succeed");

        // Should detect buffer copy pattern and generate security VCs
        assert!(
            result.patterns.iter().any(|p| matches!(p, BinaryPattern::BufferCopy { .. })),
            "should detect buffer copy pattern"
        );
        assert!(
            result.has_security_findings(),
            "should generate security VCs for memcpy"
        );
    }

    #[test]
    fn test_analyze_binary_security_only() {
        let program = buffer_copy_program();
        let result = analyze_binary_security_only(&program).expect("pipeline should succeed");

        assert!(result.standard_vcs.is_empty(), "security-only mode should skip standard VCs");
        assert!(result.has_security_findings(), "should still find security issues");
    }

    #[test]
    fn test_analyze_binary_disabled_security() {
        let program = buffer_copy_program();
        let config = BinaryPipelineConfig {
            generate_standard_vcs: true,
            enable_type_recovery: false,
            enable_security_vcs: false,
            min_severity: 1,
        };
        let result = analyze_binary(&program, &config).expect("pipeline should succeed");

        assert!(result.security_vcs.is_empty(), "should not generate security VCs");
        assert!(result.struct_layouts.is_empty(), "type recovery disabled");
    }

    #[test]
    fn test_analyze_binary_severity_filter() {
        let program = buffer_copy_program();
        let high_only = BinaryPipelineConfig {
            min_severity: 9, // Only severity >= 9 (UAF, control flow hijack)
            ..Default::default()
        };
        let result = analyze_binary(&program, &high_only).expect("pipeline should succeed");

        // Buffer overflow is severity 8, should be filtered out
        for svc in &result.security_vcs {
            assert!(
                svc.property.severity() >= 9,
                "all remaining VCs should have severity >= 9, got {}",
                svc.property.severity()
            );
        }
    }

    #[test]
    fn test_analyze_binary_empty_program() {
        let program = LiftedProgram {
            instructions: vec![],
            entry_point: 0,
            registers: vec![],
        };

        let result = analyze_binary_default(&program).expect("empty program should succeed");
        assert!(result.patterns.is_empty());
        assert!(result.security_vcs.is_empty());
        assert!(result.signature.params.is_empty());
    }

    #[test]
    fn test_binary_analysis_result_all_vcs() {
        let program = buffer_copy_program();
        let result = analyze_binary_default(&program).expect("pipeline should succeed");

        let all = result.all_vcs();
        assert_eq!(all.len(), result.total_vc_count());
    }

    #[test]
    fn test_pipeline_config_serialization() {
        let config = BinaryPipelineConfig::default();
        let json = serde_json::to_string(&config).expect("serialize");
        let round: BinaryPipelineConfig = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.generate_standard_vcs, config.generate_standard_vcs);
        assert_eq!(round.min_severity, config.min_severity);
    }

    #[test]
    fn test_pipeline_with_struct_access() {
        let base = Formula::Var("ptr".to_string(), Sort::Int);
        let program = LiftedProgram {
            instructions: vec![
                insn(
                    0x100,
                    AbstractOp::Load {
                        dst: 0,
                        access: MemoryAccess::Read {
                            addr: Formula::Add(
                                Box::new(base.clone()),
                                Box::new(Formula::Int(0)),
                            ),
                            size: 4,
                        },
                    },
                ),
                insn(
                    0x104,
                    AbstractOp::Load {
                        dst: 1,
                        access: MemoryAccess::Read {
                            addr: Formula::Add(
                                Box::new(base),
                                Box::new(Formula::Int(8)),
                            ),
                            size: 8,
                        },
                    },
                ),
                insn(0x108, AbstractOp::Return { value: Some(AbstractValue::Register(0)) }),
            ],
            entry_point: 0x100,
            registers: vec![reg(0, 32), reg(1, 64)],
        };

        let result = analyze_binary_default(&program).expect("pipeline should succeed");
        assert_eq!(result.struct_layouts.len(), 1, "should recover 1 struct layout");
        assert_eq!(result.struct_layouts[0].fields.len(), 2);
    }

    // ────────────────────────────────────────────────────────────────────────
    // tRust #565: Unified pipeline parity tests
    // ────────────────────────────────────────────────────────────────────────

    #[test]
    fn test_analyze_lifted_binary_produces_memory_model_vcs() {
        use trust_lift::cfg::{Cfg, LiftedBlock};
        use trust_lift::semantic_lift::LocalLayout;

        let layout = LocalLayout::standard();
        let mem_idx = layout.mem_local;

        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x4000,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let body = trust_types::VerifiableBody {
            locals: {
                let mut locals = Vec::new();
                locals.push(trust_types::LocalDecl {
                    index: 0,
                    ty: trust_types::Ty::Int { width: 64, signed: false },
                    name: Some("_result".into()),
                });
                locals.push(trust_types::LocalDecl {
                    index: 1,
                    ty: trust_types::Ty::Int { width: 64, signed: false },
                    name: Some("X0".into()),
                });
                locals.push(trust_types::LocalDecl {
                    index: 2,
                    ty: trust_types::Ty::Int { width: 64, signed: false },
                    name: Some("X1".into()),
                });
                for i in 3..mem_idx {
                    locals.push(trust_types::LocalDecl {
                        index: i,
                        ty: trust_types::Ty::Int { width: 64, signed: false },
                        name: Some(format!("_pad{i}")),
                    });
                }
                locals.push(trust_types::LocalDecl {
                    index: mem_idx,
                    ty: trust_types::Ty::Int { width: 64, signed: false },
                    name: Some("MEM".into()),
                });
                locals
            },
            blocks: vec![trust_types::BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![trust_types::Statement::Assign {
                    place: trust_types::Place::local(mem_idx),
                    rvalue: trust_types::Rvalue::Use(trust_types::Operand::Constant(
                        trust_types::ConstValue::Uint(0, 64),
                    )),
                    span: trust_types::SourceSpan {
                        file: "binary:0x4000".to_string(),
                        line_start: 0,
                        col_start: 0,
                        line_end: 0,
                        col_end: 0,
                    },
                }],
                terminator: trust_types::Terminator::Return,
            }],
            arg_count: 2,
            return_ty: trust_types::Ty::Int { width: 64, signed: false },
        };

        let lifted = trust_lift::LiftedFunction {
            name: "test_unified".to_string(),
            entry_point: 0x4000,
            cfg,
            tmir_body: body,
            ssa: None,
            annotations: vec![],
        };

        let result =
            analyze_lifted_binary_default(&lifted).expect("unified pipeline should succeed");

        // Should have memory model VCs (stack discipline at minimum)
        let has_stack_vc = result.standard_vcs.iter().any(|vc| {
            matches!(
                &vc.kind,
                VcKind::Assertion { message } if message.contains("stack pointer")
            )
        });
        assert!(
            has_stack_vc,
            "unified pipeline should include stack discipline VCs from memory model"
        );
    }

    #[test]
    fn test_analyze_lifted_binary_default_succeeds_on_simple_function() {
        use trust_lift::cfg::{Cfg, LiftedBlock};

        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x5000,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let body = trust_types::VerifiableBody {
            locals: vec![
                trust_types::LocalDecl {
                    index: 0,
                    ty: trust_types::Ty::Int { width: 64, signed: false },
                    name: Some("_result".into()),
                },
                trust_types::LocalDecl {
                    index: 1,
                    ty: trust_types::Ty::Int { width: 64, signed: false },
                    name: Some("X0".into()),
                },
            ],
            blocks: vec![trust_types::BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![trust_types::Statement::Assign {
                    place: trust_types::Place::local(0),
                    rvalue: trust_types::Rvalue::BinaryOp(
                        trust_types::BinOp::Add,
                        trust_types::Operand::Copy(trust_types::Place::local(1)),
                        trust_types::Operand::Copy(trust_types::Place::local(1)),
                    ),
                    span: trust_types::SourceSpan::default(),
                }],
                terminator: trust_types::Terminator::Return,
            }],
            arg_count: 1,
            return_ty: trust_types::Ty::Int { width: 64, signed: false },
        };

        let lifted = trust_lift::LiftedFunction {
            name: "test_simple_unified".to_string(),
            entry_point: 0x5000,
            cfg,
            tmir_body: body,
            ssa: None,
            annotations: vec![],
        };

        let result =
            analyze_lifted_binary_default(&lifted).expect("unified pipeline should succeed");
        assert!(
            result.total_vc_count() > 0,
            "should produce at least some VCs (standard + memory model)"
        );
    }
}
