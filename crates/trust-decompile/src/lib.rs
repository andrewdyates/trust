#![allow(dead_code)]
//! trust-decompile: tMIR to idiomatic Rust decompiler
//!
//! Converts the tRust verification IR (VerifiableFunction) back to
//! human-readable Rust source code. Three-stage pipeline:
//!   Stage 1   (raw emission): MIR -> syntactically valid unsafe Rust
//!   Stage 1.5 (ownership):    infer Box/&/&mut from pointer patterns
//!   Stage 2   (patterns):     detect idioms (for loops, Option, etc.)
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub(crate) mod beautify;
pub(crate) mod emit;
pub(crate) mod error;
pub(crate) mod ownership;
pub(crate) mod patterns;
pub(crate) mod types;

pub use error::DecompileError;
pub use types::{
    CommentLevel, DecompileOptions, DecompiledFunction, DecompiledModule, NamingStyle,
};

use trust_types::VerifiableFunction;

/// Decompiler that converts `VerifiableFunction` (tMIR) to Rust source code.
#[derive(Debug, Clone)]
#[derive(Default)]
pub struct Decompiler {
    options: DecompileOptions,
}


impl Decompiler {
    /// Create a decompiler with the given options.
    #[must_use]
    pub fn new(options: DecompileOptions) -> Self {
        Self { options }
    }

    /// Create a decompiler that only performs raw emission (Stage 1).
    #[must_use]
    pub fn raw_only() -> Self {
        Self {
            options: DecompileOptions::raw_only(),
        }
    }

    /// Decompile a `VerifiableFunction` to Rust source code.
    ///
    /// The `func` parameter is the tMIR representation (`VerifiableFunction`
    /// from `trust-types`). The issue spec refers to this as `TmirFunction`.
    ///
    /// Returns a `DecompiledFunction` containing the source code and a
    /// confidence score indicating how idiomatic the output is.
    pub fn decompile(&self, func: &VerifiableFunction) -> Result<DecompiledFunction, DecompileError> {
        // Stage 1: Raw emission
        let raw_source = if self.options.raw_emission {
            emit::emit_raw(func)?
        } else {
            return Err(DecompileError::UnsupportedConstruct(
                "raw_emission disabled with no alternative".to_string(),
            ));
        };

        let base_confidence = 0.3;

        // Stage 1.5: Ownership inference — analyze pointer patterns and rewrite
        let ownership_infos = ownership::analyze_ownership(func);
        let (source_after_ownership, ownership_boost) =
            ownership::apply_ownership_inference(&raw_source, &ownership_infos);

        // Stage 2: Pattern recovery
        let (source, pattern_boost) = if self.options.pattern_recovery {
            patterns::apply_patterns(&source_after_ownership)
        } else {
            (source_after_ownership, 0.0)
        };

        let confidence = (base_confidence + ownership_boost + pattern_boost).min(1.0);

        let fn_name = func.name.split("::").last().unwrap_or(&func.name).to_string();

        let params: Vec<(String, String)> = func
            .body
            .locals
            .iter()
            .skip(1) // skip _0 (return place)
            .take(func.body.arg_count)
            .map(|decl| {
                let name = decl
                    .name
                    .clone()
                    .unwrap_or_else(|| format!("_{}", decl.index));
                let ty = emit::ty_to_rust(&decl.ty);
                (name, ty)
            })
            .collect();

        Ok(DecompiledFunction {
            name: fn_name,
            params,
            source,
            confidence,
        })
    }

    /// Decompile a slice of `VerifiableFunction`s into a `DecompiledModule`.
    ///
    /// Functions that fail decompilation are skipped with a warning comment
    /// in the module output.
    pub fn decompile_module(
        &self,
        module_name: &str,
        funcs: &[VerifiableFunction],
    ) -> DecompiledModule {
        let mut module = DecompiledModule::new(module_name);

        for func in funcs {
            match self.decompile(func) {
                Ok(decompiled) => module.functions.push(decompiled),
                Err(e) => {
                    // Include a stub so the caller knows a function was skipped
                    module.functions.push(DecompiledFunction {
                        name: func
                            .name
                            .split("::")
                            .last()
                            .unwrap_or(&func.name)
                            .to_string(),
                        params: Vec::new(),
                        source: format!("// ERROR: could not decompile {}: {e}", func.name),
                        confidence: 0.0,
                    });
                }
            }
        }

        module
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{
        BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
        Statement, Terminator, Ty, VerifiableBody,
    };

    /// Build the midpoint function MIR for testing.
    fn midpoint_func() -> VerifiableFunction {
        VerifiableFunction {
            name: "get_midpoint".to_string(),
            def_path: "midpoint::get_midpoint".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) },
                    LocalDecl {
                        index: 3,
                        ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]),
                        name: None,
                    },
                    LocalDecl { index: 4, ty: Ty::usize(), name: None },
                    LocalDecl { index: 5, ty: Ty::usize(), name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            cond: Operand::Copy(Place::field(3, 1)),
                            expected: false,
                            msg: trust_types::AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(4),
                                rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(5),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Div,
                                    Operand::Copy(Place::local(4)),
                                    Operand::Constant(ConstValue::Uint(2, 64)),
                                ),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(0),
                                rvalue: Rvalue::Use(Operand::Copy(Place::local(5))),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 2,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_decompile_midpoint() {
        let decompiler = Decompiler::default();
        let func = midpoint_func();
        let result = decompiler.decompile(&func).expect("decompile should succeed");

        assert_eq!(result.name, "get_midpoint");
        assert!(result.confidence >= 0.3);
        assert!(result.source.contains("unsafe fn get_midpoint"));
        assert!(result.source.contains("a: u64"));
        assert!(result.source.contains("b: u64"));
        assert!(result.source.contains("-> u64"));
        assert!(result.source.contains("checked_add"));
        assert!(result.source.contains("/ 2u64"));
        assert!(result.source.contains("return _0;"));
    }

    #[test]
    fn test_decompile_raw_only() {
        let decompiler = Decompiler::raw_only();
        let func = midpoint_func();
        let result = decompiler.decompile(&func).expect("raw decompile should succeed");

        assert_eq!(result.name, "get_midpoint");
        assert!((result.confidence - 0.3).abs() < f64::EPSILON);
        assert!(result.source.contains("unsafe fn get_midpoint"));
    }

    #[test]
    fn test_decompile_empty_body_fails() {
        let func = VerifiableFunction {
            name: "empty".to_string(),
            def_path: "m::empty".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![],
                blocks: vec![],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let decompiler = Decompiler::default();
        let err = decompiler.decompile(&func).unwrap_err();
        assert!(matches!(err, DecompileError::EmptyBody));
    }

    #[test]
    fn test_decompile_simple_bool_fn() {
        let func = VerifiableFunction {
            name: "is_positive".to_string(),
            def_path: "m::is_positive".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Bool, name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(2),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Gt,
                                    Operand::Copy(Place::local(1)),
                                    Operand::Constant(ConstValue::Int(0)),
                                ),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(0),
                                rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::Bool,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let decompiler = Decompiler::default();
        let result = decompiler.decompile(&func).expect("should decompile");
        assert!(result.source.contains("x: i32"));
        assert!(result.source.contains("> 0"));
        assert!(result.source.contains("-> bool"));
    }

    #[test]
    fn test_decompile_with_switch_int() {
        let func = VerifiableFunction {
            name: "classify".to_string(),
            def_path: "m::classify".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("val".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(1)),
                            targets: vec![(0, BlockId(1)), (1, BlockId(2))],
                            otherwise: BlockId(3),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(-1))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
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
        };

        let decompiler = Decompiler::default();
        let result = decompiler.decompile(&func).expect("should decompile");
        assert!(result.source.contains("match val"));
        assert!(result.source.contains("0 =>"));
        assert!(result.source.contains("1 =>"));
        assert!(result.source.contains("_ =>"));
    }

    #[test]
    fn test_decompile_with_call() {
        let func = VerifiableFunction {
            name: "wrapper".to_string(),
            def_path: "m::wrapper".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "other_fn".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let decompiler = Decompiler::default();
        let result = decompiler.decompile(&func).expect("should decompile");
        assert!(result.source.contains("other_fn(x)"));
    }

    #[test]
    fn test_decompile_unit_return() {
        let func = VerifiableFunction {
            name: "do_nothing".to_string(),
            def_path: "m::do_nothing".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let decompiler = Decompiler::default();
        let result = decompiler.decompile(&func).expect("should decompile");
        // Unit functions don't declare _0
        assert!(!result.source.contains("-> ()"));
        assert!(result.source.contains("unsafe fn do_nothing()"));
    }

    #[test]
    fn test_decompile_params_populated() {
        let decompiler = Decompiler::default();
        let func = midpoint_func();
        let result = decompiler.decompile(&func).expect("should decompile");

        assert_eq!(result.params.len(), 2);
        assert_eq!(result.params[0], ("a".to_string(), "u64".to_string()));
        assert_eq!(result.params[1], ("b".to_string(), "u64".to_string()));
    }

    #[test]
    fn test_decompile_module() {
        let decompiler = Decompiler::default();
        let funcs = vec![midpoint_func()];
        let module = decompiler.decompile_module("test_mod", &funcs);

        assert_eq!(module.name, "test_mod");
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].name, "get_midpoint");

        let source = module.to_source();
        assert!(source.contains("// Decompiled module: test_mod"));
        assert!(source.contains("unsafe fn get_midpoint"));
    }

    #[test]
    fn test_decompile_module_with_error() {
        let decompiler = Decompiler::default();
        let empty_func = VerifiableFunction {
            name: "broken".to_string(),
            def_path: "m::broken".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![],
                blocks: vec![],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let funcs = vec![midpoint_func(), empty_func];
        let module = decompiler.decompile_module("mixed", &funcs);

        assert_eq!(module.functions.len(), 2);
        assert!(module.functions[0].confidence > 0.0);
        // Second function failed decompilation
        assert_eq!(module.functions[1].confidence, 0.0);
        assert!(module.functions[1].source.contains("ERROR"));
    }
}
