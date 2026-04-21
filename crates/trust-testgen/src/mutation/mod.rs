// trust-testgen/mutation: Mutation testing target generation
//
// Generate code mutations to measure test suite quality. Each mutant is a
// small code change (e.g., replacing `+` with `-`) that a good test suite
// should detect (kill). The mutation score is the fraction of mutants killed.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod input_mutation;
mod mir_mutation;
mod source_mutation;
mod types;

// Re-export types
pub use types::{MirMutant, Mutant, MutationResult, MutationType};

// Re-export MIR-level mutation
pub use mir_mutation::{MutationGenerator, generate_mutants_from_func, mir_mutation_score};

// Re-export source-level mutation
pub use source_mutation::{generate_mutants, mutation_score, mutation_score_heuristic};

// Re-export input-level mutation
pub use input_mutation::{
    AppliedMutation, ExpectedBehavior, MutationError, MutationOperator, MutationStrategy,
    TestMutant, apply_operator, generate_boundary_tests, input_mutation_score, mutate_test_input,
};

// Test-only re-imports for internal functions used by tests
#[cfg(test)]
use input_mutation::const_value_eq;
#[cfg(test)]
use input_mutation::max_unsigned;
#[cfg(test)]
use mir_mutation::{alternative_ops, shift_constant};
#[cfg(test)]
use mir_mutation::BinOpExt;
#[cfg(test)]
use source_mutation::{has_value_constraining_assert, is_likely_in_string};

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{
        BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
        Statement, Terminator, Ty, UnOp, VerifiableBody, VerifiableFunction,
    };

    use crate::GeneratedTest;

    fn make_func_with_stmts(name: &str, stmts: Vec<Statement>) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts,
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    // --- Source-level mutation tests (original API) ---

    #[test]
    fn test_generate_mutants_arithmetic() {
        let source = "let result = a + b;\n";
        let mutants = generate_mutants(source);
        let arith: Vec<_> = mutants
            .iter()
            .filter(|m| m.mutation_type == MutationType::ArithOp)
            .collect();
        assert!(!arith.is_empty(), "should find arithmetic mutant");
        assert_eq!(arith[0].original, " + ");
        assert_eq!(arith[0].mutated, " - ");
    }

    #[test]
    fn test_generate_mutants_comparison() {
        let source = "if x >= 0 { ok() }\n";
        let mutants = generate_mutants(source);
        let comp: Vec<_> = mutants
            .iter()
            .filter(|m| m.mutation_type == MutationType::CompOp)
            .collect();
        assert!(!comp.is_empty(), "should find comparison mutant");
        assert_eq!(comp[0].original, " >= ");
        assert_eq!(comp[0].mutated, " > ");
    }

    #[test]
    fn test_generate_mutants_boolean() {
        let source = "if a && b { ok() }\n";
        let mutants = generate_mutants(source);
        let bool_mut: Vec<_> = mutants
            .iter()
            .filter(|m| m.mutation_type == MutationType::BoolOp)
            .collect();
        assert!(!bool_mut.is_empty(), "should find boolean mutant");
        assert_eq!(bool_mut[0].original, " && ");
        assert_eq!(bool_mut[0].mutated, " || ");
    }

    #[test]
    fn test_generate_mutants_boundary_shift() {
        let source = "let limit = 42;\n";
        let mutants = generate_mutants(source);
        let boundary: Vec<_> = mutants
            .iter()
            .filter(|m| m.mutation_type == MutationType::BoundaryShift)
            .collect();
        assert!(boundary.len() >= 2, "should produce +1 and -1 variants");
        let originals: Vec<_> = boundary.iter().map(|m| m.original.as_str()).collect();
        assert!(originals.contains(&"42"));
        let mutations: Vec<_> = boundary.iter().map(|m| m.mutated.as_str()).collect();
        assert!(mutations.contains(&"43"));
        assert!(mutations.contains(&"41"));
    }

    #[test]
    fn test_generate_mutants_return_value() {
        let source = "return result;\n";
        let mutants = generate_mutants(source);
        let ret: Vec<_> = mutants
            .iter()
            .filter(|m| m.mutation_type == MutationType::ReturnValue)
            .collect();
        assert!(!ret.is_empty(), "should find return value mutant");
        assert!(ret[0].mutated.contains("Default::default()"));
    }

    #[test]
    fn test_generate_mutants_condition_negation() {
        let source = "if x > 0 {\n";
        let mutants = generate_mutants(source);
        let cond: Vec<_> = mutants
            .iter()
            .filter(|m| m.mutation_type == MutationType::ConditionNegation)
            .collect();
        assert!(!cond.is_empty(), "should find condition negation mutant");
        assert_eq!(cond[0].original, "if x > 0");
        assert_eq!(cond[0].mutated, "if !(x > 0)");
    }

    #[test]
    fn test_generate_mutants_skips_comments() {
        let source = "// a + b\nlet x = 1;\n";
        let mutants = generate_mutants(source);
        let arith: Vec<_> = mutants
            .iter()
            .filter(|m| m.mutation_type == MutationType::ArithOp)
            .collect();
        assert!(arith.is_empty(), "should not mutate inside comments");
    }

    #[test]
    fn test_generate_mutants_empty_source() {
        let mutants = generate_mutants("");
        assert!(mutants.is_empty());
    }

    #[test]
    fn test_mutation_score_no_mutants() {
        let score = mutation_score(&[], &[]);
        assert!((score - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_mutation_score_all_killed() {
        let tests = vec![GeneratedTest {
            name: "test_arith".to_string(),
            code: "let result = a + b;\nassert!(result > 0);".to_string(),
            boundary_values: vec![],
        }];
        let mutants = vec![Mutant {
            offset: 0,
            line: 1,
            mutation_type: MutationType::ArithOp,
            original: " + ".to_string(),
            mutated: " - ".to_string(),
        }];
        let score = mutation_score(&tests, &mutants);
        assert!((score - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_mutation_score_none_killed() {
        let tests = vec![GeneratedTest {
            name: "test_unrelated".to_string(),
            code: "assert!(true);".to_string(),
            boundary_values: vec![],
        }];
        let mutants = vec![Mutant {
            offset: 0,
            line: 1,
            mutation_type: MutationType::CompOp,
            original: " >= ".to_string(),
            mutated: " > ".to_string(),
        }];
        let score = mutation_score(&tests, &mutants);
        assert!((score - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_mutation_score_partial() {
        // Test has an assert_eq that constrains the + operator result,
        // but does not constrain the >= operator.
        let tests = vec![GeneratedTest {
            name: "test_add".to_string(),
            code: "let x = a + b;\nassert_eq!(x, 42);".to_string(),
            boundary_values: vec![],
        }];
        let mutants = vec![
            Mutant {
                offset: 0,
                line: 1,
                mutation_type: MutationType::ArithOp,
                original: " + ".to_string(),
                mutated: " - ".to_string(),
            },
            Mutant {
                offset: 10,
                line: 2,
                mutation_type: MutationType::CompOp,
                original: " >= ".to_string(),
                mutated: " > ".to_string(),
            },
        ];
        let score = mutation_score(&tests, &mutants);
        assert!((score - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_mutant_describe() {
        let mutant = Mutant {
            offset: 42,
            line: 10,
            mutation_type: MutationType::ArithOp,
            original: " + ".to_string(),
            mutated: " - ".to_string(),
        };
        let desc = mutant.describe();
        assert!(desc.contains("line 10"));
        assert!(desc.contains("AOR"));
        assert!(desc.contains("` + `"));
        assert!(desc.contains("` - `"));
    }

    #[test]
    fn test_mutation_type_description() {
        assert_eq!(MutationType::ArithOp.description(), "arithmetic operator replacement");
        assert_eq!(MutationType::CompOp.description(), "comparison operator replacement");
        assert_eq!(MutationType::BoolOp.description(), "boolean operator replacement");
        assert_eq!(MutationType::BoundaryShift.description(), "boundary constant shift");
        assert_eq!(MutationType::ReturnValue.description(), "return value replacement");
        assert_eq!(
            MutationType::ConditionNegation.description(),
            "condition negation"
        );
    }

    #[test]
    fn test_mutation_generator_api() {
        let source = "let x = a + b;\nif x >= 0 {\n    return x;\n}\n";
        let mutants = MutationGenerator::generate_mutants(source);
        assert!(!mutants.is_empty());

        // Heuristic score: source contains the operators, so it's > 0
        let tests = vec![GeneratedTest {
            name: "t".to_string(),
            code: source.to_string(),
            boundary_values: vec![],
        }];
        let heuristic = MutationGenerator::mutation_score_heuristic(&tests, &mutants);
        assert!(heuristic > 0.0, "heuristic should match operators in source");

        // Structural score: source has no assert, so score should be lower
        let structural = MutationGenerator::mutation_score(&tests, &mutants);
        assert!(structural <= heuristic, "structural should be stricter than heuristic");
    }

    #[test]
    fn test_is_likely_in_string() {
        assert!(!is_likely_in_string("let x = a + b;", 10));
        assert!(is_likely_in_string("let x = \"a + b\";", 11));
    }

    #[test]
    fn test_return_zero_not_mutated() {
        let source = "return 0;\n";
        let mutants = generate_mutants(source);
        let ret: Vec<_> = mutants
            .iter()
            .filter(|m| m.mutation_type == MutationType::ReturnValue)
            .collect();
        assert!(ret.is_empty(), "return 0 should not be mutated to Default::default()");
    }

    #[test]
    fn test_return_false_not_mutated() {
        let source = "return false;\n";
        let mutants = generate_mutants(source);
        let ret: Vec<_> = mutants
            .iter()
            .filter(|m| m.mutation_type == MutationType::ReturnValue)
            .collect();
        assert!(ret.is_empty(), "return false should not be mutated to Default::default()");
    }

    #[test]
    fn test_multiline_source() {
        let source = "\
fn compute(a: i32, b: i32) -> i32 {
    if a > 0 && b > 0 {
        return a + b;
    }
    return 0;
}";
        let mutants = generate_mutants(source);
        let types: Vec<_> = mutants.iter().map(|m| m.mutation_type).collect();
        assert!(types.contains(&MutationType::ArithOp));
        assert!(types.contains(&MutationType::BoolOp));
        assert!(types.contains(&MutationType::ReturnValue));
        assert!(types.contains(&MutationType::ConditionNegation));
    }

    // --- MIR-level mutation tests ---

    #[test]
    fn test_mir_mutants_binary_op_add() {
        let stmts = vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: SourceSpan::default(),
        }];
        let func = make_func_with_stmts("add_fn", stmts);
        let mutants = generate_mutants_from_func(&func);
        // Add -> Sub, Add -> Mul = 2 operator replacements
        assert!(mutants.len() >= 2);
        assert!(mutants.iter().any(|m| m.mutated_desc == "Sub"));
        assert!(mutants.iter().any(|m| m.mutated_desc == "Mul"));
    }

    #[test]
    fn test_mir_mutants_binary_op_sub_generates_swap() {
        let stmts = vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::BinaryOp(
                BinOp::Sub,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: SourceSpan::default(),
        }];
        let func = make_func_with_stmts("sub_fn", stmts);
        let mutants = generate_mutants_from_func(&func);
        // Sub is not commutative, so should include operand swap
        assert!(mutants.iter().any(|m| m.mutated_desc.contains("rhs, lhs")));
    }

    #[test]
    fn test_mir_mutants_comparison_op() {
        let stmts = vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::BinaryOp(
                BinOp::Lt,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: SourceSpan::default(),
        }];
        let func = make_func_with_stmts("cmp_fn", stmts);
        let mutants = generate_mutants_from_func(&func);
        assert!(mutants.iter().any(|m| m.mutation_type == MutationType::CompOp));
        assert!(mutants.iter().any(|m| m.mutated_desc == "Le"));
        assert!(mutants.iter().any(|m| m.mutated_desc == "Ge"));
    }

    #[test]
    fn test_mir_mutants_unary_op() {
        let stmts = vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
            span: SourceSpan::default(),
        }];
        let func = make_func_with_stmts("neg_fn", stmts);
        let mutants = generate_mutants_from_func(&func);
        // Should have: Neg->Not swap + identity removal
        assert_eq!(mutants.len(), 2);
        assert!(mutants.iter().any(|m| m.mutated_desc == "Not"));
        assert!(mutants.iter().any(|m| m.mutated_desc == "operand"));
    }

    #[test]
    fn test_mir_mutants_constant_shift() {
        let stmts = vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
            span: SourceSpan::default(),
        }];
        let func = make_func_with_stmts("const_fn", stmts);
        let mutants = generate_mutants_from_func(&func);
        // Int(42) -> Int(43), Int(41), Int(0)
        assert_eq!(mutants.len(), 3);
        assert!(mutants.iter().all(|m| m.mutation_type == MutationType::BoundaryShift));
    }

    #[test]
    fn test_mir_mutants_bool_constant() {
        let stmts = vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(true))),
            span: SourceSpan::default(),
        }];
        let func = make_func_with_stmts("bool_fn", stmts);
        let mutants = generate_mutants_from_func(&func);
        assert_eq!(mutants.len(), 1);
        assert_eq!(mutants[0].mutated_desc, "Bool(false)");
    }

    #[test]
    fn test_mir_mutants_empty_body() {
        let func = make_func_with_stmts("empty_fn", vec![]);
        let mutants = generate_mutants_from_func(&func);
        assert!(mutants.is_empty());
    }

    #[test]
    fn test_mir_mutants_nop_statement() {
        let func = make_func_with_stmts("nop_fn", vec![Statement::Nop]);
        let mutants = generate_mutants_from_func(&func);
        assert!(mutants.is_empty());
    }

    #[test]
    fn test_mir_mutants_checked_binary_op() {
        let stmts = vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::CheckedBinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: SourceSpan::default(),
        }];
        let func = make_func_with_stmts("checked_add", stmts);
        let mutants = generate_mutants_from_func(&func);
        assert!(!mutants.is_empty());
        // The mutated statement should also be CheckedBinaryOp
        for m in &mutants {
            if m.mutated_desc == "Sub"
                && let Statement::Assign { rvalue, .. } = &m.mutated_stmt {
                    assert!(matches!(rvalue, Rvalue::CheckedBinaryOp(BinOp::Sub, ..)));
                }
        }
    }

    #[test]
    fn test_mir_mutation_result_methods() {
        let killed = MutationResult::Killed {
            test_name: "test_x".into(),
        };
        assert!(killed.is_killed());
        assert!(!killed.is_survived());

        let survived = MutationResult::Survived;
        assert!(!survived.is_killed());
        assert!(survived.is_survived());

        let equiv = MutationResult::Equivalent;
        assert!(!equiv.is_killed());
        assert!(!equiv.is_survived());
    }

    #[test]
    fn test_mir_mutation_score_empty() {
        assert!((mir_mutation_score(&[]) - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_mir_mutation_score_all_killed() {
        let mutants = vec![MirMutant {
            block_idx: 0,
            stmt_idx: 0,
            mutation_type: MutationType::ArithOp,
            original_desc: "Add".into(),
            mutated_desc: "Sub".into(),
            mutated_stmt: Statement::Nop,
            result: MutationResult::Killed {
                test_name: "t1".into(),
            },
        }];
        assert!((mir_mutation_score(&mutants) - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_mir_mutation_score_mixed() {
        let mutants = vec![
            MirMutant {
                block_idx: 0,
                stmt_idx: 0,
                mutation_type: MutationType::ArithOp,
                original_desc: "Add".into(),
                mutated_desc: "Sub".into(),
                mutated_stmt: Statement::Nop,
                result: MutationResult::Killed {
                    test_name: "t1".into(),
                },
            },
            MirMutant {
                block_idx: 0,
                stmt_idx: 1,
                mutation_type: MutationType::CompOp,
                original_desc: "Lt".into(),
                mutated_desc: "Le".into(),
                mutated_stmt: Statement::Nop,
                result: MutationResult::Survived,
            },
        ];
        assert!((mir_mutation_score(&mutants) - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_mir_mutant_describe() {
        let m = MirMutant {
            block_idx: 2,
            stmt_idx: 3,
            mutation_type: MutationType::ArithOp,
            original_desc: "Add".into(),
            mutated_desc: "Sub".into(),
            mutated_stmt: Statement::Nop,
            result: MutationResult::Survived,
        };
        let desc = m.describe();
        assert!(desc.contains("block[2]"));
        assert!(desc.contains("stmt[3]"));
        assert!(desc.contains("Add"));
        assert!(desc.contains("Sub"));
    }

    #[test]
    fn test_alternative_ops_coverage() {
        // Every BinOp should produce at least one alternative
        let all_ops = [
            BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div, BinOp::Rem,
            BinOp::Eq, BinOp::Ne, BinOp::Lt, BinOp::Le, BinOp::Gt, BinOp::Ge,
            BinOp::BitAnd, BinOp::BitOr, BinOp::BitXor, BinOp::Shl, BinOp::Shr,
        ];
        for op in all_ops {
            let alts = alternative_ops(op);
            assert!(!alts.is_empty(), "{op:?} should have at least one alternative");
        }
    }

    #[test]
    fn test_shift_constant_int() {
        let shifts = shift_constant(&ConstValue::Int(5));
        assert_eq!(shifts.len(), 3); // +1, -1, 0
        assert!(matches!(shifts[0], ConstValue::Int(6)));
        assert!(matches!(shifts[1], ConstValue::Int(4)));
        assert!(matches!(shifts[2], ConstValue::Int(0)));
    }

    #[test]
    fn test_shift_constant_int_zero() {
        let shifts = shift_constant(&ConstValue::Int(0));
        assert_eq!(shifts.len(), 1); // only +1 (no -1 since n<=0, no 0 since already 0)
        assert!(matches!(shifts[0], ConstValue::Int(1)));
    }

    #[test]
    fn test_shift_constant_uint() {
        let shifts = shift_constant(&ConstValue::Uint(10, 64));
        assert_eq!(shifts.len(), 3);
    }

    #[test]
    fn test_shift_constant_bool() {
        let shifts = shift_constant(&ConstValue::Bool(true));
        assert_eq!(shifts.len(), 1);
        assert!(matches!(shifts[0], ConstValue::Bool(false)));
    }

    #[test]
    fn test_shift_constant_float_empty() {
        let shifts = shift_constant(&ConstValue::Float(1.0));
        assert!(shifts.is_empty());
    }

    #[test]
    fn test_mir_mutants_generator_api() {
        let stmts = vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: SourceSpan::default(),
        }];
        let func = make_func_with_stmts("api_fn", stmts);
        let mutants = MutationGenerator::generate_mir_mutants(&func);
        assert!(!mutants.is_empty());
        let score = MutationGenerator::mir_mutation_score(&mutants);
        assert!((score - 0.0).abs() < f64::EPSILON); // all survived initially
    }

    #[test]
    fn test_binop_ext_is_arithmetic() {
        assert!(BinOp::Add.is_arithmetic());
        assert!(BinOp::Sub.is_arithmetic());
        assert!(BinOp::Mul.is_arithmetic());
        assert!(BinOp::Div.is_arithmetic());
        assert!(BinOp::Rem.is_arithmetic());
        assert!(!BinOp::Eq.is_arithmetic());
        assert!(!BinOp::Shl.is_arithmetic());
    }

    #[test]
    fn test_binop_ext_is_comparison() {
        assert!(BinOp::Eq.is_comparison());
        assert!(BinOp::Ne.is_comparison());
        assert!(BinOp::Lt.is_comparison());
        assert!(BinOp::Le.is_comparison());
        assert!(BinOp::Gt.is_comparison());
        assert!(BinOp::Ge.is_comparison());
        assert!(!BinOp::Add.is_comparison());
    }

    #[test]
    fn test_binop_ext_is_commutative() {
        assert!(BinOp::Add.is_commutative());
        assert!(BinOp::Mul.is_commutative());
        assert!(BinOp::Eq.is_commutative());
        assert!(!BinOp::Sub.is_commutative());
        assert!(!BinOp::Div.is_commutative());
        assert!(!BinOp::Lt.is_commutative());
    }

    // --- Input-level mutation tests ---

    #[test]
    fn test_mutation_operator_all_variants() {
        assert_eq!(MutationOperator::ALL.len(), 7);
        // Verify each has a non-empty name
        for op in MutationOperator::ALL {
            assert!(!op.name().is_empty());
        }
    }

    #[test]
    fn test_apply_operator_negate_int() {
        let result = apply_operator(
            MutationOperator::Negate,
            &ConstValue::Int(42),
            &Ty::i32(),
        )
        .unwrap();
        assert!(matches!(result, ConstValue::Int(-42)));
    }

    #[test]
    fn test_apply_operator_negate_bool() {
        let result = apply_operator(
            MutationOperator::Negate,
            &ConstValue::Bool(true),
            &Ty::Bool,
        )
        .unwrap();
        assert!(matches!(result, ConstValue::Bool(false)));
    }

    #[test]
    fn test_apply_operator_zero_subst_uint() {
        let result = apply_operator(
            MutationOperator::ZeroSubst,
            &ConstValue::Uint(999, 64),
            &Ty::u32(),
        )
        .unwrap();
        assert!(matches!(result, ConstValue::Uint(0, 64)));
    }

    #[test]
    fn test_apply_operator_max_subst_i32() {
        let result = apply_operator(
            MutationOperator::MaxSubst,
            &ConstValue::Int(5),
            &Ty::i32(),
        )
        .unwrap();
        let expected = i32::MAX as i128;
        assert!(matches!(result, ConstValue::Int(v) if v == expected));
    }

    #[test]
    fn test_apply_operator_increment_decrement() {
        let inc = apply_operator(
            MutationOperator::Increment,
            &ConstValue::Int(10),
            &Ty::i32(),
        )
        .unwrap();
        assert!(matches!(inc, ConstValue::Int(11)));

        let dec = apply_operator(
            MutationOperator::Decrement,
            &ConstValue::Int(10),
            &Ty::i32(),
        )
        .unwrap();
        assert!(matches!(dec, ConstValue::Int(9)));
    }

    #[test]
    fn test_apply_operator_boundary_shift_positive() {
        let result = apply_operator(
            MutationOperator::BoundaryShift,
            &ConstValue::Int(5),
            &Ty::i32(),
        )
        .unwrap();
        // Positive -> MAX
        let expected = i32::MAX as i128;
        assert!(matches!(result, ConstValue::Int(v) if v == expected));
    }

    #[test]
    fn test_apply_operator_boundary_shift_negative() {
        let result = apply_operator(
            MutationOperator::BoundaryShift,
            &ConstValue::Int(-5),
            &Ty::i32(),
        )
        .unwrap();
        // Negative -> MIN
        let expected = i32::MIN as i128;
        assert!(matches!(result, ConstValue::Int(v) if v == expected));
    }

    #[test]
    fn test_apply_operator_type_coerce_truncation() {
        let result = apply_operator(
            MutationOperator::TypeCoerce,
            &ConstValue::Int(300),
            &Ty::i32(),
        )
        .unwrap();
        // 300 truncated to i8 = 44
        assert!(matches!(result, ConstValue::Int(44)));
    }

    #[test]
    fn test_apply_operator_incompatible() {
        let result = apply_operator(
            MutationOperator::Increment,
            &ConstValue::Unit,
            &Ty::Unit,
        );
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.to_string().contains("not applicable"));
    }

    #[test]
    fn test_mutate_test_input_single_int() {
        let inputs = vec![(ConstValue::Int(10), Ty::i32())];
        let strategy = MutationStrategy::default();
        let mutants = mutate_test_input("test_fn", &inputs, &strategy);
        // Should produce multiple mutants (at most max_mutations_per_input = 4)
        assert!(!mutants.is_empty());
        assert!(mutants.len() <= 4);
        // All should reference the original test name
        for m in &mutants {
            assert_eq!(m.original_test, "test_fn");
            assert_eq!(m.mutations_applied.len(), 1);
            assert_eq!(m.mutated_inputs.len(), 1);
        }
    }

    #[test]
    fn test_mutate_test_input_skips_noop() {
        // ZeroSubst on 0 is a no-op and should be skipped
        let inputs = vec![(ConstValue::Int(0), Ty::i32())];
        let strategy = MutationStrategy::with_operators(&[MutationOperator::ZeroSubst]);
        let mutants = mutate_test_input("test_zero", &inputs, &strategy);
        assert!(mutants.is_empty(), "no-op mutations should be skipped");
    }

    #[test]
    fn test_generate_boundary_tests_produces_variants() {
        let inputs = vec![(ConstValue::Int(42), Ty::i32())];
        let mutants = generate_boundary_tests("test_boundary", &inputs);
        // Should produce multiple boundary variants
        assert!(mutants.len() >= 3, "expected at least 3 boundary mutants, got {}", mutants.len());
        // Check that we get zero, max, increment, decrement, and boundary shift
        let ops: Vec<MutationOperator> = mutants
            .iter()
            .map(|m| m.mutations_applied[0].operator)
            .collect();
        assert!(ops.contains(&MutationOperator::ZeroSubst));
        assert!(ops.contains(&MutationOperator::MaxSubst));
        assert!(ops.contains(&MutationOperator::Increment));
        assert!(ops.contains(&MutationOperator::Decrement));
    }

    #[test]
    fn test_input_mutation_score_empty() {
        assert!((input_mutation_score(&[]) - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_input_mutation_score_all_fail() {
        let mutants = vec![TestMutant {
            original_test: "t".into(),
            mutations_applied: vec![AppliedMutation {
                operator: MutationOperator::Negate,
                original_value: ConstValue::Int(1),
                mutated_value: ConstValue::Int(-1),
            }],
            expected_behavior: ExpectedBehavior::Fail,
            mutated_inputs: vec![ConstValue::Int(-1)],
        }];
        assert!((input_mutation_score(&mutants) - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_input_mutation_score_mixed() {
        let mutants = vec![
            TestMutant {
                original_test: "t".into(),
                mutations_applied: vec![],
                expected_behavior: ExpectedBehavior::Fail,
                mutated_inputs: vec![],
            },
            TestMutant {
                original_test: "t".into(),
                mutations_applied: vec![],
                expected_behavior: ExpectedBehavior::Unknown,
                mutated_inputs: vec![],
            },
        ];
        assert!((input_mutation_score(&mutants) - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_test_mutant_describe() {
        let m = TestMutant {
            original_test: "test_add".into(),
            mutations_applied: vec![AppliedMutation {
                operator: MutationOperator::Negate,
                original_value: ConstValue::Int(5),
                mutated_value: ConstValue::Int(-5),
            }],
            expected_behavior: ExpectedBehavior::Unknown,
            mutated_inputs: vec![ConstValue::Int(-5)],
        };
        let desc = m.describe();
        assert!(desc.contains("test_add"));
        assert!(desc.contains("negate"));
        assert!(desc.contains("1 mutation(s)"));
    }

    #[test]
    fn test_mutation_strategy_with_operators() {
        let strategy = MutationStrategy::with_operators(&[
            MutationOperator::Increment,
            MutationOperator::Decrement,
        ]);
        assert_eq!(strategy.operators.len(), 2);
        assert_eq!(strategy.max_mutations_per_input, 4);
        assert_eq!(strategy.seed, 0);
    }

    #[test]
    fn test_mutation_strategy_default() {
        let strategy = MutationStrategy::default();
        assert_eq!(strategy.operators.len(), 7);
        assert_eq!(strategy.max_mutations_per_input, 4);
    }

    #[test]
    fn test_mutate_test_input_multiple_inputs() {
        let inputs = vec![
            (ConstValue::Int(10), Ty::i32()),
            (ConstValue::Uint(20, 64), Ty::u32()),
        ];
        let strategy = MutationStrategy::with_operators(&[MutationOperator::Negate]);
        let mutants = mutate_test_input("test_multi", &inputs, &strategy);
        // Should produce one mutant per input (negate on each)
        assert_eq!(mutants.len(), 2);
        // First mutant changes input 0, leaves input 1 unchanged
        assert!(!const_value_eq(&mutants[0].mutated_inputs[0], &ConstValue::Int(10)));
        assert!(const_value_eq(&mutants[0].mutated_inputs[1], &ConstValue::Uint(20, 64)));
        // Second mutant leaves input 0 unchanged, changes input 1
        assert!(const_value_eq(&mutants[1].mutated_inputs[0], &ConstValue::Int(10)));
        assert!(!const_value_eq(&mutants[1].mutated_inputs[1], &ConstValue::Uint(20, 64)));
    }

    #[test]
    fn test_apply_operator_negate_float() {
        let result = apply_operator(
            MutationOperator::Negate,
            &ConstValue::Float(3.125),
            &Ty::Float { width: 64 },
        )
        .unwrap();
        assert!(const_value_eq(&result, &ConstValue::Float(-3.125)));
    }

    #[test]
    fn test_max_unsigned_boundary_values() {
        assert_eq!(max_unsigned(8), u8::MAX as u128);
        assert_eq!(max_unsigned(16), u16::MAX as u128);
        assert_eq!(max_unsigned(32), u32::MAX as u128);
        assert_eq!(max_unsigned(64), u64::MAX as u128);
        assert_eq!(max_unsigned(128), u128::MAX);
    }

    // --- Structural vs heuristic mutation score comparison tests ---

    #[test]
    fn test_structural_rejects_operator_without_assert() {
        // Test code mentions the operator but has no assertion.
        // Heuristic: killed (string match). Structural: survived.
        let tests = vec![GeneratedTest {
            name: "test_no_assert".to_string(),
            code: "let x = a + b;".to_string(),
            boundary_values: vec![],
        }];
        let mutants = vec![Mutant {
            offset: 0,
            line: 1,
            mutation_type: MutationType::ArithOp,
            original: " + ".to_string(),
            mutated: " - ".to_string(),
        }];
        let heuristic = mutation_score_heuristic(&tests, &mutants);
        let structural = mutation_score(&tests, &mutants);
        assert!(
            (heuristic - 1.0).abs() < f64::EPSILON,
            "heuristic should match operator in code"
        );
        assert!(
            (structural - 0.0).abs() < f64::EPSILON,
            "structural should reject: no constraining assertion"
        );
    }

    #[test]
    fn test_structural_accepts_operator_with_assert_eq() {
        // Test code mentions the operator AND has assert_eq constraining the result.
        let tests = vec![GeneratedTest {
            name: "test_with_assert".to_string(),
            code: "let x = a + b;\nassert_eq!(x, 42);".to_string(),
            boundary_values: vec![],
        }];
        let mutants = vec![Mutant {
            offset: 0,
            line: 1,
            mutation_type: MutationType::ArithOp,
            original: " + ".to_string(),
            mutated: " - ".to_string(),
        }];
        let heuristic = mutation_score_heuristic(&tests, &mutants);
        let structural = mutation_score(&tests, &mutants);
        assert!((heuristic - 1.0).abs() < f64::EPSILON);
        assert!(
            (structural - 1.0).abs() < f64::EPSILON,
            "structural should accept: assert_eq constrains the value"
        );
    }

    #[test]
    fn test_structural_accepts_operator_with_relational_assert() {
        // Test has assert!() with a comparison operator.
        let tests = vec![GeneratedTest {
            name: "test_relational".to_string(),
            code: "let r = a + b;\nassert!(r > 0);".to_string(),
            boundary_values: vec![],
        }];
        let mutants = vec![Mutant {
            offset: 0,
            line: 1,
            mutation_type: MutationType::ArithOp,
            original: " + ".to_string(),
            mutated: " - ".to_string(),
        }];
        let score = mutation_score(&tests, &mutants);
        assert!(
            (score - 1.0).abs() < f64::EPSILON,
            "assert!(r > 0) constrains the arithmetic result"
        );
    }

    #[test]
    fn test_structural_rejects_assert_true() {
        // assert!(true) does not constrain any value.
        let tests = vec![GeneratedTest {
            name: "test_trivial".to_string(),
            code: "let x = a + b;\nassert!(true);".to_string(),
            boundary_values: vec![],
        }];
        let mutants = vec![Mutant {
            offset: 0,
            line: 1,
            mutation_type: MutationType::ArithOp,
            original: " + ".to_string(),
            mutated: " - ".to_string(),
        }];
        let score = mutation_score(&tests, &mutants);
        assert!(
            (score - 0.0).abs() < f64::EPSILON,
            "assert!(true) does not constrain the arithmetic result"
        );
    }

    #[test]
    fn test_structural_boundary_shift_with_boundary_values() {
        // BoundaryShift mutant killed when test has boundary values and assert.
        let tests = vec![GeneratedTest {
            name: "test_boundary".to_string(),
            code: "assert_eq!(f(42), expected);".to_string(),
            boundary_values: vec!["42".to_string(), "43".to_string()],
        }];
        let mutants = vec![Mutant {
            offset: 0,
            line: 1,
            mutation_type: MutationType::BoundaryShift,
            original: "42".to_string(),
            mutated: "43".to_string(),
        }];
        let score = mutation_score(&tests, &mutants);
        assert!(
            (score - 1.0).abs() < f64::EPSILON,
            "boundary shift should be killed by test with matching boundary values"
        );
    }

    #[test]
    fn test_structural_return_value_requires_result_check() {
        // ReturnValue mutant not killed if test doesn't check the result.
        let tests_no_check = vec![GeneratedTest {
            name: "test_no_check".to_string(),
            code: "f(42);".to_string(),
            boundary_values: vec![],
        }];
        let tests_with_check = vec![GeneratedTest {
            name: "test_with_check".to_string(),
            code: "let result = f(42);\nassert_eq!(result, 42);".to_string(),
            boundary_values: vec![],
        }];
        let mutants = vec![Mutant {
            offset: 0,
            line: 1,
            mutation_type: MutationType::ReturnValue,
            original: "return result".to_string(),
            mutated: "return Default::default()".to_string(),
        }];
        let score_no_check = mutation_score(&tests_no_check, &mutants);
        let score_with_check = mutation_score(&tests_with_check, &mutants);
        assert!(
            (score_no_check - 0.0).abs() < f64::EPSILON,
            "no result check means mutant survives"
        );
        assert!(
            (score_with_check - 1.0).abs() < f64::EPSILON,
            "result check kills return value mutant"
        );
    }

    #[test]
    fn test_structural_vs_heuristic_false_positive_rate() {
        // Demonstrate that heuristic produces false positives that structural rejects.
        // Test code mentions the operator but has NO assertion -- structural rejects,
        // heuristic accepts.
        let tests = vec![GeneratedTest {
            name: "test_no_assert".to_string(),
            code: "let x = a + b;\nlet y = a * b;\nprintln!(\"{x} {y}\");".to_string(),
            boundary_values: vec![],
        }];
        let mutants = vec![
            Mutant {
                offset: 0,
                line: 1,
                mutation_type: MutationType::ArithOp,
                original: " + ".to_string(),
                mutated: " - ".to_string(),
            },
            Mutant {
                offset: 10,
                line: 2,
                mutation_type: MutationType::ArithOp,
                original: " * ".to_string(),
                mutated: " / ".to_string(),
            },
        ];
        let heuristic = mutation_score_heuristic(&tests, &mutants);
        let structural = mutation_score(&tests, &mutants);
        // Heuristic: 2/2 killed (matches " + " and " * " in the code)
        assert!(
            (heuristic - 1.0).abs() < f64::EPSILON,
            "heuristic kills all: operators present in code, got {heuristic}"
        );
        // Structural: 0/2 killed (no assertions at all)
        assert!(
            (structural - 0.0).abs() < f64::EPSILON,
            "structural kills none: no constraining assertions, got {structural}"
        );
        assert!(
            heuristic > structural,
            "heuristic ({heuristic}) should exceed structural ({structural})"
        );
    }

    #[test]
    fn test_heuristic_score_matches_old_behavior() {
        // Verify the heuristic function preserves the original string-matching behavior.
        let tests = vec![GeneratedTest {
            name: "t".to_string(),
            code: "let x = a + b;".to_string(),
            boundary_values: vec![],
        }];
        let mutants = vec![Mutant {
            offset: 0,
            line: 1,
            mutation_type: MutationType::ArithOp,
            original: " + ".to_string(),
            mutated: " - ".to_string(),
        }];
        let score = mutation_score_heuristic(&tests, &mutants);
        assert!(
            (score - 1.0).abs() < f64::EPSILON,
            "heuristic should match: code contains the original operator"
        );
    }

    #[test]
    fn test_has_value_constraining_assert_patterns() {
        assert!(has_value_constraining_assert("assert_eq!(x, 42);", "+"));
        assert!(has_value_constraining_assert("assert_ne!(x, 0);", "+"));
        assert!(has_value_constraining_assert("assert!(x > 0);", "+"));
        assert!(has_value_constraining_assert("assert!(x == 42);", "+"));
        assert!(has_value_constraining_assert("assert!(x >= y);", "+"));
        assert!(!has_value_constraining_assert("assert!(true);", "+"));
        assert!(!has_value_constraining_assert("assert!(x.is_ok());", "+"));
        assert!(!has_value_constraining_assert("let x = a + b;", "+"));
        assert!(!has_value_constraining_assert("// assert_eq!(x, 42);", "+"));
    }
}
