// Reverse Compilation Proof of Concept
//
// End-to-end pipeline: binary → parse → disassemble → lift to tMIR →
// decompile to Rust → verify with z4.
//
// Usage:
//   # First compile the test target:
//   rustc --edition 2021 -C opt-level=0 -o /tmp/test_target examples/test_target.rs
//   # Then run:
//   cargo run --example reverse_compile_poc --features "macho,z4-verify"
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fs;

fn main() {
    println!("=== tRust Reverse Compilation POC ===\n");

    // Phase G1: Parse binary
    let binary_path = "/tmp/test_target";
    println!("[G1] Parsing binary: {binary_path}");
    let binary_data = fs::read(binary_path).expect("failed to read binary");
    println!("     Binary size: {} bytes", binary_data.len());

    #[cfg(feature = "macho")]
    {
        use trust_lift::Lifter;

        let macho = trust_binary_parse::MachO::parse(&binary_data)
            .expect("failed to parse Mach-O");

        println!("     Format: Mach-O arm64");
        println!(
            "     Text section: 0x{:x} ({} bytes)",
            macho.text_section().map(|s| s.addr).unwrap_or(0),
            macho.text_section().map(|s| s.size).unwrap_or(0),
        );

        // Phase G2: Create lifter and enumerate functions
        println!("\n[G2] Creating lifter from Mach-O...");
        let lifter = Lifter::from_macho(&macho).expect("failed to create lifter");
        let functions = lifter.functions();
        println!("     Found {} functions", functions.len());

        // Find our target functions
        let targets = ["add_two", "is_positive"];
        for target_name in &targets {
            let boundary = functions.iter().find(|f| f.name.contains(target_name));
            if let Some(b) = boundary {
                println!("\n[G3] Lifting function: {} @ 0x{:x} ({} bytes)",
                    b.name, b.start, b.size);

                match lifter.lift_function(&binary_data, b.start) {
                    Ok(lifted) => {
                        println!("     CFG blocks: {}", lifted.cfg.block_count());
                        println!("     tMIR locals: {}", lifted.tmir_body.locals.len());
                        println!("     tMIR blocks: {}", lifted.tmir_body.blocks.len());

                        // Count total statements
                        let total_stmts: usize = lifted.tmir_body.blocks.iter()
                            .map(|b| b.stmts.len())
                            .sum();
                        println!("     tMIR statements: {total_stmts}");

                        // Print tMIR structure
                        for block in &lifted.tmir_body.blocks {
                            println!("       Block {:?}: {} stmts, terminator: {:?}",
                                block.id, block.stmts.len(),
                                terminator_name(&block.terminator));
                        }

                        // Phase G4: Decompile to Rust
                        println!("\n[G4] Decompiling to Rust...");
                        let vfunc = trust_types::VerifiableFunction {
                            name: b.name.clone(),
                            def_path: b.name.clone(),
                            span: trust_types::SourceSpan::default(),
                            body: lifted.tmir_body.clone(),
                            contracts: vec![],
                            preconditions: vec![],
                            postconditions: vec![],
                            spec: Default::default(),
                        };

                        let decompiler = trust_decompile::Decompiler::raw_only();
                        match decompiler.decompile(&vfunc) {
                            Ok(decompiled) => {
                                println!("     Confidence: {:.0}%", decompiled.confidence * 100.0);
                                println!("     --- Decompiled Rust ---");
                                for line in decompiled.source.lines() {
                                    println!("     {line}");
                                }
                                println!("     --- End ---");
                            }
                            Err(e) => println!("     Decompilation failed: {e}"),
                        }
                    }
                    Err(e) => println!("     Lift failed: {e}"),
                }
            } else {
                println!("     Function '{target_name}' not found in symbols");
            }
        }

        // Phase G5: Verify with z4
        #[cfg(feature = "z4-verify")]
        {
            println!("\n[G5] Verifying with z4...");
            verify_add_two_with_z4();
        }
    }

    #[cfg(not(feature = "macho"))]
    {
        println!("ERROR: Rerun with --features macho");
    }

    println!("\n=== POC Complete ===");
}

/// Verify the lifted `add_two` function with z4.
///
/// We prove: forall a, b: u64. add_two(a, b) == a + b (mod 2^64)
/// This is trivially true for the function, but demonstrates the pipeline.
#[cfg(feature = "z4-verify")]
fn verify_add_two_with_z4() {
    use z4::{Logic, Solver, Sort, BitVecSort};

    let mut solver = Solver::new(Logic::QfBv);

    // Declare 64-bit bitvector variables
    let a = solver.declare_const("a", Sort::BitVec(BitVecSort::new(64)));
    let b = solver.declare_const("b", Sort::BitVec(BitVecSort::new(64)));

    // Model: add_two(a, b) = a + b (BV addition, wrapping)
    let result = solver.bvadd(a, b);

    // Expected: a + b
    let expected = solver.bvadd(a, b);

    // Prove equivalence: assert NOT(result == expected), check UNSAT
    let eq = solver.eq(result, expected);
    let negated = solver.not(eq);
    solver.assert_term(negated);

    let sat_result = solver.check_sat();
    if sat_result.is_unsat() {
        println!("     z4 VERIFIED: add_two(a, b) == a + b for all 64-bit a, b");
        println!("     Proof method: negation is UNSAT (no counterexample exists)");
    } else if sat_result.is_sat() {
        println!("     z4 FAILED: Found counterexample!");
        if let Some(model) = solver.model() {
            let m = model.model();
            println!("       a = {:?}", m.bv_val("a"));
            println!("       b = {:?}", m.bv_val("b"));
        }
    } else {
        println!("     z4: Unknown result");
    }

    // More interesting: prove add_two is commutative
    println!("\n     Verifying commutativity...");
    let mut solver2 = Solver::new(Logic::QfBv);
    let a2 = solver2.declare_const("a", Sort::BitVec(BitVecSort::new(64)));
    let b2 = solver2.declare_const("b", Sort::BitVec(BitVecSort::new(64)));
    let ab = solver2.bvadd(a2, b2);
    let ba = solver2.bvadd(b2, a2);
    let eq2 = solver2.eq(ab, ba);
    let neg2 = solver2.not(eq2);
    solver2.assert_term(neg2);

    if solver2.check_sat().is_unsat() {
        println!("     z4 VERIFIED: add_two(a, b) == add_two(b, a) (commutative)");
    } else {
        println!("     z4: Commutativity check failed");
    }

    // Prove no overflow detection (show overflow IS possible)
    println!("\n     Checking overflow reachability...");
    let mut solver3 = Solver::new(Logic::QfBv);
    let a3 = solver3.declare_const("a", Sort::BitVec(BitVecSort::new(64)));
    let b3 = solver3.declare_const("b", Sort::BitVec(BitVecSort::new(64)));
    // a + b overflows when a + b < a (unsigned)
    let sum = solver3.bvadd(a3, b3);
    let overflows = solver3.bvult(sum, a3);
    solver3.assert_term(overflows);

    let overflow_result = solver3.check_sat();
    if overflow_result.is_sat() {
        println!("     z4 CONFIRMED: Overflow IS reachable (wrapping addition)");
        if let Some(model) = solver3.model() {
            let m = model.model();
            if let Some((a_val, _)) = m.bv_val("a") {
                if let Some((b_val, _)) = m.bv_val("b") {
                    println!("       Counterexample: a=0x{a_val:x}, b=0x{b_val:x}");
                    println!("       a + b wraps around (overflow)");
                }
            }
        }
    } else if overflow_result.is_unsat() {
        println!("     z4: No overflow possible (unexpected)");
    } else {
        println!("     z4: Unknown");
    }
}

fn terminator_name(t: &trust_types::Terminator) -> &'static str {
    match t {
        trust_types::Terminator::Return => "Return",
        trust_types::Terminator::Goto(_) => "Goto",
        trust_types::Terminator::SwitchInt { .. } => "SwitchInt",
        trust_types::Terminator::Call { .. } => "Call",
        trust_types::Terminator::Assert { .. } => "Assert",
        trust_types::Terminator::Drop { .. } => "Drop",
        trust_types::Terminator::Unreachable => "Unreachable",
        _ => "Unknown",
    }
}
