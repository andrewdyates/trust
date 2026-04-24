// trust-integration-tests/tests/binary_to_tmir_e2e.rs
//
// End-to-end scaffold for binary -> parse -> lift -> tMIR -> VC generation.

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use trust_binary_parse::Elf64;
use trust_lift::{BinaryLiftOptions, Lifter, LocalLayout};
use trust_types::{Terminator, VcKind};

const FIXTURE_SYMBOL: &str = "trust_fixture_return";

const X86_64_RET_ASM: &str = r#"
    .text
    .byte 0x90
    .globl trust_fixture_return
    .type trust_fixture_return,@function
trust_fixture_return:
    retq
    .size trust_fixture_return, .-trust_fixture_return
    .section .note.GNU-stack,"",@progbits
"#;

#[test]
fn test_generated_elf_parse_lift_tmir_and_binary_vcs() {
    let tmp = tempfile::tempdir().expect("create temp fixture dir");
    let elf_path = match build_x86_64_elf_fixture(tmp.path()) {
        Ok(path) => path,
        Err(reason) => {
            eprintln!("SKIP: {reason}");
            return;
        }
    };

    let bytes = fs::read(&elf_path)
        .unwrap_or_else(|e| panic!("failed to read fixture {}: {e}", elf_path.display()));
    let elf = Elf64::parse(&bytes)
        .unwrap_or_else(|e| panic!("failed to parse generated ELF {}: {e}", elf_path.display()));
    assert_eq!(elf.header.e_machine, 0x3e, "fixture must be x86_64 ELF");

    let lifted_binary = trust_lift::lift_binary_to_tmir(
        &bytes,
        BinaryLiftOptions::functions_by_name([FIXTURE_SYMBOL]),
    )
    .expect("public binary-to-tMIR API should lift fixture symbol");
    assert_eq!(lifted_binary.format, "ELF");
    assert_eq!(lifted_binary.architecture, "x86-64");
    assert_eq!(lifted_binary.functions.len(), 1);
    assert!(lifted_binary.failures.is_empty());

    let lifter = Lifter::from_elf(&elf).expect("x86_64 ELF should create a lifter");
    let boundary =
        lifter.functions().iter().find(|boundary| boundary.name == FIXTURE_SYMBOL).unwrap_or_else(
            || {
                panic!(
                    "expected {FIXTURE_SYMBOL} in detected ELF function symbols; got {:?}",
                    lifter.functions()
                )
            },
        );

    let lifted = lifter
        .lift_function(&bytes, boundary.start)
        .expect("generated ELF function should lift to tMIR");
    let api_lifted = &lifted_binary.functions[0];
    assert_eq!(api_lifted.name, lifted.name);
    assert_eq!(api_lifted.entry_point, lifted.entry_point);

    assert_eq!(lifted.name, FIXTURE_SYMBOL);
    assert_eq!(lifted.entry_point, boundary.start);
    assert_eq!(lifted.cfg.block_count(), 1, "ret-only fixture should recover one CFG block");
    assert_eq!(lifted.cfg.blocks[0].instructions.len(), 1, "ret should decode as one instruction");
    assert_eq!(lifted.tmir_body.locals.len(), LocalLayout::x86_64().total);
    assert!(
        lifted.tmir_body.blocks.iter().any(|block| matches!(block.terminator, Terminator::Return)),
        "lifted tMIR should contain a return terminator"
    );
    assert!(lifted.ssa.is_some(), "lift_function should attach SSA metadata");
    assert!(!lifted.annotations.is_empty(), "lift_function should annotate decoded instructions");

    let verifiable = trust_vcgen::lift_adapter::lift_to_verifiable(&lifted);
    assert_eq!(verifiable.name, FIXTURE_SYMBOL);
    assert_eq!(verifiable.def_path, format!("binary::{FIXTURE_SYMBOL}"));
    assert_eq!(verifiable.body.blocks.len(), lifted.tmir_body.blocks.len());

    let vcs = trust_vcgen::lift_adapter::generate_binary_vcs(&lifted);
    assert!(!vcs.is_empty(), "binary VC generation should produce at least stack discipline VCs");
    assert!(vcs.iter().all(|vc| vc.function == FIXTURE_SYMBOL));
    assert!(
        vcs.iter().any(|vc| {
            matches!(
                &vc.kind,
                VcKind::Assertion { message } if message.contains("stack pointer not restored")
            )
        }),
        "ret-only binary fixture should exercise the binary stack-discipline VC path"
    );
}

fn build_x86_64_elf_fixture(dir: &Path) -> Result<PathBuf, String> {
    let asm_path = dir.join("binary_to_tmir_return.s");
    let obj_path = dir.join("binary_to_tmir_return.o");
    fs::write(&asm_path, X86_64_RET_ASM)
        .map_err(|e| format!("could not write fixture assembly {}: {e}", asm_path.display()))?;

    let mut attempts = Vec::new();
    for compiler in candidate_compilers() {
        for args in compiler_arg_sets() {
            let _ = fs::remove_file(&obj_path);
            let mut cmd = Command::new(&compiler);
            cmd.args(&args).arg("-c").arg("-x").arg("assembler").arg(&asm_path);
            cmd.arg("-o").arg(&obj_path);

            match cmd.output() {
                Ok(output) if output.status.success() && obj_path.exists() => {
                    return Ok(obj_path);
                }
                Ok(output) => attempts.push(format_attempt(&compiler, &args, &output)),
                Err(e) => attempts.push(format!("{compiler} {:?}: {e}", args)),
            }
        }
    }

    Err(format!("could not build deterministic x86_64 ELF fixture; tried {}", attempts.join("; ")))
}

fn candidate_compilers() -> Vec<String> {
    let mut compilers = Vec::new();
    if let Ok(cc) = std::env::var("TRUST_TEST_CC") {
        if !cc.trim().is_empty() {
            compilers.push(cc);
        }
    }
    compilers.push("clang".to_string());
    compilers.push("cc".to_string());
    compilers.dedup();
    compilers
}

fn compiler_arg_sets() -> Vec<Vec<&'static str>> {
    let mut arg_sets = vec![vec!["--target=x86_64-unknown-linux-gnu"]];
    if std::env::consts::OS == "linux" && std::env::consts::ARCH == "x86_64" {
        arg_sets.push(vec![]);
    }
    arg_sets
}

fn format_attempt(compiler: &str, args: &[&str], output: &Output) -> String {
    let stderr = String::from_utf8_lossy(&output.stderr);
    let stderr = stderr.trim();
    let detail = if stderr.is_empty() { "no stderr".to_string() } else { stderr.to_string() };
    format!("{compiler} {args:?} exited with {} ({detail})", output.status)
}
