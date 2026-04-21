use std::path::PathBuf;

use crate::arg_parser::TidyArgParser;

// Test all arguments
#[test]
fn test_tidy_parser_full() {
    let args = vec![
        "rust-tidy",
        "--root-path",
        "./rust",
        "--cargo-path",
        "./rust/build/x86_64-unknown-linux-gnu/stage0/bin/cargo",
        "--output-dir",
        "./rust/build",
        "--concurrency",
        "16",
        "--npm-path",
        "yarn",
        "--verbose",
        "--bless",
        "--ci",
        "--extra-checks",
        "if-installed:auto:js,auto:if-installed:py,if-installed:auto:cpp,if-installed:auto:spellcheck",
        "--", // pos_args
        "some-file",
        "some-file2",
    ];
    let cmd = TidyArgParser::command();
    let parsed_args = TidyArgParser::build(cmd.get_matches_from(args));

    assert_eq!(parsed_args.root_path, PathBuf::from("./rust"));
    assert_eq!(
        parsed_args.cargo,
        PathBuf::from("./rust/build/x86_64-unknown-linux-gnu/stage0/bin/cargo")
    );
    assert_eq!(parsed_args.output_directory, PathBuf::from("./rust/build"));
    assert_eq!(parsed_args.concurrency.get(), 16);
    assert_eq!(parsed_args.npm, PathBuf::from("yarn"));
    assert!(parsed_args.verbose);
    assert!(parsed_args.bless);
    assert!(parsed_args.ci.is_some());
    assert!(parsed_args.ci.unwrap());
    assert_eq!(
        parsed_args.extra_checks,
        Some(vec![
            "if-installed:auto:js".to_string(),
            "auto:if-installed:py".to_string(),
            "if-installed:auto:cpp".to_string(),
            "if-installed:auto:spellcheck".to_string(),
        ])
    );
    assert_eq!(parsed_args.pos_args, vec!["some-file".to_string(), "some-file2".to_string()]);
}

// The parser can take required args any order
#[test]
fn test_tidy_parser_any_order() {
    let args = vec![
        "rust-tidy",
        "--npm-path",
        "yarn",
        "--concurrency",
        "16",
        "--output-dir",
        "./rust/build",
        "--cargo-path",
        "./rust/build/x86_64-unknown-linux-gnu/stage0/bin/cargo",
        "--root-path",
        "./rust",
    ];
    let cmd = TidyArgParser::command();
    let parsed_args = TidyArgParser::build(cmd.get_matches_from(args));

    assert_eq!(parsed_args.root_path, PathBuf::from("./rust"));
    assert_eq!(
        parsed_args.cargo,
        PathBuf::from("./rust/build/x86_64-unknown-linux-gnu/stage0/bin/cargo")
    );
    assert_eq!(parsed_args.output_directory, PathBuf::from("./rust/build"));
    assert_eq!(parsed_args.concurrency.get(), 16);
    assert_eq!(parsed_args.npm, PathBuf::from("yarn"));
}

// --root-path is required
#[test]
fn test_tidy_parser_missing_root_path() {
    let args = vec![
        "rust-tidy",
        "--npm-path",
        "yarn",
        "--concurrency",
        "16",
        "--output-dir",
        "./rust/build",
        "--cargo-path",
        "./rust/build/x86_64-unknown-linux-gnu/stage0/bin/cargo",
    ];
    let cmd = TidyArgParser::command();
    assert!(cmd.try_get_matches_from(args).is_err());
}

// --cargo-path is required
#[test]
fn test_tidy_parser_missing_cargo_path() {
    let args = vec![
        "rust-tidy",
        "--npm-path",
        "yarn",
        "--concurrency",
        "16",
        "--output-dir",
        "./rust/build",
        "--root-path",
        "./rust",
    ];
    let cmd = TidyArgParser::command();
    assert!(cmd.try_get_matches_from(args).is_err());
}

// --output-dir is required
#[test]
fn test_tidy_parser_missing_output_dir() {
    let args = vec![
        "rust-tidy",
        "--npm-path",
        "yarn",
        "--concurrency",
        "16",
        "--cargo-path",
        "./rust/build/x86_64-unknown-linux-gnu/stage0/bin/cargo",
        "--root-path",
        "./rust",
    ];
    let cmd = TidyArgParser::command();
    assert!(cmd.try_get_matches_from(args).is_err());
}

// --concurrency is required
#[test]
fn test_tidy_parser_missing_concurrency() {
    let args = vec![
        "rust-tidy",
        "--npm-path",
        "yarn",
        "--output-dir",
        "./rust/build",
        "--cargo-path",
        "./rust/build/x86_64-unknown-linux-gnu/stage0/bin/cargo",
        "--root-path",
        "./rust",
    ];
    let cmd = TidyArgParser::command();
    assert!(cmd.try_get_matches_from(args).is_err());
}

// --npm-path is required
#[test]
fn test_tidy_parser_missing_npm_path() {
    let args = vec![
        "rust-tidy",
        "--concurrency",
        "16",
        "--output-dir",
        "./rust/build",
        "--cargo-path",
        "./rust/build/x86_64-unknown-linux-gnu/stage0/bin/cargo",
    ];
    let cmd = TidyArgParser::command();
    assert!(cmd.try_get_matches_from(args).is_err());
}

// --ci has some variations
#[test]
fn test_tidy_parse_ci_flag() {
    // They are requried
    let base_args = vec![
        "rust-tidy",
        "--root-path",
        "./rust",
        "--cargo-path",
        "./rust/build/x86_64-unknown-linux-gnu/stage0/bin/cargo",
        "--output-dir",
        "./rust/build",
        "--concurrency",
        "16",
        "--npm-path",
        "yarn",
    ];

    // No --ci
    let parsed_args = TidyArgParser::build(TidyArgParser::command().get_matches_from(&base_args));
    assert!(parsed_args.ci.is_none());

    // --ci
    let mut args1 = base_args.clone();
    args1.push("--ci");
    let parsed_args = TidyArgParser::build(TidyArgParser::command().get_matches_from(args1));
    assert!(parsed_args.ci.is_some());

    // --ci=true
    let mut args2 = base_args.clone();
    args2.extend_from_slice(&["--ci", "true"]);
    let parsed_args = TidyArgParser::build(TidyArgParser::command().get_matches_from(args2));
    assert!(parsed_args.ci.is_some());
    assert!(parsed_args.ci.unwrap());

    // --ci=false
    let mut args2 = base_args.clone();
    args2.extend_from_slice(&["--ci", "false"]);
    let parsed_args = TidyArgParser::build(TidyArgParser::command().get_matches_from(args2));
    assert!(parsed_args.ci.is_some());
    assert!(!parsed_args.ci.unwrap());
}
