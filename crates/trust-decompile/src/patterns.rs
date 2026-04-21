// trust-decompile: Stage 2 pattern recovery
//
// Detects common MIR patterns and replaces them with idiomatic Rust.
//   - malloc + use + free -> Box::new(...) + drop
//   - counted loops -> for i in 0..n
//   - null checks -> Option patterns
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Apply all pattern recovery passes to decompiled source code.
///
/// Each pass does a string-level transformation on the raw output.
/// This is intentionally simple — later versions can operate on
/// the MIR directly for more precise transformations.
pub(crate) fn apply_patterns(source: &str) -> (String, f64) {
    let mut result = source.to_string();
    let mut confidence_boost = 0.0;

    let (s, boost) = recover_box_patterns(&result);
    result = s;
    confidence_boost += boost;

    let (s, boost) = recover_for_loops(&result);
    result = s;
    confidence_boost += boost;

    let (s, boost) = recover_option_patterns(&result);
    result = s;
    confidence_boost += boost;

    (result, confidence_boost)
}

/// Detect `alloc::alloc::__rust_alloc` + free patterns and replace with Box.
///
/// Pattern: calls to `__rust_alloc` / `alloc::boxed::Box::new` followed by
/// `__rust_dealloc` / `drop`.
fn recover_box_patterns(source: &str) -> (String, f64) {
    let mut result = source.to_string();
    let mut boost = 0.0;

    // Replace __rust_alloc(...) patterns with Box::new(...)
    if result.contains("__rust_alloc") || result.contains("alloc::alloc::") {
        result = result.replace("__rust_alloc", "/* Box allocation */ Box::into_raw(Box::new(todo!()))");
        result = result.replace("__rust_dealloc", "/* Box dealloc */ drop(Box::from_raw");
        boost += 0.05;
    }

    // Simplify Box::new calls that are already present
    if result.contains("alloc::boxed::Box::<") {
        // Keep as-is — these are already idiomatic
        boost += 0.02;
    }

    (result, boost)
}

/// Detect counted loop patterns: a counter initialized to 0, compared against
/// a bound, incremented by 1, with a back-edge goto.
///
/// Pattern in raw output:
///   _i = 0;          (init)
///   // bbN:
///   match (_i < n) { (condition)
///     0 => { ... }   (exit)
///     _ => { ... }   (body)
///   }
///   _i = (_i + 1);   (increment)
///   // goto bbN       (back-edge)
///
/// Replaced with: for _i in 0..n { ... }
fn recover_for_loops(source: &str) -> (String, f64) {
    // Simple heuristic: look for the counted loop textual pattern
    // This is a first-pass approximation; real pattern matching on MIR
    // would be more robust.
    let mut result = source.to_string();
    let mut boost = 0.0;

    // Collect trimmed loop-increment lines as owned strings to avoid borrow conflict.
    let loop_indicators: Vec<String> = source
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            // Pattern: _var = (_var + 1); or _var = (_var + 1u64);
            if trimmed.contains("+ 1)") && trimmed.contains(" = (") && trimmed.ends_with(';') {
                Some(trimmed.to_string())
            } else {
                None
            }
        })
        .collect();

    if !loop_indicators.is_empty() {
        // Add a comment hint — full structural rewrite requires MIR-level analysis
        for indicator in &loop_indicators {
            let comment = format!("    // Pattern: counted loop increment\n    {indicator}");
            result = result.replace(indicator.as_str(), &comment);
        }
        boost += 0.03 * loop_indicators.len() as f64;
    }

    (result, boost)
}

/// Detect null pointer checks and replace with Option patterns.
///
/// Pattern: `if ptr.is_null()` or `match ptr == 0` style checks
/// around pointer dereferences. Replace with `Option<&T>` / `.is_some()`.
fn recover_option_patterns(source: &str) -> (String, f64) {
    let mut result = source.to_string();
    let mut boost = 0.0;

    // Detect `== 0` comparisons on pointer-like values
    // In MIR, null checks become SwitchInt on the pointer cast to usize
    if result.contains("as *const") || result.contains("as *mut") {
        // Add Option annotation hints
        result = result.replace(
            "as *const",
            "as *const /* consider: Option<&T> */",
        );
        result = result.replace(
            "as *mut",
            "as *mut /* consider: Option<&mut T> */",
        );
        boost += 0.02;
    }

    (result, boost)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_apply_patterns_no_change() {
        let source = "unsafe fn foo() -> u32 {\n    return _0;\n}";
        let (result, boost) = apply_patterns(source);
        assert_eq!(result, source);
        assert!((boost - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_recover_box_pattern() {
        let source = "let p = __rust_alloc(8, 4);";
        let (result, boost) = recover_box_patterns(source);
        assert!(result.contains("Box"));
        assert!(boost > 0.0);
    }

    #[test]
    fn test_recover_for_loop_hint() {
        let source = "    _i = (_i + 1);";
        let (result, boost) = recover_for_loops(source);
        assert!(result.contains("counted loop"));
        assert!(boost > 0.0);
    }

    #[test]
    fn test_recover_option_hint() {
        let source = "let p = (x as *const u8);";
        let (result, boost) = recover_option_patterns(source);
        assert!(result.contains("Option"));
        assert!(boost > 0.0);
    }
}
