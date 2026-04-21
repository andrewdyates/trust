// tests/mock_compiler.rs: Mock compiler stderr output for golden tests
//
// Hardcoded stderr strings representing what stage1 rustc outputs when
// verifying binary_search.rs at each iteration of the loop.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Mock stderr for iteration 1: 3 overflow bugs detected.
///
/// Represents the initial verification of buggy binary_search.rs:
/// - overflow:add — `(low + high) / 2` can overflow usize
/// - overflow:shift — `high >> 1` shift by >= bit width is UB
/// - overflow:cast — `mid as i32` truncation when usize > i32::MAX
pub fn mock_stderr_iter1() -> &'static str {
    concat!(
        "note: [trust-verify] verifying `binary_search`\n",
        "note: [trust-verify]   VC 1/3: overflow:add at binary_search.rs:6:19\n",
        "note: [trust-verify]     (low + high) / 2 — addition may overflow usize\n",
        "note: [trust-verify]     counterexample: low = 9223372036854775807, high = 9223372036854775807\n",
        "note: [trust-verify]     [FAIL] overflow:add (z4, 8ms)\n",
        "note: [trust-verify]   VC 2/3: overflow:shift at binary_search.rs:6:30\n",
        "note: [trust-verify]     high >> 1 — shift may exceed bit width\n",
        "note: [trust-verify]     counterexample: high = 18446744073709551615\n",
        "note: [trust-verify]     [FAIL] overflow:shift (z4, 5ms)\n",
        "note: [trust-verify]   VC 3/3: overflow:cast at binary_search.rs:8:12\n",
        "note: [trust-verify]     mid as i32 — usize-to-i32 truncation\n",
        "note: [trust-verify]     counterexample: mid = 2147483648\n",
        "note: [trust-verify]     [FAIL] overflow:cast (z4, 3ms)\n",
        "note: [trust-verify] result: 0 proved, 3 failed, 0 unknown (16ms total)\n",
    )
}

/// Mock stderr for iteration 2: 2 proved, 1 remaining.
///
/// After backprop applied fixes for overflow:add and overflow:shift:
/// - overflow:add — PROVED (safe midpoint formula)
/// - overflow:shift — PROVED (wrapping shift)
/// - overflow:cast — still FAILS (not yet fixed)
pub fn mock_stderr_iter2() -> &'static str {
    concat!(
        "note: [trust-verify] verifying `binary_search`\n",
        "note: [trust-verify]   VC 1/3: overflow:add at binary_search.rs:6:19\n",
        "note: [trust-verify]     low + (high - low) / 2 — safe midpoint\n",
        "note: [trust-verify]     [PROVED] overflow:add (z4, 4ms)\n",
        "note: [trust-verify]   VC 2/3: overflow:shift at binary_search.rs:6:30\n",
        "note: [trust-verify]     high.wrapping_shr(1) — wrapping shift\n",
        "note: [trust-verify]     [PROVED] overflow:shift (z4, 3ms)\n",
        "note: [trust-verify]   VC 3/3: overflow:cast at binary_search.rs:8:12\n",
        "note: [trust-verify]     mid as i32 — usize-to-i32 truncation\n",
        "note: [trust-verify]     counterexample: mid = 2147483648\n",
        "note: [trust-verify]     [FAIL] overflow:cast (z4, 3ms)\n",
        "note: [trust-verify] result: 2 proved, 1 failed, 0 unknown (10ms total)\n",
    )
}

/// Mock stderr for iteration 3: all proved.
///
/// After backprop applied fix for overflow:cast:
/// - overflow:add — PROVED
/// - overflow:shift — PROVED
/// - overflow:cast — PROVED (try_from)
pub fn mock_stderr_iter3() -> &'static str {
    concat!(
        "note: [trust-verify] verifying `binary_search`\n",
        "note: [trust-verify]   VC 1/3: overflow:add at binary_search.rs:6:19\n",
        "note: [trust-verify]     low + (high - low) / 2 — safe midpoint\n",
        "note: [trust-verify]     [PROVED] overflow:add (z4, 4ms)\n",
        "note: [trust-verify]   VC 2/3: overflow:shift at binary_search.rs:6:30\n",
        "note: [trust-verify]     high.wrapping_shr(1) — wrapping shift\n",
        "note: [trust-verify]     [PROVED] overflow:shift (z4, 3ms)\n",
        "note: [trust-verify]   VC 3/3: overflow:cast at binary_search.rs:8:12\n",
        "note: [trust-verify]     i32::try_from(mid).expect(\"index fits i32\") — checked cast\n",
        "note: [trust-verify]     [PROVED] overflow:cast (z4, 2ms)\n",
        "note: [trust-verify] result: 3 proved, 0 failed, 0 unknown (9ms total)\n",
    )
}
