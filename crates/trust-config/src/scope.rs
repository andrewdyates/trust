// trust-config/scope.rs: Verification scope filtering
//
// Defines `VerificationScope` and `ScopeFilter` for controlling which
// functions enter the verification pipeline. Supports glob patterns
// (e.g., "my_module::*") without pulling in a regex dependency.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

/// tRust #234: Which functions to include in verification.
///
/// Used by trust-driver to decide which extracted `VerifiableFunction`s
/// proceed to VCGen. `All` is the default (verify everything that is
/// enabled in `TrustConfig`). The other variants narrow the scope.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum VerificationScope {
    /// Verify all functions (subject to TrustConfig skip/verify lists).
    #[default]
    All,
    /// Verify only functions whose `def_path` starts with the given module path.
    /// Supports glob: `"my_crate::util::*"` matches any function in `my_crate::util`.
    Module(String),
    /// Verify a single function by exact name or glob pattern.
    /// `"binary_search"` matches any function whose name equals `binary_search`.
    /// `"my_crate::*search*"` matches via glob.
    Function(String),
    /// Verify only functions that carry at least one spec annotation
    /// (`#[requires]`, `#[ensures]`, `#[invariant]`).
    Annotated,
}

/// tRust #234: Stateless filter that applies a `VerificationScope` to
/// function metadata.
///
/// # Example
///
/// ```
/// use trust_config::scope::{ScopeFilter, VerificationScope};
///
/// let scope = VerificationScope::Module("my_crate::util::*".into());
/// assert!(ScopeFilter::matches(&scope, "helper", "my_crate::util::helper", true));
/// assert!(!ScopeFilter::matches(&scope, "main", "my_crate::main", false));
/// ```
pub struct ScopeFilter;

impl ScopeFilter {
    /// Returns `true` if the function passes the scope filter.
    ///
    /// * `scope`       — the active verification scope
    /// * `func_name`   — short function name (e.g., `"binary_search"`)
    /// * `func_path`   — fully-qualified path (e.g., `"my_crate::search::binary_search"`)
    /// * `has_specs`    — whether the function has any spec annotations
    #[must_use]
    pub fn matches(
        scope: &VerificationScope,
        func_name: &str,
        func_path: &str,
        has_specs: bool,
    ) -> bool {
        match scope {
            VerificationScope::All => true,
            VerificationScope::Module(pattern) => glob_matches(pattern, func_path),
            VerificationScope::Function(pattern) => {
                // Try matching against both the short name and the full path.
                glob_matches(pattern, func_name) || glob_matches(pattern, func_path)
            }
            VerificationScope::Annotated => has_specs,
        }
    }
}

/// tRust #234: Filter a slice of function metadata by scope.
///
/// Each element is `(name, def_path, has_specs)`. Returns indices of
/// functions that match. This avoids coupling to `VerifiableFunction`
/// directly (which lives in trust-types).
#[must_use]
pub fn filter_functions<'a, I>(scope: &VerificationScope, functions: I) -> Vec<usize>
where
    I: IntoIterator<Item = (&'a str, &'a str, bool)>,
{
    functions
        .into_iter()
        .enumerate()
        .filter(|(_, (name, path, has_specs))| ScopeFilter::matches(scope, name, path, *has_specs))
        .map(|(idx, _)| idx)
        .collect()
}

// ---------------------------------------------------------------------------
// Simple glob matching (no regex dependency)
// ---------------------------------------------------------------------------

/// Match `pattern` against `text` using simple glob rules:
///
/// - `*` matches zero or more characters (non-greedy within a segment)
/// - `?` matches exactly one character
/// - All other characters match literally
///
/// The match is against the **entire** `text` (anchored at both ends).
#[must_use]
pub(crate) fn glob_matches(pattern: &str, text: &str) -> bool {
    glob_matches_inner(pattern.as_bytes(), text.as_bytes())
}

/// Recursive byte-level glob matcher. Uses a two-pointer approach with
/// backtracking on `*`. The recursion depth is bounded by the number of
/// `*` characters in the pattern, which is tiny in practice.
fn glob_matches_inner(pattern: &[u8], text: &[u8]) -> bool {
    let mut pi = 0;
    let mut ti = 0;
    let mut star_pi: Option<usize> = None;
    let mut star_ti: usize = 0;

    while ti < text.len() {
        if pi < pattern.len() && (pattern[pi] == b'?' || pattern[pi] == text[ti]) {
            pi += 1;
            ti += 1;
        } else if pi < pattern.len() && pattern[pi] == b'*' {
            star_pi = Some(pi);
            star_ti = ti;
            pi += 1;
        } else if let Some(sp) = star_pi {
            pi = sp + 1;
            star_ti += 1;
            ti = star_ti;
        } else {
            return false;
        }
    }

    // Consume trailing stars in the pattern.
    while pi < pattern.len() && pattern[pi] == b'*' {
        pi += 1;
    }

    pi == pattern.len()
}

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------------
    // glob_matches unit tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_glob_exact_match() {
        assert!(glob_matches("hello", "hello"));
        assert!(!glob_matches("hello", "world"));
    }

    #[test]
    fn test_glob_star_suffix() {
        assert!(glob_matches("my_crate::*", "my_crate::foo"));
        assert!(glob_matches("my_crate::*", "my_crate::foo::bar"));
        assert!(!glob_matches("my_crate::*", "other_crate::foo"));
    }

    #[test]
    fn test_glob_star_prefix() {
        assert!(glob_matches("*::search", "my_crate::search"));
        assert!(!glob_matches("*::search", "my_crate::search::inner"));
    }

    #[test]
    fn test_glob_star_middle() {
        assert!(glob_matches("my_crate::*::helper", "my_crate::util::helper"));
        assert!(glob_matches("my_crate::*::helper", "my_crate::deep::nested::helper"));
    }

    #[test]
    fn test_glob_double_star() {
        assert!(glob_matches("**", "anything"));
        assert!(glob_matches("**", ""));
    }

    #[test]
    fn test_glob_question_mark() {
        assert!(glob_matches("he??o", "hello"));
        assert!(glob_matches("he??o", "heyyo"));
        assert!(!glob_matches("he??o", "helllo"));
    }

    #[test]
    fn test_glob_empty() {
        assert!(glob_matches("", ""));
        assert!(!glob_matches("", "notempty"));
        assert!(glob_matches("*", ""));
        assert!(glob_matches("*", "anything"));
    }

    #[test]
    fn test_glob_star_only() {
        assert!(glob_matches("*", "my_crate::deep::path"));
    }

    #[test]
    fn test_glob_no_partial_match() {
        // Pattern must match the entire string, not a substring.
        assert!(!glob_matches("search", "binary_search"));
        assert!(glob_matches("*search", "binary_search"));
        assert!(glob_matches("*search*", "binary_search_impl"));
    }

    // -----------------------------------------------------------------------
    // ScopeFilter::matches tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_scope_all_matches_everything() {
        let scope = VerificationScope::All;
        assert!(ScopeFilter::matches(&scope, "any_fn", "any::path", false));
        assert!(ScopeFilter::matches(&scope, "any_fn", "any::path", true));
    }

    #[test]
    fn test_scope_module_basic() {
        let scope = VerificationScope::Module("my_crate::util::*".into());
        assert!(ScopeFilter::matches(&scope, "helper", "my_crate::util::helper", false));
        assert!(ScopeFilter::matches(&scope, "sort", "my_crate::util::sort", true));
        assert!(!ScopeFilter::matches(&scope, "main", "my_crate::main", false));
    }

    #[test]
    fn test_scope_module_exact() {
        // Module pattern without glob matches only that exact path.
        let scope = VerificationScope::Module("my_crate::util".into());
        assert!(ScopeFilter::matches(&scope, "util", "my_crate::util", false));
        assert!(!ScopeFilter::matches(&scope, "helper", "my_crate::util::helper", false));
    }

    #[test]
    fn test_scope_function_by_name() {
        let scope = VerificationScope::Function("binary_search".into());
        assert!(ScopeFilter::matches(
            &scope,
            "binary_search",
            "my_crate::search::binary_search",
            false,
        ));
        assert!(!ScopeFilter::matches(
            &scope,
            "linear_search",
            "my_crate::search::linear_search",
            false
        ));
    }

    #[test]
    fn test_scope_function_by_path_glob() {
        let scope = VerificationScope::Function("*::search::*".into());
        assert!(ScopeFilter::matches(
            &scope,
            "binary_search",
            "my_crate::search::binary_search",
            false,
        ));
        assert!(!ScopeFilter::matches(&scope, "sort", "my_crate::util::sort", false,));
    }

    #[test]
    fn test_scope_function_glob_in_name() {
        let scope = VerificationScope::Function("*search*".into());
        assert!(ScopeFilter::matches(&scope, "binary_search", "m::binary_search", false));
        assert!(ScopeFilter::matches(&scope, "search_all", "m::search_all", false));
        assert!(!ScopeFilter::matches(&scope, "sort", "m::sort", false));
    }

    #[test]
    fn test_scope_annotated_requires_specs() {
        let scope = VerificationScope::Annotated;
        assert!(ScopeFilter::matches(&scope, "proven_fn", "m::proven_fn", true));
        assert!(!ScopeFilter::matches(&scope, "unproven", "m::unproven", false));
    }

    // -----------------------------------------------------------------------
    // filter_functions tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_filter_functions_all() {
        let funcs = vec![("a", "m::a", false), ("b", "m::b", true)];
        let indices = filter_functions(&VerificationScope::All, funcs);
        assert_eq!(indices, vec![0, 1]);
    }

    #[test]
    fn test_filter_functions_annotated() {
        let funcs = vec![
            ("a", "m::a", false),
            ("b", "m::b", true),
            ("c", "m::c", false),
            ("d", "m::d", true),
        ];
        let indices = filter_functions(&VerificationScope::Annotated, funcs);
        assert_eq!(indices, vec![1, 3]);
    }

    #[test]
    fn test_filter_functions_module_glob() {
        let funcs = vec![
            ("helper", "my_crate::util::helper", false),
            ("main", "my_crate::main", false),
            ("sort", "my_crate::util::sort", true),
        ];
        let indices =
            filter_functions(&VerificationScope::Module("my_crate::util::*".into()), funcs);
        assert_eq!(indices, vec![0, 2]);
    }

    #[test]
    fn test_filter_functions_empty_input() {
        let funcs: Vec<(&str, &str, bool)> = vec![];
        let indices = filter_functions(&VerificationScope::All, funcs);
        assert!(indices.is_empty());
    }

    #[test]
    fn test_filter_functions_none_match() {
        let funcs = vec![("a", "m::a", false), ("b", "m::b", false)];
        let indices = filter_functions(&VerificationScope::Annotated, funcs);
        assert!(indices.is_empty());
    }

    // -----------------------------------------------------------------------
    // VerificationScope serde roundtrip
    // -----------------------------------------------------------------------

    #[test]
    fn test_scope_serde_roundtrip() {
        let scopes = vec![
            VerificationScope::All,
            VerificationScope::Module("foo::bar::*".into()),
            VerificationScope::Function("baz".into()),
            VerificationScope::Annotated,
        ];
        for scope in &scopes {
            let json = serde_json::to_string(scope).expect("serialize");
            let round: VerificationScope = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(&round, scope, "roundtrip failed for {scope:?}");
        }
    }

    #[test]
    fn test_scope_default_is_all() {
        assert_eq!(VerificationScope::default(), VerificationScope::All);
    }
}
