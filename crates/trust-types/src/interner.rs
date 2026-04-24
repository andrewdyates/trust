// tRust #696: String interning for Formula variable names.
//
// Provides a lightweight interned string type backed by a global interner table.
// Symbol(u32) enables Copy semantics, integer comparison, and zero-cost clone
// for variable names that appear repeatedly across formulas.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::fx::FxHashMap;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;
use std::sync::{Mutex, OnceLock};

/// An interned string symbol for variable names in formulas.
///
/// Uses a `u32` index into a global intern table. This gives:
/// - `Copy` semantics (no heap allocation per reference)
/// - O(1) equality comparison (integer compare)
/// - Zero-cost clone
///
/// Resolve back to the string via [`Symbol::as_str()`] or [`Display`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(u32);

impl Symbol {
    /// Intern a string and return its symbol.
    ///
    /// If the string was previously interned, returns the same `Symbol`.
    #[must_use]
    pub fn intern(s: &str) -> Self {
        global_interner().lock().expect("interner lock poisoned").intern(s)
    }

    /// Resolve this symbol back to its string representation.
    ///
    /// Returns a `&'static str` because interned strings are never freed.
    ///
    /// # Panics
    ///
    /// Panics if the symbol index is invalid (should never happen with
    /// symbols obtained from [`Symbol::intern`]).
    #[must_use]
    pub fn as_str(&self) -> &'static str {
        global_interner().lock().expect("interner lock poisoned").resolve(*self)
    }

    /// Get the raw index of this symbol (for debugging/testing).
    #[must_use]
    pub fn index(self) -> u32 {
        self.0
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Symbol({}, {:?})", self.0, self.as_str())
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl From<&str> for Symbol {
    fn from(s: &str) -> Self {
        Self::intern(s)
    }
}

impl From<String> for Symbol {
    fn from(s: String) -> Self {
        Self::intern(&s)
    }
}

impl AsRef<str> for Symbol {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

// tRust #883: Enable `assert_eq!(symbol, "str")` and `symbol == "str"` comparisons.
impl PartialEq<&str> for Symbol {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

impl PartialEq<str> for Symbol {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<String> for Symbol {
    fn eq(&self, other: &String) -> bool {
        self.as_str() == other.as_str()
    }
}

// tRust #883: Enable Symbol to convert back to String via From/Into
impl From<Symbol> for String {
    fn from(sym: Symbol) -> Self {
        sym.as_str().to_owned()
    }
}

impl From<&Symbol> for String {
    fn from(sym: &Symbol) -> Self {
        sym.as_str().to_owned()
    }
}

// tRust #883: Enable `symbol.as_bytes()` for hashing/caching paths
// tRust #883: Delegate common str methods for ergonomic use
impl Symbol {
    /// Get the byte representation of the interned string.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        self.as_str().as_bytes()
    }

    /// Check if the interned string contains a pattern.
    #[must_use]
    pub fn contains(&self, pat: &str) -> bool {
        self.as_str().contains(pat)
    }

    /// Check if the interned string starts with a pattern.
    #[must_use]
    pub fn starts_with(&self, pat: &str) -> bool {
        self.as_str().starts_with(pat)
    }

    /// Check if the interned string ends with a pattern.
    #[must_use]
    pub fn ends_with(&self, pat: &str) -> bool {
        self.as_str().ends_with(pat)
    }

    /// Check if the interned string is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.as_str().is_empty()
    }

    /// Get the length of the interned string in bytes.
    #[must_use]
    pub fn len(&self) -> usize {
        self.as_str().len()
    }
}

// NOTE: We intentionally do NOT impl Borrow<str> for Symbol because it would
// violate the Borrow contract — Symbol hashes by u32 index while str hashes by
// content, so HashMap lookups via get("str") would silently fail. Use
// Symbol::as_str() or AsRef<str> for string access instead.

impl Serialize for Symbol {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.as_str().serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Symbol {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s = String::deserialize(deserializer)?;
        Ok(Symbol::intern(&s))
    }
}

/// The global interner table for string symbols.
///
/// Strings are stored as `Box<str>` and leaked to `&'static str` so that
/// [`Symbol::as_str()`] can return `&'static str` without lifetime issues.
/// This is intentional: interned strings live for the entire program.
pub struct Interner {
    /// Map from string content to its symbol index.
    map: FxHashMap<&'static str, Symbol>,
    /// Indexed storage: `strings[symbol.0]` is the interned `&'static str`.
    strings: Vec<&'static str>,
}

impl Interner {
    /// Create a new empty interner.
    #[must_use]
    pub fn new() -> Self {
        Self { map: FxHashMap::default(), strings: Vec::new() }
    }

    /// Intern a string, returning its symbol.
    ///
    /// If the string was previously interned, returns the existing symbol.
    pub fn intern(&mut self, s: &str) -> Symbol {
        if let Some(&sym) = self.map.get(s) {
            return sym;
        }
        let idx = u32::try_from(self.strings.len())
            .expect("interner overflow: more than 2^32 unique strings");
        // Leak the string so we can store &'static str.
        // This is intentional: interned strings live for the program's lifetime.
        let leaked: &'static str = Box::leak(s.to_owned().into_boxed_str());
        let sym = Symbol(idx);
        self.strings.push(leaked);
        self.map.insert(leaked, sym);
        sym
    }

    /// Resolve a symbol back to its string.
    ///
    /// # Panics
    ///
    /// Panics if the symbol index is out of bounds.
    #[must_use]
    pub fn resolve(&self, sym: Symbol) -> &'static str {
        self.strings[sym.0 as usize]
    }

    /// Return the number of unique strings interned.
    #[must_use]
    pub fn len(&self) -> usize {
        self.strings.len()
    }

    /// Return true if no strings have been interned.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.strings.is_empty()
    }
}

impl Default for Interner {
    fn default() -> Self {
        Self::new()
    }
}

/// Access the global interner instance.
///
/// Initialized on first access via `OnceLock`. Thread-safe via `Mutex`.
fn global_interner() -> &'static Mutex<Interner> {
    static INTERNER: OnceLock<Mutex<Interner>> = OnceLock::new();
    INTERNER.get_or_init(|| Mutex::new(Interner::new()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_intern_returns_same_symbol_for_same_string() {
        let a = Symbol::intern("x");
        let b = Symbol::intern("x");
        assert_eq!(a, b);
        assert_eq!(a.index(), b.index());
    }

    #[test]
    fn test_intern_returns_different_symbols_for_different_strings() {
        let a = Symbol::intern("alpha_test_1");
        let b = Symbol::intern("beta_test_1");
        assert_ne!(a, b);
        assert_ne!(a.index(), b.index());
    }

    #[test]
    fn test_resolve_roundtrip() {
        let sym = Symbol::intern("roundtrip_var");
        assert_eq!(sym.as_str(), "roundtrip_var");
    }

    #[test]
    fn test_display() {
        let sym = Symbol::intern("display_test");
        assert_eq!(format!("{sym}"), "display_test");
    }

    #[test]
    fn test_debug() {
        let sym = Symbol::intern("debug_test");
        let dbg = format!("{sym:?}");
        assert!(dbg.contains("debug_test"), "Debug output: {dbg}");
        assert!(dbg.starts_with("Symbol("), "Debug output: {dbg}");
    }

    #[test]
    fn test_from_str() {
        let sym: Symbol = "from_str_test".into();
        assert_eq!(sym.as_str(), "from_str_test");
    }

    #[test]
    fn test_from_string() {
        let sym: Symbol = String::from("from_string_test").into();
        assert_eq!(sym.as_str(), "from_string_test");
    }

    #[test]
    fn test_as_ref_str() {
        let sym = Symbol::intern("as_ref_test");
        let s: &str = sym.as_ref();
        assert_eq!(s, "as_ref_test");
    }

    #[test]
    fn test_copy_semantics() {
        let a = Symbol::intern("copy_test");
        let b = a; // Copy, not move
        let c = a; // Still valid because Symbol is Copy
        assert_eq!(a, b);
        assert_eq!(b, c);
    }

    #[test]
    fn test_hash_consistency() {
        use crate::fx::FxHashSet;
        let a = Symbol::intern("hash_test_a");
        let b = Symbol::intern("hash_test_a");
        let mut set = FxHashSet::default();
        set.insert(a);
        assert!(set.contains(&b));
    }

    #[test]
    fn test_ord() {
        let a = Symbol::intern("ord_a");
        let b = Symbol::intern("ord_b");
        // Ordering is by index, not lexicographic
        assert!(a < b || b < a);
    }

    #[test]
    fn test_interner_len() {
        let mut interner = Interner::new();
        assert!(interner.is_empty());
        assert_eq!(interner.len(), 0);
        interner.intern("len_test_1");
        assert_eq!(interner.len(), 1);
        interner.intern("len_test_2");
        assert_eq!(interner.len(), 2);
        // Duplicate does not increase length
        interner.intern("len_test_1");
        assert_eq!(interner.len(), 2);
    }

    #[test]
    fn test_interner_resolve() {
        let mut interner = Interner::new();
        let sym = interner.intern("resolve_test");
        assert_eq!(interner.resolve(sym), "resolve_test");
    }

    #[test]
    fn test_serialize_deserialize() {
        let sym = Symbol::intern("serde_test");
        let json = serde_json::to_string(&sym).expect("serialize");
        assert_eq!(json, "\"serde_test\"");
        let deserialized: Symbol = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(deserialized, sym);
        assert_eq!(deserialized.as_str(), "serde_test");
    }

    #[test]
    fn test_empty_string() {
        let sym = Symbol::intern("");
        assert_eq!(sym.as_str(), "");
        assert_eq!(format!("{sym}"), "");
    }

    #[test]
    fn test_unicode() {
        let sym = Symbol::intern("variableα");
        assert_eq!(sym.as_str(), "variableα");
    }

    #[test]
    fn test_global_interner_is_shared() {
        // Two calls to Symbol::intern should share the same global table
        let a = Symbol::intern("global_shared_test");
        let b = Symbol::intern("global_shared_test");
        assert_eq!(a.index(), b.index());
    }

    // tRust #883: Tests for backward-compatible conversions added for interning extension

    #[test]
    fn test_symbol_partial_eq_str() {
        let sym = Symbol::intern("eq_str_test");
        assert!(sym == "eq_str_test");
        assert!(sym == *"eq_str_test");
        assert!(sym != "other");
    }

    #[test]
    fn test_symbol_partial_eq_string() {
        let sym = Symbol::intern("eq_string_test");
        let s = String::from("eq_string_test");
        assert!(sym == s);
    }

    #[test]
    fn test_symbol_to_string() {
        let sym = Symbol::intern("to_string_test");
        let s: String = sym.into();
        assert_eq!(s, "to_string_test");
    }

    #[test]
    fn test_symbol_ref_to_string() {
        let sym = Symbol::intern("ref_to_string_test");
        let s: String = (&sym).into();
        assert_eq!(s, "ref_to_string_test");
    }

    #[test]
    fn test_symbol_as_bytes() {
        let sym = Symbol::intern("bytes_test");
        assert_eq!(sym.as_bytes(), b"bytes_test");
    }

    #[test]
    fn test_symbol_contains() {
        let sym = Symbol::intern("foo::bar::baz");
        assert!(sym.contains("bar"));
        assert!(!sym.contains("qux"));
    }

    #[test]
    fn test_symbol_starts_with() {
        let sym = Symbol::intern("foo::bar::baz");
        assert!(sym.starts_with("foo"));
        assert!(!sym.starts_with("bar"));
    }

    #[test]
    fn test_symbol_ends_with() {
        let sym = Symbol::intern("foo::bar::baz");
        assert!(sym.ends_with("baz"));
        assert!(!sym.ends_with("bar"));
    }

    #[test]
    fn test_symbol_is_empty_and_len() {
        let empty = Symbol::intern("");
        assert!(empty.is_empty());
        assert_eq!(empty.len(), 0);

        let nonempty = Symbol::intern("nonempty_test");
        assert!(!nonempty.is_empty());
        assert_eq!(nonempty.len(), 13);
    }

    #[test]
    fn test_symbol_as_ref_str_generic() {
        // Symbol implements AsRef<str> for generic contexts
        fn takes_as_ref(s: &impl AsRef<str>) -> &str {
            s.as_ref()
        }
        let sym = Symbol::intern("as_ref_generic_test");
        assert_eq!(takes_as_ref(&sym), "as_ref_generic_test");
    }

    #[test]
    fn test_symbol_in_hashmap_lookup_by_symbol() {
        // Symbol keys in HashMap are looked up by Symbol (fast u32 comparison)
        use crate::fx::FxHashMap;
        let mut map = FxHashMap::default();
        let key = Symbol::intern("map_key_test");
        map.insert(key, 42);
        // Lookup by same Symbol works (same u32 index)
        let lookup = Symbol::intern("map_key_test");
        assert_eq!(map.get(&lookup), Some(&42));
    }

    #[test]
    fn test_symbol_copy_semantics_zero_cost() {
        // Verify that interning the same string 1000 times costs nothing
        let first = Symbol::intern("copy_cost_test");
        for _ in 0..1000 {
            let sym = Symbol::intern("copy_cost_test");
            assert_eq!(sym.index(), first.index());
        }
        // Symbol is 4 bytes
        assert_eq!(std::mem::size_of::<Symbol>(), 4);
    }
}
