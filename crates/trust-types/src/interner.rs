// tRust #696: String interning for Formula variable names.
//
// Provides a lightweight interned string type backed by a global interner table.
// Symbol(u32) enables Copy semantics, integer comparison, and zero-cost clone
// for variable names that appear repeatedly across formulas.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Deserializer, Serialize, Serializer};
use crate::fx::FxHashMap;
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
        global_interner()
            .lock()
            .expect("interner lock poisoned")
            .resolve(*self)
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
        Self {
            map: FxHashMap::default(),
            strings: Vec::new(),
        }
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
}
