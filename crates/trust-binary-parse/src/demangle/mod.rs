// Author: Andrew Yates <andrew@andrewdyates.com>
// trust-binary-parse demangle: Multi-language symbol demangling
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;

mod itanium;
mod objc;
mod rust_v0;
mod swift;

/// Detected mangling scheme for a symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ManglingScheme {
    RustV0,
    ItaniumCpp,
    Swift,
    ObjC,
    Unknown,
}

/// A demangled symbol with structured components.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DemangledSymbol {
    pub(crate) scheme: ManglingScheme,
    pub(crate) name: String,
    pub(crate) namespace: Vec<String>,
    pub(crate) parameters: Vec<String>,
    pub(crate) return_type: Option<String>,
    pub(crate) is_const: bool,
    pub(crate) is_static: bool,
    pub(crate) template_args: Vec<String>,
}

impl DemangledSymbol {
    pub fn new(scheme: ManglingScheme, name: impl Into<String>) -> Self {
        Self {
            scheme,
            name: name.into(),
            namespace: Vec::new(),
            parameters: Vec::new(),
            return_type: None,
            is_const: false,
            is_static: false,
            template_args: Vec::new(),
        }
    }

    pub fn with_namespace(
        scheme: ManglingScheme,
        namespace: Vec<String>,
        name: impl Into<String>,
    ) -> Self {
        let mut symbol = Self::new(scheme, name);
        symbol.namespace = namespace;
        symbol
    }
}

impl fmt::Display for DemangledSymbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.scheme == ManglingScheme::ObjC {
            let sigil = if self.is_static { '+' } else { '-' };
            let class_name = self.namespace.first().map(String::as_str).unwrap_or("");
            return write!(f, "{}[{} {}]", sigil, class_name, self.name);
        }

        let mut path = String::new();
        if !self.namespace.is_empty() {
            path.push_str(&self.namespace.join("::"));
            if !self.name.is_empty() {
                path.push_str("::");
            }
        }
        path.push_str(&self.name);

        if !self.template_args.is_empty() {
            if self.scheme == ManglingScheme::RustV0 {
                path.push_str("::<");
            } else {
                path.push('<');
            }
            path.push_str(&self.template_args.join(", "));
            path.push('>');
        }

        let show_params = !self.parameters.is_empty() || self.return_type.is_some();
        if show_params {
            path.push('(');
            path.push_str(&self.parameters.join(", "));
            path.push(')');
        }

        if self.is_const && self.scheme == ManglingScheme::ItaniumCpp && show_params {
            path.push_str(" const");
        }

        if let Some(return_type) = &self.return_type
            && !return_type.is_empty()
        {
            path.push_str(" -> ");
            path.push_str(return_type);
        }

        write!(f, "{path}")
    }
}

/// Detect which mangling scheme a symbol uses.
pub fn detect_scheme(symbol: &str) -> ManglingScheme {
    let trimmed = symbol.trim();
    if trimmed.starts_with("_R") {
        ManglingScheme::RustV0
    } else if trimmed.starts_with("_Z") {
        ManglingScheme::ItaniumCpp
    } else if trimmed.starts_with("$s")
        || trimmed.starts_with("_$s")
        || trimmed.starts_with("$S")
        || trimmed.starts_with("_$S")
    {
        ManglingScheme::Swift
    } else if objc::is_objc_symbol(trimmed) {
        ManglingScheme::ObjC
    } else {
        ManglingScheme::Unknown
    }
}

/// Demangle any supported symbol.
pub fn demangle(symbol: &str) -> Option<DemangledSymbol> {
    match detect_scheme(symbol) {
        ManglingScheme::RustV0 => rust_v0::demangle_rust_v0(symbol),
        ManglingScheme::ItaniumCpp => itanium::demangle_itanium(symbol),
        ManglingScheme::Swift => swift::demangle_swift(symbol),
        ManglingScheme::ObjC => objc::demangle_objc(symbol),
        ManglingScheme::Unknown => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{ManglingScheme, demangle, detect_scheme};

    #[test]
    fn detects_supported_schemes() {
        assert_eq!(detect_scheme("_RNvCs15kBYyAo9fc_7mycrate7example"), ManglingScheme::RustV0);
        assert_eq!(detect_scheme("_ZN3std6vectorIiE9push_backEi"), ManglingScheme::ItaniumCpp);
        assert_eq!(detect_scheme("$s4main3fooyyF"), ManglingScheme::Swift);
        assert_eq!(detect_scheme("+[NSString stringWithFormat:]"), ManglingScheme::ObjC);
        assert_eq!(detect_scheme("plain_symbol"), ManglingScheme::Unknown);
    }

    #[test]
    fn dispatches_to_rust_demangler() {
        let symbol = demangle("_RNvCs15kBYyAo9fc_7mycrate7example").unwrap();
        assert_eq!(symbol.to_string(), "mycrate::example");
    }

    #[test]
    fn dispatches_to_itanium_demangler() {
        let symbol = demangle("_ZN3std6vectorIiE9push_backEi").unwrap();
        assert_eq!(symbol.to_string(), "std::vector<int>::push_back(int)");
    }

    #[test]
    fn dispatches_to_swift_demangler() {
        let symbol = demangle("$s4main3FooC3baryyF").unwrap();
        assert_eq!(symbol.to_string(), "main::Foo::bar()");
    }

    #[test]
    fn dispatches_to_objc_demangler() {
        let symbol = demangle("-[NSArray objectAtIndex:]").unwrap();
        assert_eq!(symbol.to_string(), "-[NSArray objectAtIndex:]");
    }

    #[test]
    fn demangle_issue_506_rust_v0_example() {
        // Issue #506 specified symbol: Rust v0 mangling
        let result = demangle("_RNvNtCs123_4core3fmt9Arguments6new_v1");
        assert!(result.is_some(), "should demangle Rust v0 symbol");
        let symbol = result.unwrap();
        assert_eq!(symbol.scheme, ManglingScheme::RustV0);
        let rendered = symbol.to_string();
        assert!(
            rendered.contains("core") && rendered.contains("fmt"),
            "should contain core::fmt path components, got: {rendered}"
        );
    }

    #[test]
    fn demangle_issue_506_itanium_example() {
        // Issue #506 specified symbol: C++ Itanium mangling
        let symbol = demangle("_ZN3std6vectorIiE9push_backEi").unwrap();
        assert_eq!(symbol.scheme, ManglingScheme::ItaniumCpp);
        assert_eq!(symbol.to_string(), "std::vector<int>::push_back(int)");
    }

    #[test]
    fn demangle_issue_506_swift_example() {
        // Issue #506 specified symbol: Swift mangling
        let result = demangle("$s4main5helloyyF");
        assert!(result.is_some(), "should demangle Swift symbol");
        let symbol = result.unwrap();
        assert_eq!(symbol.scheme, ManglingScheme::Swift);
        assert_eq!(symbol.to_string(), "main::hello()");
    }

    #[test]
    fn demangle_unknown_returns_none() {
        assert!(demangle("plain_symbol").is_none());
        assert!(demangle("").is_none());
        assert!(demangle("just_a_name").is_none());
    }

    // --- Edge case tests for improved coverage ---

    #[test]
    fn test_detect_scheme_whitespace_trimming() {
        assert_eq!(detect_scheme("  _RNvCs15kBYyAo9fc_7mycrate7example  "), ManglingScheme::RustV0);
        assert_eq!(detect_scheme("  _Z3foov  "), ManglingScheme::ItaniumCpp);
        assert_eq!(detect_scheme("  $s4main3fooyyF  "), ManglingScheme::Swift);
    }

    #[test]
    fn test_detect_scheme_all_swift_prefixes() {
        assert_eq!(detect_scheme("$s4main3fooyyF"), ManglingScheme::Swift);
        assert_eq!(detect_scheme("_$s4main3fooyyF"), ManglingScheme::Swift);
        assert_eq!(detect_scheme("$S4main3fooyyF"), ManglingScheme::Swift);
        assert_eq!(detect_scheme("_$S4main3fooyyF"), ManglingScheme::Swift);
    }

    #[test]
    fn test_detect_scheme_partial_prefixes_are_unknown() {
        assert_eq!(detect_scheme("_"), ManglingScheme::Unknown);
        assert_eq!(detect_scheme("_X"), ManglingScheme::Unknown);
        assert_eq!(detect_scheme("$"), ManglingScheme::Unknown);
        assert_eq!(detect_scheme("$x"), ManglingScheme::Unknown);
    }

    #[test]
    fn test_demangled_symbol_display_with_template_args_rust() {
        let mut sym = super::DemangledSymbol::with_namespace(
            ManglingScheme::RustV0,
            vec!["std".to_string(), "vec".to_string()],
            "push".to_string(),
        );
        sym.template_args = vec!["u8".to_string()];
        assert_eq!(sym.to_string(), "std::vec::push::<u8>");
    }

    #[test]
    fn test_demangled_symbol_display_with_template_args_cpp() {
        let mut sym = super::DemangledSymbol::with_namespace(
            ManglingScheme::ItaniumCpp,
            vec!["std".to_string()],
            "vector".to_string(),
        );
        sym.template_args = vec!["int".to_string()];
        // C++ uses < not ::<
        assert_eq!(sym.to_string(), "std::vector<int>");
    }

    #[test]
    fn test_demangled_symbol_display_with_params_and_return() {
        let mut sym = super::DemangledSymbol::with_namespace(
            ManglingScheme::ItaniumCpp,
            vec!["Foo".to_string()],
            "bar".to_string(),
        );
        sym.parameters = vec!["int".to_string(), "float".to_string()];
        sym.return_type = Some("bool".to_string());
        assert_eq!(sym.to_string(), "Foo::bar(int, float) -> bool");
    }

    #[test]
    fn test_demangled_symbol_display_const_cpp_method() {
        let mut sym = super::DemangledSymbol::with_namespace(
            ManglingScheme::ItaniumCpp,
            vec!["Foo".to_string()],
            "get".to_string(),
        );
        sym.parameters = vec![];
        sym.return_type = Some(String::new());
        sym.is_const = true;
        assert_eq!(sym.to_string(), "Foo::get() const");
    }

    #[test]
    fn test_demangled_symbol_display_objc_format() {
        let mut sym = super::DemangledSymbol::with_namespace(
            ManglingScheme::ObjC,
            vec!["NSString".to_string()],
            "length".to_string(),
        );
        sym.is_static = false;
        assert_eq!(sym.to_string(), "-[NSString length]");

        sym.is_static = true;
        assert_eq!(sym.to_string(), "+[NSString length]");
    }

    #[test]
    fn test_demangled_symbol_display_empty_name() {
        let sym = super::DemangledSymbol::with_namespace(
            ManglingScheme::RustV0,
            vec!["crate".to_string()],
            String::new(),
        );
        // Should not have trailing :: when name is empty
        assert_eq!(sym.to_string(), "crate");
    }

    #[test]
    fn test_demangled_symbol_display_no_namespace() {
        let sym = super::DemangledSymbol::new(ManglingScheme::RustV0, "main");
        assert_eq!(sym.to_string(), "main");
    }

    #[test]
    fn test_demangled_symbol_display_empty_return_type_not_shown() {
        let mut sym = super::DemangledSymbol::new(ManglingScheme::ItaniumCpp, "foo");
        sym.parameters = vec!["int".to_string()];
        sym.return_type = Some(String::new());
        // Empty return type string should not produce " -> "
        assert_eq!(sym.to_string(), "foo(int)");
    }
}
