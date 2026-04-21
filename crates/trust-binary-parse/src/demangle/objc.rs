// Author: Andrew Yates <andrew@andrewdyates.com>
// trust-binary-parse demangle::objc: Objective-C selector parsing
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::{DemangledSymbol, ManglingScheme};

pub(crate) fn is_objc_symbol(symbol: &str) -> bool {
    let trimmed = symbol.trim();
    if !(trimmed.starts_with("+[") || trimmed.starts_with("-[")) || !trimmed.ends_with(']') {
        return false;
    }

    let inner = &trimmed[2..trimmed.len() - 1];
    let mut parts = inner.splitn(2, char::is_whitespace);
    let class_name = parts.next().unwrap_or("").trim();
    let selector = parts.next().unwrap_or("").trim();
    !class_name.is_empty() && !selector.is_empty()
}

pub(crate) fn demangle_objc(symbol: &str) -> Option<DemangledSymbol> {
    let trimmed = symbol.trim();
    if !is_objc_symbol(trimmed) {
        return None;
    }

    let is_static = trimmed.starts_with("+[");
    let inner = &trimmed[2..trimmed.len() - 1];
    let mut parts = inner.splitn(2, char::is_whitespace);
    let class_name = parts.next()?.trim();
    let selector = parts.next()?.trim();

    let parameter_count = selector.bytes().filter(|byte| *byte == b':').count();
    let mut demangled = DemangledSymbol::with_namespace(
        ManglingScheme::ObjC,
        vec![class_name.to_string()],
        selector.to_string(),
    );
    demangled.is_static = is_static;
    demangled.parameters = vec!["id".to_string(); parameter_count];
    Some(demangled)
}

#[cfg(test)]
mod tests {
    use super::demangle_objc;

    #[test]
    fn parses_class_methods() {
        let symbol = demangle_objc("+[NSString stringWithFormat:]").unwrap();
        assert!(symbol.is_static);
        assert_eq!(symbol.namespace, vec!["NSString"]);
        assert_eq!(symbol.name, "stringWithFormat:");
        assert_eq!(symbol.parameters, vec!["id"]);
        assert_eq!(symbol.to_string(), "+[NSString stringWithFormat:]");
    }

    #[test]
    fn parses_instance_methods() {
        let symbol = demangle_objc("-[NSArray objectAtIndex:]").unwrap();
        assert!(!symbol.is_static);
        assert_eq!(symbol.namespace, vec!["NSArray"]);
        assert_eq!(symbol.name, "objectAtIndex:");
        assert_eq!(symbol.parameters.len(), 1);
        assert_eq!(symbol.to_string(), "-[NSArray objectAtIndex:]");
    }

    #[test]
    fn parses_multi_parameter_selectors() {
        let symbol = demangle_objc("-[UITableView initWithFrame:style:]").unwrap();
        assert_eq!(symbol.parameters.len(), 2);
        assert_eq!(symbol.to_string(), "-[UITableView initWithFrame:style:]");
    }

    // --- Edge case tests for improved coverage ---

    #[test]
    fn test_objc_not_objc_returns_none() {
        assert!(demangle_objc("").is_none());
        assert!(demangle_objc("plain_symbol").is_none());
        assert!(demangle_objc("_Z3foo").is_none());
        assert!(demangle_objc("[NSArray]").is_none()); // no +/- prefix
        assert!(demangle_objc("+[]").is_none()); // empty class and selector
        assert!(demangle_objc("+[NSString]").is_none()); // no selector (only class)
    }

    #[test]
    fn test_objc_zero_parameter_selector() {
        let symbol = demangle_objc("-[NSArray count]").unwrap();
        assert!(!symbol.is_static);
        assert_eq!(symbol.parameters.len(), 0);
        assert_eq!(symbol.name, "count");
    }

    #[test]
    fn test_objc_many_parameter_selector() {
        let symbol =
            demangle_objc("-[NSDictionary initWithObjects:forKeys:count:]").unwrap();
        assert_eq!(symbol.parameters.len(), 3);
        assert_eq!(symbol.name, "initWithObjects:forKeys:count:");
    }

    #[test]
    fn test_objc_whitespace_trimming() {
        let symbol = demangle_objc("  +[NSString alloc]  ").unwrap();
        assert!(symbol.is_static);
        assert_eq!(symbol.namespace, vec!["NSString"]);
        assert_eq!(symbol.name, "alloc");
    }

    #[test]
    fn test_objc_display_class_method_format() {
        let symbol = demangle_objc("+[NSObject new]").unwrap();
        assert_eq!(symbol.to_string(), "+[NSObject new]");
    }

    #[test]
    fn test_objc_display_instance_method_format() {
        let symbol = demangle_objc("-[NSObject init]").unwrap();
        assert_eq!(symbol.to_string(), "-[NSObject init]");
    }
}
