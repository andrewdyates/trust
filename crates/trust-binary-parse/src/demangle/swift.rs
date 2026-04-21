// Author: Andrew Yates <andrew@andrewdyates.com>
// trust-binary-parse demangle::swift: Basic Swift symbol extraction
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::{DemangledSymbol, ManglingScheme};

fn strip_swift_prefix(symbol: &str) -> Option<&str> {
    ["_$s", "$s", "_$S", "$S"].into_iter().find_map(|prefix| symbol.strip_prefix(prefix))
}

fn parse_length_prefixed_identifiers(body: &str) -> Vec<String> {
    let bytes = body.as_bytes();
    let mut pos = 0usize;
    let mut identifiers = Vec::new();

    while pos < bytes.len() {
        if !bytes[pos].is_ascii_digit() {
            pos += 1;
            continue;
        }

        let start = pos;
        let mut len = 0usize;
        while pos < bytes.len() && bytes[pos].is_ascii_digit() {
            len = len.saturating_mul(10).saturating_add((bytes[pos] - b'0') as usize);
            pos += 1;
        }

        if pos == start || pos + len > bytes.len() {
            break;
        }

        if let Ok(identifier) = std::str::from_utf8(&bytes[pos..pos + len]) {
            identifiers.push(identifier.to_string());
        }
        pos += len;
    }

    identifiers
}

pub(crate) fn demangle_swift(symbol: &str) -> Option<DemangledSymbol> {
    let body = strip_swift_prefix(symbol)?;
    let identifiers = parse_length_prefixed_identifiers(body);
    if identifiers.is_empty() {
        return None;
    }

    let mut demangled = if body.contains("Ma") {
        DemangledSymbol::with_namespace(ManglingScheme::Swift, identifiers, "metadata accessor")
    } else if body.contains("Mn") {
        DemangledSymbol::with_namespace(
            ManglingScheme::Swift,
            identifiers,
            "nominal type descriptor",
        )
    } else if let Some((name, namespace)) = identifiers.split_last() {
        DemangledSymbol::with_namespace(ManglingScheme::Swift, namespace.to_vec(), name.clone())
    } else {
        return None;
    };

    if body.contains('F')
        && demangled.name != "metadata accessor"
        && demangled.name != "nominal type descriptor"
    {
        demangled.return_type = Some(String::new());
    }

    Some(demangled)
}

#[cfg(test)]
mod tests {
    use super::demangle_swift;

    #[test]
    fn demangles_basic_functions_and_methods() {
        let function = demangle_swift("$s4main3fooyyF").unwrap();
        assert_eq!(function.namespace, vec!["main"]);
        assert_eq!(function.name, "foo");
        assert_eq!(function.to_string(), "main::foo()");

        let method = demangle_swift("$s4main3FooC3baryyF").unwrap();
        assert_eq!(method.namespace, vec!["main", "Foo"]);
        assert_eq!(method.name, "bar");
        assert_eq!(method.to_string(), "main::Foo::bar()");
    }

    #[test]
    fn demangles_nominal_type_metadata_entries() {
        let metadata = demangle_swift("$s4main3FooCMa").unwrap();
        assert_eq!(metadata.to_string(), "main::Foo::metadata accessor");

        let descriptor = demangle_swift("_$s4main3FooCMn").unwrap();
        assert_eq!(descriptor.to_string(), "main::Foo::nominal type descriptor");
    }

    // --- Edge case tests for improved coverage ---

    #[test]
    fn test_swift_all_prefix_variants() {
        // $s prefix
        let result = demangle_swift("$s4main5helloyyF");
        assert!(result.is_some());

        // _$s prefix
        let result = demangle_swift("_$s4main5helloyyF");
        assert!(result.is_some());

        // $S prefix
        let result = demangle_swift("$S4main5helloyyF");
        assert!(result.is_some());

        // _$S prefix
        let result = demangle_swift("_$S4main5helloyyF");
        assert!(result.is_some());
    }

    #[test]
    fn test_swift_not_swift_prefix_returns_none() {
        assert!(demangle_swift("").is_none());
        assert!(demangle_swift("_Z3foo").is_none());
        assert!(demangle_swift("_R3foo").is_none());
        assert!(demangle_swift("plain").is_none());
        assert!(demangle_swift("$x4main3fooyyF").is_none());
    }

    #[test]
    fn test_swift_no_identifiers_returns_none() {
        // Body with no length-prefixed identifiers
        assert!(demangle_swift("$syyF").is_none());
    }

    #[test]
    fn test_swift_deeply_nested_method() {
        let result = demangle_swift("$s4main3FooC3BarC3bazyyF").unwrap();
        assert_eq!(result.namespace.len(), 3);
        assert_eq!(result.name, "baz");
    }

    #[test]
    fn test_swift_function_flag_sets_return_type() {
        let result = demangle_swift("$s4main3fooyyF").unwrap();
        // Contains 'F' so return_type should be Some
        assert!(result.return_type.is_some());
    }

    #[test]
    fn test_swift_no_function_flag_no_return_type() {
        // Metadata accessor has no function flag concern; it's a special name
        let result = demangle_swift("$s4main3FooCMa").unwrap();
        assert!(result.return_type.is_none());
    }
}
