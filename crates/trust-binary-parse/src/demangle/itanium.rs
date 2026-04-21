// Author: Andrew Yates <andrew@andrewdyates.com>
// trust-binary-parse demangle::itanium: C++ Itanium ABI demangling
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::{DemangledSymbol, ManglingScheme};

#[derive(Debug, Clone, PartialEq, Eq)]
struct NameComponent {
    base: String,
    template_args: Vec<String>,
}

impl NameComponent {
    fn render(&self) -> String {
        if self.template_args.is_empty() {
            self.base.clone()
        } else {
            format!("{}<{}>", self.base, self.template_args.join(", "))
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ParsedName {
    namespace: Vec<String>,
    name: String,
    template_args: Vec<String>,
    is_const_method: bool,
}

struct ItaniumParser<'a> {
    input: &'a [u8],
    pos: usize,
    substitutions: Vec<String>,
}

impl<'a> ItaniumParser<'a> {
    fn new(input: &'a str) -> Self {
        Self { input: input.as_bytes(), pos: 0, substitutions: Vec::new() }
    }

    fn peek_char(&self) -> Option<char> {
        self.input.get(self.pos).map(|byte| char::from(*byte))
    }

    fn next_char(&mut self) -> Option<char> {
        let ch = self.peek_char()?;
        self.pos += 1;
        Some(ch)
    }

    fn consume_if(&mut self, expected: char) -> bool {
        if self.peek_char() == Some(expected) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn consume_str(&mut self, expected: &str) -> bool {
        let bytes = expected.as_bytes();
        if self.input.get(self.pos..self.pos + bytes.len()).is_some_and(|slice| slice == bytes) {
            self.pos += bytes.len();
            true
        } else {
            false
        }
    }

    fn parse_number(&mut self) -> Option<usize> {
        let start = self.pos;
        let mut value = 0usize;
        while let Some(ch) = self.peek_char() {
            if !ch.is_ascii_digit() {
                break;
            }
            value = value.checked_mul(10)?.checked_add((ch as u8 - b'0') as usize)?;
            self.pos += 1;
        }
        if self.pos == start { None } else { Some(value) }
    }

    fn read_bytes(&mut self, len: usize) -> Option<&'a [u8]> {
        let end = self.pos.checked_add(len)?;
        let bytes = self.input.get(self.pos..end)?;
        self.pos = end;
        Some(bytes)
    }

    fn push_substitution(&mut self, value: String) {
        if !self.substitutions.contains(&value) {
            self.substitutions.push(value);
        }
    }

    fn parse_seq_id(&mut self) -> Option<usize> {
        let mut value = 0usize;
        let mut saw_digit = false;
        loop {
            let ch = self.next_char()?;
            if ch == '_' {
                return if saw_digit { value.checked_add(1) } else { Some(0) };
            }
            let digit = match ch {
                '0'..='9' => (ch as u8 - b'0') as usize,
                'A'..='Z' => (ch as u8 - b'A') as usize + 10,
                'a'..='z' => (ch as u8 - b'a') as usize + 10,
                _ => return None,
            };
            saw_digit = true;
            value = value.checked_mul(36)?.checked_add(digit)?;
        }
    }

    fn parse_substitution_ref(&mut self) -> Option<String> {
        self.consume_if('S').then_some(())?;
        let special = match self.peek_char() {
            Some('t') => Some("std"),
            Some('a') => Some("std::allocator"),
            Some('b') => Some("std::basic_string"),
            Some('s') => Some("std::string"),
            Some('i') => Some("std::istream"),
            Some('o') => Some("std::ostream"),
            Some('d') => Some("std::iostream"),
            _ => None,
        };
        if let Some(value) = special {
            self.pos += 1;
            return Some(value.to_string());
        }

        let index = self.parse_seq_id()?;
        self.substitutions.get(index).cloned()
    }

    fn parse_source_name(&mut self) -> Option<NameComponent> {
        let len = self.parse_number()?;
        let rendered = String::from_utf8(self.read_bytes(len)?.to_vec()).ok()?;
        let template_args =
            if self.consume_if('I') { self.parse_template_args()? } else { Vec::new() };
        Some(NameComponent { base: rendered, template_args })
    }

    fn parse_operator_name(&mut self) -> Option<NameComponent> {
        let code = self.input.get(self.pos..self.pos + 2)?;
        let code = std::str::from_utf8(code).ok()?;
        let base = match code {
            "aa" => "operator&&",
            "cl" => "operator()",
            "da" => "operator delete[]",
            "dl" => "operator delete",
            "dv" => "operator/",
            "eq" => "operator==",
            "ge" => "operator>=",
            "gt" => "operator>",
            "ix" => "operator[]",
            "le" => "operator<=",
            "ls" => "operator<<",
            "lt" => "operator<",
            "mi" => "operator-",
            "ml" => "operator*",
            "na" => "operator new[]",
            "ne" => "operator!=",
            "nw" => "operator new",
            "oo" => "operator||",
            "pl" => "operator+",
            "pp" => "operator++",
            "rs" => "operator>>",
            _ => return None,
        };
        self.pos += 2;
        Some(NameComponent { base: base.to_string(), template_args: Vec::new() })
    }

    fn parse_name_component(&mut self) -> Option<NameComponent> {
        match self.peek_char()? {
            '0'..='9' => self.parse_source_name(),
            'S' => self
                .parse_substitution_ref()
                .map(|value| NameComponent { base: value, template_args: Vec::new() }),
            _ => self.parse_operator_name(),
        }
    }

    fn parse_nested_name(&mut self) -> Option<ParsedName> {
        self.consume_if('N').then_some(())?;

        let mut is_const_method = false;
        while let Some(ch) = self.peek_char() {
            match ch {
                'K' => {
                    is_const_method = true;
                    self.pos += 1;
                }
                'V' | 'r' | 'R' => self.pos += 1,
                _ => break,
            }
        }

        let mut rendered_components = Vec::new();
        let mut prefixes = Vec::new();
        let mut last_component: Option<NameComponent> = None;

        while !self.consume_if('E') {
            let component = self.parse_name_component()?;
            let rendered = component.render();

            let prefix = if let Some(prev) = prefixes.last() {
                format!("{prev}::{rendered}")
            } else {
                rendered.clone()
            };
            self.push_substitution(prefix.clone());

            prefixes.push(prefix);
            rendered_components.push(rendered);
            last_component = Some(component);
        }

        let last_component = last_component?;
        let _ = rendered_components.pop();
        Some(ParsedName {
            namespace: rendered_components,
            name: last_component.base,
            template_args: last_component.template_args,
            is_const_method,
        })
    }

    fn parse_name(&mut self) -> Option<ParsedName> {
        if self.peek_char() == Some('N') {
            return self.parse_nested_name();
        }

        let component = self.parse_name_component()?;
        let rendered = component.render();
        self.push_substitution(rendered);
        Some(ParsedName {
            namespace: Vec::new(),
            name: component.base,
            template_args: component.template_args,
            is_const_method: false,
        })
    }

    fn render_parsed_name(&self, name: &ParsedName) -> String {
        let mut rendered = String::new();
        if !name.namespace.is_empty() {
            rendered.push_str(&name.namespace.join("::"));
            rendered.push_str("::");
        }
        rendered.push_str(&name.name);
        if !name.template_args.is_empty() {
            rendered.push('<');
            rendered.push_str(&name.template_args.join(", "));
            rendered.push('>');
        }
        rendered
    }

    fn parse_literal_arg(&mut self) -> Option<String> {
        self.consume_if('L').then_some(())?;
        let ty = self.parse_type()?;
        let negative = self.consume_if('n');
        let start = self.pos;
        while let Some(ch) = self.peek_char() {
            if ch == 'E' {
                break;
            }
            self.pos += 1;
        }
        let digits = String::from_utf8(self.input.get(start..self.pos)?.to_vec()).ok()?;
        self.consume_if('E').then_some(())?;
        render_literal_arg(&ty, negative, &digits)
    }

    fn parse_template_arg(&mut self) -> Option<String> {
        if self.peek_char() == Some('L') { self.parse_literal_arg() } else { self.parse_type() }
    }

    fn parse_template_args(&mut self) -> Option<Vec<String>> {
        let mut args = Vec::new();
        while !self.consume_if('E') {
            args.push(self.parse_template_arg()?);
        }
        Some(args)
    }

    fn parse_type(&mut self) -> Option<String> {
        let basic = match self.peek_char()? {
            'v' => Some("void"),
            'w' => Some("wchar_t"),
            'b' => Some("bool"),
            'c' => Some("char"),
            'a' => Some("signed char"),
            'h' => Some("unsigned char"),
            's' => Some("short"),
            't' => Some("unsigned short"),
            'i' => Some("int"),
            'j' => Some("unsigned int"),
            'l' => Some("long"),
            'm' => Some("unsigned long"),
            'x' => Some("long long"),
            'y' => Some("unsigned long long"),
            'n' => Some("__int128"),
            'o' => Some("unsigned __int128"),
            'f' => Some("float"),
            'd' => Some("double"),
            'e' => Some("long double"),
            _ => None,
        };
        if let Some(rendered) = basic {
            self.pos += 1;
            return Some(rendered.to_string());
        }

        match self.peek_char()? {
            'P' => {
                self.pos += 1;
                let inner = self.parse_type()?;
                Some(format!("{inner}*"))
            }
            'R' => {
                self.pos += 1;
                let inner = self.parse_type()?;
                Some(format!("{inner}&"))
            }
            'O' => {
                self.pos += 1;
                let inner = self.parse_type()?;
                Some(format!("{inner}&&"))
            }
            'K' => {
                self.pos += 1;
                let inner = self.parse_type()?;
                Some(format!("{inner} const"))
            }
            'V' => {
                self.pos += 1;
                let inner = self.parse_type()?;
                Some(format!("{inner} volatile"))
            }
            'L' => self.parse_literal_arg(),
            'N' | '0'..='9' | 'S' => {
                let name = self.parse_name()?;
                let rendered = self.render_parsed_name(&name);
                self.push_substitution(rendered.clone());
                Some(rendered)
            }
            _ => None,
        }
    }

    fn parse_bare_function_type(&mut self) -> Option<Vec<String>> {
        if self.pos >= self.input.len() {
            return Some(Vec::new());
        }
        if self.peek_char() == Some('v') && self.pos + 1 == self.input.len() {
            self.pos += 1;
            return Some(Vec::new());
        }

        let mut params = Vec::new();
        while self.pos < self.input.len() {
            params.push(self.parse_type()?);
        }
        Some(params)
    }

    fn consume_identifier_suffix(&mut self, rendered: &mut String) {
        while self.peek_char().is_some_and(|ch| ch.is_ascii_alphabetic() || ch == '_') {
            if let Some(ch) = self.next_char() {
                rendered.push(ch);
            } else {
                break;
            }
        }
    }
}

fn render_literal_arg(ty: &str, negative: bool, digits: &str) -> Option<String> {
    match ty {
        "bool" => match digits {
            "0" => Some("false".to_string()),
            "1" => Some("true".to_string()),
            _ => None,
        },
        "char" => {
            let value = digits.parse::<u32>().ok()?;
            let ch = char::from_u32(value)?;
            let escaped = ch.escape_default().collect::<String>();
            Some(format!("'{escaped}'"))
        }
        "signed char" | "short" | "int" | "long" | "long long" | "__int128" => {
            let value = digits.parse::<i128>().ok()?;
            Some(if negative { format!("-{value}") } else { value.to_string() })
        }
        "unsigned char" | "unsigned short" | "unsigned int" | "unsigned long"
        | "unsigned long long" | "unsigned __int128" => {
            Some(digits.parse::<u128>().ok()?.to_string())
        }
        _ => Some(if negative { format!("-{digits}") } else { digits.to_string() }),
    }
}

pub(crate) fn demangle_itanium(symbol: &str) -> Option<DemangledSymbol> {
    if !symbol.starts_with("_Z") {
        return None;
    }

    let body = &symbol[2..];
    let mut parser = ItaniumParser::new(body);

    if parser.consume_str("TV") {
        let mut ty = parser.parse_type()?;
        parser.consume_identifier_suffix(&mut ty);
        return Some(DemangledSymbol::new(ManglingScheme::ItaniumCpp, format!("vtable for {ty}")));
    }
    if parser.consume_str("TI") {
        let mut ty = parser.parse_type()?;
        parser.consume_identifier_suffix(&mut ty);
        return Some(DemangledSymbol::new(
            ManglingScheme::ItaniumCpp,
            format!("typeinfo for {ty}"),
        ));
    }
    if parser.consume_str("TS") {
        let mut ty = parser.parse_type()?;
        parser.consume_identifier_suffix(&mut ty);
        return Some(DemangledSymbol::new(
            ManglingScheme::ItaniumCpp,
            format!("typeinfo name for {ty}"),
        ));
    }
    if parser.consume_str("GV") {
        let target = parser.parse_name()?;
        let rendered = parser.render_parsed_name(&target);
        return Some(DemangledSymbol::new(
            ManglingScheme::ItaniumCpp,
            format!("guard variable for {rendered}"),
        ));
    }

    let name = parser.parse_name()?;
    let is_function = parser.pos < parser.input.len();
    let parameters = if is_function { parser.parse_bare_function_type()? } else { Vec::new() };

    let mut symbol =
        DemangledSymbol::with_namespace(ManglingScheme::ItaniumCpp, name.namespace, name.name);
    symbol.template_args = name.template_args;
    symbol.parameters = parameters;
    symbol.is_const = name.is_const_method;
    if is_function && symbol.parameters.is_empty() {
        symbol.return_type = Some(String::new());
    }
    Some(symbol)
}

#[cfg(test)]
mod tests {
    use super::{ItaniumParser, demangle_itanium};

    #[test]
    fn parses_builtin_and_qualified_types() {
        let mut parser = ItaniumParser::new("iRK6String");
        assert_eq!(parser.parse_type().unwrap(), "int");
        assert_eq!(parser.parse_type().unwrap(), "String const&");
    }

    #[test]
    fn demangles_simple_and_nested_functions() {
        let simple = demangle_itanium("_Z3foov").unwrap();
        assert_eq!(simple.to_string(), "foo()");

        let nested = demangle_itanium("_ZN5MyApp10MyFunction3barEv").unwrap();
        assert_eq!(nested.to_string(), "MyApp::MyFunction::bar()");
    }

    #[test]
    fn demangles_templates_and_substitutions() {
        let vector = demangle_itanium("_ZN3std6vectorIiE9push_backEi").unwrap();
        assert_eq!(vector.to_string(), "std::vector<int>::push_back(int)");

        let substitution = demangle_itanium("_ZN3Foo3BarIS_E3bazES0_").unwrap();
        assert_eq!(substitution.to_string(), "Foo::Bar<Foo>::baz(Foo::Bar<Foo>)");
    }

    #[test]
    fn demangles_operator_functions() {
        let symbol = demangle_itanium("_ZplRK6Stringi").unwrap();
        assert_eq!(symbol.to_string(), "operator+(String const&, int)");
    }

    #[test]
    fn demangles_special_names() {
        assert_eq!(demangle_itanium("_ZTV7MyClass").unwrap().to_string(), "vtable for MyClass");
        assert_eq!(demangle_itanium("_ZTI7MyClass").unwrap().to_string(), "typeinfo for MyClass");
        assert_eq!(
            demangle_itanium("_ZTS7MyClass").unwrap().to_string(),
            "typeinfo name for MyClass"
        );
        assert_eq!(
            demangle_itanium("_ZGVN3Foo3barE").unwrap().to_string(),
            "guard variable for Foo::bar"
        );
    }

    // --- Edge case tests for improved coverage ---

    #[test]
    fn test_itanium_not_itanium_prefix_returns_none() {
        assert!(demangle_itanium("").is_none());
        assert!(demangle_itanium("_R").is_none());
        assert!(demangle_itanium("Z3foo").is_none());
        assert!(demangle_itanium("plain").is_none());
    }

    #[test]
    fn test_itanium_all_builtin_types() {
        let cases = [
            ("v", "void"),
            ("w", "wchar_t"),
            ("b", "bool"),
            ("c", "char"),
            ("a", "signed char"),
            ("h", "unsigned char"),
            ("s", "short"),
            ("t", "unsigned short"),
            ("i", "int"),
            ("j", "unsigned int"),
            ("l", "long"),
            ("m", "unsigned long"),
            ("x", "long long"),
            ("y", "unsigned long long"),
            ("n", "__int128"),
            ("o", "unsigned __int128"),
            ("f", "float"),
            ("d", "double"),
            ("e", "long double"),
        ];
        for (input, expected) in cases {
            let mut parser = ItaniumParser::new(input);
            assert_eq!(parser.parse_type().unwrap(), expected, "failed for input: {input}");
        }
    }

    #[test]
    fn test_itanium_pointer_and_reference_types() {
        let mut parser = ItaniumParser::new("Pi");
        assert_eq!(parser.parse_type().unwrap(), "int*");

        let mut parser = ItaniumParser::new("Ri");
        assert_eq!(parser.parse_type().unwrap(), "int&");

        let mut parser = ItaniumParser::new("Oi");
        assert_eq!(parser.parse_type().unwrap(), "int&&");
    }

    #[test]
    fn test_itanium_const_volatile_qualifiers() {
        let mut parser = ItaniumParser::new("Ki");
        assert_eq!(parser.parse_type().unwrap(), "int const");

        let mut parser = ItaniumParser::new("Vi");
        assert_eq!(parser.parse_type().unwrap(), "int volatile");

        // const pointer to int
        let mut parser = ItaniumParser::new("KPi");
        assert_eq!(parser.parse_type().unwrap(), "int* const");
    }

    #[test]
    fn test_itanium_nested_pointer_types() {
        // pointer to pointer to int
        let mut parser = ItaniumParser::new("PPi");
        assert_eq!(parser.parse_type().unwrap(), "int**");
    }

    #[test]
    fn test_itanium_const_method_demangle() {
        let symbol = demangle_itanium("_ZNK3Foo3getEv").unwrap();
        assert!(symbol.is_const);
        assert_eq!(symbol.to_string(), "Foo::get() const");
    }

    #[test]
    fn test_itanium_void_parameter_function() {
        let symbol = demangle_itanium("_Z3foov").unwrap();
        assert_eq!(symbol.parameters.len(), 0);
        assert_eq!(symbol.to_string(), "foo()");
    }

    #[test]
    fn test_itanium_multiple_parameters() {
        let symbol = demangle_itanium("_Z3fooifl").unwrap();
        assert_eq!(symbol.parameters, vec!["int", "float", "long"]);
        assert_eq!(symbol.to_string(), "foo(int, float, long)");
    }

    #[test]
    fn test_itanium_std_substitutions() {
        let mut parser = ItaniumParser::new("St");
        let result = parser.parse_substitution_ref().unwrap();
        assert_eq!(result, "std");

        let mut parser = ItaniumParser::new("Ss");
        let result = parser.parse_substitution_ref().unwrap();
        assert_eq!(result, "std::string");

        let mut parser = ItaniumParser::new("So");
        let result = parser.parse_substitution_ref().unwrap();
        assert_eq!(result, "std::ostream");

        let mut parser = ItaniumParser::new("Si");
        let result = parser.parse_substitution_ref().unwrap();
        assert_eq!(result, "std::istream");

        let mut parser = ItaniumParser::new("Sd");
        let result = parser.parse_substitution_ref().unwrap();
        assert_eq!(result, "std::iostream");
    }

    #[test]
    fn test_itanium_no_args_data_symbol() {
        // A symbol with no function parameters (data symbol)
        let symbol = demangle_itanium("_ZN3Foo3barE").unwrap();
        assert!(symbol.parameters.is_empty());
        assert_eq!(symbol.name, "bar");
        assert_eq!(symbol.namespace, vec!["Foo"]);
    }

    #[test]
    fn test_itanium_literal_template_arg_bool() {
        // Template with bool literal: _Z3fooILb1EEvv
        let result = demangle_itanium("_Z3fooILb1EEvv");
        // May or may not parse depending on parser completeness
        // but should not panic
        let _ = result;
    }
}
