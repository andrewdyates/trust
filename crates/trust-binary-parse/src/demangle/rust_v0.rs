// Author: Andrew Yates <andrew@andrewdyates.com>
// trust-binary-parse demangle::rust_v0: Rust RFC 2603 demangling
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::{DemangledSymbol, ManglingScheme};

#[derive(Debug, Clone, PartialEq, Eq)]
struct RustIdentifier {
    name: String,
    disambiguator: u64,
}

pub(crate) struct RustV0Parser<'a> {
    input: &'a [u8],
    pos: usize,
    backref_depth: usize,
}

impl<'a> RustV0Parser<'a> {
    fn new(input: &'a str, pos: usize) -> Self {
        Self { input: input.as_bytes(), pos, backref_depth: 0 }
    }

    fn with_backref(input: &'a [u8], pos: usize, backref_depth: usize) -> Self {
        Self { input, pos, backref_depth }
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

    fn expect_char(&mut self, expected: char) -> Option<()> {
        if self.consume_if(expected) { Some(()) } else { None }
    }

    fn read_bytes(&mut self, len: usize) -> Option<&'a [u8]> {
        let end = self.pos.checked_add(len)?;
        let bytes = self.input.get(self.pos..end)?;
        self.pos = end;
        Some(bytes)
    }

    fn parse_decimal_number(&mut self) -> Option<usize> {
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

    fn parse_base62(&mut self) -> Option<u64> {
        let mut value = 0u64;
        let mut saw_digit = false;
        loop {
            let ch = self.next_char()?;
            if ch == '_' {
                return if saw_digit { value.checked_add(1) } else { Some(0) };
            }
            let digit = match ch {
                '0'..='9' => (ch as u8 - b'0') as u64,
                'a'..='z' => (ch as u8 - b'a') as u64 + 10,
                'A'..='Z' => (ch as u8 - b'A') as u64 + 36,
                _ => return None,
            };
            saw_digit = true;
            value = value.checked_mul(62)?.checked_add(digit)?;
        }
    }

    fn parse_opt_disambiguator(&mut self) -> Option<u64> {
        if self.consume_if('s') { self.parse_base62()?.checked_add(1) } else { Some(0) }
    }

    pub(crate) fn parse_identifier(&mut self) -> Option<String> {
        self.parse_identifier_parts().map(|identifier| identifier.name)
    }

    fn parse_identifier_parts(&mut self) -> Option<RustIdentifier> {
        let disambiguator = self.parse_opt_disambiguator()?;
        let _is_punycode = self.consume_if('u');
        let len = self.parse_decimal_number()?;
        let _has_separator = self.consume_if('_');
        let name = String::from_utf8(self.read_bytes(len)?.to_vec()).ok()?;
        Some(RustIdentifier { name, disambiguator })
    }

    fn parse_lifetime(&mut self) -> Option<String> {
        self.expect_char('L')?;
        let index = self.parse_base62()?;
        if index == 0 {
            Some("'_".to_string())
        } else if index <= 26 {
            let letter = char::from(b'a' + (index as u8 - 1));
            Some(format!("'{letter}"))
        } else {
            Some(format!("'_{}", index))
        }
    }

    fn parse_fn_type(&mut self) -> Option<String> {
        self.expect_char('F')?;
        let binder_count =
            if self.consume_if('G') { self.parse_base62()?.checked_add(1)? } else { 0 };
        let is_unsafe = self.consume_if('U');
        let abi = if self.consume_if('K') {
            if self.consume_if('C') {
                Some("extern \"C\" ".to_string())
            } else {
                let abi_name = self.parse_undisambiguated_identifier()?;
                Some(format!("extern \"{}\" ", abi_name))
            }
        } else {
            None
        };

        let mut params = Vec::new();
        while !self.consume_if('E') {
            if self.peek_char()? == 'v' {
                self.pos += 1;
                params.push("...".to_string());
            } else {
                params.push(self.parse_type()?);
            }
        }
        let return_type = self.parse_type()?;

        let mut rendered = String::new();
        if binder_count > 0 {
            rendered.push_str("for<");
            let names = (0..binder_count)
                .map(|idx| format!("'{}", char::from(b'a' + (idx as u8 % 26))))
                .collect::<Vec<_>>();
            rendered.push_str(&names.join(", "));
            rendered.push_str("> ");
        }
        if is_unsafe {
            rendered.push_str("unsafe ");
        }
        if let Some(abi) = abi {
            rendered.push_str(&abi);
        }
        rendered.push_str("fn(");
        rendered.push_str(&params.join(", "));
        rendered.push(')');
        if return_type != "()" {
            rendered.push_str(" -> ");
            rendered.push_str(&return_type);
        }
        Some(rendered)
    }

    fn parse_undisambiguated_identifier(&mut self) -> Option<String> {
        let _is_punycode = self.consume_if('u');
        let len = self.parse_decimal_number()?;
        let _has_separator = self.consume_if('_');
        String::from_utf8(self.read_bytes(len)?.to_vec()).ok()
    }

    pub(crate) fn parse_const(&mut self) -> Option<String> {
        if self.consume_if('p') {
            return Some("_".to_string());
        }
        if self.peek_char() == Some('B') {
            return self.parse_backref(|parser| parser.parse_const());
        }

        let ty = self.parse_type()?;
        let negative = self.consume_if('n');
        let start = self.pos;
        while let Some(ch) = self.peek_char() {
            if ch == '_' {
                break;
            }
            if !ch.is_ascii_hexdigit() {
                return None;
            }
            self.pos += 1;
        }
        let digits = String::from_utf8(self.input.get(start..self.pos)?.to_vec()).ok()?;
        self.expect_char('_')?;
        render_const_value(&ty, negative, &digits)
    }

    pub(crate) fn parse_generic_args(&mut self) -> Option<Vec<String>> {
        let mut args = Vec::new();
        loop {
            if self.consume_if('E') {
                break;
            }
            let arg = if self.peek_char()? == 'L' {
                self.parse_lifetime()?
            } else if self.consume_if('K') {
                self.parse_const()?
            } else {
                self.parse_type()?
            };
            args.push(arg);
        }
        Some(args)
    }

    fn render_nested_path(
        &self,
        namespace: char,
        parent: String,
        identifier: RustIdentifier,
    ) -> String {
        match namespace {
            'C' => {
                if identifier.name.is_empty() {
                    format!("{parent}::{{closure#{}}}", identifier.disambiguator)
                } else {
                    format!(
                        "{parent}::{{closure:{}#{}}}",
                        identifier.name, identifier.disambiguator
                    )
                }
            }
            'S' => {
                if identifier.name.is_empty() {
                    format!("{parent}::{{shim#{}}}", identifier.disambiguator)
                } else {
                    format!("{parent}::{{shim:{}#{}}}", identifier.name, identifier.disambiguator)
                }
            }
            _ if identifier.name.is_empty() => parent,
            _ => format!("{parent}::{}", identifier.name),
        }
    }

    pub(crate) fn parse_path(&mut self) -> Option<String> {
        match self.peek_char()? {
            'C' => {
                self.pos += 1;
                self.parse_identifier()
            }
            'M' => {
                self.pos += 1;
                let _impl_disambiguator = self.parse_opt_disambiguator()?;
                let _parent = self.parse_path()?;
                let self_ty = self.parse_type()?;
                Some(format!("<{self_ty}>"))
            }
            'X' => {
                self.pos += 1;
                let _impl_disambiguator = self.parse_opt_disambiguator()?;
                let _parent = self.parse_path()?;
                let self_ty = self.parse_type()?;
                let trait_path = self.parse_path()?;
                Some(format!("<{self_ty} as {trait_path}>"))
            }
            'Y' => {
                self.pos += 1;
                let self_ty = self.parse_type()?;
                let trait_path = self.parse_path()?;
                Some(format!("<{self_ty} as {trait_path}>"))
            }
            'N' => {
                self.pos += 1;
                let namespace = self.next_char()?;
                let parent = self.parse_path()?;
                let identifier = self.parse_identifier_parts()?;
                Some(self.render_nested_path(namespace, parent, identifier))
            }
            'I' => {
                self.pos += 1;
                let base = self.parse_path()?;
                let _wrapped_example_args = self.consume_if('I');
                let args = self.parse_generic_args()?;
                Some(render_rust_generic_path(&base, &args))
            }
            'B' => self.parse_backref(|parser| parser.parse_path()),
            _ => None,
        }
    }

    pub(crate) fn parse_type(&mut self) -> Option<String> {
        let basic_type = match self.peek_char()? {
            'a' => Some("i8"),
            'b' => Some("bool"),
            'c' => Some("char"),
            'd' => Some("f64"),
            'e' => Some("str"),
            'f' => Some("f32"),
            'h' => Some("u8"),
            'i' => Some("isize"),
            'j' => Some("usize"),
            'l' => Some("i32"),
            'm' => Some("u32"),
            'n' => Some("i128"),
            'o' => Some("u128"),
            'p' => Some("_"),
            's' => Some("i16"),
            't' => Some("u16"),
            'u' => Some("()"),
            'v' => Some("..."),
            'x' => Some("i64"),
            'y' => Some("u64"),
            'z' => Some("!"),
            _ => None,
        };
        if let Some(rendered) = basic_type {
            self.pos += 1;
            return Some(rendered.to_string());
        }

        match self.peek_char()? {
            'A' => {
                self.pos += 1;
                let element_ty = self.parse_type()?;
                let len = self.parse_const()?;
                Some(format!("[{element_ty}; {len}]"))
            }
            'S' => {
                self.pos += 1;
                let element_ty = self.parse_type()?;
                Some(format!("[{element_ty}]"))
            }
            'T' => {
                self.pos += 1;
                let mut fields = Vec::new();
                while !self.consume_if('E') {
                    fields.push(self.parse_type()?);
                }
                if fields.len() == 1 {
                    Some(format!("({},)", fields[0]))
                } else {
                    Some(format!("({})", fields.join(", ")))
                }
            }
            'R' => {
                self.pos += 1;
                if self.peek_char() == Some('L') {
                    let _lifetime = self.parse_lifetime()?;
                }
                let inner = self.parse_type()?;
                Some(format!("&{inner}"))
            }
            'Q' => {
                self.pos += 1;
                if self.peek_char() == Some('L') {
                    let _lifetime = self.parse_lifetime()?;
                }
                let inner = self.parse_type()?;
                Some(format!("&mut {inner}"))
            }
            'P' => {
                self.pos += 1;
                let inner = self.parse_type()?;
                Some(format!("*const {inner}"))
            }
            'O' => {
                self.pos += 1;
                let inner = self.parse_type()?;
                Some(format!("*mut {inner}"))
            }
            'F' => self.parse_fn_type(),
            'D' => {
                self.pos += 1;
                if self.consume_if('G') {
                    let _binder_count = self.parse_base62()?.checked_add(1)?;
                }
                let mut traits = Vec::new();
                while !self.consume_if('E') {
                    traits.push(self.parse_path()?);
                }
                let lifetime = self.parse_lifetime()?;
                Some(format!("dyn {} + {}", traits.join(" + "), lifetime))
            }
            'W' => {
                self.pos += 1;
                let inner = self.parse_type()?;
                Some(format!("{inner} /* pattern */"))
            }
            'C' | 'M' | 'X' | 'Y' | 'N' | 'I' => self.parse_path(),
            'B' => self.parse_backref(|parser| parser.parse_type()),
            _ => None,
        }
    }

    fn parse_backref<T>(
        &mut self,
        parse_value: impl FnOnce(&mut RustV0Parser<'a>) -> Option<T>,
    ) -> Option<T> {
        const MAX_BACKREF_DEPTH: usize = 32;

        let backref_start = self.pos;
        self.expect_char('B')?;
        let offset = self.parse_base62()? as usize;
        if offset >= backref_start || self.backref_depth >= MAX_BACKREF_DEPTH {
            return None;
        }

        let mut parser = RustV0Parser::with_backref(self.input, offset, self.backref_depth + 1);
        parse_value(&mut parser)
    }
}

fn render_const_value(ty: &str, negative: bool, digits: &str) -> Option<String> {
    match ty {
        "bool" => match digits {
            "0" => Some("false".to_string()),
            "1" => Some("true".to_string()),
            _ => None,
        },
        "char" => {
            let value = u32::from_str_radix(digits, 16).ok()?;
            let ch = char::from_u32(value)?;
            let escaped = ch.escape_default().collect::<String>();
            Some(format!("'{escaped}'"))
        }
        "i8" | "i16" | "i32" | "i64" | "i128" | "isize" => {
            let value = i128::from_str_radix(digits, 16).ok()?;
            Some(if negative { format!("-{value}") } else { value.to_string() })
        }
        "u8" | "u16" | "u32" | "u64" | "u128" | "usize" => {
            let value = u128::from_str_radix(digits, 16).ok()?;
            Some(value.to_string())
        }
        _ => Some(if negative { format!("-0x{digits}") } else { format!("0x{digits}") }),
    }
}

fn render_rust_generic_path(base: &str, args: &[String]) -> String {
    let joined = args.join(", ");
    if last_segment_is_type_like(base) {
        format!("{base}<{joined}>")
    } else {
        format!("{base}::<{joined}>")
    }
}

fn last_segment_is_type_like(path: &str) -> bool {
    let segments = split_rust_path(path);
    let segment = segments.last().map(String::as_str).unwrap_or(path).trim();
    let first = segment.chars().next();
    segment.starts_with('<')
        || segment.starts_with('[')
        || segment.starts_with('&')
        || segment.starts_with('*')
        || segment.starts_with('(')
        || segment.contains(" as ")
        || first.is_some_and(char::is_uppercase)
}

fn split_rust_path(path: &str) -> Vec<String> {
    let mut segments = Vec::new();
    let mut start = 0usize;
    let mut angle_depth = 0i32;
    let mut brace_depth = 0i32;
    let mut bracket_depth = 0i32;
    let mut paren_depth = 0i32;
    let chars: Vec<(usize, char)> = path.char_indices().collect();

    let mut idx = 0usize;
    while idx < chars.len() {
        let (byte_idx, ch) = chars[idx];
        match ch {
            '<' => angle_depth += 1,
            '>' => angle_depth -= 1,
            '{' => brace_depth += 1,
            '}' => brace_depth -= 1,
            '[' => bracket_depth += 1,
            ']' => bracket_depth -= 1,
            '(' => paren_depth += 1,
            ')' => paren_depth -= 1,
            ':' if angle_depth == 0
                && brace_depth == 0
                && bracket_depth == 0
                && paren_depth == 0
                && idx + 1 < chars.len()
                && chars[idx + 1].1 == ':'
                && !(idx + 2 < chars.len() && chars[idx + 2].1 == '<') =>
            {
                segments.push(path[start..byte_idx].to_string());
                start = chars[idx + 1].0 + chars[idx + 1].1.len_utf8();
                idx += 1;
            }
            _ => {}
        }
        idx += 1;
    }

    if start <= path.len() {
        segments.push(path[start..].to_string());
    }
    segments
}

fn split_top_level_args(args: &str) -> Vec<String> {
    let mut values = Vec::new();
    let mut start = 0usize;
    let mut angle_depth = 0i32;
    let mut bracket_depth = 0i32;
    let mut paren_depth = 0i32;

    for (idx, ch) in args.char_indices() {
        match ch {
            '<' => angle_depth += 1,
            '>' => angle_depth -= 1,
            '[' => bracket_depth += 1,
            ']' => bracket_depth -= 1,
            '(' => paren_depth += 1,
            ')' => paren_depth -= 1,
            ',' if angle_depth == 0 && bracket_depth == 0 && paren_depth == 0 => {
                values.push(args[start..idx].trim().to_string());
                start = idx + ch.len_utf8();
            }
            _ => {}
        }
    }

    if start < args.len() {
        values.push(args[start..].trim().to_string());
    }

    values.into_iter().filter(|value| !value.is_empty()).collect()
}

fn split_name_and_template_args(segment: &str) -> (String, Vec<String>) {
    if let Some(prefix_idx) = segment.find("::<")
        && segment.ends_with('>')
    {
        let name = segment[..prefix_idx].to_string();
        let args = &segment[prefix_idx + 3..segment.len() - 1];
        return (name, split_top_level_args(args));
    }
    (segment.to_string(), Vec::new())
}

fn symbol_from_rendered_path(path: String) -> DemangledSymbol {
    let segments = split_rust_path(&path);
    if let Some((last, namespace)) = segments.split_last() {
        let (name, template_args) = split_name_and_template_args(last);
        let mut symbol =
            DemangledSymbol::with_namespace(ManglingScheme::RustV0, namespace.to_vec(), name);
        symbol.template_args = template_args;
        symbol
    } else {
        DemangledSymbol::new(ManglingScheme::RustV0, path)
    }
}

pub(crate) fn demangle_rust_v0(symbol: &str) -> Option<DemangledSymbol> {
    if !symbol.starts_with("_R") {
        return None;
    }

    let body = &symbol[2..];
    let mut parser = RustV0Parser::new(body, 0);
    while parser.peek_char().is_some_and(|ch| ch.is_ascii_digit()) {
        parser.pos += 1;
    }

    let path = parser.parse_path()?;
    Some(symbol_from_rendered_path(path))
}

#[cfg(test)]
mod tests {
    use super::{RustV0Parser, demangle_rust_v0};

    #[test]
    fn parses_basic_types() {
        let mut parser = RustV0Parser::new("bhQhAtj8_", 0);
        assert_eq!(parser.parse_type().unwrap(), "bool");
        assert_eq!(parser.parse_type().unwrap(), "u8");
        assert_eq!(parser.parse_type().unwrap(), "&mut u8");
        assert_eq!(parser.parse_type().unwrap(), "[u16; 8]");
    }

    #[test]
    fn parses_identifiers_and_consts() {
        let mut parser = RustV0Parser::new("s_0j1_", 0);
        let identifier = parser.parse_identifier_parts().unwrap();
        assert_eq!(identifier.name, "");
        assert_eq!(identifier.disambiguator, 1);
        assert_eq!(parser.parse_const().unwrap(), "1");
    }

    #[test]
    fn demangles_simple_path() {
        let symbol = demangle_rust_v0("_RNvCs15kBYyAo9fc_7mycrate7example").unwrap();
        assert_eq!(symbol.namespace, vec!["mycrate"]);
        assert_eq!(symbol.name, "example");
        assert_eq!(symbol.to_string(), "mycrate::example");
    }

    #[test]
    fn demangles_nested_path() {
        let symbol = demangle_rust_v0("_RNvNtCs12345_5crate3foo3bar").unwrap();
        assert_eq!(symbol.namespace, vec!["crate", "foo"]);
        assert_eq!(symbol.name, "bar");
        assert_eq!(symbol.to_string(), "crate::foo::bar");
    }

    #[test]
    fn demangles_generic_args_and_const_generics() {
        let generic = demangle_rust_v0("_RINvNtCs12345_5crate3vec4pushIhEE").unwrap();
        assert_eq!(generic.namespace, vec!["crate", "vec"]);
        assert_eq!(generic.name, "push");
        assert_eq!(generic.template_args, vec!["u8"]);
        assert_eq!(generic.to_string(), "crate::vec::push::<u8>");

        let const_generic =
            demangle_rust_v0("_RINvCsgStHSCytQ6I_7mycrate7examplelKj1_EB2_").unwrap();
        assert_eq!(const_generic.to_string(), "mycrate::example::<i32, 1>");
    }

    #[test]
    fn demangles_closures_and_impl_blocks() {
        let closure = demangle_rust_v0("_RNCNvCs12345_5crate4main0").unwrap();
        assert_eq!(closure.to_string(), "crate::main::{closure#0}");

        let inherent = demangle_rust_v0("_RNvMs_Cs4Cv8Wi1oAIB_7mycrateNtB4_7Example3foo").unwrap();
        assert_eq!(inherent.to_string(), "<mycrate::Example>::foo");

        let trait_impl =
            demangle_rust_v0("_RNvXCs15kBYyAo9fc_7mycrateNtB2_7ExampleNtB2_5Trait3foo").unwrap();
        assert_eq!(trait_impl.to_string(), "<mycrate::Example as mycrate::Trait>::foo");
    }

    // --- Edge case tests for improved coverage ---

    #[test]
    fn test_rust_v0_not_rust_prefix_returns_none() {
        assert!(demangle_rust_v0("").is_none());
        assert!(demangle_rust_v0("_Z3foo").is_none());
        assert!(demangle_rust_v0("_r").is_none());
        assert!(demangle_rust_v0("R").is_none());
        assert!(demangle_rust_v0("plain_symbol").is_none());
    }

    #[test]
    fn test_rust_v0_parse_basic_type_all_variants() {
        let mut parser = RustV0Parser::new("abcdefhijlmnopstuvxyz", 0);
        assert_eq!(parser.parse_type().unwrap(), "i8");       // a
        assert_eq!(parser.parse_type().unwrap(), "bool");     // b
        assert_eq!(parser.parse_type().unwrap(), "char");     // c
        assert_eq!(parser.parse_type().unwrap(), "f64");      // d
        assert_eq!(parser.parse_type().unwrap(), "str");      // e
        assert_eq!(parser.parse_type().unwrap(), "f32");      // f
        assert_eq!(parser.parse_type().unwrap(), "u8");       // h
        assert_eq!(parser.parse_type().unwrap(), "isize");    // i
        assert_eq!(parser.parse_type().unwrap(), "usize");    // j
        assert_eq!(parser.parse_type().unwrap(), "i32");      // l
        assert_eq!(parser.parse_type().unwrap(), "u32");      // m
        assert_eq!(parser.parse_type().unwrap(), "i128");     // n
        assert_eq!(parser.parse_type().unwrap(), "u128");     // o
        assert_eq!(parser.parse_type().unwrap(), "_");        // p
        assert_eq!(parser.parse_type().unwrap(), "i16");      // s
        assert_eq!(parser.parse_type().unwrap(), "u16");      // t
        assert_eq!(parser.parse_type().unwrap(), "()");       // u
        assert_eq!(parser.parse_type().unwrap(), "...");      // v
        assert_eq!(parser.parse_type().unwrap(), "i64");      // x
        assert_eq!(parser.parse_type().unwrap(), "u64");      // y
        assert_eq!(parser.parse_type().unwrap(), "!");        // z
    }

    #[test]
    fn test_rust_v0_parse_reference_types() {
        let mut parser = RustV0Parser::new("RhQl", 0);
        assert_eq!(parser.parse_type().unwrap(), "&u8");
        assert_eq!(parser.parse_type().unwrap(), "&mut i32");
    }

    #[test]
    fn test_rust_v0_parse_pointer_types() {
        let mut parser = RustV0Parser::new("PhOl", 0);
        assert_eq!(parser.parse_type().unwrap(), "*const u8");
        assert_eq!(parser.parse_type().unwrap(), "*mut i32");
    }

    #[test]
    fn test_rust_v0_parse_slice_type() {
        let mut parser = RustV0Parser::new("Sh", 0);
        assert_eq!(parser.parse_type().unwrap(), "[u8]");
    }

    #[test]
    fn test_rust_v0_parse_tuple_types() {
        // Empty tuple -> ()
        let mut parser = RustV0Parser::new("TE", 0);
        assert_eq!(parser.parse_type().unwrap(), "()");

        // Single-element tuple -> (T,)
        let mut parser = RustV0Parser::new("ThE", 0);
        assert_eq!(parser.parse_type().unwrap(), "(u8,)");

        // Two-element tuple -> (T, U)
        let mut parser = RustV0Parser::new("ThlE", 0);
        assert_eq!(parser.parse_type().unwrap(), "(u8, i32)");
    }

    #[test]
    fn test_rust_v0_parse_const_bool_values() {
        let mut parser = RustV0Parser::new("b0_b1_", 0);
        assert_eq!(parser.parse_const().unwrap(), "false");
        assert_eq!(parser.parse_const().unwrap(), "true");
    }

    #[test]
    fn test_rust_v0_parse_const_placeholder() {
        let mut parser = RustV0Parser::new("p", 0);
        assert_eq!(parser.parse_const().unwrap(), "_");
    }

    #[test]
    fn test_rust_v0_parse_const_unsigned_integer() {
        let mut parser = RustV0Parser::new("j2a_", 0);
        assert_eq!(parser.parse_const().unwrap(), "42");
    }

    #[test]
    fn test_rust_v0_parse_const_negative_integer() {
        let mut parser = RustV0Parser::new("ln5_", 0);
        assert_eq!(parser.parse_const().unwrap(), "-5");
    }

    #[test]
    fn test_rust_v0_parse_const_char() {
        let mut parser = RustV0Parser::new("c41_", 0);
        assert_eq!(parser.parse_const().unwrap(), "'A'");
    }

    #[test]
    fn test_rust_v0_base62_edge_cases() {
        // '_' immediately => 0
        let mut parser = RustV0Parser::new("_", 0);
        assert_eq!(parser.parse_base62().unwrap(), 0);

        // '0_' => 0 + 1 = 1
        let mut parser = RustV0Parser::new("0_", 0);
        assert_eq!(parser.parse_base62().unwrap(), 1);

        // 'Z_' => Z maps to 36 + ('Z' - 'A') = 36 + 25 = 61, then +1 = 62
        let mut parser = RustV0Parser::new("Z_", 0);
        assert_eq!(parser.parse_base62().unwrap(), 62);
    }

    #[test]
    fn test_rust_v0_parse_lifetime() {
        // L_ => anonymous lifetime
        let mut parser = RustV0Parser::new("L_", 0);
        assert_eq!(parser.parse_lifetime().unwrap(), "'_");

        // L0_ => first named lifetime 'a
        let mut parser = RustV0Parser::new("L0_", 0);
        assert_eq!(parser.parse_lifetime().unwrap(), "'a");

        // L1_ => 'b
        let mut parser = RustV0Parser::new("L1_", 0);
        assert_eq!(parser.parse_lifetime().unwrap(), "'b");
    }

    #[test]
    fn test_rust_v0_backref_depth_limit() {
        // Create a symbol that would cause deep backref recursion
        // B followed by offset pointing before current position
        // This should return None due to depth limit or invalid offset
        assert!(demangle_rust_v0("_RB_").is_none());
    }

    #[test]
    fn test_rust_v0_generic_args_multiple_types() {
        let result = demangle_rust_v0("_RINvCs12345_5crate3funhlbEE").unwrap();
        assert!(result.template_args.len() >= 2);
    }

    #[test]
    fn test_rust_v0_decimal_number_parsing() {
        let mut parser = RustV0Parser::new("12345_abc", 0);
        assert_eq!(parser.parse_decimal_number().unwrap(), 12345);
        assert_eq!(parser.pos, 5);
    }

    #[test]
    fn test_rust_v0_decimal_number_no_digits() {
        let mut parser = RustV0Parser::new("abc", 0);
        assert!(parser.parse_decimal_number().is_none());
        assert_eq!(parser.pos, 0);
    }
}
