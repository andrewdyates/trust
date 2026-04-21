// trust-types/spec_parse.rs: Parser for simple contract expressions
//
// Parses spec expression strings from #[requires("...")], #[ensures("...")], etc.
// into Formula values suitable for SMT solving.
//
// Supports:
// - Boolean operators: &&, ||, !, =>
// - Comparison operators: <, <=, >, >=, ==, !=
// - Arithmetic: +, -, *, /
// - Quantifiers: forall(i, 0..n, expr), exists(i, 0..n, expr)
// - Method-style access: arr.len(), s.is_empty()
// - Special names: result (maps to _0), old(x) (maps to old_x)
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::spec::SpecParseError;
use crate::{Formula, Sort};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Token {
    Ident(String),
    Int(i128),
    Gt,
    Ge,
    Lt,
    Le,
    EqEq,
    Ne,
    Plus,
    Minus,
    Star,
    Slash,
    AndAnd,
    OrOr,
    Bang,
    Implies,
    LParen,
    RParen,
    Comma,
    Dot,
    DotDot,
    Colon,
    Percent,
    LBracket,
    RBracket,
}

/// Parse a simple specification predicate body into a solver formula.
///
/// Returns `None` on any parse failure. For structured errors, use
/// [`parse_spec_expr_result`] instead.
#[must_use]
pub fn parse_spec_expr(input: &str) -> Option<Formula> {
    parse_spec_expr_result(input).ok()
}

/// Parse a specification expression with structured error reporting.
pub fn parse_spec_expr_result(input: &str) -> Result<Formula, SpecParseError> {
    if input.trim().is_empty() {
        return Err(SpecParseError::Empty);
    }

    let tokens = tokenize(input)?;
    let mut parser = Parser::new(tokens);
    let formula = parser.parse_implies()?;

    if parser.is_eof() { Ok(formula) } else { Err(SpecParseError::TrailingTokens) }
}

pub(crate) fn tokenize(input: &str) -> Result<Vec<Token>, SpecParseError> {
    let bytes = input.as_bytes();
    let mut tokens = Vec::new();
    let mut index = 0;

    while index < bytes.len() {
        let byte = bytes[index];

        if byte.is_ascii_whitespace() {
            index += 1;
            continue;
        }

        if byte.is_ascii_digit() {
            let start = index;
            index += 1;

            while index < bytes.len() && bytes[index].is_ascii_digit() {
                index += 1;
            }

            let value = input[start..index].parse::<i128>().map_err(|_| {
                SpecParseError::UnexpectedToken {
                    position: start,
                    expected: "valid integer literal".into(),
                }
            })?;
            tokens.push(Token::Int(value));
            continue;
        }

        if byte.is_ascii_alphabetic() || byte == b'_' {
            let start = index;
            index += 1;

            while index < bytes.len()
                && (bytes[index].is_ascii_alphanumeric() || bytes[index] == b'_')
            {
                index += 1;
            }

            tokens.push(Token::Ident(input[start..index].to_string()));
            continue;
        }

        let token = match (byte, bytes.get(index + 1).copied()) {
            (b'>', Some(b'=')) => {
                index += 2;
                Token::Ge
            }
            (b'<', Some(b'=')) => {
                index += 2;
                Token::Le
            }
            (b'=', Some(b'=')) => {
                index += 2;
                Token::EqEq
            }
            (b'!', Some(b'=')) => {
                index += 2;
                Token::Ne
            }
            (b'&', Some(b'&')) => {
                index += 2;
                Token::AndAnd
            }
            (b'|', Some(b'|')) => {
                index += 2;
                Token::OrOr
            }
            (b'=', Some(b'>')) => {
                index += 2;
                Token::Implies
            }
            (b'.', Some(b'.')) => {
                index += 2;
                Token::DotDot
            }
            (b'>', _) => {
                index += 1;
                Token::Gt
            }
            (b'<', _) => {
                index += 1;
                Token::Lt
            }
            (b'+', _) => {
                index += 1;
                Token::Plus
            }
            (b'-', _) => {
                index += 1;
                Token::Minus
            }
            (b'*', _) => {
                index += 1;
                Token::Star
            }
            (b'/', _) => {
                index += 1;
                Token::Slash
            }
            (b'!', _) => {
                index += 1;
                Token::Bang
            }
            (b'(', _) => {
                index += 1;
                Token::LParen
            }
            (b')', _) => {
                index += 1;
                Token::RParen
            }
            (b',', _) => {
                index += 1;
                Token::Comma
            }
            (b'.', _) => {
                index += 1;
                Token::Dot
            }
            (b':', _) => {
                index += 1;
                Token::Colon
            }
            (b'%', _) => {
                index += 1;
                Token::Percent
            }
            (b'[', _) => {
                index += 1;
                Token::LBracket
            }
            (b']', _) => {
                index += 1;
                Token::RBracket
            }
            _ => {
                return Err(SpecParseError::UnexpectedChar { ch: byte as char, position: index });
            }
        };

        tokens.push(token);
    }

    Ok(tokens)
}

struct Parser {
    tokens: Vec<Token>,
    index: usize,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, index: 0 }
    }

    fn is_eof(&self) -> bool {
        self.index == self.tokens.len()
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.index)
    }

    fn bump(&mut self) -> Result<Token, SpecParseError> {
        self.tokens
            .get(self.index)
            .cloned()
            .inspect(|_t| {
                self.index += 1;
            })
            .ok_or_else(|| SpecParseError::UnexpectedEof { expected: "token".into() })
    }

    fn eat(&mut self, expected: &Token) -> bool {
        if self.peek() == Some(expected) {
            self.index += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, expected: &Token, label: &str) -> Result<(), SpecParseError> {
        if self.eat(expected) {
            Ok(())
        } else if self.is_eof() {
            Err(SpecParseError::UnexpectedEof { expected: label.into() })
        } else {
            Err(SpecParseError::UnexpectedToken { position: self.index, expected: label.into() })
        }
    }

    fn parse_implies(&mut self) -> Result<Formula, SpecParseError> {
        let lhs = self.parse_or()?;

        if self.eat(&Token::Implies) {
            let rhs = self.parse_implies()?;
            Ok(Formula::Implies(Box::new(lhs), Box::new(rhs)))
        } else {
            Ok(lhs)
        }
    }

    fn parse_or(&mut self) -> Result<Formula, SpecParseError> {
        let first = self.parse_and()?;
        let mut terms = vec![first];

        while self.eat(&Token::OrOr) {
            terms.push(self.parse_and()?);
        }

        if terms.len() == 1 {
            Ok(terms.pop().expect("invariant: non-empty"))
        } else {
            Ok(Formula::Or(terms))
        }
    }

    fn parse_and(&mut self) -> Result<Formula, SpecParseError> {
        let first = self.parse_comparison()?;
        let mut terms = vec![first];

        while self.eat(&Token::AndAnd) {
            terms.push(self.parse_comparison()?);
        }

        if terms.len() == 1 {
            Ok(terms.pop().expect("invariant: non-empty"))
        } else {
            Ok(Formula::And(terms))
        }
    }

    fn parse_comparison(&mut self) -> Result<Formula, SpecParseError> {
        let lhs = self.parse_add_sub()?;

        match self.peek().cloned() {
            Some(Token::Gt) => {
                self.bump()?;
                let rhs = self.parse_add_sub()?;
                Ok(Formula::Gt(Box::new(lhs), Box::new(rhs)))
            }
            Some(Token::Ge) => {
                self.bump()?;
                let rhs = self.parse_add_sub()?;
                Ok(Formula::Ge(Box::new(lhs), Box::new(rhs)))
            }
            Some(Token::Lt) => {
                self.bump()?;
                let rhs = self.parse_add_sub()?;
                Ok(Formula::Lt(Box::new(lhs), Box::new(rhs)))
            }
            Some(Token::Le) => {
                self.bump()?;
                let rhs = self.parse_add_sub()?;
                Ok(Formula::Le(Box::new(lhs), Box::new(rhs)))
            }
            Some(Token::EqEq) => {
                self.bump()?;
                let rhs = self.parse_add_sub()?;
                Ok(Formula::Eq(Box::new(lhs), Box::new(rhs)))
            }
            Some(Token::Ne) => {
                self.bump()?;
                let rhs = self.parse_add_sub()?;
                let eq = Formula::Eq(Box::new(lhs), Box::new(rhs));
                Ok(Formula::Not(Box::new(eq)))
            }
            _ => Ok(lhs),
        }
    }

    fn parse_add_sub(&mut self) -> Result<Formula, SpecParseError> {
        let mut expr = self.parse_mul_div()?;

        loop {
            if self.eat(&Token::Plus) {
                let rhs = self.parse_mul_div()?;
                expr = Formula::Add(Box::new(expr), Box::new(rhs));
            } else if self.eat(&Token::Minus) {
                let rhs = self.parse_mul_div()?;
                expr = Formula::Sub(Box::new(expr), Box::new(rhs));
            } else {
                return Ok(expr);
            }
        }
    }

    fn parse_mul_div(&mut self) -> Result<Formula, SpecParseError> {
        let mut expr = self.parse_unary()?;

        loop {
            if self.eat(&Token::Star) {
                let rhs = self.parse_unary()?;
                expr = Formula::Mul(Box::new(expr), Box::new(rhs));
            } else if self.eat(&Token::Slash) {
                let rhs = self.parse_unary()?;
                expr = Formula::Div(Box::new(expr), Box::new(rhs));
            } else if self.eat(&Token::Percent) {
                let rhs = self.parse_unary()?;
                expr = Formula::Rem(Box::new(expr), Box::new(rhs));
            } else {
                return Ok(expr);
            }
        }
    }

    fn parse_unary(&mut self) -> Result<Formula, SpecParseError> {
        if self.eat(&Token::Bang) {
            let expr = self.parse_unary()?;
            Ok(Formula::Not(Box::new(expr)))
        } else if self.eat(&Token::Minus) {
            let expr = self.parse_unary()?;
            Ok(Formula::Neg(Box::new(expr)))
        } else {
            self.parse_postfix()
        }
    }

    fn parse_postfix(&mut self) -> Result<Formula, SpecParseError> {
        let mut expr = self.parse_atom()?;

        // Handle dot-access: arr.len(), s.is_empty()
        while self.eat(&Token::Dot) {
            let method = match self.bump()? {
                Token::Ident(name) => name,
                _ => {
                    return Err(SpecParseError::UnexpectedToken {
                        position: self.index.saturating_sub(1),
                        expected: "method name after '.'".into(),
                    });
                }
            };

            // Check for () call syntax
            if self.eat(&Token::LParen) {
                self.expect(&Token::RParen, "')' after method call")?;
            }

            // Map known methods to formula operations
            expr = map_method_call(expr, &method)?;
        }

        Ok(expr)
    }

    fn parse_atom(&mut self) -> Result<Formula, SpecParseError> {
        match self.bump()? {
            Token::Ident(name) => self.parse_ident(name),
            Token::Int(value) => Ok(Formula::Int(value)),
            Token::LParen => {
                let expr = self.parse_implies()?;
                self.expect(&Token::RParen, "closing ')'")?;
                Ok(expr)
            }
            _ => Err(SpecParseError::UnexpectedToken {
                position: self.index.saturating_sub(1),
                expected: "identifier, integer, or '('".into(),
            }),
        }
    }

    fn parse_ident(&mut self, name: String) -> Result<Formula, SpecParseError> {
        match name.as_str() {
            "true" => Ok(Formula::Bool(true)),
            "false" => Ok(Formula::Bool(false)),
            "old" if self.eat(&Token::LParen) => {
                let inner = match self.bump()? {
                    Token::Ident(inner) => inner,
                    _ => {
                        return Err(SpecParseError::UnexpectedToken {
                            position: self.index.saturating_sub(1),
                            expected: "variable name inside old()".into(),
                        });
                    }
                };
                self.expect(&Token::RParen, "closing ')' for old()")?;
                Ok(int_var(format!("old_{}", map_var_name(&inner))))
            }
            "forall" if self.peek() == Some(&Token::LParen) => self.parse_quantifier(true),
            "exists" if self.peek() == Some(&Token::LParen) => self.parse_quantifier(false),
            _ => Ok(int_var(map_var_name(&name))),
        }
    }

    /// Parse `forall(var, lo..hi, body)` or `exists(var, lo..hi, body)`.
    ///
    /// Desugars into:
    /// - `forall(i, lo..hi, P(i))` => `Forall([(i, Int)], Implies(lo <= i && i < hi, P(i)))`
    /// - `exists(i, lo..hi, P(i))` => `Exists([(i, Int)], And(lo <= i, i < hi, P(i)))`
    fn parse_quantifier(&mut self, is_forall: bool) -> Result<Formula, SpecParseError> {
        let label = if is_forall { "forall" } else { "exists" };

        self.expect(&Token::LParen, &format!("'(' after {label}"))?;

        // Parse bound variable name
        let var_name = match self.bump()? {
            Token::Ident(name) => name,
            _ => {
                return Err(SpecParseError::InvalidQuantifier {
                    detail: format!("{label}: expected variable name"),
                });
            }
        };

        self.expect(&Token::Comma, &format!("',' after variable in {label}"))?;

        // Parse range: lo..hi
        let lo = self.parse_add_sub()?;
        if !self.eat(&Token::DotDot) {
            return Err(SpecParseError::InvalidQuantifier {
                detail: format!("{label}: expected '..' in range"),
            });
        }
        let hi = self.parse_add_sub()?;

        self.expect(&Token::Comma, &format!("',' after range in {label}"))?;

        // Parse body expression
        let body = self.parse_implies()?;

        self.expect(&Token::RParen, &format!("closing ')' for {label}"))?;

        let bound_var = Formula::Var(var_name.clone(), Sort::Int);
        let bindings = vec![(var_name, Sort::Int)];

        // Build range guard: lo <= var && var < hi
        let range_guard = Formula::And(vec![
            Formula::Le(Box::new(lo), Box::new(bound_var.clone())),
            Formula::Lt(Box::new(bound_var), Box::new(hi)),
        ]);

        if is_forall {
            // forall: range_guard => body
            Ok(Formula::Forall(
                bindings,
                Box::new(Formula::Implies(Box::new(range_guard), Box::new(body))),
            ))
        } else {
            // exists: range_guard && body
            Ok(Formula::Exists(bindings, Box::new(Formula::And(vec![range_guard, body]))))
        }
    }
}

/// Map a method call on a formula to the appropriate representation.
///
/// Known methods:
/// - `.len()` => `Var("<base>_len", Int)` (models collection length)
/// - `.is_empty()` => `Eq(<base>_len, 0)` (models emptiness check)
fn map_method_call(base: Formula, method: &str) -> Result<Formula, SpecParseError> {
    let base_name = match &base {
        Formula::Var(name, _) => name.clone(),
        _ => return Err(SpecParseError::UnsupportedMethod { method: method.into() }),
    };

    match method {
        "len" => Ok(int_var(format!("{base_name}_len"))),
        "is_empty" => Ok(Formula::Eq(
            Box::new(int_var(format!("{base_name}_len"))),
            Box::new(Formula::Int(0)),
        )),
        _ => Err(SpecParseError::UnsupportedMethod { method: method.into() }),
    }
}

fn int_var(name: String) -> Formula {
    Formula::Var(name, Sort::Int)
}

fn map_var_name(name: &str) -> String {
    if name == "result" { "_0".to_string() } else { name.to_string() }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spec::SpecParseError;

    fn var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    fn int(value: i128) -> Formula {
        Formula::Int(value)
    }

    // === Backward-compatible tests (Option API) ===

    #[test]
    fn parses_simple_comparison() {
        let expected = Formula::Gt(Box::new(var("x")), Box::new(int(0)));
        assert_eq!(parse_spec_expr("x > 0"), Some(expected));
    }

    #[test]
    fn parses_result_mapping_and_arithmetic() {
        let expected = Formula::Ge(
            Box::new(var("_0")),
            Box::new(Formula::Add(Box::new(var("a")), Box::new(var("b")))),
        );

        assert_eq!(parse_spec_expr("result >= a + b"), Some(expected));
    }

    #[test]
    fn parses_not_equal_as_negated_equality() {
        let expected = Formula::Not(Box::new(Formula::Eq(Box::new(var("n")), Box::new(int(0)))));

        assert_eq!(parse_spec_expr("n != 0"), Some(expected));
    }

    #[test]
    fn parses_old_syntax() {
        let expected = Formula::Le(Box::new(var("old_x")), Box::new(var("_0")));
        assert_eq!(parse_spec_expr("old(x) <= result"), Some(expected));
    }

    #[test]
    fn old_is_only_special_when_called() {
        let expected = Formula::Add(Box::new(var("old")), Box::new(int(1)));
        assert_eq!(parse_spec_expr("old + 1"), Some(expected));
    }

    #[test]
    fn parses_boolean_literals_and_logical_precedence() {
        let expected = Formula::Or(vec![
            Formula::Gt(Box::new(var("a")), Box::new(int(0))),
            Formula::And(vec![
                Formula::Gt(Box::new(var("b")), Box::new(int(0))),
                Formula::Gt(Box::new(var("c")), Box::new(int(0))),
            ]),
        ]);

        assert_eq!(parse_spec_expr("a > 0 || b > 0 && c > 0"), Some(expected));
    }

    #[test]
    fn parses_parentheses_before_logical_ops() {
        let expected = Formula::And(vec![
            Formula::Or(vec![
                Formula::Gt(Box::new(var("a")), Box::new(int(0))),
                Formula::Gt(Box::new(var("b")), Box::new(int(0))),
            ]),
            Formula::Gt(Box::new(var("c")), Box::new(int(0))),
        ]);

        assert_eq!(parse_spec_expr("(a > 0 || b > 0) && c > 0"), Some(expected));
    }

    #[test]
    fn parses_implication_at_lowest_precedence() {
        let expected = Formula::Implies(
            Box::new(Formula::Gt(Box::new(var("x")), Box::new(int(0)))),
            Box::new(Formula::Or(vec![
                Formula::Gt(Box::new(var("_0")), Box::new(var("x"))),
                Formula::Eq(Box::new(var("_0")), Box::new(var("x"))),
            ])),
        );

        assert_eq!(parse_spec_expr("x > 0 => result > x || result == x"), Some(expected));
    }

    #[test]
    fn parses_unary_not() {
        let expected = Formula::Not(Box::new(Formula::Eq(Box::new(var("x")), Box::new(int(0)))));

        assert_eq!(parse_spec_expr("!(x == 0)"), Some(expected));
    }

    #[test]
    fn parses_arithmetic_precedence_and_associativity() {
        let expected = Formula::Sub(
            Box::new(Formula::Add(
                Box::new(var("a")),
                Box::new(Formula::Mul(Box::new(var("b")), Box::new(var("c")))),
            )),
            Box::new(Formula::Div(Box::new(var("d")), Box::new(var("e")))),
        );

        assert_eq!(parse_spec_expr("a + b * c - d / e"), Some(expected));
    }

    #[test]
    fn parses_unary_minus() {
        let expected = Formula::Add(Box::new(Formula::Neg(Box::new(var("x")))), Box::new(int(1)));

        assert_eq!(parse_spec_expr("-x + 1"), Some(expected));
    }

    #[test]
    fn parses_boolean_literals() {
        assert_eq!(parse_spec_expr("true"), Some(Formula::Bool(true)));
        assert_eq!(parse_spec_expr("false"), Some(Formula::Bool(false)));
    }

    #[test]
    fn rejects_invalid_inputs() {
        for input in ["", "x >", "old(x", "old(x + 1)", "a < b < c", "()", "x @ 1"] {
            assert_eq!(parse_spec_expr(input), None, "input should fail: {input}");
        }
    }

    // === Result API tests ===

    #[test]
    fn test_result_api_empty_input() {
        let err = parse_spec_expr_result("").unwrap_err();
        assert!(matches!(err, SpecParseError::Empty));

        let err = parse_spec_expr_result("   ").unwrap_err();
        assert!(matches!(err, SpecParseError::Empty));
    }

    #[test]
    fn test_result_api_unexpected_char() {
        let err = parse_spec_expr_result("x @ 1").unwrap_err();
        match err {
            SpecParseError::UnexpectedChar { ch, position } => {
                assert_eq!(ch, '@');
                assert_eq!(position, 2);
            }
            other => panic!("expected UnexpectedChar, got {other:?}"),
        }
    }

    #[test]
    fn test_result_api_trailing_tokens() {
        let err = parse_spec_expr_result("a < b < c").unwrap_err();
        assert!(matches!(err, SpecParseError::TrailingTokens));
    }

    #[test]
    fn test_result_api_success() {
        let formula = parse_spec_expr_result("x > 0").expect("should parse");
        assert!(matches!(formula, Formula::Gt(..)));
    }

    // === Quantifier tests ===

    #[test]
    fn test_forall_basic() {
        let formula = parse_spec_expr_result("forall(i, 0..n, i >= 0)").expect("should parse");
        match formula {
            Formula::Forall(bindings, body) => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].0, "i");
                // body should be Implies(range_guard, i >= 0)
                assert!(matches!(*body, Formula::Implies(..)));
            }
            other => panic!("expected Forall, got {other:?}"),
        }
    }

    #[test]
    fn test_exists_basic() {
        let formula = parse_spec_expr_result("exists(j, 0..n, j == k)").expect("should parse");
        match formula {
            Formula::Exists(bindings, body) => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].0, "j");
                // body should be And([range_guard, j == k])
                assert!(matches!(*body, Formula::And(..)));
            }
            other => panic!("expected Exists, got {other:?}"),
        }
    }

    #[test]
    fn test_forall_with_complex_body() {
        let formula =
            parse_spec_expr_result("forall(i, 0..n, arr > 0 && arr < 100)").expect("should parse");
        assert!(matches!(formula, Formula::Forall(..)));
    }

    #[test]
    fn test_quantifier_missing_comma() {
        let err = parse_spec_expr_result("forall(i 0..n, true)").unwrap_err();
        assert!(matches!(err, SpecParseError::UnexpectedToken { .. }), "got {err:?}");
    }

    #[test]
    fn test_quantifier_missing_range() {
        let err = parse_spec_expr_result("forall(i, 0, true)").unwrap_err();
        assert!(matches!(err, SpecParseError::InvalidQuantifier { .. }), "got {err:?}");
    }

    #[test]
    fn test_forall_not_called_is_variable() {
        // "forall" without parens should be treated as a variable name
        let formula = parse_spec_expr_result("forall + 1").expect("should parse");
        assert!(matches!(formula, Formula::Add(..)));
    }

    // === Dot-access tests ===

    #[test]
    fn test_dot_len() {
        let formula = parse_spec_expr_result("arr.len() > 0").expect("should parse");
        match formula {
            Formula::Gt(lhs, rhs) => {
                assert_eq!(*lhs, var("arr_len"));
                assert_eq!(*rhs, int(0));
            }
            other => panic!("expected Gt, got {other:?}"),
        }
    }

    #[test]
    fn test_dot_is_empty() {
        let formula = parse_spec_expr_result("s.is_empty()").expect("should parse");
        match formula {
            Formula::Eq(lhs, rhs) => {
                assert_eq!(*lhs, var("s_len"));
                assert_eq!(*rhs, int(0));
            }
            other => panic!("expected Eq, got {other:?}"),
        }
    }

    #[test]
    fn test_dot_len_in_comparison() {
        let formula = parse_spec_expr_result("arr.len() > i").expect("should parse");
        assert!(matches!(formula, Formula::Gt(..)));
    }

    #[test]
    fn test_unsupported_method() {
        let err = parse_spec_expr_result("x.foo()").unwrap_err();
        assert!(matches!(err, SpecParseError::UnsupportedMethod { .. }));
    }

    // === Complex expression tests ===

    #[test]
    fn test_nested_quantifier_in_conjunction() {
        let formula =
            parse_spec_expr_result("n > 0 && forall(i, 0..n, i >= 0)").expect("should parse");
        assert!(matches!(formula, Formula::And(..)));
    }

    #[test]
    fn test_result_equals_sum() {
        let formula = parse_spec_expr_result("result == a + b").expect("should parse");
        match formula {
            Formula::Eq(lhs, rhs) => {
                assert_eq!(*lhs, var("_0"));
                assert!(matches!(*rhs, Formula::Add(..)));
            }
            other => panic!("expected Eq, got {other:?}"),
        }
    }

    #[test]
    fn test_complex_spec_with_implication_and_quantifier() {
        let formula =
            parse_spec_expr_result("n > 0 => forall(i, 0..n, i >= 0)").expect("should parse");
        assert!(matches!(formula, Formula::Implies(..)));
    }

    #[test]
    fn test_error_display_messages() {
        let cases = vec![
            (SpecParseError::Empty, "empty spec expression"),
            (
                SpecParseError::UnexpectedChar { ch: '#', position: 3 },
                "unexpected character '#' at position 3",
            ),
            (SpecParseError::TrailingTokens, "trailing tokens after expression"),
            (
                SpecParseError::InvalidQuantifier { detail: "bad range".into() },
                "invalid quantifier syntax: bad range",
            ),
            (
                SpecParseError::UnsupportedMethod { method: "foo".into() },
                "unsupported method call: foo",
            ),
        ];

        for (err, expected_msg) in cases {
            assert_eq!(err.to_string(), expected_msg);
        }
    }
}
