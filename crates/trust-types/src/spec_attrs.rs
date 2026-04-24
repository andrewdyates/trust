// trust-types/spec_attrs.rs: High-level specification attribute AST and parser
//
// Represents specification expressions before lowering to SMT-level Formula,
// enabling spec-level transformations such as inlining and strengthening.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::spec::SpecParseError;
use crate::spec_parse::{Token, tokenize};
use crate::{Formula, Sort};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SpecExpr {
    BoolLit(bool),
    IntLit(i128),
    Var(String),
    BinOp { lhs: Box<SpecExpr>, op: SpecBinOp, rhs: Box<SpecExpr> },
    UnaryOp { op: SpecUnaryOp, expr: Box<SpecExpr> },
    FnCall { name: String, args: Vec<SpecExpr> },
    Forall { var: String, ty: String, body: Box<SpecExpr> },
    Exists { var: String, ty: String, body: Box<SpecExpr> },
    Old(Box<SpecExpr>),
    Result,
    Field { base: Box<SpecExpr>, field: String },
    Index { base: Box<SpecExpr>, index: Box<SpecExpr> },
    Implies { lhs: Box<SpecExpr>, rhs: Box<SpecExpr> },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SpecBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SpecUnaryOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum HighLevelSpecAttr {
    Requires(SpecExpr),
    Ensures(SpecExpr),
    Invariant(SpecExpr),
    Decreases(SpecExpr),
    Pure,
    Trusted,
}

pub fn parse_spec_attr(
    attr_name: &str,
    content: &str,
) -> Result<HighLevelSpecAttr, SpecParseError> {
    match attr_name {
        "pure" => Ok(HighLevelSpecAttr::Pure),
        "trusted" => Ok(HighLevelSpecAttr::Trusted),
        "requires" => parse_spec_expr(content).map(HighLevelSpecAttr::Requires),
        "ensures" => parse_spec_expr(content).map(HighLevelSpecAttr::Ensures),
        "invariant" => parse_spec_expr(content).map(HighLevelSpecAttr::Invariant),
        "decreases" => parse_spec_expr(content).map(HighLevelSpecAttr::Decreases),
        _ => Err(SpecParseError::UnexpectedToken {
            position: 0,
            expected: "known spec attribute name".into(),
        }),
    }
}

pub fn spec_expr_to_formula(expr: &SpecExpr) -> Formula {
    match expr {
        SpecExpr::BoolLit(value) => Formula::Bool(*value),
        SpecExpr::IntLit(value) => Formula::Int(*value),
        SpecExpr::Var(name) => Formula::Var(name.clone(), Sort::Int),
        SpecExpr::BinOp { lhs, op, rhs } => {
            let lhs = Box::new(spec_expr_to_formula(lhs));
            let rhs = Box::new(spec_expr_to_formula(rhs));

            match op {
                SpecBinOp::Add => Formula::Add(lhs, rhs),
                SpecBinOp::Sub => Formula::Sub(lhs, rhs),
                SpecBinOp::Mul => Formula::Mul(lhs, rhs),
                SpecBinOp::Div => Formula::Div(lhs, rhs),
                SpecBinOp::Mod => Formula::Rem(lhs, rhs),
                SpecBinOp::Eq => Formula::Eq(lhs, rhs),
                SpecBinOp::Ne => Formula::Not(Box::new(Formula::Eq(lhs, rhs))),
                SpecBinOp::Lt => Formula::Lt(lhs, rhs),
                SpecBinOp::Le => Formula::Le(lhs, rhs),
                SpecBinOp::Gt => Formula::Gt(lhs, rhs),
                SpecBinOp::Ge => Formula::Ge(lhs, rhs),
                SpecBinOp::And => Formula::And(vec![*lhs, *rhs]),
                SpecBinOp::Or => Formula::Or(vec![*lhs, *rhs]),
            }
        }
        SpecExpr::UnaryOp { op, expr } => {
            let expr = Box::new(spec_expr_to_formula(expr));
            match op {
                SpecUnaryOp::Not => Formula::Not(expr),
                SpecUnaryOp::Neg => Formula::Neg(expr),
            }
        }
        SpecExpr::FnCall { name, .. } => Formula::Var(name.clone(), Sort::Int),
        SpecExpr::Forall { var, ty: _, body } => Formula::Forall(
            vec![(crate::Symbol::intern(var), Sort::Int)],
            Box::new(spec_expr_to_formula(body)),
        ),
        SpecExpr::Exists { var, ty: _, body } => Formula::Exists(
            vec![(crate::Symbol::intern(var), Sort::Int)],
            Box::new(spec_expr_to_formula(body)),
        ),
        SpecExpr::Old(inner) => match inner.as_ref() {
            SpecExpr::Var(name) => Formula::Var(format!("old_{name}"), Sort::Int),
            _ => spec_expr_to_formula(inner),
        },
        SpecExpr::Result => Formula::Var("_0".to_string(), Sort::Int),
        SpecExpr::Field { base, field } => match base.as_ref() {
            SpecExpr::Var(name) => Formula::Var(format!("{name}_{field}"), Sort::Int),
            _ => spec_expr_to_formula(base),
        },
        SpecExpr::Index { base, index } => Formula::Select(
            Box::new(spec_expr_to_formula(base)),
            Box::new(spec_expr_to_formula(index)),
        ),
        SpecExpr::Implies { lhs, rhs } => Formula::Implies(
            Box::new(spec_expr_to_formula(lhs)),
            Box::new(spec_expr_to_formula(rhs)),
        ),
    }
}

fn parse_spec_expr(input: &str) -> Result<SpecExpr, SpecParseError> {
    if input.trim().is_empty() {
        return Err(SpecParseError::Empty);
    }

    let tokens = tokenize(input)?;
    let mut parser = SpecExprParser::new(tokens);
    let expr = parser.parse_implies()?;

    if parser.is_eof() { Ok(expr) } else { Err(SpecParseError::TrailingTokens) }
}

struct SpecExprParser {
    tokens: Vec<Token>,
    index: usize,
}

impl SpecExprParser {
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
            .inspect(|_| {
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

    fn parse_implies(&mut self) -> Result<SpecExpr, SpecParseError> {
        let lhs = self.parse_or()?;

        if self.eat(&Token::Implies) {
            let rhs = self.parse_implies()?;
            Ok(SpecExpr::Implies { lhs: Box::new(lhs), rhs: Box::new(rhs) })
        } else {
            Ok(lhs)
        }
    }

    fn parse_or(&mut self) -> Result<SpecExpr, SpecParseError> {
        self.parse_left_assoc(Self::parse_and, &[(Token::OrOr, SpecBinOp::Or)])
    }

    fn parse_and(&mut self) -> Result<SpecExpr, SpecParseError> {
        self.parse_left_assoc(Self::parse_comparison, &[(Token::AndAnd, SpecBinOp::And)])
    }

    fn parse_comparison(&mut self) -> Result<SpecExpr, SpecParseError> {
        let lhs = self.parse_add_sub()?;

        let Some(op) = self.peek().and_then(token_to_comparison_op) else {
            return Ok(lhs);
        };

        self.bump()?;
        let rhs = self.parse_add_sub()?;
        Ok(SpecExpr::BinOp { lhs: Box::new(lhs), op, rhs: Box::new(rhs) })
    }

    fn parse_add_sub(&mut self) -> Result<SpecExpr, SpecParseError> {
        self.parse_left_assoc(
            Self::parse_mul_div,
            &[(Token::Plus, SpecBinOp::Add), (Token::Minus, SpecBinOp::Sub)],
        )
    }

    fn parse_mul_div(&mut self) -> Result<SpecExpr, SpecParseError> {
        self.parse_left_assoc(
            Self::parse_unary,
            &[
                (Token::Star, SpecBinOp::Mul),
                (Token::Slash, SpecBinOp::Div),
                (Token::Percent, SpecBinOp::Mod),
            ],
        )
    }

    fn parse_unary(&mut self) -> Result<SpecExpr, SpecParseError> {
        if self.eat(&Token::Bang) {
            let expr = self.parse_unary()?;
            Ok(SpecExpr::UnaryOp { op: SpecUnaryOp::Not, expr: Box::new(expr) })
        } else if self.eat(&Token::Minus) {
            let expr = self.parse_unary()?;
            Ok(SpecExpr::UnaryOp { op: SpecUnaryOp::Neg, expr: Box::new(expr) })
        } else {
            self.parse_postfix()
        }
    }

    fn parse_postfix(&mut self) -> Result<SpecExpr, SpecParseError> {
        let mut expr = self.parse_atom()?;

        loop {
            if self.eat(&Token::Dot) {
                let field = match self.bump()? {
                    Token::Ident(name) => name,
                    _ => {
                        return Err(SpecParseError::UnexpectedToken {
                            position: self.index.saturating_sub(1),
                            expected: "field name after '.'".into(),
                        });
                    }
                };

                if self.eat(&Token::LParen) {
                    self.expect(&Token::RParen, "')' after field access")?;
                }

                expr = SpecExpr::Field { base: Box::new(expr), field };
                continue;
            }

            if self.eat(&Token::LBracket) {
                let index = self.parse_implies()?;
                self.expect(&Token::RBracket, "closing ']'")?;
                expr = SpecExpr::Index { base: Box::new(expr), index: Box::new(index) };
                continue;
            }

            return Ok(expr);
        }
    }

    fn parse_atom(&mut self) -> Result<SpecExpr, SpecParseError> {
        match self.bump()? {
            Token::Ident(name) => self.parse_ident(name),
            Token::Int(value) => Ok(SpecExpr::IntLit(value)),
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

    fn parse_ident(&mut self, name: String) -> Result<SpecExpr, SpecParseError> {
        match name.as_str() {
            "true" => Ok(SpecExpr::BoolLit(true)),
            "false" => Ok(SpecExpr::BoolLit(false)),
            "result" => Ok(SpecExpr::Result),
            "old" if self.peek() == Some(&Token::LParen) => {
                self.expect(&Token::LParen, "'(' after old")?;
                let expr = self.parse_implies()?;
                self.expect(&Token::RParen, "closing ')' for old()")?;
                Ok(SpecExpr::Old(Box::new(expr)))
            }
            "forall" if self.peek() == Some(&Token::LParen) => self.parse_quantifier(true),
            "exists" if self.peek() == Some(&Token::LParen) => self.parse_quantifier(false),
            _ if self.peek() == Some(&Token::LParen) => self.parse_fn_call(name),
            _ => Ok(SpecExpr::Var(name)),
        }
    }

    fn parse_fn_call(&mut self, name: String) -> Result<SpecExpr, SpecParseError> {
        self.expect(&Token::LParen, &format!("'(' after function name '{name}'"))?;
        let mut args = Vec::new();

        if !self.eat(&Token::RParen) {
            loop {
                args.push(self.parse_implies()?);
                if self.eat(&Token::Comma) {
                    continue;
                }

                self.expect(&Token::RParen, "closing ')' after function call")?;
                break;
            }
        }

        Ok(SpecExpr::FnCall { name, args })
    }

    fn parse_quantifier(&mut self, is_forall: bool) -> Result<SpecExpr, SpecParseError> {
        let label = if is_forall { "forall" } else { "exists" };
        self.expect(&Token::LParen, &format!("'(' after {label}"))?;

        let var = match self.bump()? {
            Token::Ident(name) => name,
            _ => {
                return Err(SpecParseError::InvalidQuantifier {
                    detail: format!("{label}: expected variable name"),
                });
            }
        };

        if !self.eat(&Token::Colon) {
            return Err(SpecParseError::InvalidQuantifier {
                detail: format!("{label}: expected ':' after variable"),
            });
        }

        let ty = match self.bump()? {
            Token::Ident(name) => name,
            _ => {
                return Err(SpecParseError::InvalidQuantifier {
                    detail: format!("{label}: expected type name"),
                });
            }
        };

        self.expect(&Token::Comma, &format!("',' after type in {label}"))?;
        let body = self.parse_implies()?;
        self.expect(&Token::RParen, &format!("closing ')' for {label}"))?;

        if is_forall {
            Ok(SpecExpr::Forall { var, ty, body: Box::new(body) })
        } else {
            Ok(SpecExpr::Exists { var, ty, body: Box::new(body) })
        }
    }

    fn parse_left_assoc(
        &mut self,
        parser: fn(&mut Self) -> Result<SpecExpr, SpecParseError>,
        ops: &[(Token, SpecBinOp)],
    ) -> Result<SpecExpr, SpecParseError> {
        let mut expr = parser(self)?;

        loop {
            let Some(op) =
                ops.iter().find_map(|(token, op)| (self.peek() == Some(token)).then_some(*op))
            else {
                return Ok(expr);
            };

            self.bump()?;
            let rhs = parser(self)?;
            expr = SpecExpr::BinOp { lhs: Box::new(expr), op, rhs: Box::new(rhs) };
        }
    }
}

fn token_to_comparison_op(token: &Token) -> Option<SpecBinOp> {
    match token {
        Token::EqEq => Some(SpecBinOp::Eq),
        Token::Ne => Some(SpecBinOp::Ne),
        Token::Lt => Some(SpecBinOp::Lt),
        Token::Le => Some(SpecBinOp::Le),
        Token::Gt => Some(SpecBinOp::Gt),
        Token::Ge => Some(SpecBinOp::Ge),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str) -> SpecExpr {
        SpecExpr::Var(name.to_string())
    }

    fn int(value: i128) -> SpecExpr {
        SpecExpr::IntLit(value)
    }

    #[test]
    fn spec_attrs_parses_simple_requires() {
        let attr = parse_spec_attr("requires", "x > 0").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Requires(SpecExpr::BinOp {
                lhs: Box::new(var("x")),
                op: SpecBinOp::Gt,
                rhs: Box::new(int(0)),
            })
        );
    }

    #[test]
    fn spec_attrs_parses_ensures_with_result() {
        let attr = parse_spec_attr("ensures", "result >= x").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Ensures(SpecExpr::BinOp {
                lhs: Box::new(SpecExpr::Result),
                op: SpecBinOp::Ge,
                rhs: Box::new(var("x")),
            })
        );
    }

    #[test]
    fn spec_attrs_parses_compound_and() {
        let attr = parse_spec_attr("requires", "x > 0 && y > 0").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Requires(SpecExpr::BinOp {
                lhs: Box::new(SpecExpr::BinOp {
                    lhs: Box::new(var("x")),
                    op: SpecBinOp::Gt,
                    rhs: Box::new(int(0)),
                }),
                op: SpecBinOp::And,
                rhs: Box::new(SpecExpr::BinOp {
                    lhs: Box::new(var("y")),
                    op: SpecBinOp::Gt,
                    rhs: Box::new(int(0)),
                }),
            })
        );
    }

    #[test]
    fn spec_attrs_parses_forall() {
        let attr = parse_spec_attr("requires", "forall(i: int, i >= 0)").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Requires(SpecExpr::Forall {
                var: "i".to_string(),
                ty: "int".to_string(),
                body: Box::new(SpecExpr::BinOp {
                    lhs: Box::new(var("i")),
                    op: SpecBinOp::Ge,
                    rhs: Box::new(int(0)),
                }),
            })
        );
    }

    #[test]
    fn spec_attrs_parses_old() {
        let attr = parse_spec_attr("ensures", "old(x) <= result").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Ensures(SpecExpr::BinOp {
                lhs: Box::new(SpecExpr::Old(Box::new(var("x")))),
                op: SpecBinOp::Le,
                rhs: Box::new(SpecExpr::Result),
            })
        );
    }

    #[test]
    fn spec_attrs_parses_nested_arithmetic() {
        let attr = parse_spec_attr("requires", "a + b * c - d").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Requires(SpecExpr::BinOp {
                lhs: Box::new(SpecExpr::BinOp {
                    lhs: Box::new(var("a")),
                    op: SpecBinOp::Add,
                    rhs: Box::new(SpecExpr::BinOp {
                        lhs: Box::new(var("b")),
                        op: SpecBinOp::Mul,
                        rhs: Box::new(var("c")),
                    }),
                }),
                op: SpecBinOp::Sub,
                rhs: Box::new(var("d")),
            })
        );
    }

    #[test]
    fn spec_attrs_parses_implies() {
        let attr = parse_spec_attr("ensures", "x > 0 => result > x").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Ensures(SpecExpr::Implies {
                lhs: Box::new(SpecExpr::BinOp {
                    lhs: Box::new(var("x")),
                    op: SpecBinOp::Gt,
                    rhs: Box::new(int(0)),
                }),
                rhs: Box::new(SpecExpr::BinOp {
                    lhs: Box::new(SpecExpr::Result),
                    op: SpecBinOp::Gt,
                    rhs: Box::new(var("x")),
                }),
            })
        );
    }

    #[test]
    fn spec_attrs_parses_not() {
        let attr = parse_spec_attr("requires", "!(x == 0)").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Requires(SpecExpr::UnaryOp {
                op: SpecUnaryOp::Not,
                expr: Box::new(SpecExpr::BinOp {
                    lhs: Box::new(var("x")),
                    op: SpecBinOp::Eq,
                    rhs: Box::new(int(0)),
                }),
            })
        );
    }

    #[test]
    fn spec_attrs_parses_pure() {
        let attr = parse_spec_attr("pure", "").expect("should parse");
        assert_eq!(attr, HighLevelSpecAttr::Pure);
    }

    #[test]
    fn spec_attrs_parses_trusted() {
        let attr = parse_spec_attr("trusted", "ignored").expect("should parse");
        assert_eq!(attr, HighLevelSpecAttr::Trusted);
    }

    #[test]
    fn spec_attrs_rejects_unknown_attr() {
        let err = parse_spec_attr("unknown", "x > 0").unwrap_err();
        assert_eq!(
            err,
            SpecParseError::UnexpectedToken {
                position: 0,
                expected: "known spec attribute name".into(),
            }
        );
    }

    #[test]
    fn spec_attrs_rejects_empty_content() {
        let err = parse_spec_attr("requires", "").unwrap_err();
        assert_eq!(err, SpecParseError::Empty);
    }

    #[test]
    fn spec_attrs_rejects_invalid_syntax() {
        let err = parse_spec_attr("requires", "x &&").unwrap_err();
        assert!(matches!(err, SpecParseError::UnexpectedEof { .. }));
    }

    #[test]
    fn spec_attrs_to_formula_basic() {
        let formula = spec_expr_to_formula(&SpecExpr::BoolLit(true));
        assert_eq!(formula, Formula::Bool(true));
    }

    #[test]
    fn spec_attrs_to_formula_comparison() {
        let expr =
            SpecExpr::BinOp { lhs: Box::new(var("x")), op: SpecBinOp::Lt, rhs: Box::new(int(1)) };
        let formula = spec_expr_to_formula(&expr);
        assert_eq!(
            formula,
            Formula::Lt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(1)),
            )
        );
    }

    #[test]
    fn spec_attrs_to_formula_result() {
        let formula = spec_expr_to_formula(&SpecExpr::Result);
        assert_eq!(formula, Formula::Var("_0".to_string(), Sort::Int));
    }

    #[test]
    fn spec_attrs_to_formula_old() {
        let formula = spec_expr_to_formula(&SpecExpr::Old(Box::new(var("x"))));
        assert_eq!(formula, Formula::Var("old_x".to_string(), Sort::Int));
    }

    #[test]
    fn spec_attrs_to_formula_index() {
        let expr = SpecExpr::Index { base: Box::new(var("arr")), index: Box::new(var("i")) };
        let formula = spec_expr_to_formula(&expr);
        assert_eq!(
            formula,
            Formula::Select(
                Box::new(Formula::Var("arr".to_string(), Sort::Int)),
                Box::new(Formula::Var("i".to_string(), Sort::Int)),
            )
        );
    }

    #[test]
    fn spec_attrs_to_formula_field() {
        let expr = SpecExpr::Field { base: Box::new(var("point")), field: "x".to_string() };
        let formula = spec_expr_to_formula(&expr);
        assert_eq!(formula, Formula::Var("point_x".to_string(), Sort::Int));
    }

    #[test]
    fn spec_attrs_to_formula_forall() {
        let expr = SpecExpr::Forall {
            var: "i".to_string(),
            ty: "int".to_string(),
            body: Box::new(SpecExpr::BinOp {
                lhs: Box::new(var("i")),
                op: SpecBinOp::Ge,
                rhs: Box::new(int(0)),
            }),
        };
        let formula = spec_expr_to_formula(&expr);
        assert_eq!(
            formula,
            Formula::Forall(
                vec![("i".into(), Sort::Int)],
                Box::new(Formula::Ge(
                    Box::new(Formula::Var("i".to_string(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                )),
            )
        );
    }

    #[test]
    fn spec_attrs_parses_field_and_index() {
        let attr = parse_spec_attr("requires", "arr[i].len").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Requires(SpecExpr::Field {
                base: Box::new(SpecExpr::Index {
                    base: Box::new(var("arr")),
                    index: Box::new(var("i")),
                }),
                field: "len".to_string(),
            })
        );
    }

    #[test]
    fn spec_attrs_parses_function_call() {
        let attr = parse_spec_attr("requires", "pred(x, y + 1)").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Requires(SpecExpr::FnCall {
                name: "pred".to_string(),
                args: vec![
                    var("x"),
                    SpecExpr::BinOp {
                        lhs: Box::new(var("y")),
                        op: SpecBinOp::Add,
                        rhs: Box::new(int(1)),
                    },
                ],
            })
        );
    }
}
