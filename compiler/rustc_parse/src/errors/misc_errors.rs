// tRust: split from errors.rs

use std::borrow::Cow;
use std::path::PathBuf;

use rustc_ast::token::{self, InvisibleOrigin, MetaVarKind, Token};
use rustc_ast::util::parser::ExprPrecedence;
use rustc_ast::{Path, Visibility};
use rustc_errors::codes::*;
use rustc_errors::{
    Applicability, Diag, DiagArgValue, DiagCtxtHandle, Diagnostic, EmissionGuarantee, IntoDiagArg,
    Level, Subdiagnostic, SuggestionStyle, msg,
};
use rustc_macros::{Diagnostic, Subdiagnostic};
use rustc_session::errors::ExprParenthesesNeeded;
use rustc_span::edition::{Edition, LATEST_STABLE_EDITION};
use rustc_span::{Ident, Span, Symbol};

#[derive(Diagnostic)]
#[diag(
    "expected {$is_bound ->
        [true] a pattern range bound
        *[false] a pattern
    }, found an expression"
)]
#[note(
    "arbitrary expressions are not allowed in patterns: <https://doc.rust-lang.org/book/ch19-00-patterns.html>"
)]
pub(crate) struct UnexpectedExpressionInPattern {
    /// The unexpected expr's span.
    #[primary_span]
    #[label("not a pattern")]
    pub span: Span,
    /// Was a `RangePatternBound` expected?
    pub is_bound: bool,
    /// The unexpected expr's precedence (used in match arm guard suggestions).
    pub expr_precedence: ExprPrecedence,
}

#[derive(Subdiagnostic)]
pub(crate) enum UnexpectedExpressionInPatternSugg {
    #[multipart_suggestion(
        "consider moving the expression to a match arm guard",
        applicability = "maybe-incorrect"
    )]
    CreateGuard {
        /// Where to put the suggested identifier.
        #[suggestion_part(code = "{ident}")]
        ident_span: Span,
        /// Where to put the match arm.
        #[suggestion_part(code = " if {ident} == {expr}")]
        pat_hi: Span,
        /// The suggested identifier.
        ident: String,
        /// The unexpected expression.
        expr: String,
    },

    #[multipart_suggestion(
        "consider moving the expression to the match arm guard",
        applicability = "maybe-incorrect"
    )]
    UpdateGuard {
        /// Where to put the suggested identifier.
        #[suggestion_part(code = "{ident}")]
        ident_span: Span,
        /// The beginning of the match arm guard's expression (insert a `(` if `Some`).
        #[suggestion_part(code = "(")]
        guard_lo: Option<Span>,
        /// The end of the match arm guard's expression.
        #[suggestion_part(code = "{guard_hi_paren} && {ident} == {expr}")]
        guard_hi: Span,
        /// Either `")"` or `""`.
        guard_hi_paren: &'static str,
        /// The suggested identifier.
        ident: String,
        /// The unexpected expression.
        expr: String,
    },

    #[multipart_suggestion(
        "consider extracting the expression into a `const`",
        applicability = "has-placeholders"
    )]
    Const {
        /// Where to put the extracted constant declaration.
        #[suggestion_part(code = "{indentation}const {ident}: /* Type */ = {expr};\n")]
        stmt_lo: Span,
        /// Where to put the suggested identifier.
        #[suggestion_part(code = "{ident}")]
        ident_span: Span,
        /// The suggested identifier.
        ident: String,
        /// The unexpected expression.
        expr: String,
        /// The statement's block's indentation.
        indentation: String,
    },
}

#[derive(Diagnostic)]
#[diag("range pattern bounds cannot have parentheses")]
pub(crate) struct UnexpectedParenInRangePat {
    #[primary_span]
    pub span: Vec<Span>,
    #[subdiagnostic]
    pub sugg: UnexpectedParenInRangePatSugg,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion("remove these parentheses", applicability = "machine-applicable")]
pub(crate) struct UnexpectedParenInRangePatSugg {
    #[suggestion_part(code = "")]
    pub start_span: Span,
    #[suggestion_part(code = "")]
    pub end_span: Span,
}

#[derive(Diagnostic)]
#[diag("return types are denoted using `->`")]
pub(crate) struct ReturnTypesUseThinArrow {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "use `->` instead",
        style = "verbose",
        code = " -> ",
        applicability = "machine-applicable"
    )]
    pub suggestion: Span,
}

#[derive(Diagnostic)]
#[diag("lifetimes must be followed by `+` to form a trait object type")]
pub(crate) struct NeedPlusAfterTraitObjectLifetime {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "consider adding a trait bound after the potential lifetime bound",
        code = " + /* Trait */",
        applicability = "has-placeholders"
    )]
    pub suggestion: Span,
}

#[derive(Diagnostic)]
#[diag("expected `mut` or `const` keyword in raw pointer type")]
pub(crate) struct ExpectedMutOrConstInRawPointerType {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "add `mut` or `const` here",
        code("mut ", "const "),
        applicability = "has-placeholders",
        style = "verbose"
    )]
    pub after_asterisk: Span,
}

#[derive(Diagnostic)]
#[diag("lifetime must precede `mut`")]
pub(crate) struct LifetimeAfterMut {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "place the lifetime before `mut`",
        code = "&{snippet} mut",
        applicability = "maybe-incorrect",
        style = "verbose"
    )]
    pub suggest_lifetime: Option<Span>,
    pub snippet: String,
}

#[derive(Diagnostic)]
#[diag("`mut` must precede `dyn`")]
pub(crate) struct DynAfterMut {
    #[primary_span]
    #[suggestion(
        "place `mut` before `dyn`",
        code = "&mut dyn",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("an `fn` pointer type cannot be `const`")]
#[note("allowed qualifiers are: `unsafe` and `extern`")]
pub(crate) struct FnPointerCannotBeConst {
    #[primary_span]
    #[label("`const` because of this")]
    pub span: Span,
    #[suggestion(
        "remove the `const` qualifier",
        code = "",
        applicability = "maybe-incorrect",
        style = "verbose"
    )]
    pub suggestion: Span,
}

#[derive(Diagnostic)]
#[diag("an `fn` pointer type cannot be `async`")]
#[note("allowed qualifiers are: `unsafe` and `extern`")]
pub(crate) struct FnPointerCannotBeAsync {
    #[primary_span]
    #[label("`async` because of this")]
    pub span: Span,
    #[suggestion(
        "remove the `async` qualifier",
        code = "",
        applicability = "maybe-incorrect",
        style = "verbose"
    )]
    pub suggestion: Span,
}

#[derive(Diagnostic)]
#[diag("C-variadic type `...` may not be nested inside another type", code = E0743)]
pub(crate) struct NestedCVariadicType {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("unexpected `...`")]
#[note(
    "only `extern \"C\"` and `extern \"C-unwind\"` functions may have a C variable argument list"
)]
pub(crate) struct InvalidCVariadicType {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("invalid `dyn` keyword")]
#[help("`dyn` is only needed at the start of a trait `+`-separated list")]
pub(crate) struct InvalidDynKeyword {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "remove this keyword",
        code = "",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub suggestion: Span,
}

#[derive(Subdiagnostic)]
pub(crate) enum HelpUseLatestEdition {
    #[help("set `edition = \"{$edition}\"` in `Cargo.toml`")]
    #[note("for more on editions, read https://doc.rust-lang.org/edition-guide")]
    Cargo { edition: Edition },
    #[help("pass `--edition {$edition}` to `rustc`")]
    #[note("for more on editions, read https://doc.rust-lang.org/edition-guide")]
    Standalone { edition: Edition },
}

impl HelpUseLatestEdition {
    pub(crate) fn new() -> Self {
        let edition = LATEST_STABLE_EDITION;
        if rustc_session::utils::was_invoked_from_cargo() {
            Self::Cargo { edition }
        } else {
            Self::Standalone { edition }
        }
    }
}

#[derive(Diagnostic)]
#[diag("`box_syntax` has been removed")]
pub(crate) struct BoxSyntaxRemoved {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub sugg: AddBoxNew,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "use `Box::new()` instead",
    applicability = "machine-applicable",
    style = "verbose"
)]
pub(crate) struct AddBoxNew {
    #[suggestion_part(code = "Box::new(")]
    pub box_kw_and_lo: Span,
    #[suggestion_part(code = ")")]
    pub hi: Span,
}

#[derive(Diagnostic)]
#[diag("return type not allowed with return type notation")]
pub(crate) struct BadReturnTypeNotationOutput {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "remove the return type",
        code = "",
        applicability = "maybe-incorrect",
        style = "verbose"
    )]
    pub suggestion: Span,
}

#[derive(Diagnostic)]
#[diag("bounds on associated types do not belong here")]
pub(crate) struct BadAssocTypeBounds {
    #[primary_span]
    #[label("belongs in `where` clause")]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("trailing attribute after generic parameter")]
pub(crate) struct AttrAfterGeneric {
    #[primary_span]
    #[label("attributes must go before parameters")]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("attribute without generic parameters")]
pub(crate) struct AttrWithoutGenerics {
    #[primary_span]
    #[label("attributes are only permitted when preceding parameters")]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("generic parameters on `where` clauses are reserved for future use")]
pub(crate) struct WhereOnGenerics {
    #[primary_span]
    #[label("currently unsupported")]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("unexpected generic arguments in path")]
pub(crate) struct GenericsInPath {
    #[primary_span]
    pub span: Vec<Span>,
}

#[derive(Diagnostic)]
#[diag("lifetimes are not permitted in this context")]
#[help("if you meant to specify a trait object, write `dyn /* Trait */ + {$lifetime}`")]
pub(crate) struct LifetimeInEqConstraint {
    #[primary_span]
    #[label("lifetime is not allowed here")]
    pub span: Span,
    pub lifetime: Ident,
    #[label("this introduces an associated item binding")]
    pub binding_label: Span,
    #[suggestion(
        "you might have meant to write a bound here",
        style = "verbose",
        applicability = "maybe-incorrect",
        code = ": "
    )]
    pub colon_sugg: Span,
}

#[derive(Diagnostic)]
#[diag("`{$modifier}` may only modify trait bounds, not lifetime bounds")]
pub(crate) struct ModifierLifetime {
    #[primary_span]
    #[suggestion(
        "remove the `{$modifier}`",
        style = "tool-only",
        applicability = "maybe-incorrect",
        code = ""
    )]
    pub span: Span,
    pub modifier: &'static str,
}

#[derive(Diagnostic)]
#[diag("underscore literal suffix is not allowed")]
pub(crate) struct UnderscoreLiteralSuffix {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("expected a label, found an identifier")]
pub(crate) struct ExpectedLabelFoundIdent {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "labels start with a tick",
        code = "'",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub start: Span,
}

#[derive(Diagnostic)]
#[diag("{$article} {$descr} cannot be `default`")]
#[note("only associated `fn`, `const`, and `type` items can be `default`")]
pub(crate) struct InappropriateDefault {
    #[primary_span]
    #[label("`default` because of this")]
    pub span: Span,
    pub article: &'static str,
    pub descr: &'static str,
}

#[derive(Diagnostic)]
#[diag("expected item, found {$token_name}")]
pub(crate) struct RecoverImportAsUse {
    #[primary_span]
    #[suggestion(
        "items are imported using the `use` keyword",
        code = "use",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub span: Span,
    pub token_name: String,
}

#[derive(Diagnostic)]
#[diag("{$article} {$descr} cannot be `final`")]
#[note("only associated functions in traits can be `final`")]
pub(crate) struct InappropriateFinal {
    #[primary_span]
    #[label("`final` because of this")]
    pub span: Span,
    pub article: &'static str,
    pub descr: &'static str,
}

#[derive(Diagnostic)]
#[diag("expected `::`, found `:`")]
#[note("import paths are delimited using `::`")]
pub(crate) struct SingleColonImportPath {
    #[primary_span]
    #[suggestion(
        "use double colon",
        code = "::",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("{$descr} is not supported in {$ctx}")]
pub(crate) struct BadItemKind {
    #[primary_span]
    pub span: Span,
    pub descr: &'static str,
    pub ctx: &'static str,
    #[help("consider moving the {$descr} out to a nearby module scope")]
    pub help: bool,
}

#[derive(Diagnostic)]
#[diag("expected `!` after `macro_rules`")]
pub(crate) struct MacroRulesMissingBang {
    #[primary_span]
    pub span: Span,
    #[suggestion("add a `!`", code = "!", applicability = "machine-applicable", style = "verbose")]
    pub hi: Span,
}

#[derive(Diagnostic)]
#[diag("macro names aren't followed by a `!`")]
pub(crate) struct MacroNameRemoveBang {
    #[primary_span]
    #[suggestion(
        "remove the `!`",
        code = "",
        applicability = "machine-applicable",
        style = "short"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("can't qualify macro_rules invocation with `{$vis}`")]
pub(crate) struct MacroRulesVisibility<'a> {
    #[primary_span]
    #[suggestion(
        "try exporting the macro",
        code = "#[macro_export]",
        applicability = "maybe-incorrect",
        style = "verbose"
    )]
    pub span: Span,
    pub vis: &'a str,
}

#[derive(Diagnostic)]
#[diag("can't qualify macro invocation with `pub`")]
#[help("try adjusting the macro to put `{$vis}` inside the invocation")]
pub(crate) struct MacroInvocationVisibility<'a> {
    #[primary_span]
    #[suggestion(
        "remove the visibility",
        code = "",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub span: Span,
    pub vis: &'a str,
}

#[derive(Diagnostic)]
#[diag("`{$kw_str}` definition cannot be nested inside `{$keyword}`")]
pub(crate) struct NestedAdt<'a> {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "consider creating a new `{$kw_str}` definition instead of nesting",
        code = "",
        applicability = "maybe-incorrect",
        style = "verbose"
    )]
    pub item: Span,
    pub keyword: &'a str,
    pub kw_str: Cow<'a, str>,
}

#[derive(Diagnostic)]
#[diag("function body cannot be `= expression;`")]
pub(crate) struct FunctionBodyEqualsExpr {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub sugg: FunctionBodyEqualsExprSugg,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    r#"surround the expression with `{"{"}` and `{"}"}` instead of `=` and `;`"#,
    applicability = "machine-applicable"
)]
pub(crate) struct FunctionBodyEqualsExprSugg {
    #[suggestion_part(code = "{{")]
    pub eq: Span,
    #[suggestion_part(code = " }}")]
    pub semi: Span,
}

#[derive(Diagnostic)]
#[diag("expected pattern, found {$descr}")]
pub(crate) struct BoxNotPat {
    #[primary_span]
    pub span: Span,
    #[note("`box` is a reserved keyword")]
    pub kw: Span,
    #[suggestion(
        "escape `box` to use it as an identifier",
        code = "r#",
        applicability = "maybe-incorrect",
        style = "verbose"
    )]
    pub lo: Span,
    pub descr: String,
}

#[derive(Diagnostic)]
#[diag(
    "unmatched angle {$plural ->
        [true] brackets
        *[false] bracket
    }"
)]
pub(crate) struct UnmatchedAngle {
    #[primary_span]
    #[suggestion(
        "remove extra angle {$plural ->
            [true] brackets
            *[false] bracket
        }",
        code = "",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub span: Span,
    pub plural: bool,
}

#[derive(Diagnostic)]
#[diag("expected `+` between lifetime and {$sym}")]
pub(crate) struct MissingPlusBounds {
    #[primary_span]
    pub span: Span,
    #[suggestion("add `+`", code = " +", applicability = "maybe-incorrect", style = "verbose")]
    pub hi: Span,
    pub sym: Symbol,
}

#[derive(Diagnostic)]
#[diag("incorrect parentheses around trait bounds")]
pub(crate) struct IncorrectParensTraitBounds {
    #[primary_span]
    pub span: Vec<Span>,
    #[subdiagnostic]
    pub sugg: IncorrectParensTraitBoundsSugg,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion("fix the parentheses", applicability = "machine-applicable")]
pub(crate) struct IncorrectParensTraitBoundsSugg {
    #[suggestion_part(code = " ")]
    pub wrong_span: Span,
    #[suggestion_part(code = "(")]
    pub new_span: Span,
}

#[derive(Diagnostic)]
#[diag("keyword `{$kw}` is written in the wrong case")]
pub(crate) struct KwBadCase<'a> {
    #[primary_span]
    #[suggestion(
        "write it in {$case}",
        code = "{kw}",
        style = "verbose",
        applicability = "machine-applicable"
    )]
    pub span: Span,
    pub kw: &'a str,
    pub case: Case,
}

pub(crate) enum Case {
    Upper,
    Lower,
    Mixed,
}

impl IntoDiagArg for Case {
    fn into_diag_arg(self, path: &mut Option<PathBuf>) -> DiagArgValue {
        match self {
            Case::Upper => "uppercase",
            Case::Lower => "lowercase",
            Case::Mixed => "the correct case",
        }
        .into_diag_arg(path)
    }
}

#[derive(Diagnostic)]
#[diag("unknown `builtin #` construct `{$name}`")]
pub(crate) struct UnknownBuiltinConstruct {
    #[primary_span]
    pub span: Span,
    pub name: Ident,
}

#[derive(Diagnostic)]
#[diag("expected identifier after `builtin #`")]
pub(crate) struct ExpectedBuiltinIdent {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("static items may not have generic parameters")]
pub(crate) struct StaticWithGenerics {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("where clauses are not allowed before const item bodies")]
pub(crate) struct WhereClauseBeforeConstBody {
    #[primary_span]
    #[label("unexpected where clause")]
    pub span: Span,
    #[label("while parsing this const item")]
    pub name: Span,
    #[label("the item body")]
    pub body: Span,
    #[subdiagnostic]
    pub sugg: Option<WhereClauseBeforeConstBodySugg>,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "move the body before the where clause",
    applicability = "machine-applicable"
)]
pub(crate) struct WhereClauseBeforeConstBodySugg {
    #[suggestion_part(code = "= {snippet} ")]
    pub left: Span,
    pub snippet: String,
    #[suggestion_part(code = "")]
    pub right: Span,
}

#[derive(Diagnostic)]
#[diag("generic args in patterns require the turbofish syntax")]
pub(crate) struct GenericArgsInPatRequireTurbofishSyntax {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "use `::<...>` instead of `<...>` to specify lifetime, type, or const arguments",
        style = "verbose",
        code = "::",
        applicability = "maybe-incorrect"
    )]
    pub suggest_turbofish: Span,
}

#[derive(Diagnostic)]
#[diag("`for<...>` expected after `{$kw}`, not before")]
pub(crate) struct TransposeDynOrImpl<'a> {
    #[primary_span]
    pub span: Span,
    pub kw: &'a str,
    #[subdiagnostic]
    pub sugg: TransposeDynOrImplSugg<'a>,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion("move `{$kw}` before the `for<...>`", applicability = "machine-applicable")]
pub(crate) struct TransposeDynOrImplSugg<'a> {
    #[suggestion_part(code = "")]
    pub removal_span: Span,
    #[suggestion_part(code = "{kw} ")]
    pub insertion_span: Span,
    pub kw: &'a str,
}

#[derive(Diagnostic)]
#[diag("array indexing not supported in offset_of")]
pub(crate) struct ArrayIndexInOffsetOf(#[primary_span] pub Span);

#[derive(Diagnostic)]
#[diag("offset_of expects dot-separated field and variant names")]
pub(crate) struct InvalidOffsetOf(#[primary_span] pub Span);

#[derive(Diagnostic)]
#[diag("`async` trait implementations are unsupported")]
pub(crate) struct AsyncImpl {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("`->` is not valid syntax for field accesses and method calls")]
#[help(
    "the `.` operator will automatically dereference the value, except if the value is a raw pointer"
)]
pub(crate) struct ExprRArrowCall {
    #[primary_span]
    #[suggestion(
        "try using `.` instead",
        style = "verbose",
        applicability = "machine-applicable",
        code = "."
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("attributes are not allowed on range expressions starting with `..`")]
pub(crate) struct DotDotRangeAttribute {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("`for<...>` binder should be placed before trait bound modifiers")]
pub(crate) struct BinderBeforeModifiers {
    #[primary_span]
    pub binder_span: Span,
    #[label("place the `for<...>` binder before any modifiers")]
    pub modifiers_span: Span,
}

#[derive(Diagnostic)]
#[diag("`for<...>` binder not allowed with `{$polarity}` trait polarity modifier")]
pub(crate) struct BinderAndPolarity {
    #[primary_span]
    pub polarity_span: Span,
    #[label("there is not a well-defined meaning for a higher-ranked `{$polarity}` trait")]
    pub binder_span: Span,
    pub polarity: &'static str,
}

#[derive(Diagnostic)]
#[diag("`{$modifiers_concatenated}` trait not allowed with `{$polarity}` trait polarity modifier")]
pub(crate) struct PolarityAndModifiers {
    #[primary_span]
    pub polarity_span: Span,
    #[label(
        "there is not a well-defined meaning for a `{$modifiers_concatenated} {$polarity}` trait"
    )]
    pub modifiers_span: Span,
    pub polarity: &'static str,
    pub modifiers_concatenated: String,
}

#[derive(Diagnostic)]
#[diag("type not allowed for shorthand `self` parameter")]
pub(crate) struct IncorrectTypeOnSelf {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub move_self_modifier: MoveSelfModifier,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "move the modifiers on `self` to the type",
    applicability = "machine-applicable"
)]
pub(crate) struct MoveSelfModifier {
    #[suggestion_part(code = "")]
    pub removal_span: Span,
    #[suggestion_part(code = "{modifier}")]
    pub insertion_span: Span,
    pub modifier: String,
}

#[derive(Diagnostic)]
#[diag("the `{$symbol}` operand cannot be used with `{$macro_name}!`")]
pub(crate) struct AsmUnsupportedOperand<'a> {
    #[primary_span]
    #[label(
        "the `{$symbol}` operand is not meaningful for global-scoped inline assembly, remove it"
    )]
    pub(crate) span: Span,
    pub(crate) symbol: &'a str,
    pub(crate) macro_name: &'static str,
}

#[derive(Diagnostic)]
#[diag("_ cannot be used for input operands")]
pub(crate) struct AsmUnderscoreInput {
    #[primary_span]
    pub(crate) span: Span,
}

#[derive(Diagnostic)]
#[diag("expected a path for argument to `sym`")]
pub(crate) struct AsmSymNoPath {
    #[primary_span]
    pub(crate) span: Span,
}

#[derive(Diagnostic)]
#[diag("requires at least a template string argument")]
pub(crate) struct AsmRequiresTemplate {
    #[primary_span]
    pub(crate) span: Span,
}

#[derive(Diagnostic)]
#[diag("expected token: `,`")]
pub(crate) struct AsmExpectedComma {
    #[primary_span]
    #[label("expected `,`")]
    pub(crate) span: Span,
}

#[derive(Diagnostic)]
#[diag(
    "expected operand, {$is_inline_asm ->
        [false] options
        *[true] clobber_abi, options
    }, or additional template string"
)]
pub(crate) struct AsmExpectedOther {
    #[primary_span]
    #[label(
        "expected operand, {$is_inline_asm ->
            [false] options
            *[true] clobber_abi, options
        }, or additional template string"
    )]
    pub(crate) span: Span,
    pub(crate) is_inline_asm: bool,
}

#[derive(Diagnostic)]
#[diag("at least one abi must be provided as an argument to `clobber_abi`")]
pub(crate) struct NonABI {
    #[primary_span]
    pub(crate) span: Span,
}

#[derive(Diagnostic)]
#[diag("expected string literal")]
pub(crate) struct AsmExpectedStringLiteral {
    #[primary_span]
    #[label("not a string literal")]
    pub(crate) span: Span,
}

#[derive(Diagnostic)]
#[diag("expected register class or explicit register")]
pub(crate) struct ExpectedRegisterClassOrExplicitRegister {
    #[primary_span]
    pub(crate) span: Span,
}

#[derive(Diagnostic)]
#[diag("unicode codepoint changing visible direction of text present in {$label}")]
#[note(
    "these kind of unicode codepoints change the way text flows on applications that support them, but can cause confusion because they change the order of characters on the screen"
)]
pub(crate) struct HiddenUnicodeCodepointsDiag {
    pub label: String,
    pub count: usize,
    #[label(
        "this {$label} contains {$count ->
            [one] an invisible
            *[other] invisible
        } unicode text flow control {$count ->
            [one] codepoint
            *[other] codepoints
        }"
    )]
    pub span_label: Span,
    #[subdiagnostic]
    pub labels: Option<HiddenUnicodeCodepointsDiagLabels>,
    #[subdiagnostic]
    pub sub: HiddenUnicodeCodepointsDiagSub,
}

pub(crate) struct HiddenUnicodeCodepointsDiagLabels {
    pub spans: Vec<(char, Span)>,
}

impl Subdiagnostic for HiddenUnicodeCodepointsDiagLabels {
    fn add_to_diag<G: EmissionGuarantee>(self, diag: &mut Diag<'_, G>) {
        for (c, span) in self.spans {
            diag.span_label(span, format!("{c:?}"));
        }
    }
}

pub(crate) enum HiddenUnicodeCodepointsDiagSub {
    Escape { spans: Vec<(char, Span)> },
    NoEscape { spans: Vec<(char, Span)>, is_doc_comment: bool },
}

// Used because of multiple multipart_suggestion and note
impl Subdiagnostic for HiddenUnicodeCodepointsDiagSub {
    fn add_to_diag<G: EmissionGuarantee>(self, diag: &mut Diag<'_, G>) {
        match self {
            HiddenUnicodeCodepointsDiagSub::Escape { spans } => {
                diag.multipart_suggestion_with_style(
                    msg!("if their presence wasn't intentional, you can remove them"),
                    spans.iter().map(|(_, span)| (*span, "".to_string())).collect(),
                    Applicability::MachineApplicable,
                    SuggestionStyle::HideCodeAlways,
                );
                diag.multipart_suggestion(
                    msg!("if you want to keep them but make them visible in your source code, you can escape them"),
                    spans
                        .into_iter()
                        .map(|(c, span)| {
                            let c = format!("{c:?}");
                            (span, c[1..c.len() - 1].to_string())
                        })
                        .collect(),
                    Applicability::MachineApplicable,
                );
            }
            HiddenUnicodeCodepointsDiagSub::NoEscape { spans, is_doc_comment } => {
                // tRust: known issue —: in other suggestions we've reversed the inner spans of doc comments. We
                // should do the same here to provide the same good suggestions as we do for
                // literals above.
                diag.arg(
                    "escaped",
                    spans
                        .into_iter()
                        .map(|(c, _)| format!("{c:?}"))
                        .collect::<Vec<String>>()
                        .join(", "),
                );
                diag.note(msg!("if their presence wasn't intentional, you can remove them"));
                if is_doc_comment {
                    diag.note(msg!(r#"if you need to keep them and make them explicit in source, rewrite this doc comment as a `#[doc = "..."]` attribute and use Unicode escapes such as {$escaped}"#));
                } else {
                    diag.note(msg!("if you want to keep them but make them visible in your source code, you can escape them: {$escaped}"));
                }
            }
        }
    }
}

#[derive(Diagnostic)]
#[diag("missing pattern for `...` argument")]
pub(crate) struct VarargsWithoutPattern {
    #[suggestion(
        "name the argument, or use `_` to continue ignoring it",
        code = "_: ...",
        applicability = "machine-applicable"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("only trait impls can be reused")]
pub(crate) struct ImplReuseInherentImpl {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("placeholder `_` is not allowed for the path in struct literals")]
pub(crate) struct StructLiteralPlaceholderPath {
    #[primary_span]
    #[label("not allowed in struct literals")]
    #[suggestion(
        "replace it with the correct type",
        applicability = "has-placeholders",
        code = "/* Type */",
        style = "verbose"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("struct literal body without path")]
pub(crate) struct StructLiteralWithoutPathLate {
    #[primary_span]
    #[label("struct name missing for struct literal")]
    pub span: Span,
    #[suggestion(
        "add the correct type",
        applicability = "has-placeholders",
        code = "/* Type */ ",
        style = "verbose"
    )]
    pub suggestion_span: Span,
}

/// Used to forbid `let` expressions in certain syntactic locations.
#[derive(Clone, Copy, Subdiagnostic)]
pub(crate) enum ForbiddenLetReason {
    /// `let` is not valid and the source environment is not important
    OtherForbidden,
    /// A let chain with the `||` operator
    #[note("`||` operators are not supported in let chain expressions")]
    NotSupportedOr(#[primary_span] Span),
    /// A let chain with invalid parentheses
    ///
    /// For example, `let 1 = 1 && (expr && expr)` is allowed
    /// but `(let 1 = 1 && (let 1 = 1 && (let 1 = 1))) && let a = 1` is not
    #[note("`let`s wrapped in parentheses are not supported in a context with let chains")]
    NotSupportedParentheses(#[primary_span] Span),
}

#[derive(Debug, rustc_macros::Subdiagnostic)]
#[suggestion(
    "{$is_incorrect_case ->
        [true] write keyword `{$similar_kw}` in lowercase
        *[false] there is a keyword `{$similar_kw}` with a similar name
    }",
    applicability = "machine-applicable",
    code = "{similar_kw}",
    style = "verbose"
)]
pub(crate) struct MisspelledKw {
    // We use a String here because `Symbol::into_diag_arg` calls `Symbol::to_ident_string`, which
    // prefix the keyword with a `r#` because it aims to print the symbol as an identifier.
    pub similar_kw: String,
    #[primary_span]
    pub span: Span,
    pub is_incorrect_case: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum TokenDescription {
    ReservedIdentifier,
    Keyword,
    ReservedKeyword,
    DocComment,

    // Expanded metavariables are wrapped in invisible delimiters which aren't
    // pretty-printed. In error messages we must handle these specially
    // otherwise we get confusing things in messages like "expected `(`, found
    // ``". It's better to say e.g. "expected `(`, found type metavariable".
    MetaVar(MetaVarKind),
}

impl TokenDescription {
    pub(super) fn from_token(token: &Token) -> Option<Self> {
        match token.kind {
            _ if token.is_special_ident() => Some(TokenDescription::ReservedIdentifier),
            _ if token.is_used_keyword() => Some(TokenDescription::Keyword),
            _ if token.is_unused_keyword() => Some(TokenDescription::ReservedKeyword),
            token::DocComment(..) => Some(TokenDescription::DocComment),
            token::OpenInvisible(InvisibleOrigin::MetaVar(kind)) => {
                Some(TokenDescription::MetaVar(kind))
            }
            _ => None,
        }
    }
}

#[derive(Diagnostic)]
#[diag(
    "this labeled break expression is easy to confuse with an unlabeled break with a labeled value expression"
)]
pub(crate) struct BreakWithLabelAndLoop {
    #[subdiagnostic]
    pub sub: BreakWithLabelAndLoopSub,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion("wrap this expression in parentheses", applicability = "machine-applicable")]
pub(crate) struct BreakWithLabelAndLoopSub {
    #[suggestion_part(code = "(")]
    pub left: Span,
    #[suggestion_part(code = ")")]
    pub right: Span,
}

#[derive(Diagnostic)]
#[diag("prefix `'r` is reserved")]
pub(crate) struct RawPrefix {
    #[label("reserved prefix")]
    pub label: Span,
    #[suggestion(
        "insert whitespace here to avoid this being parsed as a prefix in Rust 2021",
        code = " ",
        applicability = "machine-applicable"
    )]
    pub suggestion: Span,
}

#[derive(Diagnostic)]
#[diag("unicode codepoint changing visible direction of text present in comment")]
#[note(
    "these kind of unicode codepoints change the way text flows on applications that support them, but can cause confusion because they change the order of characters on the screen"
)]
pub(crate) struct UnicodeTextFlow {
    #[label(
        "{$num_codepoints ->
            [1] this comment contains an invisible unicode text flow control codepoint
            *[other] this comment contains invisible unicode text flow control codepoints
        }"
    )]
    pub comment_span: Span,
    #[subdiagnostic]
    pub characters: Vec<UnicodeCharNoteSub>,
    #[subdiagnostic]
    pub suggestions: Option<UnicodeTextFlowSuggestion>,

    pub num_codepoints: usize,
}

#[derive(Subdiagnostic)]
#[label("{$c_debug}")]
pub(crate) struct UnicodeCharNoteSub {
    #[primary_span]
    pub span: Span,
    pub c_debug: String,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "if their presence wasn't intentional, you can remove them",
    applicability = "machine-applicable",
    style = "hidden"
)]
pub(crate) struct UnicodeTextFlowSuggestion {
    #[suggestion_part(code = "")]
    pub spans: Vec<Span>,
}

#[derive(Diagnostic)]
#[diag("prefix `{$prefix}` is unknown")]
pub(crate) struct ReservedPrefix {
    #[label("unknown prefix")]
    pub label: Span,
    #[suggestion(
        "insert whitespace here to avoid this being parsed as a prefix in Rust 2021",
        code = " ",
        applicability = "machine-applicable"
    )]
    pub suggestion: Span,

    pub prefix: String,
}

#[derive(Diagnostic)]
#[diag("will be parsed as a guarded string in Rust 2024")]
pub(crate) struct ReservedStringLint {
    #[suggestion(
        "insert whitespace here to avoid this being parsed as a guarded string in Rust 2024",
        code = " ",
        applicability = "machine-applicable"
    )]
    pub suggestion: Span,
}

#[derive(Diagnostic)]
#[diag("reserved token in Rust 2024")]
pub(crate) struct ReservedMultihashLint {
    #[suggestion(
        "insert whitespace here to avoid this being parsed as a forbidden token in Rust 2024",
        code = " ",
        applicability = "machine-applicable"
    )]
    pub suggestion: Span,
}
