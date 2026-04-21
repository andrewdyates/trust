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
#[diag("suffixes on a tuple index are invalid")]
pub(crate) struct InvalidLiteralSuffixOnTupleIndex {
    #[primary_span]
    #[label("invalid suffix `{$suffix}`")]
    pub span: Span,
    pub suffix: Symbol,
}

#[derive(Diagnostic)]
#[diag("non-string ABI literal")]
pub(crate) struct NonStringAbiLiteral {
    #[primary_span]
    #[suggestion(
        "specify the ABI with a string literal",
        code = "\"C\"",
        applicability = "maybe-incorrect",
        style = "verbose"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("mismatched closing delimiter: `{$delimiter}`")]
pub(crate) struct MismatchedClosingDelimiter {
    #[primary_span]
    pub spans: Vec<Span>,
    pub delimiter: String,
    #[label("mismatched closing delimiter")]
    pub unmatched: Span,
    #[label("closing delimiter possibly meant for this")]
    pub opening_candidate: Option<Span>,
    #[label("unclosed delimiter")]
    pub unclosed: Option<Span>,
}

#[derive(Diagnostic)]
#[diag("incorrect visibility restriction", code = E0704)]
#[help(
    "some possible visibility restrictions are:
    `pub(crate)`: visible only on the current crate
    `pub(super)`: visible only in the current module's parent
    `pub(in path::to::module)`: visible only on the specified path"
)]
pub(crate) struct IncorrectVisibilityRestriction {
    #[primary_span]
    #[suggestion(
        "make this visible only to module `{$inner_str}` with `in`",
        code = "in {inner_str}",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub span: Span,
    pub inner_str: String,
}

#[derive(Diagnostic)]
#[diag("incorrect `impl` restriction")]
#[help(
    "some possible `impl` restrictions are:
    `impl(crate)`: can only be implemented in the current crate
    `impl(super)`: can only be implemented in the parent module
    `impl(self)`: can only be implemented in current module
    `impl(in path::to::module)`: can only be implemented in the specified path"
)]
pub(crate) struct IncorrectImplRestriction {
    #[primary_span]
    #[suggestion(
        "help: use `in` to restrict implementations to the path `{$inner_str}`",
        code = "in {inner_str}",
        applicability = "machine-applicable"
    )]
    pub span: Span,
    pub inner_str: String,
}

#[derive(Diagnostic)]
#[diag("<assignment> ... else {\"{\"} ... {\"}\"} is not allowed")]
pub(crate) struct AssignmentElseNotAllowed {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("expected statement after outer attribute")]
pub(crate) struct ExpectedStatementAfterOuterAttr {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("found a documentation comment that doesn't document anything", code = E0585)]
#[help("doc comments must come before what they document, if a comment was intended use `//`")]
pub(crate) struct DocCommentDoesNotDocumentAnything {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "missing comma here",
        code = ",",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub missing_comma: Option<Span>,
}

#[derive(Diagnostic)]
#[diag("`const` and `let` are mutually exclusive")]
pub(crate) struct ConstLetMutuallyExclusive {
    #[primary_span]
    #[suggestion(
        "remove `let`",
        code = "const",
        applicability = "maybe-incorrect",
        style = "verbose"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("a `{$operator}` expression cannot be directly assigned in `let...else`")]
pub(crate) struct InvalidExpressionInLetElse {
    #[primary_span]
    pub span: Span,
    pub operator: &'static str,
    #[subdiagnostic]
    pub sugg: WrapInParentheses,
}

#[derive(Diagnostic)]
#[diag("right curly brace `{\"}\"}` before `else` in a `let...else` statement not allowed")]
pub(crate) struct InvalidCurlyInLetElse {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub sugg: WrapInParentheses,
}

#[derive(Diagnostic)]
#[diag("can't reassign to an uninitialized variable")]
#[help("if you meant to overwrite, remove the `let` binding")]
pub(crate) struct CompoundAssignmentExpressionInLet {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "initialize the variable",
        style = "verbose",
        code = "",
        applicability = "maybe-incorrect"
    )]
    pub suggestion: Span,
}

#[derive(Diagnostic)]
#[diag("suffixed literals are not allowed in attributes")]
#[help(
    "instead of using a suffixed literal (`1u8`, `1.0f32`, etc.), use an unsuffixed version (`1`, `1.0`, etc.)"
)]
pub(crate) struct SuffixedLiteralInAttribute {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("expected unsuffixed literal, found {$descr}")]
pub(crate) struct InvalidMetaItem {
    #[primary_span]
    pub span: Span,
    pub descr: String,
    #[subdiagnostic]
    pub quote_ident_sugg: Option<InvalidMetaItemQuoteIdentSugg>,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "surround the identifier with quotation marks to make it into a string literal",
    applicability = "machine-applicable"
)]
pub(crate) struct InvalidMetaItemQuoteIdentSugg {
    #[suggestion_part(code = "\"")]
    pub before: Span,
    #[suggestion_part(code = "\"")]
    pub after: Span,
}

#[derive(Subdiagnostic)]
#[suggestion(
    "escape `{$ident_name}` to use it as an identifier",
    style = "verbose",
    applicability = "maybe-incorrect",
    code = "r#"
)]
pub(crate) struct SuggEscapeIdentifier {
    #[primary_span]
    pub span: Span,
    pub ident_name: String,
}

#[derive(Subdiagnostic)]
#[suggestion(
    "remove this comma",
    applicability = "machine-applicable",
    code = "",
    style = "verbose"
)]
pub(crate) struct SuggRemoveComma {
    #[primary_span]
    pub span: Span,
}

#[derive(Subdiagnostic)]
#[suggestion(
    "you might have meant to introduce a new binding",
    style = "verbose",
    applicability = "maybe-incorrect",
    code = "let "
)]
pub(crate) struct SuggAddMissingLetStmt {
    #[primary_span]
    pub span: Span,
}

#[derive(Subdiagnostic)]
pub(crate) enum ExpectedIdentifierFound {
    #[label("expected identifier, found reserved identifier")]
    ReservedIdentifier(#[primary_span] Span),
    #[label("expected identifier, found keyword")]
    Keyword(#[primary_span] Span),
    #[label("expected identifier, found reserved keyword")]
    ReservedKeyword(#[primary_span] Span),
    #[label("expected identifier, found doc comment")]
    DocComment(#[primary_span] Span),
    #[label("expected identifier, found metavariable")]
    MetaVar(#[primary_span] Span),
    #[label("expected identifier")]
    Other(#[primary_span] Span),
}

impl ExpectedIdentifierFound {
    pub(crate) fn new(token_descr: Option<TokenDescription>, span: Span) -> Self {
        (match token_descr {
            Some(TokenDescription::ReservedIdentifier) => {
                ExpectedIdentifierFound::ReservedIdentifier
            }
            Some(TokenDescription::Keyword) => ExpectedIdentifierFound::Keyword,
            Some(TokenDescription::ReservedKeyword) => ExpectedIdentifierFound::ReservedKeyword,
            Some(TokenDescription::DocComment) => ExpectedIdentifierFound::DocComment,
            Some(TokenDescription::MetaVar(_)) => ExpectedIdentifierFound::MetaVar,
            None => ExpectedIdentifierFound::Other,
        })(span)
    }
}

pub(crate) struct ExpectedIdentifier {
    pub span: Span,
    pub token: Token,
    pub suggest_raw: Option<SuggEscapeIdentifier>,
    pub suggest_remove_comma: Option<SuggRemoveComma>,
    pub help_cannot_start_number: Option<HelpIdentifierStartsWithNumber>,
}

impl<'a, G: EmissionGuarantee> Diagnostic<'a, G> for ExpectedIdentifier {
    #[track_caller]
    fn into_diag(self, dcx: DiagCtxtHandle<'a>, level: Level) -> Diag<'a, G> {
        let token_descr = TokenDescription::from_token(&self.token);

        let mut add_token = true;
        let mut diag = Diag::new(
            dcx,
            level,
            match token_descr {
                Some(TokenDescription::ReservedIdentifier) => {
                    msg!("expected identifier, found reserved identifier `{$token}`")
                }
                Some(TokenDescription::Keyword) => {
                    msg!("expected identifier, found keyword `{$token}`")
                }
                Some(TokenDescription::ReservedKeyword) => {
                    msg!("expected identifier, found reserved keyword `{$token}`")
                }
                Some(TokenDescription::DocComment) => {
                    msg!("expected identifier, found doc comment `{$token}`")
                }
                Some(TokenDescription::MetaVar(_)) => {
                    add_token = false;
                    msg!("expected identifier, found metavariable")
                }
                None => msg!("expected identifier, found `{$token}`"),
            },
        );
        diag.span(self.span);
        if add_token {
            diag.arg("token", self.token);
        }

        if let Some(sugg) = self.suggest_raw {
            sugg.add_to_diag(&mut diag);
        }

        ExpectedIdentifierFound::new(token_descr, self.span).add_to_diag(&mut diag);

        if let Some(sugg) = self.suggest_remove_comma {
            sugg.add_to_diag(&mut diag);
        }

        if let Some(help) = self.help_cannot_start_number {
            help.add_to_diag(&mut diag);
        }

        diag
    }
}

#[derive(Subdiagnostic)]
#[help("identifiers cannot start with a number")]
pub(crate) struct HelpIdentifierStartsWithNumber {
    #[primary_span]
    pub num_span: Span,
}

pub(crate) struct ExpectedSemi {
    pub span: Span,
    pub token: Token,
    pub unexpected_token_label: Option<Span>,
    pub sugg: ExpectedSemiSugg,
}

impl<'a, G: EmissionGuarantee> Diagnostic<'a, G> for ExpectedSemi {
    #[track_caller]
    fn into_diag(self, dcx: DiagCtxtHandle<'a>, level: Level) -> Diag<'a, G> {
        let token_descr = TokenDescription::from_token(&self.token);

        let mut add_token = true;
        let mut diag = Diag::new(
            dcx,
            level,
            match token_descr {
                Some(TokenDescription::ReservedIdentifier) => {
                    msg!("expected `;`, found reserved identifier `{$token}`")
                }
                Some(TokenDescription::Keyword) => {
                    msg!("expected `;`, found keyword `{$token}`")
                }
                Some(TokenDescription::ReservedKeyword) => {
                    msg!("expected `;`, found reserved keyword `{$token}`")
                }
                Some(TokenDescription::DocComment) => {
                    msg!("expected `;`, found doc comment `{$token}`")
                }
                Some(TokenDescription::MetaVar(_)) => {
                    add_token = false;
                    msg!("expected `;`, found metavariable")
                }
                None => msg!("expected `;`, found `{$token}`"),
            },
        );
        diag.span(self.span);
        if add_token {
            diag.arg("token", self.token);
        }

        if let Some(unexpected_token_label) = self.unexpected_token_label {
            diag.span_label(unexpected_token_label, msg!("unexpected token"));
        }

        self.sugg.add_to_diag(&mut diag);

        diag
    }
}

#[derive(Subdiagnostic)]
pub(crate) enum ExpectedSemiSugg {
    #[suggestion(
        "change this to `;`",
        code = ";",
        applicability = "machine-applicable",
        style = "short"
    )]
    ChangeToSemi(#[primary_span] Span),
    #[suggestion("add `;` here", code = ";", applicability = "machine-applicable", style = "short")]
    AddSemi(#[primary_span] Span),
}

#[derive(Diagnostic)]
#[diag("struct literal body without path")]
pub(crate) struct StructLiteralBodyWithoutPath {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub sugg: StructLiteralBodyWithoutPathSugg,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "you might have forgotten to add the struct literal inside the block",
    applicability = "has-placeholders"
)]
pub(crate) struct StructLiteralBodyWithoutPathSugg {
    #[suggestion_part(code = "{{ SomeStruct ")]
    pub before: Span,
    #[suggestion_part(code = " }}")]
    pub after: Span,
}

#[derive(Diagnostic)]
#[diag(
    "{$num_extra_brackets ->
        [one] unmatched angle bracket
        *[other] unmatched angle brackets
    }"
)]
pub(crate) struct UnmatchedAngleBrackets {
    #[primary_span]
    #[suggestion(
        "{$num_extra_brackets ->
            [one] remove extra angle bracket
            *[other] remove extra angle brackets
        }",
        code = "",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub span: Span,
    pub num_extra_brackets: usize,
}

#[derive(Diagnostic)]
#[diag("generic parameters without surrounding angle brackets")]
pub(crate) struct GenericParamsWithoutAngleBrackets {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub sugg: GenericParamsWithoutAngleBracketsSugg,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "surround the type parameters with angle brackets",
    applicability = "machine-applicable"
)]
pub(crate) struct GenericParamsWithoutAngleBracketsSugg {
    #[suggestion_part(code = "<")]
    pub left: Span,
    #[suggestion_part(code = ">")]
    pub right: Span,
}

#[derive(Diagnostic)]
#[diag("comparison operators cannot be chained")]
pub(crate) struct ComparisonOperatorsCannotBeChained {
    #[primary_span]
    pub span: Vec<Span>,
    #[suggestion(
        "use `::<...>` instead of `<...>` to specify lifetime, type, or const arguments",
        style = "verbose",
        code = "::",
        applicability = "maybe-incorrect"
    )]
    pub suggest_turbofish: Option<Span>,
    #[help("use `::<...>` instead of `<...>` to specify lifetime, type, or const arguments")]
    #[help("or use `(...)` if you meant to specify fn arguments")]
    pub help_turbofish: bool,
    #[subdiagnostic]
    pub chaining_sugg: Option<ComparisonOperatorsCannotBeChainedSugg>,
}

#[derive(Subdiagnostic)]
pub(crate) enum ComparisonOperatorsCannotBeChainedSugg {
    #[suggestion(
        "split the comparison into two",
        style = "verbose",
        code = " && {middle_term}",
        applicability = "maybe-incorrect"
    )]
    SplitComparison {
        #[primary_span]
        span: Span,
        middle_term: String,
    },
    #[multipart_suggestion("parenthesize the comparison", applicability = "maybe-incorrect")]
    Parenthesize {
        #[suggestion_part(code = "(")]
        left: Span,
        #[suggestion_part(code = ")")]
        right: Span,
    },
}

#[derive(Diagnostic)]
#[diag("invalid `?` in type")]
pub(crate) struct QuestionMarkInType {
    #[primary_span]
    #[label("`?` is only allowed on expressions, not types")]
    pub span: Span,
    #[subdiagnostic]
    pub sugg: QuestionMarkInTypeSugg,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "if you meant to express that the type might not contain a value, use the `Option` wrapper type",
    applicability = "machine-applicable"
)]
pub(crate) struct QuestionMarkInTypeSugg {
    #[suggestion_part(code = "Option<")]
    pub left: Span,
    #[suggestion_part(code = ">")]
    pub right: Span,
}

#[derive(Diagnostic)]
#[diag("unexpected parentheses surrounding `for` loop head")]
pub(crate) struct ParenthesesInForHead {
    #[primary_span]
    pub span: Vec<Span>,
    #[subdiagnostic]
    pub sugg: ParenthesesInForHeadSugg,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion("remove parentheses in `for` loop", applicability = "machine-applicable")]
pub(crate) struct ParenthesesInForHeadSugg {
    #[suggestion_part(code = " ")]
    pub left: Span,
    #[suggestion_part(code = " ")]
    pub right: Span,
}

#[derive(Diagnostic)]
#[diag("unexpected parentheses surrounding `match` arm pattern")]
pub(crate) struct ParenthesesInMatchPat {
    #[primary_span]
    pub span: Vec<Span>,
    #[subdiagnostic]
    pub sugg: ParenthesesInMatchPatSugg,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "remove parentheses surrounding the pattern",
    applicability = "machine-applicable"
)]
pub(crate) struct ParenthesesInMatchPatSugg {
    #[suggestion_part(code = "")]
    pub left: Span,
    #[suggestion_part(code = "")]
    pub right: Span,
}

#[derive(Diagnostic)]
#[diag("documentation comments cannot be applied to a function parameter's type")]
pub(crate) struct DocCommentOnParamType {
    #[primary_span]
    #[label("doc comments are not allowed here")]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("attributes cannot be applied to a function parameter's type")]
pub(crate) struct AttributeOnParamType {
    #[primary_span]
    #[label("attributes are not allowed here")]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("attributes cannot be applied to types")]
pub(crate) struct AttributeOnType {
    #[primary_span]
    #[label("attributes are not allowed here")]
    pub span: Span,
    #[suggestion(
        "remove attribute from here",
        code = "",
        applicability = "machine-applicable",
        style = "tool-only"
    )]
    pub fix_span: Span,
}

#[derive(Diagnostic)]
#[diag("attributes cannot be applied to generic arguments")]
pub(crate) struct AttributeOnGenericArg {
    #[primary_span]
    #[label("attributes are not allowed here")]
    pub span: Span,
    #[suggestion(
        "remove attribute from here",
        code = "",
        applicability = "machine-applicable",
        style = "tool-only"
    )]
    pub fix_span: Span,
}

#[derive(Diagnostic)]
#[diag("attributes cannot be applied here")]
pub(crate) struct AttributeOnEmptyType {
    #[primary_span]
    #[label("attributes are not allowed here")]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("patterns aren't allowed in methods without bodies", code = E0642)]
pub(crate) struct PatternMethodParamWithoutBody {
    #[primary_span]
    #[suggestion(
        "give this argument a name or use an underscore to ignore it",
        code = "_",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("unexpected `self` parameter in function")]
pub(crate) struct SelfParamNotFirst {
    #[primary_span]
    #[label("must be the first parameter of an associated function")]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("expressions must be enclosed in braces to be used as const generic arguments")]
pub(crate) struct ConstGenericWithoutBraces {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub sugg: ConstGenericWithoutBracesSugg,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "enclose the `const` expression in braces",
    applicability = "machine-applicable"
)]
pub(crate) struct ConstGenericWithoutBracesSugg {
    #[suggestion_part(code = "{{ ")]
    pub left: Span,
    #[suggestion_part(code = " }}")]
    pub right: Span,
}

#[derive(Diagnostic)]
#[diag("unexpected `const` parameter declaration")]
pub(crate) struct UnexpectedConstParamDeclaration {
    #[primary_span]
    #[label("expected a `const` expression, not a parameter declaration")]
    pub span: Span,
    #[subdiagnostic]
    pub sugg: Option<UnexpectedConstParamDeclarationSugg>,
}

#[derive(Subdiagnostic)]
pub(crate) enum UnexpectedConstParamDeclarationSugg {
    #[multipart_suggestion(
        "`const` parameters must be declared for the `impl`",
        applicability = "machine-applicable"
    )]
    AddParam {
        #[suggestion_part(code = "<{snippet}>")]
        impl_generics: Span,
        #[suggestion_part(code = "{ident}")]
        incorrect_decl: Span,
        snippet: String,
        ident: String,
    },
    #[multipart_suggestion(
        "`const` parameters must be declared for the `impl`",
        applicability = "machine-applicable"
    )]
    AppendParam {
        #[suggestion_part(code = ", {snippet}")]
        impl_generics_end: Span,
        #[suggestion_part(code = "{ident}")]
        incorrect_decl: Span,
        snippet: String,
        ident: String,
    },
}

#[derive(Diagnostic)]
#[diag("expected lifetime, type, or constant, found keyword `const`")]
pub(crate) struct UnexpectedConstInGenericParam {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "the `const` keyword is only needed in the definition of the type",
        style = "verbose",
        code = "",
        applicability = "maybe-incorrect"
    )]
    pub to_remove: Option<Span>,
}

#[derive(Diagnostic)]
#[diag("the order of `move` and `async` is incorrect")]
pub(crate) struct AsyncMoveOrderIncorrect {
    #[primary_span]
    #[suggestion(
        "try switching the order",
        style = "verbose",
        code = "async move",
        applicability = "maybe-incorrect"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("the order of `use` and `async` is incorrect")]
pub(crate) struct AsyncUseOrderIncorrect {
    #[primary_span]
    #[suggestion(
        "try switching the order",
        style = "verbose",
        code = "async use",
        applicability = "maybe-incorrect"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("expected `:` followed by trait or lifetime")]
pub(crate) struct DoubleColonInBound {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "use single colon",
        code = ": ",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub between: Span,
}

#[derive(Diagnostic)]
#[diag("function pointer types may not have generic parameters")]
pub(crate) struct FnPtrWithGenerics {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub sugg: Option<FnPtrWithGenericsSugg>,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "place the return type after the function parameters",
    style = "verbose",
    applicability = "maybe-incorrect"
)]
pub(crate) struct MisplacedReturnType {
    #[suggestion_part(code = " {snippet}")]
    pub fn_params_end: Span,
    pub snippet: String,
    #[suggestion_part(code = "")]
    pub ret_ty_span: Span,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "consider moving the lifetime {$arity ->
        [one] parameter
        *[other] parameters
    } to {$for_param_list_exists ->
        [true] the
        *[false] a
    } `for` parameter list",
    applicability = "maybe-incorrect"
)]
pub(crate) struct FnPtrWithGenericsSugg {
    #[suggestion_part(code = "{snippet}")]
    pub left: Span,
    pub snippet: String,
    #[suggestion_part(code = "")]
    pub right: Span,
    pub arity: usize,
    pub for_param_list_exists: bool,
}

pub(crate) struct FnTraitMissingParen {
    pub span: Span,
}

impl Subdiagnostic for FnTraitMissingParen {
    fn add_to_diag<G: EmissionGuarantee>(self, diag: &mut Diag<'_, G>) {
        diag.span_label(self.span, msg!("`Fn` bounds require arguments in parentheses"));
        diag.span_suggestion_short(
            self.span.shrink_to_hi(),
            msg!("try adding parentheses"),
            "()",
            Applicability::MachineApplicable,
        );
    }
}

#[derive(Diagnostic)]
#[diag("unexpected `if` in the condition expression")]
pub(crate) struct UnexpectedIfWithIf(
    #[primary_span]
    #[suggestion(
        "remove the `if`",
        applicability = "machine-applicable",
        code = " ",
        style = "verbose"
    )]
    pub Span,
);

#[derive(Diagnostic)]
#[diag("you might have meant to write `impl` instead of `fn`")]
pub(crate) struct FnTypoWithImpl {
    #[primary_span]
    #[suggestion(
        "replace `fn` with `impl` here",
        applicability = "maybe-incorrect",
        code = "impl",
        style = "verbose"
    )]
    pub fn_span: Span,
}

#[derive(Diagnostic)]
#[diag("expected identifier, found keyword `fn`")]
pub(crate) struct ExpectedFnPathFoundFnKeyword {
    #[primary_span]
    #[suggestion(
        "use `Fn` to refer to the trait",
        applicability = "machine-applicable",
        code = "Fn",
        style = "verbose"
    )]
    pub fn_token_span: Span,
}

#[derive(Diagnostic)]
#[diag("`Trait(...)` syntax does not support named parameters")]
pub(crate) struct FnPathFoundNamedParams {
    #[primary_span]
    #[suggestion("remove the parameter name", applicability = "machine-applicable", code = "")]
    pub named_param_span: Span,
}

#[derive(Diagnostic)]
#[diag("`Trait(...)` syntax does not support c_variadic parameters")]
pub(crate) struct PathFoundCVariadicParams {
    #[primary_span]
    #[suggestion("remove the `...`", applicability = "machine-applicable", code = "")]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("`Trait(...)` syntax does not support attributes in parameters")]
pub(crate) struct PathFoundAttributeInParams {
    #[primary_span]
    #[suggestion("remove the attributes", applicability = "machine-applicable", code = "")]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("path separator must be a double colon")]
pub(crate) struct PathSingleColon {
    #[primary_span]
    pub span: Span,

    #[suggestion(
        "use a double colon instead",
        applicability = "machine-applicable",
        code = ":",
        style = "verbose"
    )]
    pub suggestion: Span,
}

#[derive(Diagnostic)]
#[diag("path separator must be a double colon")]
pub(crate) struct PathTripleColon {
    #[primary_span]
    #[suggestion(
        "use a double colon instead",
        applicability = "maybe-incorrect",
        code = "",
        style = "verbose"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("statements are terminated with a semicolon")]
pub(crate) struct ColonAsSemi {
    #[primary_span]
    #[suggestion(
        "use a semicolon instead",
        applicability = "machine-applicable",
        code = ";",
        style = "verbose"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("where clauses are not allowed before tuple struct bodies")]
pub(crate) struct WhereClauseBeforeTupleStructBody {
    #[primary_span]
    #[label("unexpected where clause")]
    pub span: Span,
    #[label("while parsing this tuple struct")]
    pub name: Span,
    #[label("the struct body")]
    pub body: Span,
    #[subdiagnostic]
    pub sugg: Option<WhereClauseBeforeTupleStructBodySugg>,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "move the body before the where clause",
    applicability = "machine-applicable"
)]
pub(crate) struct WhereClauseBeforeTupleStructBodySugg {
    #[suggestion_part(code = "{snippet}")]
    pub left: Span,
    pub snippet: String,
    #[suggestion_part(code = "")]
    pub right: Span,
}

#[derive(Diagnostic)]
#[diag("`async fn` is not permitted in Rust 2015", code = E0670)]
pub(crate) struct AsyncFnIn2015 {
    #[primary_span]
    #[label("to use `async fn`, switch to Rust 2018 or later")]
    pub span: Span,
    #[subdiagnostic]
    pub help: HelpUseLatestEdition,
}

#[derive(Subdiagnostic)]
#[label("`async` blocks are only allowed in Rust 2018 or later")]
pub(crate) struct AsyncBlockIn2015 {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("`async move` blocks are only allowed in Rust 2018 or later")]
pub(crate) struct AsyncMoveBlockIn2015 {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("`async use` blocks are only allowed in Rust 2018 or later")]
pub(crate) struct AsyncUseBlockIn2015 {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("`async` trait bounds are only allowed in Rust 2018 or later")]
pub(crate) struct AsyncBoundModifierIn2015 {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub help: HelpUseLatestEdition,
}

#[derive(Diagnostic)]
#[diag("let chains are only allowed in Rust 2024 or later")]
pub(crate) struct LetChainPre2024 {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("cannot pass `self` by raw pointer")]
pub(crate) struct SelfArgumentPointer {
    #[primary_span]
    #[label("cannot pass `self` by raw pointer")]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("unexpected token: {$actual}")]
pub(crate) struct UnexpectedTokenAfterDot {
    #[primary_span]
    pub span: Span,
    pub actual: String,
}

#[derive(Diagnostic)]
#[diag("visibility `{$vis}` is not followed by an item")]
#[help("you likely meant to define an item, e.g., `{$vis} fn foo() {\"{}\"}`")]
pub(crate) struct VisibilityNotFollowedByItem {
    #[primary_span]
    #[label("the visibility")]
    pub span: Span,
    pub vis: Visibility,
}

#[derive(Diagnostic)]
#[diag("`default` is not followed by an item")]
#[note("only `fn`, `const`, `type`, or `impl` items may be prefixed by `default`")]
pub(crate) struct DefaultNotFollowedByItem {
    #[primary_span]
    #[label("the `default` qualifier")]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("`final` is not followed by an item")]
#[note("only associated functions in traits may be prefixed by `final`")]
pub(crate) struct FinalNotFollowedByItem {
    #[primary_span]
    #[label("the `final` qualifier")]
    pub span: Span,
}

#[derive(Diagnostic)]
pub(crate) enum MissingKeywordForItemDefinition {
    #[diag("missing `enum` for enum definition")]
    Enum {
        #[primary_span]
        span: Span,
        #[suggestion(
            "add `enum` here to parse `{$ident}` as an enum",
            style = "verbose",
            applicability = "maybe-incorrect",
            code = "enum "
        )]
        insert_span: Span,
        ident: Ident,
    },
    #[diag("missing `enum` or `struct` for enum or struct definition")]
    EnumOrStruct {
        #[primary_span]
        span: Span,
    },
    #[diag("missing `struct` for struct definition")]
    Struct {
        #[primary_span]
        span: Span,
        #[suggestion(
            "add `struct` here to parse `{$ident}` as a struct",
            style = "verbose",
            applicability = "maybe-incorrect",
            code = "struct "
        )]
        insert_span: Span,
        ident: Ident,
    },
    #[diag("missing `fn` for function definition")]
    Function {
        #[primary_span]
        span: Span,
        #[suggestion(
            "add `fn` here to parse `{$ident}` as a function",
            style = "verbose",
            applicability = "maybe-incorrect",
            code = "fn "
        )]
        insert_span: Span,
        ident: Ident,
    },
    #[diag("missing `fn` for method definition")]
    Method {
        #[primary_span]
        span: Span,
        #[suggestion(
            "add `fn` here to parse `{$ident}` as a method",
            style = "verbose",
            applicability = "maybe-incorrect",
            code = "fn "
        )]
        insert_span: Span,
        ident: Ident,
    },
    #[diag("missing `fn` or `struct` for function or struct definition")]
    Ambiguous {
        #[primary_span]
        span: Span,
        #[subdiagnostic]
        subdiag: Option<AmbiguousMissingKwForItemSub>,
    },
}

#[derive(Subdiagnostic)]
pub(crate) enum AmbiguousMissingKwForItemSub {
    #[suggestion(
        "if you meant to call a macro, try",
        applicability = "maybe-incorrect",
        code = "{snippet}!",
        style = "verbose"
    )]
    SuggestMacro {
        #[primary_span]
        span: Span,
        snippet: String,
    },
    #[help(
        "if you meant to call a macro, remove the `pub` and add a trailing `!` after the identifier"
    )]
    HelpMacro,
}
