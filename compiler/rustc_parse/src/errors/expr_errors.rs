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
#[diag("ambiguous `+` in a type")]
pub(crate) struct AmbiguousPlus {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub suggestion: AddParen,
}

#[derive(Diagnostic)]
#[diag("expected a path on the left-hand side of `+`", code = E0178)]
pub(crate) struct BadTypePlus {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub sub: BadTypePlusSub,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion("try adding parentheses", applicability = "machine-applicable")]
pub(crate) struct AddParen {
    #[suggestion_part(code = "(")]
    pub lo: Span,
    #[suggestion_part(code = ")")]
    pub hi: Span,
}

#[derive(Subdiagnostic)]
pub(crate) enum BadTypePlusSub {
    AddParen {
        #[subdiagnostic]
        suggestion: AddParen,
    },
    #[label("perhaps you forgot parentheses?")]
    ForgotParen {
        #[primary_span]
        span: Span,
    },
    #[label("expected a path")]
    ExpectPath {
        #[primary_span]
        span: Span,
    },
}

#[derive(Diagnostic)]
#[diag("missing angle brackets in associated item path")]
pub(crate) struct BadQPathStage2 {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub wrap: WrapType,
}

#[derive(Diagnostic)]
#[diag("inherent impls cannot be {$modifier_name}")]
#[note("only trait implementations may be annotated with `{$modifier}`")]
pub(crate) struct TraitImplModifierInInherentImpl {
    #[primary_span]
    pub span: Span,
    pub modifier: &'static str,
    pub modifier_name: &'static str,
    #[label("{$modifier_name} because of this")]
    pub modifier_span: Span,
    #[label("inherent impl for this type")]
    pub self_ty: Span,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "types that don't start with an identifier need to be surrounded with angle brackets in qualified paths",
    applicability = "machine-applicable"
)]
pub(crate) struct WrapType {
    #[suggestion_part(code = "<")]
    pub lo: Span,
    #[suggestion_part(code = ">")]
    pub hi: Span,
}

#[derive(Diagnostic)]
#[diag("expected item, found `;`")]
pub(crate) struct IncorrectSemicolon<'a> {
    #[primary_span]
    #[suggestion(
        "remove this semicolon",
        style = "verbose",
        code = "",
        applicability = "machine-applicable"
    )]
    pub span: Span,
    #[help("{$name} declarations are not followed by a semicolon")]
    pub show_help: bool,
    pub name: &'a str,
}

#[derive(Diagnostic)]
#[diag("incorrect use of `await`")]
pub(crate) struct IncorrectUseOfAwait {
    #[primary_span]
    #[suggestion(
        "`await` is not a method call, remove the parentheses",
        style = "verbose",
        code = "",
        applicability = "machine-applicable"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("incorrect use of `use`")]
pub(crate) struct IncorrectUseOfUse {
    #[primary_span]
    #[suggestion(
        "`use` is not a method call, try removing the parentheses",
        style = "verbose",
        code = "",
        applicability = "machine-applicable"
    )]
    pub span: Span,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion("`await` is a postfix operation", applicability = "machine-applicable")]
pub(crate) struct AwaitSuggestion {
    #[suggestion_part(code = "")]
    pub removal: Span,
    #[suggestion_part(code = ".await{question_mark}")]
    pub dot_await: Span,
    pub question_mark: &'static str,
}

#[derive(Diagnostic)]
#[diag("incorrect use of `await`")]
pub(crate) struct IncorrectAwait {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub suggestion: AwaitSuggestion,
}

#[derive(Diagnostic)]
#[diag("expected iterable, found keyword `in`")]
pub(crate) struct InInTypo {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "remove the duplicated `in`",
        code = "",
        style = "verbose",
        applicability = "machine-applicable"
    )]
    pub sugg_span: Span,
}

#[derive(Diagnostic)]
#[diag("invalid variable declaration")]
pub(crate) struct InvalidVariableDeclaration {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub sub: InvalidVariableDeclarationSub,
}

#[derive(Subdiagnostic)]
pub(crate) enum InvalidVariableDeclarationSub {
    #[suggestion(
        "switch the order of `mut` and `let`",
        style = "verbose",
        applicability = "maybe-incorrect",
        code = "let mut"
    )]
    SwitchMutLetOrder(#[primary_span] Span),
    #[suggestion(
        "missing keyword",
        applicability = "machine-applicable",
        style = "verbose",
        code = "let mut"
    )]
    MissingLet(#[primary_span] Span),
    #[suggestion(
        "write `let` instead of `auto` to introduce a new variable",
        style = "verbose",
        applicability = "machine-applicable",
        code = "let"
    )]
    UseLetNotAuto(#[primary_span] Span),
    #[suggestion(
        "write `let` instead of `var` to introduce a new variable",
        style = "verbose",
        applicability = "machine-applicable",
        code = "let"
    )]
    UseLetNotVar(#[primary_span] Span),
}

#[derive(Diagnostic)]
#[diag("switch the order of `ref` and `box`")]
pub(crate) struct SwitchRefBoxOrder {
    #[primary_span]
    #[suggestion(
        "swap them",
        applicability = "machine-applicable",
        style = "verbose",
        code = "box ref"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("invalid comparison operator `{$invalid}`")]
pub(crate) struct InvalidComparisonOperator {
    #[primary_span]
    pub span: Span,
    pub invalid: String,
    #[subdiagnostic]
    pub sub: InvalidComparisonOperatorSub,
}

#[derive(Subdiagnostic)]
pub(crate) enum InvalidComparisonOperatorSub {
    #[suggestion(
        "`{$invalid}` is not a valid comparison operator, use `{$correct}`",
        style = "verbose",
        applicability = "machine-applicable",
        code = "{correct}"
    )]
    Correctable {
        #[primary_span]
        span: Span,
        invalid: String,
        correct: String,
    },
    #[label("`<=>` is not a valid comparison operator, use `std::cmp::Ordering`")]
    Spaceship(#[primary_span] Span),
}

#[derive(Diagnostic)]
#[diag("`{$incorrect}` is not a logical operator")]
#[note("unlike in e.g., Python and PHP, `&&` and `||` are used for logical operators")]
pub(crate) struct InvalidLogicalOperator {
    #[primary_span]
    pub span: Span,
    pub incorrect: String,
    #[subdiagnostic]
    pub sub: InvalidLogicalOperatorSub,
}

#[derive(Subdiagnostic)]
pub(crate) enum InvalidLogicalOperatorSub {
    #[suggestion(
        "use `&&` to perform logical conjunction",
        style = "verbose",
        applicability = "machine-applicable",
        code = "&&"
    )]
    Conjunction(#[primary_span] Span),
    #[suggestion(
        "use `||` to perform logical disjunction",
        style = "verbose",
        applicability = "machine-applicable",
        code = "||"
    )]
    Disjunction(#[primary_span] Span),
}

#[derive(Diagnostic)]
#[diag("`~` cannot be used as a unary operator")]
pub(crate) struct TildeAsUnaryOperator(
    #[primary_span]
    #[suggestion(
        "use `!` to perform bitwise not",
        style = "verbose",
        applicability = "machine-applicable",
        code = "!"
    )]
    pub Span,
);

#[derive(Diagnostic)]
#[diag("unexpected {$negated_desc} after identifier")]
pub(crate) struct NotAsNegationOperator {
    #[primary_span]
    pub negated: Span,
    pub negated_desc: String,
    #[subdiagnostic]
    pub sub: NotAsNegationOperatorSub,
}

#[derive(Subdiagnostic)]
pub(crate) enum NotAsNegationOperatorSub {
    #[suggestion(
        "use `!` to perform logical negation or bitwise not",
        style = "verbose",
        applicability = "machine-applicable",
        code = "!"
    )]
    SuggestNotDefault(#[primary_span] Span),

    #[suggestion(
        "use `!` to perform bitwise not",
        style = "verbose",
        applicability = "machine-applicable",
        code = "!"
    )]
    SuggestNotBitwise(#[primary_span] Span),

    #[suggestion(
        "use `!` to perform logical negation",
        style = "verbose",
        applicability = "machine-applicable",
        code = "!"
    )]
    SuggestNotLogical(#[primary_span] Span),
}

#[derive(Diagnostic)]
#[diag("malformed loop label")]
pub(crate) struct MalformedLoopLabel {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "use the correct loop label format",
        applicability = "machine-applicable",
        code = "'",
        style = "verbose"
    )]
    pub suggestion: Span,
}

#[derive(Diagnostic)]
#[diag("borrow expressions cannot be annotated with lifetimes")]
pub(crate) struct LifetimeInBorrowExpression {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "remove the lifetime annotation",
        applicability = "machine-applicable",
        code = "",
        style = "verbose"
    )]
    #[label("annotated with lifetime here")]
    pub lifetime_span: Span,
}

#[derive(Diagnostic)]
#[diag("field expressions cannot have generic arguments")]
pub(crate) struct FieldExpressionWithGeneric(#[primary_span] pub Span);

#[derive(Diagnostic)]
#[diag("macros cannot use qualified paths")]
pub(crate) struct MacroInvocationWithQualifiedPath(#[primary_span] pub Span);

#[derive(Diagnostic)]
#[diag("expected `while`, `for`, `loop` or `{\"{\"}` after a label")]
pub(crate) struct UnexpectedTokenAfterLabel {
    #[primary_span]
    #[label("expected `while`, `for`, `loop` or `{\"{\"}` after a label")]
    pub span: Span,
    #[suggestion("consider removing the label", style = "verbose", code = "")]
    pub remove_label: Option<Span>,
    #[subdiagnostic]
    pub enclose_in_block: Option<UnexpectedTokenAfterLabelSugg>,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "consider enclosing expression in a block",
    applicability = "machine-applicable"
)]
pub(crate) struct UnexpectedTokenAfterLabelSugg {
    #[suggestion_part(code = "{{ ")]
    pub left: Span,
    #[suggestion_part(code = " }}")]
    pub right: Span,
}

#[derive(Diagnostic)]
#[diag("labeled expression must be followed by `:`")]
#[note("labels are used before loops and blocks, allowing e.g., `break 'label` to them")]
pub(crate) struct RequireColonAfterLabeledExpression {
    #[primary_span]
    pub span: Span,
    #[label("the label")]
    pub label: Span,
    #[suggestion(
        "add `:` after the label",
        style = "verbose",
        applicability = "machine-applicable",
        code = ": "
    )]
    pub label_end: Span,
}

#[derive(Diagnostic)]
#[diag("found removed `do catch` syntax")]
#[note("following RFC #2388, the new non-placeholder syntax is `try`")]
pub(crate) struct DoCatchSyntaxRemoved {
    #[primary_span]
    #[suggestion(
        "replace with the new syntax",
        applicability = "machine-applicable",
        code = "try",
        style = "verbose"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("float literals must have an integer part")]
pub(crate) struct FloatLiteralRequiresIntegerPart {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "must have an integer part",
        applicability = "machine-applicable",
        code = "0",
        style = "verbose"
    )]
    pub suggestion: Span,
}

#[derive(Diagnostic)]
#[diag("expected `;`, found `[`")]
pub(crate) struct MissingSemicolonBeforeArray {
    #[primary_span]
    pub open_delim: Span,
    #[suggestion(
        "consider adding `;` here",
        style = "verbose",
        applicability = "maybe-incorrect",
        code = ";"
    )]
    pub semicolon: Span,
}

#[derive(Diagnostic)]
#[diag("expected `..`, found `...`")]
pub(crate) struct MissingDotDot {
    #[primary_span]
    pub token_span: Span,
    #[suggestion(
        "use `..` to fill in the rest of the fields",
        applicability = "maybe-incorrect",
        code = "..",
        style = "verbose"
    )]
    pub sugg_span: Span,
}

#[derive(Diagnostic)]
#[diag("cannot use a `block` macro fragment here")]
pub(crate) struct InvalidBlockMacroSegment {
    #[primary_span]
    pub span: Span,
    #[label("the `block` fragment is within this context")]
    pub context: Span,
    #[subdiagnostic]
    pub wrap: WrapInExplicitBlock,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion("wrap this in another block", applicability = "machine-applicable")]
pub(crate) struct WrapInExplicitBlock {
    #[suggestion_part(code = "{{ ")]
    pub lo: Span,
    #[suggestion_part(code = " }}")]
    pub hi: Span,
}

#[derive(Diagnostic)]
#[diag("this `if` expression is missing a block after the condition")]
pub(crate) struct IfExpressionMissingThenBlock {
    #[primary_span]
    pub if_span: Span,
    #[subdiagnostic]
    pub missing_then_block_sub: IfExpressionMissingThenBlockSub,
    #[subdiagnostic]
    pub let_else_sub: Option<IfExpressionLetSomeSub>,
}

#[derive(Subdiagnostic)]
pub(crate) enum IfExpressionMissingThenBlockSub {
    #[help("this binary operation is possibly unfinished")]
    UnfinishedCondition(#[primary_span] Span),
    #[help("add a block here")]
    AddThenBlock(#[primary_span] Span),
}

#[derive(Diagnostic)]
#[diag("Rust has no ternary operator")]
pub(crate) struct TernaryOperator {
    #[primary_span]
    pub span: Span,
    /// If we have a span for the condition expression, suggest the if/else
    #[subdiagnostic]
    pub sugg: Option<TernaryOperatorSuggestion>,
    /// Otherwise, just print the suggestion message
    #[help("use an `if-else` expression instead")]
    pub no_sugg: bool,
}

#[derive(Subdiagnostic, Copy, Clone)]
#[multipart_suggestion(
    "use an `if-else` expression instead",
    applicability = "maybe-incorrect",
    style = "verbose"
)]
pub(crate) struct TernaryOperatorSuggestion {
    #[suggestion_part(code = "if ")]
    pub before_cond: Span,
    #[suggestion_part(code = "{{")]
    pub question: Span,
    #[suggestion_part(code = "}} else {{")]
    pub colon: Span,
    #[suggestion_part(code = " }}")]
    pub end: Span,
}

#[derive(Subdiagnostic)]
#[suggestion(
    "remove the `if` if you meant to write a `let...else` statement",
    applicability = "maybe-incorrect",
    code = "",
    style = "verbose"
)]
pub(crate) struct IfExpressionLetSomeSub {
    #[primary_span]
    pub if_span: Span,
}

#[derive(Diagnostic)]
#[diag("missing condition for `if` expression")]
pub(crate) struct IfExpressionMissingCondition {
    #[primary_span]
    #[label("expected condition here")]
    pub if_span: Span,
    #[label(
        "if this block is the condition of the `if` expression, then it must be followed by another block"
    )]
    pub block_span: Span,
}

#[derive(Diagnostic)]
#[diag("expected expression, found `let` statement")]
#[note("only supported directly in conditions of `if` and `while` expressions")]
pub(crate) struct ExpectedExpressionFoundLet {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub reason: ForbiddenLetReason,
    #[subdiagnostic]
    pub missing_let: Option<MaybeMissingLet>,
    #[subdiagnostic]
    pub comparison: Option<MaybeComparison>,
}

#[derive(Diagnostic)]
#[diag("let-chain with missing `let`")]
pub(crate) struct LetChainMissingLet {
    #[primary_span]
    pub span: Span,
    #[label("expected `let` expression, found assignment")]
    pub label_span: Span,
    #[label("let expression later in the condition")]
    pub rhs_span: Span,
    #[suggestion(
        "add `let` before the expression",
        applicability = "maybe-incorrect",
        code = "let ",
        style = "verbose"
    )]
    pub sug_span: Span,
}

#[derive(Diagnostic)]
#[diag("`||` operators are not supported in let chain conditions")]
pub(crate) struct OrInLetChain {
    #[primary_span]
    pub span: Span,
}

#[derive(Subdiagnostic, Clone, Copy)]
#[multipart_suggestion(
    "you might have meant to continue the let-chain",
    applicability = "maybe-incorrect",
    style = "verbose"
)]
pub(crate) struct MaybeMissingLet {
    #[suggestion_part(code = "let ")]
    pub span: Span,
}

#[derive(Subdiagnostic, Clone, Copy)]
#[multipart_suggestion(
    "you might have meant to compare for equality",
    applicability = "maybe-incorrect",
    style = "verbose"
)]
pub(crate) struct MaybeComparison {
    #[suggestion_part(code = "=")]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("expected `=`, found `==`")]
pub(crate) struct ExpectedEqForLetExpr {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "consider using `=` here",
        applicability = "maybe-incorrect",
        code = "=",
        style = "verbose"
    )]
    pub sugg_span: Span,
}

#[derive(Diagnostic)]
#[diag("expected `{\"{\"}`, found {$first_tok}")]
pub(crate) struct ExpectedElseBlock {
    #[primary_span]
    pub first_tok_span: Span,
    pub first_tok: String,
    #[label("expected an `if` or a block after this `else`")]
    pub else_span: Span,
    #[suggestion(
        "add an `if` if this is the condition of a chained `else if` statement",
        applicability = "maybe-incorrect",
        code = "if ",
        style = "verbose"
    )]
    pub condition_start: Span,
}

#[derive(Diagnostic)]
#[diag("expected one of `,`, `:`, or `{\"}\"}`, found `{$token}`")]
pub(crate) struct ExpectedStructField {
    #[primary_span]
    #[label("expected one of `,`, `:`, or `{\"}\"}`")]
    pub span: Span,
    pub token: Token,
    #[label("while parsing this struct field")]
    pub ident_span: Span,
}

#[derive(Diagnostic)]
#[diag("outer attributes are not allowed on `if` and `else` branches")]
pub(crate) struct OuterAttributeNotAllowedOnIfElse {
    #[primary_span]
    pub last: Span,

    #[label("the attributes are attached to this branch")]
    pub branch_span: Span,

    #[label("the branch belongs to this `{$ctx}`")]
    pub ctx_span: Span,
    pub ctx: String,

    #[suggestion(
        "remove the attributes",
        applicability = "machine-applicable",
        code = "",
        style = "verbose"
    )]
    pub attributes: Span,
}

#[derive(Diagnostic)]
#[diag("missing `in` in `for` loop")]
pub(crate) struct MissingInInForLoop {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub sub: MissingInInForLoopSub,
}

#[derive(Subdiagnostic)]
pub(crate) enum MissingInInForLoopSub {
    // User wrote `for pat of expr {}`
    // Has been misleading, at least in the past (closed Issue #48492), thus maybe-incorrect
    #[suggestion(
        "try using `in` here instead",
        style = "verbose",
        applicability = "maybe-incorrect",
        code = "in"
    )]
    InNotOf(#[primary_span] Span),
    // User wrote `for pat = expr {}`
    #[suggestion(
        "try using `in` here instead",
        style = "verbose",
        applicability = "maybe-incorrect",
        code = "in"
    )]
    InNotEq(#[primary_span] Span),
    #[suggestion(
        "try adding `in` here",
        style = "verbose",
        applicability = "maybe-incorrect",
        code = " in "
    )]
    AddIn(#[primary_span] Span),
}

#[derive(Diagnostic)]
#[diag("missing expression to iterate on in `for` loop")]
pub(crate) struct MissingExpressionInForLoop {
    #[primary_span]
    #[suggestion(
        "try adding an expression to the `for` loop",
        code = "/* expression */ ",
        applicability = "has-placeholders",
        style = "verbose"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("`{$loop_kind}...else` loops are not supported")]
#[note(
    "consider moving this `else` clause to a separate `if` statement and use a `bool` variable to control if it should run"
)]
pub(crate) struct LoopElseNotSupported {
    #[primary_span]
    pub span: Span,
    pub loop_kind: &'static str,
    #[label("`else` is attached to this loop")]
    pub loop_kw: Span,
}

#[derive(Diagnostic)]
#[diag("expected `,` following `match` arm")]
pub(crate) struct MissingCommaAfterMatchArm {
    #[primary_span]
    #[suggestion(
        "missing a comma here to end this `match` arm",
        applicability = "machine-applicable",
        code = ",",
        style = "verbose"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("keyword `catch` cannot follow a `try` block")]
#[help("try using `match` on the result of the `try` block instead")]
pub(crate) struct CatchAfterTry {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("cannot use a comma after the base struct")]
#[note("the base struct must always be the last field")]
pub(crate) struct CommaAfterBaseStruct {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "remove this comma",
        style = "verbose",
        applicability = "machine-applicable",
        code = ""
    )]
    pub comma: Span,
}

#[derive(Diagnostic)]
#[diag("expected `:`, found `=`")]
pub(crate) struct EqFieldInit {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "replace equals symbol with a colon",
        applicability = "machine-applicable",
        code = ":",
        style = "verbose"
    )]
    pub eq: Span,
}

#[derive(Diagnostic)]
#[diag("unexpected token: `...`")]
pub(crate) struct DotDotDot {
    #[primary_span]
    #[suggestion(
        "use `..` for an exclusive range",
        applicability = "maybe-incorrect",
        code = "..",
        style = "verbose"
    )]
    #[suggestion(
        "or `..=` for an inclusive range",
        applicability = "maybe-incorrect",
        code = "..=",
        style = "verbose"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("unexpected token: `<-`")]
pub(crate) struct LeftArrowOperator {
    #[primary_span]
    #[suggestion(
        "if you meant to write a comparison against a negative value, add a space in between `<` and `-`",
        applicability = "maybe-incorrect",
        code = "< -",
        style = "verbose"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("expected pattern, found `let`")]
pub(crate) struct RemoveLet {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "remove the unnecessary `let` keyword",
        applicability = "machine-applicable",
        code = "",
        style = "verbose"
    )]
    pub suggestion: Span,
}

#[derive(Diagnostic)]
#[diag("unexpected `==`")]
pub(crate) struct UseEqInstead {
    #[primary_span]
    #[suggestion(
        "try using `=` instead",
        style = "verbose",
        applicability = "machine-applicable",
        code = "="
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("expected { \"`{}`\" }, found `;`")]
pub(crate) struct UseEmptyBlockNotSemi {
    #[primary_span]
    #[suggestion(
        r#"try using { "`{}`" } instead"#,
        style = "hidden",
        applicability = "machine-applicable",
        code = "{{}}"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("`<` is interpreted as a start of generic arguments for `{$type}`, not a comparison")]
pub(crate) struct ComparisonInterpretedAsGeneric {
    #[primary_span]
    #[label("not interpreted as comparison")]
    pub comparison: Span,
    pub r#type: Path,
    #[label("interpreted as generic arguments")]
    pub args: Span,
    #[subdiagnostic]
    pub suggestion: ComparisonInterpretedAsGenericSugg,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion("try comparing the cast value", applicability = "machine-applicable")]
pub(crate) struct ComparisonInterpretedAsGenericSugg {
    #[suggestion_part(code = "(")]
    pub left: Span,
    #[suggestion_part(code = ")")]
    pub right: Span,
}

#[derive(Diagnostic)]
#[diag("`<<` is interpreted as a start of generic arguments for `{$type}`, not a shift")]
pub(crate) struct ShiftInterpretedAsGeneric {
    #[primary_span]
    #[label("not interpreted as shift")]
    pub shift: Span,
    pub r#type: Path,
    #[label("interpreted as generic arguments")]
    pub args: Span,
    #[subdiagnostic]
    pub suggestion: ShiftInterpretedAsGenericSugg,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion("try shifting the cast value", applicability = "machine-applicable")]
pub(crate) struct ShiftInterpretedAsGenericSugg {
    #[suggestion_part(code = "(")]
    pub left: Span,
    #[suggestion_part(code = ")")]
    pub right: Span,
}

#[derive(Diagnostic)]
#[diag("expected expression, found `{$token}`")]
pub(crate) struct FoundExprWouldBeStmt {
    #[primary_span]
    #[label("expected expression")]
    pub span: Span,
    pub token: Token,
    #[subdiagnostic]
    pub suggestion: ExprParenthesesNeeded,
}

#[derive(Diagnostic)]
#[diag("extra characters after frontmatter close are not allowed")]
pub(crate) struct FrontmatterExtraCharactersAfterClose {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("invalid infostring for frontmatter")]
#[note("frontmatter infostrings must be a single identifier immediately following the opening")]
pub(crate) struct FrontmatterInvalidInfostring {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("invalid preceding whitespace for frontmatter opening")]
pub(crate) struct FrontmatterInvalidOpeningPrecedingWhitespace {
    #[primary_span]
    pub span: Span,
    #[note("frontmatter opening should not be preceded by whitespace")]
    pub note_span: Span,
}

#[derive(Diagnostic)]
#[diag("unclosed frontmatter")]
pub(crate) struct FrontmatterUnclosed {
    #[primary_span]
    pub span: Span,
    #[note("frontmatter opening here was not closed")]
    pub note_span: Span,
}

#[derive(Diagnostic)]
#[diag("invalid preceding whitespace for frontmatter close")]
pub(crate) struct FrontmatterInvalidClosingPrecedingWhitespace {
    #[primary_span]
    pub span: Span,
    #[note("frontmatter close should not be preceded by whitespace")]
    pub note_span: Span,
}

#[derive(Diagnostic)]
#[diag("frontmatter close does not match the opening")]
pub(crate) struct FrontmatterLengthMismatch {
    #[primary_span]
    pub span: Span,
    #[label("the opening here has {$len_opening} dashes...")]
    pub opening: Span,
    #[label("...while the close has {$len_close} dashes")]
    pub close: Span,
    pub len_opening: usize,
    pub len_close: usize,
}

#[derive(Diagnostic)]
#[diag(
    "too many `-` symbols: frontmatter openings may be delimited by up to 255 `-` symbols, but found {$len_opening}"
)]
pub(crate) struct FrontmatterTooManyDashes {
    pub len_opening: usize,
}

#[derive(Diagnostic)]
#[diag("bare CR not allowed in frontmatter")]
pub(crate) struct BareCrFrontmatter {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("leading `+` is not supported")]
pub(crate) struct LeadingPlusNotSupported {
    #[primary_span]
    #[label("unexpected `+`")]
    pub span: Span,
    #[suggestion(
        "try removing the `+`",
        style = "verbose",
        code = "",
        applicability = "machine-applicable"
    )]
    pub remove_plus: Option<Span>,
    #[subdiagnostic]
    pub add_parentheses: Option<ExprParenthesesNeeded>,
}

#[derive(Diagnostic)]
#[diag("invalid `struct` delimiters or `fn` call arguments")]
pub(crate) struct ParenthesesWithStructFields {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub braces_for_struct: BracesForStructLiteral,
    #[subdiagnostic]
    pub no_fields_for_fn: NoFieldsForFnCall,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "if `{$type}` is a struct, use braces as delimiters",
    applicability = "maybe-incorrect"
)]
pub(crate) struct BracesForStructLiteral {
    pub r#type: Path,
    #[suggestion_part(code = " {{ ")]
    pub first: Span,
    #[suggestion_part(code = " }}")]
    pub second: Span,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "if `{$type}` is a function, use the arguments directly",
    applicability = "maybe-incorrect"
)]
pub(crate) struct NoFieldsForFnCall {
    pub r#type: Path,
    #[suggestion_part(code = "")]
    pub fields: Vec<Span>,
}

#[derive(Diagnostic)]
#[diag(
    "parentheses are required around this expression to avoid confusion with a labeled break expression"
)]
pub(crate) struct LabeledLoopInBreak {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub sub: WrapInParentheses,
}

#[derive(Subdiagnostic)]
pub(crate) enum WrapInParentheses {
    #[multipart_suggestion(
        "wrap the expression in parentheses",
        applicability = "machine-applicable"
    )]
    Expression {
        #[suggestion_part(code = "(")]
        left: Span,
        #[suggestion_part(code = ")")]
        right: Span,
    },
    #[multipart_suggestion(
        "use parentheses instead of braces for this macro",
        applicability = "machine-applicable"
    )]
    MacroArgs {
        #[suggestion_part(code = "(")]
        left: Span,
        #[suggestion_part(code = ")")]
        right: Span,
    },
}

#[derive(Diagnostic)]
#[diag("this is a block expression, not an array")]
pub(crate) struct ArrayBracketsInsteadOfBraces {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub sub: ArrayBracketsInsteadOfBracesSugg,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "to make an array, use square brackets instead of curly braces",
    applicability = "maybe-incorrect"
)]
pub(crate) struct ArrayBracketsInsteadOfBracesSugg {
    #[suggestion_part(code = "[")]
    pub left: Span,
    #[suggestion_part(code = "]")]
    pub right: Span,
}

#[derive(Diagnostic)]
#[diag("`match` arm body without braces")]
pub(crate) struct MatchArmBodyWithoutBraces {
    #[primary_span]
    #[label(
        "{$num_statements ->
            [one] this statement is not surrounded by a body
            *[other] these statements are not surrounded by a body
        }"
    )]
    pub statements: Span,
    #[label("while parsing the `match` arm starting here")]
    pub arrow: Span,
    pub num_statements: usize,
    #[subdiagnostic]
    pub sub: MatchArmBodyWithoutBracesSugg,
}

#[derive(Diagnostic)]
#[diag("unexpected `=` after inclusive range")]
#[note("inclusive ranges end with a single equals sign (`..=`)")]
pub(crate) struct InclusiveRangeExtraEquals {
    #[primary_span]
    #[suggestion(
        "use `..=` instead",
        style = "verbose",
        code = "..=",
        applicability = "maybe-incorrect"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("unexpected `>` after inclusive range")]
pub(crate) struct InclusiveRangeMatchArrow {
    #[primary_span]
    pub arrow: Span,
    #[label("this is parsed as an inclusive range `..=`")]
    pub span: Span,
    #[suggestion(
        "add a space between the pattern and `=>`",
        style = "verbose",
        code = " ",
        applicability = "machine-applicable"
    )]
    pub after_pat: Span,
}

#[derive(Diagnostic)]
#[diag("inclusive range with no end", code = E0586)]
#[note("inclusive ranges must be bounded at the end (`..=b` or `a..=b`)")]
pub(crate) struct InclusiveRangeNoEnd {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "use `..` instead",
        code = "",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub suggestion: Span,
}

#[derive(Subdiagnostic)]
pub(crate) enum MatchArmBodyWithoutBracesSugg {
    #[multipart_suggestion(
        "surround the {$num_statements ->
            [one] statement
            *[other] statements
        } with a body",
        applicability = "machine-applicable"
    )]
    AddBraces {
        #[suggestion_part(code = "{{ ")]
        left: Span,
        #[suggestion_part(code = " }}")]
        right: Span,
        num_statements: usize,
    },
    #[suggestion(
        "replace `;` with `,` to end a `match` arm expression",
        code = ",",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    UseComma {
        #[primary_span]
        semicolon: Span,
    },
}

#[derive(Diagnostic)]
#[diag("struct literals are not allowed here")]
pub(crate) struct StructLiteralNotAllowedHere {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub sub: StructLiteralNotAllowedHereSugg,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "surround the struct literal with parentheses",
    applicability = "machine-applicable"
)]
pub(crate) struct StructLiteralNotAllowedHereSugg {
    #[suggestion_part(code = "(")]
    pub left: Span,
    #[suggestion_part(code = ")")]
    pub right: Span,
}
