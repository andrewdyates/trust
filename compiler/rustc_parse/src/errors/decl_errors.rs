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
#[diag("missing parameters for function definition")]
pub(crate) struct MissingFnParams {
    #[primary_span]
    #[suggestion(
        "add a parameter list",
        code = "()",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("invalid path separator in function definition")]
pub(crate) struct InvalidPathSepInFnDefinition {
    #[primary_span]
    #[suggestion(
        "remove invalid path separator",
        code = "",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("missing trait in a trait impl")]
pub(crate) struct MissingTraitInTraitImpl {
    #[primary_span]
    #[suggestion(
        "add a trait here",
        code = " Trait ",
        applicability = "has-placeholders",
        style = "verbose"
    )]
    pub span: Span,
    #[suggestion(
        "for an inherent impl, drop this `for`",
        code = "",
        applicability = "maybe-incorrect",
        style = "verbose"
    )]
    pub for_span: Span,
}

#[derive(Diagnostic)]
#[diag("missing `for` in a trait impl")]
pub(crate) struct MissingForInTraitImpl {
    #[primary_span]
    #[suggestion(
        "add `for` here",
        style = "verbose",
        code = " for ",
        applicability = "machine-applicable"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("expected a trait, found type")]
pub(crate) struct ExpectedTraitInTraitImplFoundType {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("unexpected `impl` keyword")]
pub(crate) struct ExtraImplKeywordInTraitImpl {
    #[primary_span]
    #[suggestion(
        "remove the extra `impl`",
        code = "",
        applicability = "maybe-incorrect",
        style = "short"
    )]
    pub extra_impl_kw: Span,
    #[note("this is parsed as an `impl Trait` type, but a trait is expected at this position")]
    pub impl_trait_span: Span,
}

#[derive(Diagnostic)]
#[diag("bounds are not allowed on trait aliases")]
pub(crate) struct BoundsNotAllowedOnTraitAliases {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("trait aliases cannot be `auto`")]
pub(crate) struct TraitAliasCannotBeAuto {
    #[primary_span]
    #[label("trait aliases cannot be `auto`")]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("trait aliases cannot be `unsafe`")]
pub(crate) struct TraitAliasCannotBeUnsafe {
    #[primary_span]
    #[label("trait aliases cannot be `unsafe`")]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("trait aliases cannot be `impl`-restricted")]
pub(crate) struct TraitAliasCannotBeImplRestricted {
    #[primary_span]
    #[label("trait aliases cannot be `impl`-restricted")]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("associated `static` items are not allowed")]
pub(crate) struct AssociatedStaticItemNotAllowed {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("crate name using dashes are not valid in `extern crate` statements")]
pub(crate) struct ExternCrateNameWithDashes {
    #[primary_span]
    #[label("dash-separated idents are not valid")]
    pub span: Span,
    #[subdiagnostic]
    pub sugg: ExternCrateNameWithDashesSugg,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "if the original crate name uses dashes you need to use underscores in the code",
    applicability = "machine-applicable"
)]
pub(crate) struct ExternCrateNameWithDashesSugg {
    #[suggestion_part(code = "_")]
    pub dashes: Vec<Span>,
}

#[derive(Diagnostic)]
#[diag("extern items cannot be `const`")]
#[note("for more information, visit https://doc.rust-lang.org/std/keyword.extern.html")]
pub(crate) struct ExternItemCannotBeConst {
    #[primary_span]
    pub ident_span: Span,
    #[suggestion(
        "try using a static value",
        code = "static ",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub const_span: Option<Span>,
}

#[derive(Diagnostic)]
#[diag("const globals cannot be mutable")]
pub(crate) struct ConstGlobalCannotBeMutable {
    #[primary_span]
    #[label("cannot be mutable")]
    pub ident_span: Span,
    #[suggestion(
        "you might want to declare a static instead",
        code = "static",
        style = "verbose",
        applicability = "maybe-incorrect"
    )]
    pub const_span: Span,
}

#[derive(Diagnostic)]
#[diag("missing type for `{$kind}` item")]
pub(crate) struct MissingConstType {
    #[primary_span]
    #[suggestion(
        "provide a type for the item",
        code = "{colon} <type>",
        style = "verbose",
        applicability = "has-placeholders"
    )]
    pub span: Span,

    pub kind: &'static str,
    pub colon: &'static str,
}

#[derive(Diagnostic)]
#[diag("`enum` and `struct` are mutually exclusive")]
pub(crate) struct EnumStructMutuallyExclusive {
    #[primary_span]
    #[suggestion(
        "replace `enum struct` with",
        code = "enum",
        style = "verbose",
        applicability = "machine-applicable"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
pub(crate) enum UnexpectedTokenAfterStructName {
    #[diag(
        "expected `where`, `{\"{\"}`, `(`, or `;` after struct name, found reserved identifier `{$token}`"
    )]
    ReservedIdentifier {
        #[primary_span]
        #[label("expected `where`, `{\"{\"}`, `(`, or `;` after struct name")]
        span: Span,
        token: Token,
    },
    #[diag("expected `where`, `{\"{\"}`, `(`, or `;` after struct name, found keyword `{$token}`")]
    Keyword {
        #[primary_span]
        #[label("expected `where`, `{\"{\"}`, `(`, or `;` after struct name")]
        span: Span,
        token: Token,
    },
    #[diag(
        "expected `where`, `{\"{\"}`, `(`, or `;` after struct name, found reserved keyword `{$token}`"
    )]
    ReservedKeyword {
        #[primary_span]
        #[label("expected `where`, `{\"{\"}`, `(`, or `;` after struct name")]
        span: Span,
        token: Token,
    },
    #[diag(
        "expected `where`, `{\"{\"}`, `(`, or `;` after struct name, found doc comment `{$token}`"
    )]
    DocComment {
        #[primary_span]
        #[label("expected `where`, `{\"{\"}`, `(`, or `;` after struct name")]
        span: Span,
        token: Token,
    },
    #[diag("expected `where`, `{\"{\"}`, `(`, or `;` after struct name, found metavar")]
    MetaVar {
        #[primary_span]
        #[label("expected `where`, `{\"{\"}`, `(`, or `;` after struct name")]
        span: Span,
    },
    #[diag("expected `where`, `{\"{\"}`, `(`, or `;` after struct name, found `{$token}`")]
    Other {
        #[primary_span]
        #[label("expected `where`, `{\"{\"}`, `(`, or `;` after struct name")]
        span: Span,
        token: Token,
    },
}

impl UnexpectedTokenAfterStructName {
    pub(crate) fn new(span: Span, token: Token) -> Self {
        match TokenDescription::from_token(&token) {
            Some(TokenDescription::ReservedIdentifier) => Self::ReservedIdentifier { span, token },
            Some(TokenDescription::Keyword) => Self::Keyword { span, token },
            Some(TokenDescription::ReservedKeyword) => Self::ReservedKeyword { span, token },
            Some(TokenDescription::DocComment) => Self::DocComment { span, token },
            Some(TokenDescription::MetaVar(_)) => Self::MetaVar { span },
            None => Self::Other { span, token },
        }
    }
}

#[derive(Diagnostic)]
#[diag("unexpected keyword `Self` in generic parameters")]
#[note("you cannot use `Self` as a generic parameter because it is reserved for associated items")]
pub(crate) struct UnexpectedSelfInGenericParameters {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("unexpected default lifetime parameter")]
pub(crate) struct UnexpectedDefaultValueForLifetimeInGenericParameters {
    #[primary_span]
    #[label("lifetime parameters cannot have default values")]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("cannot define duplicate `where` clauses on an item")]
pub(crate) struct MultipleWhereClauses {
    #[primary_span]
    pub span: Span,
    #[label("previous `where` clause starts here")]
    pub previous: Span,
    #[suggestion(
        "consider joining the two `where` clauses into one",
        style = "verbose",
        code = ",",
        applicability = "maybe-incorrect"
    )]
    pub between: Span,
}

#[derive(Diagnostic)]
pub(crate) enum UnexpectedNonterminal {
    #[diag("expected an item keyword")]
    Item(#[primary_span] Span),
    #[diag("expected a statement")]
    Statement(#[primary_span] Span),
    #[diag("expected ident, found `{$token}`")]
    Ident {
        #[primary_span]
        span: Span,
        token: Token,
    },
    #[diag("expected a lifetime, found `{$token}`")]
    Lifetime {
        #[primary_span]
        span: Span,
        token: Token,
    },
}

#[derive(Diagnostic)]
pub(crate) enum TopLevelOrPatternNotAllowed {
    #[diag("`let` bindings require top-level or-patterns in parentheses")]
    LetBinding {
        #[primary_span]
        span: Span,
        #[subdiagnostic]
        sub: Option<TopLevelOrPatternNotAllowedSugg>,
    },
    #[diag("function parameters require top-level or-patterns in parentheses")]
    FunctionParameter {
        #[primary_span]
        span: Span,
        #[subdiagnostic]
        sub: Option<TopLevelOrPatternNotAllowedSugg>,
    },
}

#[derive(Diagnostic)]
#[diag("`{$ident}` cannot be a raw identifier")]
pub(crate) struct CannotBeRawIdent {
    #[primary_span]
    pub span: Span,
    pub ident: Symbol,
}

#[derive(Diagnostic)]
#[diag("`{$ident}` cannot be a raw lifetime")]
pub(crate) struct CannotBeRawLifetime {
    #[primary_span]
    pub span: Span,
    pub ident: Symbol,
}

#[derive(Diagnostic)]
#[diag("lifetimes cannot use keyword names")]
pub(crate) struct KeywordLifetime {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("labels cannot use keyword names")]
pub(crate) struct KeywordLabel {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag(
    "bare CR not allowed in {$block ->
        [true] block doc-comment
        *[false] doc-comment
    }"
)]
pub(crate) struct CrDocComment {
    #[primary_span]
    pub span: Span,
    pub block: bool,
}

#[derive(Diagnostic)]
#[diag("no valid digits found for number", code = E0768)]
pub(crate) struct NoDigitsLiteral {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("invalid digit for a base {$base} literal")]
pub(crate) struct InvalidDigitLiteral {
    #[primary_span]
    pub span: Span,
    pub base: u32,
}

#[derive(Diagnostic)]
#[diag("expected at least one digit in exponent")]
pub(crate) struct EmptyExponentFloat {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("{$base} float literal is not supported")]
pub(crate) struct FloatLiteralUnsupportedBase {
    #[primary_span]
    pub span: Span,
    pub base: &'static str,
}

#[derive(Diagnostic)]
#[diag("prefix `{$prefix}` is unknown")]
#[note("prefixed identifiers and literals are reserved since Rust 2021")]
pub(crate) struct UnknownPrefix<'a> {
    #[primary_span]
    #[label("unknown prefix")]
    pub span: Span,
    pub prefix: &'a str,
    #[subdiagnostic]
    pub sugg: Option<UnknownPrefixSugg>,
}

#[derive(Subdiagnostic)]
#[note("macros cannot expand to {$adt_ty} fields")]
pub(crate) struct MacroExpandsToAdtField<'a> {
    pub adt_ty: &'a str,
}

#[derive(Subdiagnostic)]
pub(crate) enum UnknownPrefixSugg {
    #[suggestion(
        "use `br` for a raw byte string",
        code = "br",
        applicability = "maybe-incorrect",
        style = "verbose"
    )]
    UseBr(#[primary_span] Span),
    #[suggestion(
        "use `cr` for a raw C-string",
        code = "cr",
        applicability = "maybe-incorrect",
        style = "verbose"
    )]
    UseCr(#[primary_span] Span),
    #[suggestion(
        "consider inserting whitespace here",
        code = " ",
        applicability = "maybe-incorrect",
        style = "verbose"
    )]
    Whitespace(#[primary_span] Span),
    #[multipart_suggestion(
        "if you meant to write a string literal, use double quotes",
        applicability = "maybe-incorrect",
        style = "verbose"
    )]
    MeantStr {
        #[suggestion_part(code = "\"")]
        start: Span,
        #[suggestion_part(code = "\"")]
        end: Span,
    },
}

#[derive(Diagnostic)]
#[diag("reserved multi-hash token is forbidden")]
#[note("sequences of two or more # are reserved for future use since Rust 2024")]
pub(crate) struct ReservedMultihash {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub sugg: Option<GuardedStringSugg>,
}
#[derive(Diagnostic)]
#[diag("invalid string literal")]
#[note("unprefixed guarded string literals are reserved for future use since Rust 2024")]
pub(crate) struct ReservedString {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub sugg: Option<GuardedStringSugg>,
}
#[derive(Subdiagnostic)]
#[suggestion(
    "consider inserting whitespace here",
    code = " ",
    applicability = "maybe-incorrect",
    style = "verbose"
)]
pub(crate) struct GuardedStringSugg(#[primary_span] pub Span);

#[derive(Diagnostic)]
#[diag(
    "too many `#` symbols: raw strings may be delimited by up to 255 `#` symbols, but found {$num}"
)]
pub(crate) struct TooManyHashes {
    #[primary_span]
    pub span: Span,
    pub num: u32,
}

#[derive(Diagnostic)]
#[diag("unknown start of token: {$escaped}")]
pub(crate) struct UnknownTokenStart {
    #[primary_span]
    pub span: Span,
    pub escaped: String,
    #[subdiagnostic]
    pub sugg: Option<TokenSubstitution>,
    #[help(
        "source files must contain UTF-8 encoded text, unexpected null bytes might occur when a different encoding is used"
    )]
    pub null: bool,
    #[subdiagnostic]
    pub repeat: Option<UnknownTokenRepeat>,
    #[help("invisible characters like '{$escaped}' are not usually visible in text editors")]
    pub invisible: bool,
}

#[derive(Subdiagnostic)]
pub(crate) enum TokenSubstitution {
    #[suggestion(
        "Unicode characters '“' (Left Double Quotation Mark) and '”' (Right Double Quotation Mark) look like '{$ascii_str}' ({$ascii_name}), but are not",
        code = "{suggestion}",
        applicability = "maybe-incorrect",
        style = "verbose"
    )]
    DirectedQuotes {
        #[primary_span]
        span: Span,
        suggestion: String,
        ascii_str: &'static str,
        ascii_name: &'static str,
    },
    #[suggestion(
        "Unicode character '{$ch}' ({$u_name}) looks like '{$ascii_str}' ({$ascii_name}), but it is not",
        code = "{suggestion}",
        applicability = "maybe-incorrect",
        style = "verbose"
    )]
    Other {
        #[primary_span]
        span: Span,
        suggestion: String,
        ch: String,
        u_name: &'static str,
        ascii_str: &'static str,
        ascii_name: &'static str,
    },
}

#[derive(Subdiagnostic)]
#[note(
    "character appears {$repeats ->
        [one] once more
        *[other] {$repeats} more times
    }"
)]
pub(crate) struct UnknownTokenRepeat {
    pub repeats: usize,
}

#[derive(Diagnostic)]
pub(crate) enum UnescapeError {
    #[diag("invalid unicode character escape")]
    #[help(
        "unicode escape must {$surrogate ->
            [true] not be a surrogate
            *[false] be at most 10FFFF
        }"
    )]
    InvalidUnicodeEscape {
        #[primary_span]
        #[label("invalid escape")]
        span: Span,
        surrogate: bool,
    },
    #[diag(
        "{$byte ->
            [true] byte
            *[false] character
        } constant must be escaped: `{$escaped_msg}`"
    )]
    EscapeOnlyChar {
        #[primary_span]
        span: Span,
        #[suggestion(
            "escape the character",
            applicability = "machine-applicable",
            code = "{escaped_sugg}",
            style = "verbose"
        )]
        char_span: Span,
        escaped_sugg: String,
        escaped_msg: String,
        byte: bool,
    },
    #[diag(
        r#"{$double_quotes ->
            [true] bare CR not allowed in string, use `\r` instead
            *[false] character constant must be escaped: `\r`
        }"#
    )]
    BareCr {
        #[primary_span]
        #[suggestion(
            "escape the character",
            applicability = "machine-applicable",
            code = "\\r",
            style = "verbose"
        )]
        span: Span,
        double_quotes: bool,
    },
    #[diag("bare CR not allowed in raw string")]
    BareCrRawString(#[primary_span] Span),
    #[diag("numeric character escape is too short")]
    TooShortHexEscape(#[primary_span] Span),
    #[diag(
        "invalid character in {$is_hex ->
            [true] numeric character
            *[false] unicode
        } escape: `{$ch}`"
    )]
    InvalidCharInEscape {
        #[primary_span]
        #[label(
            "invalid character in {$is_hex ->
                [true] numeric character
                *[false] unicode
            } escape"
        )]
        span: Span,
        is_hex: bool,
        ch: String,
    },
    #[diag("invalid start of unicode escape: `_`")]
    LeadingUnderscoreUnicodeEscape {
        #[primary_span]
        #[label("invalid start of unicode escape")]
        span: Span,
        ch: String,
    },
    #[diag("overlong unicode escape")]
    OverlongUnicodeEscape(
        #[primary_span]
        #[label("must have at most 6 hex digits")]
        Span,
    ),
    #[diag("unterminated unicode escape")]
    UnclosedUnicodeEscape(
        #[primary_span]
        #[label(r#"missing a closing `{"}"}`"#)]
        Span,
        #[suggestion(
            "terminate the unicode escape",
            code = "}}",
            applicability = "maybe-incorrect",
            style = "verbose"
        )]
        Span,
    ),
    #[diag("incorrect unicode escape sequence")]
    NoBraceInUnicodeEscape {
        #[primary_span]
        span: Span,
        #[label("incorrect unicode escape sequence")]
        label: Option<Span>,
        #[subdiagnostic]
        sub: NoBraceUnicodeSub,
    },
    #[diag("unicode escape in byte string")]
    #[help("unicode escape sequences cannot be used as a byte or in a byte string")]
    UnicodeEscapeInByte(
        #[primary_span]
        #[label("unicode escape in byte string")]
        Span,
    ),
    #[diag("empty unicode escape")]
    EmptyUnicodeEscape(
        #[primary_span]
        #[label("this escape must have at least 1 hex digit")]
        Span,
    ),
    #[diag("empty character literal")]
    ZeroChars(
        #[primary_span]
        #[label("empty character literal")]
        Span,
    ),
    #[diag("invalid trailing slash in literal")]
    LoneSlash(
        #[primary_span]
        #[label("invalid trailing slash in literal")]
        Span,
    ),
    #[diag("whitespace symbol '{$ch}' is not skipped")]
    UnskippedWhitespace {
        #[primary_span]
        span: Span,
        #[label("whitespace symbol '{$ch}' is not skipped")]
        char_span: Span,
        ch: String,
    },
    #[diag("multiple lines skipped by escaped newline")]
    MultipleSkippedLinesWarning(
        #[primary_span]
        #[label("skipping everything up to and including this point")]
        Span,
    ),
    #[diag("character literal may only contain one codepoint")]
    MoreThanOneChar {
        #[primary_span]
        span: Span,
        #[subdiagnostic]
        note: Option<MoreThanOneCharNote>,
        #[subdiagnostic]
        suggestion: MoreThanOneCharSugg,
    },
    #[diag("null characters in C string literals are not supported")]
    NulInCStr {
        #[primary_span]
        span: Span,
    },
}

#[derive(Subdiagnostic)]
pub(crate) enum MoreThanOneCharSugg {
    #[suggestion(
        "consider using the normalized form `{$ch}` of this character",
        code = "{normalized}",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    NormalizedForm {
        #[primary_span]
        span: Span,
        ch: String,
        normalized: String,
    },
    #[suggestion(
        "consider removing the non-printing characters",
        code = "{ch}",
        applicability = "maybe-incorrect",
        style = "verbose"
    )]
    RemoveNonPrinting {
        #[primary_span]
        span: Span,
        ch: String,
    },
    #[suggestion(
        "if you meant to write a {$is_byte ->
            [true] byte string
            *[false] string
        } literal, use double quotes",
        code = "{sugg}",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    QuotesFull {
        #[primary_span]
        span: Span,
        is_byte: bool,
        sugg: String,
    },
    #[multipart_suggestion(
        "if you meant to write a {$is_byte ->
            [true] byte string
            *[false] string
        } literal, use double quotes",
        applicability = "machine-applicable"
    )]
    Quotes {
        #[suggestion_part(code = "{prefix}\"")]
        start: Span,
        #[suggestion_part(code = "\"")]
        end: Span,
        is_byte: bool,
        prefix: &'static str,
    },
}

#[derive(Subdiagnostic)]
pub(crate) enum MoreThanOneCharNote {
    #[note(
        "this `{$chr}` is followed by the combining {$len ->
            [one] mark
            *[other] marks
        } `{$escaped_marks}`"
    )]
    AllCombining {
        #[primary_span]
        span: Span,
        chr: String,
        len: usize,
        escaped_marks: String,
    },
    #[note("there are non-printing characters, the full sequence is `{$escaped}`")]
    NonPrinting {
        #[primary_span]
        span: Span,
        escaped: String,
    },
}

#[derive(Subdiagnostic)]
pub(crate) enum NoBraceUnicodeSub {
    #[suggestion(
        "format of unicode escape sequences uses braces",
        code = "{suggestion}",
        applicability = "maybe-incorrect",
        style = "verbose"
    )]
    Suggestion {
        #[primary_span]
        span: Span,
        suggestion: String,
    },
    #[help(r#"format of unicode escape sequences is `\u{"{...}"}`"#)]
    Help,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion("wrap the pattern in parentheses", applicability = "machine-applicable")]
pub(crate) struct WrapInParens {
    #[suggestion_part(code = "(")]
    pub(crate) lo: Span,
    #[suggestion_part(code = ")")]
    pub(crate) hi: Span,
}

#[derive(Subdiagnostic)]
pub(crate) enum TopLevelOrPatternNotAllowedSugg {
    #[suggestion(
        "remove the `|`",
        code = "",
        applicability = "machine-applicable",
        style = "tool-only"
    )]
    RemoveLeadingVert {
        #[primary_span]
        span: Span,
    },
    WrapInParens {
        #[primary_span]
        span: Span,
        #[subdiagnostic]
        suggestion: WrapInParens,
    },
}

#[derive(Diagnostic)]
#[diag("unexpected `||` before function parameter")]
#[note("alternatives in or-patterns are separated with `|`, not `||`")]
pub(crate) struct UnexpectedVertVertBeforeFunctionParam {
    #[primary_span]
    #[suggestion(
        "remove the `||`",
        code = "",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("unexpected token `||` in pattern")]
pub(crate) struct UnexpectedVertVertInPattern {
    #[primary_span]
    #[suggestion(
        "use a single `|` to separate multiple alternative patterns",
        code = "|",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub span: Span,
    #[label("while parsing this or-pattern starting here")]
    pub start: Option<Span>,
}

#[derive(Subdiagnostic)]
#[suggestion(
    "a trailing `{$token}` is not allowed in an or-pattern",
    code = "",
    applicability = "machine-applicable",
    style = "tool-only"
)]
pub(crate) struct TrailingVertSuggestion {
    #[primary_span]
    pub span: Span,
    pub token: Token,
}

#[derive(Diagnostic)]
#[diag("a trailing `{$token}` is not allowed in an or-pattern")]
pub(crate) struct TrailingVertNotAllowed {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub suggestion: TrailingVertSuggestion,
    #[label("while parsing this or-pattern starting here")]
    pub start: Option<Span>,
    pub token: Token,
    #[note("alternatives in or-patterns are separated with `|`, not `||`")]
    pub note_double_vert: bool,
}

#[derive(Diagnostic)]
#[diag("unexpected `...`")]
pub(crate) struct DotDotDotRestPattern {
    #[primary_span]
    #[label("not a valid pattern")]
    pub span: Span,
    #[suggestion(
        "for a rest pattern, use `..` instead of `...`",
        style = "verbose",
        code = "",
        applicability = "machine-applicable"
    )]
    pub suggestion: Option<Span>,
    #[note(
        "only `extern \"C\"` and `extern \"C-unwind\"` functions may have a C variable argument list"
    )]
    pub var_args: Option<()>,
}

#[derive(Diagnostic)]
#[diag("pattern on wrong side of `@`")]
pub(crate) struct PatternOnWrongSideOfAt {
    #[primary_span]
    #[suggestion(
        "switch the order",
        code = "{whole_pat}",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub whole_span: Span,
    pub whole_pat: String,
    #[label("pattern on the left, should be on the right")]
    pub pattern: Span,
    #[label("binding on the right, should be on the left")]
    pub binding: Span,
}

#[derive(Diagnostic)]
#[diag("left-hand side of `@` must be a binding")]
#[note("bindings are `x`, `mut x`, `ref x`, and `ref mut x`")]
pub(crate) struct ExpectedBindingLeftOfAt {
    #[primary_span]
    pub whole_span: Span,
    #[label("interpreted as a pattern, not a binding")]
    pub lhs: Span,
    #[label("also a pattern")]
    pub rhs: Span,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion(
    "add parentheses to clarify the precedence",
    applicability = "machine-applicable"
)]
pub(crate) struct ParenRangeSuggestion {
    #[suggestion_part(code = "(")]
    pub lo: Span,
    #[suggestion_part(code = ")")]
    pub hi: Span,
}

#[derive(Diagnostic)]
#[diag("the range pattern here has ambiguous interpretation")]
pub(crate) struct AmbiguousRangePattern {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub suggestion: ParenRangeSuggestion,
}

#[derive(Diagnostic)]
#[diag("unexpected lifetime `{$symbol}` in pattern")]
pub(crate) struct UnexpectedLifetimeInPattern {
    #[primary_span]
    pub span: Span,
    pub symbol: Symbol,
    #[suggestion(
        "remove the lifetime",
        code = "",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub suggestion: Span,
}

#[derive(Diagnostic)]
pub(crate) enum InvalidMutInPattern {
    #[diag("`mut` must be attached to each individual binding")]
    #[note("`mut` may be followed by `variable` and `variable @ pattern`")]
    NestedIdent {
        #[primary_span]
        #[suggestion(
            "add `mut` to each binding",
            code = "{pat}",
            applicability = "machine-applicable",
            style = "verbose"
        )]
        span: Span,
        pat: String,
    },
    #[diag("`mut` must be followed by a named binding")]
    #[note("`mut` may be followed by `variable` and `variable @ pattern`")]
    NonIdent {
        #[primary_span]
        #[suggestion(
            "remove the `mut` prefix",
            code = "",
            applicability = "machine-applicable",
            style = "verbose"
        )]
        span: Span,
    },
}

#[derive(Diagnostic)]
#[diag("`mut` on a binding may not be repeated")]
pub(crate) struct RepeatedMutInPattern {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "remove the additional `mut`s",
        code = "",
        applicability = "machine-applicable",
        style = "verbose"
    )]
    pub suggestion: Span,
}

#[derive(Diagnostic)]
#[diag("range-to patterns with `...` are not allowed")]
pub(crate) struct DotDotDotRangeToPatternNotAllowed {
    #[primary_span]
    #[suggestion(
        "use `..=` instead",
        style = "verbose",
        code = "..=",
        applicability = "machine-applicable"
    )]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("expected identifier, found enum pattern")]
pub(crate) struct EnumPatternInsteadOfIdentifier {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("`@ ..` is not supported in struct patterns")]
pub(crate) struct AtDotDotInStructPattern {
    #[primary_span]
    pub span: Span,
    #[suggestion(
        "bind to each field separately or, if you don't need them, just remove `{$ident} @`",
        code = "",
        style = "verbose",
        applicability = "machine-applicable"
    )]
    pub remove: Span,
    pub ident: Ident,
}

#[derive(Diagnostic)]
#[diag("unexpected `@` in struct pattern")]
#[note("struct patterns use `field: pattern` syntax to bind to fields")]
#[help(
    "consider replacing `new_name @ field_name` with `field_name: new_name` if that is what you intended"
)]
pub(crate) struct AtInStructPattern {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("expected field pattern, found `{$token_str}`")]
pub(crate) struct DotDotDotForRemainingFields {
    #[primary_span]
    #[suggestion(
        "to omit remaining fields, use `..`",
        code = "..",
        style = "verbose",
        applicability = "machine-applicable"
    )]
    pub span: Span,
    pub token_str: Cow<'static, str>,
}

#[derive(Diagnostic)]
#[diag("expected `,`")]
pub(crate) struct ExpectedCommaAfterPatternField {
    #[primary_span]
    pub span: Span,
}
