//! Built-in lint definitions (M-R).
//!
//! This file is part of the `builtin` module split. See `mod.rs` for the
//! `declare_lint_pass!` that registers these lints.

// tRust: split from builtin.rs for file size reduction
use crate::{declare_lint, fcw};

declare_lint! {
    /// The `macro_use_extern_crate` lint detects the use of the [`macro_use` attribute].
    ///
    /// ### Example
    ///
    /// ```rust,ignore (needs extern crate)
    /// #![deny(macro_use_extern_crate)]
    ///
    /// #[macro_use]
    /// extern crate serde_json;
    ///
    /// fn main() {
    ///     let _ = json!{{}};
    /// }
    /// ```
    ///
    /// This will produce:
    ///
    /// ```text
    /// error: applying the `#[macro_use]` attribute to an `extern crate` item is deprecated
    ///  --> src/main.rs:3:1
    ///   |
    /// 3 | #[macro_use]
    ///   | ^^^^^^^^^^^^
    ///   |
    ///   = help: remove it and import macros at use sites with a `use` item instead
    /// note: the lint level is defined here
    ///  --> src/main.rs:1:9
    ///   |
    /// 1 | #![deny(macro_use_extern_crate)]
    ///   |         ^^^^^^^^^^^^^^^^^^^^^^
    /// ```
    ///
    /// ### Explanation
    ///
    /// The [`macro_use` attribute] on an [`extern crate`] item causes
    /// macros in that external crate to be brought into the prelude of the
    /// crate, making the macros in scope everywhere. As part of the efforts
    /// to simplify handling of dependencies in the [2018 edition], the use of
    /// `extern crate` is being phased out. To bring macros from extern crates
    /// into scope, it is recommended to use a [`use` import].
    ///
    /// This lint is "allow" by default because this is a stylistic choice
    /// that has not been settled, see [issue #52043] for more information.
    ///
    /// [`macro_use` attribute]: https://doc.rust-lang.org/reference/macros-by-example.html#the-macro_use-attribute
    /// [`use` import]: https://doc.rust-lang.org/reference/items/use-declarations.html
    /// [issue #52043]: https://github.com/rust-lang/rust/issues/52043
    pub MACRO_USE_EXTERN_CRATE,
    Allow,
    "the `#[macro_use]` attribute is now deprecated in favor of using macros \
     via the module system"
}

declare_lint! {
    /// The `malformed_diagnostic_attributes` lint detects malformed diagnostic attributes.
    ///
    /// ### Example
    ///
    /// ```rust
    /// #[diagnostic::do_not_recommend(message = "message")]
    /// trait Trait {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// It is usually a mistake to use options or syntax that is not supported. Check the spelling,
    /// and check the diagnostic attribute listing for the correct name and syntax. Also consider if
    /// you are using an old version of the compiler; perhaps the option or syntax is only available
    /// in a newer version. See the [reference] for a list of diagnostic attributes and the syntax
    /// of each.
    ///
    /// [reference]: https://doc.rust-lang.org/nightly/reference/attributes/diagnostics.html#the-diagnostic-tool-attribute-namespace
    pub MALFORMED_DIAGNOSTIC_ATTRIBUTES,
    Warn,
    "detects malformed diagnostic attributes",
}

declare_lint! {
    /// The `malformed_diagnostic_format_literals` lint detects malformed diagnostic format
    /// literals.
    ///
    /// ### Example
    ///
    /// ```rust
    /// #[diagnostic::on_unimplemented(message = "{Self}} does not implement `Trait`")]
    /// trait Trait {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// The `#[diagnostic::on_unimplemented]` attribute accepts string literal values that are
    /// similar to `format!`'s string literal. See the [reference] for details on what is permitted
    /// in this string literal.
    ///
    /// [reference]: https://doc.rust-lang.org/nightly/reference/attributes/diagnostics.html#the-diagnostic-tool-attribute-namespace
    pub MALFORMED_DIAGNOSTIC_FORMAT_LITERALS,
    Warn,
    "detects diagnostic attribute with malformed diagnostic format literals",
}

declare_lint! {
    /// The `meta_variable_misuse` lint detects possible meta-variable misuse
    /// in macro definitions.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(meta_variable_misuse)]
    ///
    /// macro_rules! foo {
    ///     () => {};
    ///     ($( $i:ident = $($j:ident),+ );*) => { $( $( $i = $k; )+ )* };
    /// }
    ///
    /// fn main() {
    ///     foo!();
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// There are quite a few different ways a [`macro_rules`] macro can be
    /// improperly defined. Many of these errors were previously only detected
    /// when the macro was expanded or not at all. This lint is an attempt to
    /// catch some of these problems when the macro is *defined*.
    ///
    /// This lint is "allow" by default because it may have false positives
    /// and other issues. See [issue #61053] for more details.
    ///
    /// [`macro_rules`]: https://doc.rust-lang.org/reference/macros-by-example.html
    /// [issue #61053]: https://github.com/rust-lang/rust/issues/61053
    pub META_VARIABLE_MISUSE,
    Allow,
    "possible meta-variable misuse at macro definition"
}

declare_lint! {
    /// The `misplaced_diagnostic_attributes` lint detects wrongly placed diagnostic attributes.
    ///
    /// ### Example
    ///
    /// ```rust
    /// #[diagnostic::do_not_recommend]
    /// struct NotUserFacing;
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// It is usually a mistake to specify a diagnostic attribute on an item it is not meant for.
    /// For example, `#[diagnostic::do_not_recommend]` can only be placed on trait implementations,
    /// and does nothing if placed elsewhere. See the [reference] for a list of diagnostic
    /// attributes and their correct positions.
    ///
    /// [reference]: https://doc.rust-lang.org/nightly/reference/attributes/diagnostics.html#the-diagnostic-tool-attribute-namespace
    pub MISPLACED_DIAGNOSTIC_ATTRIBUTES,
    Warn,
    "detects diagnostic attributes that are placed on the wrong item",
}

declare_lint! {
    /// The `missing_abi` lint detects cases where the ABI is omitted from
    /// `extern` declarations.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(missing_abi)]
    ///
    /// extern fn foo() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// For historic reasons, Rust implicitly selects `C` as the default ABI for
    /// `extern` declarations. [Other ABIs] like `C-unwind` and `system` have
    /// been added since then, and especially with their addition seeing the ABI
    /// easily makes code review easier.
    ///
    /// [Other ABIs]: https://doc.rust-lang.org/reference/items/external-blocks.html#abi
    pub MISSING_ABI,
    Warn,
    "No declared ABI for extern declaration"
}

declare_lint! {
    /// The `missing_unsafe_on_extern` lint detects missing unsafe keyword on extern declarations.
    ///
    /// ### Example
    ///
    /// ```rust,edition2021
    /// #![warn(missing_unsafe_on_extern)]
    /// #![allow(dead_code)]
    ///
    /// extern "C" {
    ///     fn foo(_: i32);
    /// }
    ///
    /// fn main() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Declaring extern items, even without ever using them, can cause Undefined Behavior. We
    /// should consider all sources of Undefined Behavior to be unsafe.
    ///
    /// This is a [future-incompatible] lint to transition this to a
    /// hard error in the future.
    ///
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub MISSING_UNSAFE_ON_EXTERN,
    Allow,
    "detects missing unsafe keyword on extern declarations",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(EditionError 2024 "unsafe-extern"),
    };
}

declare_lint! {
    /// The `must_not_suspend` lint guards against values that shouldn't be held across suspend points
    /// (`.await`)
    ///
    /// ### Example
    ///
    /// ```rust
    /// #![feature(must_not_suspend)]
    /// #![warn(must_not_suspend)]
    ///
    /// #[must_not_suspend]
    /// struct SyncThing {}
    ///
    /// async fn yield_now() {}
    ///
    /// pub async fn uhoh() {
    ///     let guard = SyncThing {};
    ///     yield_now().await;
    ///     let _guard = guard;
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// The `must_not_suspend` lint detects values that are marked with the `#[must_not_suspend]`
    /// attribute being held across suspend points. A "suspend" point is usually a `.await` in an async
    /// function.
    ///
    /// This attribute can be used to mark values that are semantically incorrect across suspends
    /// (like certain types of timers), values that have async alternatives, and values that
    /// regularly cause problems with the `Send`-ness of async fn's returned futures (like
    /// `MutexGuard`'s)
    ///
    pub MUST_NOT_SUSPEND,
    Allow,
    "use of a `#[must_not_suspend]` value across a yield point",
    @feature_gate = must_not_suspend;
}

declare_lint! {
    /// The `named_arguments_used_positionally` lint detects cases where named arguments are only
    /// used positionally in format strings. This usage is valid but potentially very confusing.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(named_arguments_used_positionally)]
    /// fn main() {
    ///     let _x = 5;
    ///     println!("{}", _x = 1); // Prints 1, will trigger lint
    ///
    ///     println!("{}", _x); // Prints 5, no lint emitted
    ///     println!("{_x}", _x = _x); // Prints 5, no lint emitted
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Rust formatting strings can refer to named arguments by their position, but this usage is
    /// potentially confusing. In particular, readers can incorrectly assume that the declaration
    /// of named arguments is an assignment (which would produce the unit type).
    /// For backwards compatibility, this is not a hard error.
    pub NAMED_ARGUMENTS_USED_POSITIONALLY,
    Warn,
    "named arguments in format used positionally"
}

declare_lint! {
    /// The `never_type_fallback_flowing_into_unsafe` lint detects cases where never type fallback
    /// affects unsafe function calls.
    ///
    /// ### Never type fallback
    ///
    /// When the compiler sees a value of type [`!`] it implicitly inserts a coercion (if possible),
    /// to allow type check to infer any type:
    ///
    /// ```ignore (illustrative-and-has-placeholders)
    /// // this
    /// let x: u8 = panic!();
    ///
    /// // is (essentially) turned by the compiler into
    /// let x: u8 = absurd(panic!());
    ///
    /// // where absurd is a function with the following signature
    /// // (it's sound, because `!` always marks unreachable code):
    /// fn absurd<T>(never: !) -> T { ... }
    /// ```
    ///
    /// While it's convenient to be able to use non-diverging code in one of the branches (like
    /// `if a { b } else { return }`) this could lead to compilation errors:
    ///
    /// ```compile_fail
    /// // this
    /// { panic!() };
    ///
    /// // gets turned into this
    /// { absurd(panic!()) }; // error: can't infer the type of `absurd`
    /// ```
    ///
    /// To prevent such errors, compiler remembers where it inserted `absurd` calls, and if it
    /// can't infer their type, it sets the type to fallback. `{ absurd::<Fallback>(panic!()) };`.
    /// This is what is known as "never type fallback".
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// fn main() {
    ///     if true {
    ///         // return has type `!` which, is some cases, causes never type fallback
    ///         return
    ///     } else {
    ///         // `zeroed` is an unsafe function, which returns an unbounded type
    ///         // SAFETY: Illustrative example in lint documentation; not executed.
    ///         unsafe { std::mem::zeroed() }
    ///     };
    ///     // depending on the fallback, `zeroed` may create `()` (which is completely sound),
    ///     // or `!` (which is instant undefined behavior)
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Due to historic reasons never type fallback was `()`, meaning that `!` got spontaneously
    /// coerced to `()`. There are plans to change that, but they may make the code such as above
    /// unsound. Instead of depending on the fallback, you should specify the type explicitly:
    /// ```
    /// if true {
    ///     return
    /// } else {
    ///     // type is explicitly specified, fallback can't hurt us no more
    ///     // SAFETY: Illustrative example in lint documentation; not executed.
    ///     unsafe { std::mem::zeroed::<()>() }
    /// };
    /// ```
    ///
    /// See [Tracking Issue for making `!` fall back to `!`](https://github.com/rust-lang/rust/issues/123748).
    ///
    /// [`!`]: https://doc.rust-lang.org/core/primitive.never.html
    /// [`()`]: https://doc.rust-lang.org/core/primitive.unit.html
    pub NEVER_TYPE_FALLBACK_FLOWING_INTO_UNSAFE,
    Deny,
    "never type fallback affecting unsafe function calls",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(EditionAndFutureReleaseSemanticsChange 2024 "never-type-fallback"),
        report_in_deps: true,
    };
    @edition Edition2024 => Deny;
    report_in_external_macro
}

declare_lint! {
    /// The `non_contiguous_range_endpoints` lint detects likely off-by-one errors when using
    /// exclusive [range patterns].
    ///
    /// [range patterns]: https://doc.rust-lang.org/nightly/reference/patterns.html#range-patterns
    ///
    /// ### Example
    ///
    /// ```rust
    /// let x = 123u32;
    /// match x {
    ///     0..100 => { println!("small"); }
    ///     101..1000 => { println!("large"); }
    ///     _ => { println!("larger"); }
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// It is likely a mistake to have range patterns in a match expression that miss out a single
    /// number. Check that the beginning and end values are what you expect, and keep in mind that
    /// with `..=` the right bound is inclusive, and with `..` it is exclusive.
    pub NON_CONTIGUOUS_RANGE_ENDPOINTS,
    Warn,
    "detects off-by-one errors with exclusive range patterns"
}

declare_lint! {
    /// The `non_exhaustive_omitted_patterns` lint aims to help consumers of a `#[non_exhaustive]`
    /// struct or enum who want to match all of its fields/variants explicitly.
    ///
    /// The `#[non_exhaustive]` annotation forces matches to use wildcards, so exhaustiveness
    /// checking cannot be used to ensure that all fields/variants are matched explicitly. To remedy
    /// this, this allow-by-default lint warns the user when a match mentions some but not all of
    /// the fields/variants of a `#[non_exhaustive]` struct or enum.
    ///
    /// ### Example
    ///
    /// ```rust,ignore (needs separate crate)
    /// // crate A
    /// #[non_exhaustive]
    /// pub enum Bar {
    ///     A,
    ///     B, // added variant in non breaking change
    /// }
    ///
    /// // in crate B
    /// #![feature(non_exhaustive_omitted_patterns_lint)]
    /// #[warn(non_exhaustive_omitted_patterns)]
    /// match Bar::A {
    ///     Bar::A => {},
    ///     _ => {},
    /// }
    /// ```
    ///
    /// This will produce:
    ///
    /// ```text
    /// warning: some variants are not matched explicitly
    ///    --> $DIR/reachable-patterns.rs:70:9
    ///    |
    /// LL |         match Bar::A {
    ///    |               ^ pattern `Bar::B` not covered
    ///    |
    ///  note: the lint level is defined here
    ///   --> $DIR/reachable-patterns.rs:69:16
    ///    |
    /// LL |         #[warn(non_exhaustive_omitted_patterns)]
    ///    |                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    ///    = help: ensure that all variants are matched explicitly by adding the suggested match arms
    ///    = note: the matched value is of type `Bar` and the `non_exhaustive_omitted_patterns` attribute was found
    /// ```
    ///
    /// Warning: setting this to `deny` will make upstream non-breaking changes (adding fields or
    /// variants to a `#[non_exhaustive]` struct or enum) break your crate. This goes against
    /// expected semver behavior.
    ///
    /// ### Explanation
    ///
    /// Structs and enums tagged with `#[non_exhaustive]` force the user to add a (potentially
    /// redundant) wildcard when pattern-matching, to allow for future addition of fields or
    /// variants. The `non_exhaustive_omitted_patterns` lint detects when such a wildcard happens to
    /// actually catch some fields/variants. In other words, when the match without the wildcard
    /// would not be exhaustive. This lets the user be informed if new fields/variants were added.
    pub NON_EXHAUSTIVE_OMITTED_PATTERNS,
    Allow,
    "detect when patterns of types marked `non_exhaustive` are missed",
    @feature_gate = non_exhaustive_omitted_patterns_lint;
}

declare_lint! {
    /// The `out_of_scope_macro_calls` lint detects `macro_rules` called when they are not in scope,
    /// above their definition, which may happen in key-value attributes.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![doc = in_root!()]
    ///
    /// macro_rules! in_root { () => { "" } }
    ///
    /// fn main() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// The scope in which a `macro_rules` item is visible starts at that item and continues
    /// below it. This is more similar to `let` than to other items, which are in scope both above
    /// and below their definition.
    /// Due to a bug `macro_rules` were accidentally in scope inside some key-value attributes
    /// above their definition. The lint catches such cases.
    /// To address the issue turn the `macro_rules` into a regularly scoped item by importing it
    /// with `use`.
    ///
    /// This is a [future-incompatible] lint to transition this to a
    /// hard error in the future.
    ///
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub OUT_OF_SCOPE_MACRO_CALLS,
    Deny,
    "detects out of scope calls to `macro_rules` in key-value attributes",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #124535),
        report_in_deps: true,
    };
}

declare_lint! {
    /// The `overlapping_range_endpoints` lint detects `match` arms that have [range patterns] that
    /// overlap on their endpoints.
    ///
    /// [range patterns]: https://doc.rust-lang.org/nightly/reference/patterns.html#range-patterns
    ///
    /// ### Example
    ///
    /// ```rust
    /// let x = 123u8;
    /// match x {
    ///     0..=100 => { println!("small"); }
    ///     100..=255 => { println!("large"); }
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// It is likely a mistake to have range patterns in a match expression that overlap in this
    /// way. Check that the beginning and end values are what you expect, and keep in mind that
    /// with `..=` the left and right bounds are inclusive.
    pub OVERLAPPING_RANGE_ENDPOINTS,
    Warn,
    "detects range patterns with overlapping endpoints"
}

declare_lint! {
    /// The `patterns_in_fns_without_body` lint detects `mut` identifier
    /// patterns as a parameter in functions without a body.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// trait Trait {
    ///     fn foo(mut arg: u8);
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// To fix this, remove `mut` from the parameter in the trait definition;
    /// it can be used in the implementation. That is, the following is OK:
    ///
    /// ```rust
    /// trait Trait {
    ///     fn foo(arg: u8); // Removed `mut` here
    /// }
    ///
    /// impl Trait for i32 {
    ///     fn foo(mut arg: u8) { // `mut` here is OK
    ///
    ///     }
    /// }
    /// ```
    ///
    /// Trait definitions can define functions without a body to specify a
    /// function that implementors must define. The parameter names in the
    /// body-less functions are only allowed to be `_` or an [identifier] for
    /// documentation purposes (only the type is relevant). Previous versions
    /// of the compiler erroneously allowed [identifier patterns] with the
    /// `mut` keyword, but this was not intended to be allowed. This is a
    /// [future-incompatible] lint to transition this to a hard error in the
    /// future. See [issue #35203] for more details.
    ///
    /// [identifier]: https://doc.rust-lang.org/reference/identifiers.html
    /// [identifier patterns]: https://doc.rust-lang.org/reference/patterns.html#identifier-patterns
    /// [issue #35203]: https://github.com/rust-lang/rust/issues/35203
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub PATTERNS_IN_FNS_WITHOUT_BODY,
    Deny,
    "patterns in functions without body were erroneously allowed",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #35203),
    };
}

declare_lint! {
    /// The `private_bounds` lint detects types in a secondary interface of an item,
    /// that are more private than the item itself. Secondary interface of an item consists of
    /// bounds on generic parameters and where clauses, including supertraits for trait items.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// # #![allow(unused)]
    /// #![deny(private_bounds)]
    ///
    /// struct PrivTy;
    /// pub struct S
    ///     where PrivTy:
    /// {}
    /// # fn main() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Having private types or traits in item bounds makes it less clear what interface
    /// the item actually provides.
    pub PRIVATE_BOUNDS,
    Warn,
    "private type in secondary interface of an item",
}

declare_lint! {
    /// The `private_interfaces` lint detects types in a primary interface of an item,
    /// that are more private than the item itself. Primary interface of an item is all
    /// its interface except for bounds on generic parameters and where clauses.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// # #![allow(unused)]
    /// #![deny(private_interfaces)]
    /// struct SemiPriv;
    ///
    /// mod m1 {
    ///     struct Priv;
    ///     impl crate::SemiPriv {
    ///         pub fn f(_: Priv) {}
    ///     }
    /// }
    ///
    /// # fn main() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Having something private in primary interface guarantees that
    /// the item will be unusable from outer modules due to type privacy.
    pub PRIVATE_INTERFACES,
    Warn,
    "private type in primary interface of an item",
}

declare_lint! {
    /// The `private_macro_use` lint detects private macros that are imported
    /// with `#[macro_use]`.
    ///
    /// ### Example
    ///
    /// ```rust,ignore (needs extern crate)
    /// // extern_macro.rs
    /// macro_rules! foo_ { () => {}; }
    /// use foo_ as foo;
    ///
    /// // code.rs
    ///
    /// #![deny(private_macro_use)]
    ///
    /// #[macro_use]
    /// extern crate extern_macro;
    ///
    /// fn main() {
    ///     foo!();
    /// }
    /// ```
    ///
    /// This will produce:
    ///
    /// ```text
    /// error: cannot find macro `foo` in this scope
    /// ```
    ///
    /// ### Explanation
    ///
    /// This lint arises from overlooking visibility checks for macros
    /// in an external crate.
    ///
    /// This is a [future-incompatible] lint to transition this to a
    /// hard error in the future.
    ///
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub PRIVATE_MACRO_USE,
    Deny,
    "detects certain macro bindings that should not be re-exported",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #120192),
        report_in_deps: true,
    };
}

declare_lint! {
    /// The `proc_macro_derive_resolution_fallback` lint detects proc macro
    /// derives using inaccessible names from parent modules.
    ///
    /// ### Example
    ///
    /// ```rust,ignore (proc-macro)
    /// // foo.rs
    /// #![crate_type = "proc-macro"]
    ///
    /// extern crate proc_macro;
    ///
    /// use proc_macro::*;
    ///
    /// #[proc_macro_derive(Foo)]
    /// pub fn foo1(a: TokenStream) -> TokenStream {
    ///     drop(a);
    ///     "mod __bar { static mut BAR: Option<Something> = None; }".parse().unwrap()
    /// }
    /// ```
    ///
    /// ```rust,ignore (needs-dependency)
    /// // bar.rs
    /// #[macro_use]
    /// extern crate foo;
    ///
    /// struct Something;
    ///
    /// #[derive(Foo)]
    /// struct Another;
    ///
    /// fn main() {}
    /// ```
    ///
    /// This will produce:
    ///
    /// ```text
    /// warning: cannot find type `Something` in this scope
    ///  --> src/main.rs:8:10
    ///   |
    /// 8 | #[derive(Foo)]
    ///   |          ^^^ names from parent modules are not accessible without an explicit import
    ///   |
    ///   = note: `#[warn(proc_macro_derive_resolution_fallback)]` on by default
    ///   = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
    ///   = note: for more information, see issue #50504 <https://github.com/rust-lang/rust/issues/50504>
    /// ```
    ///
    /// ### Explanation
    ///
    /// If a proc-macro generates a module, the compiler unintentionally
    /// allowed items in that module to refer to items in the crate root
    /// without importing them. This is a [future-incompatible] lint to
    /// transition this to a hard error in the future. See [issue #50504] for
    /// more details.
    ///
    /// [issue #50504]: https://github.com/rust-lang/rust/issues/50504
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub PROC_MACRO_DERIVE_RESOLUTION_FALLBACK,
    Deny,
    "detects proc macro derives using inaccessible names from parent modules",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #83583),
        report_in_deps: true,
    };
}

declare_lint! {
    /// The `pub_use_of_private_extern_crate` lint detects a specific
    /// situation of re-exporting a private `extern crate`.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// extern crate core;
    /// pub use core as reexported_core;
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// A public `use` declaration should not be used to publically re-export a
    /// private `extern crate`. `pub extern crate` should be used instead.
    ///
    /// This was historically allowed, but is not the intended behavior
    /// according to the visibility rules. This is a [future-incompatible]
    /// lint to transition this to a hard error in the future. See [issue
    /// #127909] for more details.
    ///
    /// [issue #127909]: https://github.com/rust-lang/rust/issues/127909
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub PUB_USE_OF_PRIVATE_EXTERN_CRATE,
    Deny,
    "detect public re-exports of private extern crates",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #127909),
        report_in_deps: true,
    };
}

declare_lint! {
    /// The `redundant_imports` lint detects imports that are redundant due to being
    /// imported already; either through a previous import, or being present in
    /// the prelude.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(redundant_imports)]
    /// use std::option::Option::None;
    /// fn foo() -> Option<i32> { None }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Redundant imports are unnecessary and can be removed to simplify code.
    /// If you intended to re-export the item to make it available outside of the
    /// module, add a visibility modifier like `pub`.
    pub REDUNDANT_IMPORTS,
    Allow,
    "imports that are redundant due to being imported already"
}

declare_lint! {
    /// The `redundant_lifetimes` lint detects lifetime parameters that are
    /// redundant because they are equal to another named lifetime.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #[deny(redundant_lifetimes)]
    ///
    /// // `'a = 'static`, so all usages of `'a` can be replaced with `'static`
    /// pub fn bar<'a: 'static>() {}
    ///
    /// // `'a = 'b`, so all usages of `'b` can be replaced with `'a`
    /// pub fn bar<'a: 'b, 'b: 'a>() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Unused lifetime parameters may signal a mistake or unfinished code.
    /// Consider removing the parameter.
    pub REDUNDANT_LIFETIMES,
    Allow,
    "detects lifetime parameters that are redundant because they are equal to some other named lifetime"
}

declare_lint! {
    /// The `refining_impl_trait_internal` lint detects `impl Trait` return
    /// types in method signatures that are refined by a trait implementation,
    /// meaning the implementation adds information about the return type that
    /// is not present in the trait.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(refining_impl_trait)]
    ///
    /// use std::fmt::Display;
    ///
    /// trait AsDisplay {
    ///     fn as_display(&self) -> impl Display;
    /// }
    ///
    /// impl<'s> AsDisplay for &'s str {
    ///     fn as_display(&self) -> Self {
    ///         *self
    ///     }
    /// }
    ///
    /// fn main() {
    ///     // users can observe that the return type of
    ///     // `<&str as AsDisplay>::as_display()` is `&str`.
    ///     let _x: &str = "".as_display();
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Callers of methods for types where the implementation is known are
    /// able to observe the types written in the impl signature. This may be
    /// intended behavior, but may also lead to implementation details being
    /// revealed unintentionally. In particular, it may pose a semver hazard
    /// for authors of libraries who do not wish to make stronger guarantees
    /// about the types than what is written in the trait signature.
    ///
    /// `refining_impl_trait` is a lint group composed of two lints:
    ///
    /// * `refining_impl_trait_reachable`, for refinements that are publically
    ///   reachable outside a crate, and
    /// * `refining_impl_trait_internal`, for refinements that are only visible
    ///    within a crate.
    ///
    /// We are seeking feedback on each of these lints; see issue
    /// [#121718](https://github.com/rust-lang/rust/issues/121718) for more
    /// information.
    pub REFINING_IMPL_TRAIT_INTERNAL,
    Warn,
    "impl trait in impl method signature does not match trait method signature",
}

declare_lint! {
    /// The `refining_impl_trait_reachable` lint detects `impl Trait` return
    /// types in method signatures that are refined by a publically reachable
    /// trait implementation, meaning the implementation adds information about
    /// the return type that is not present in the trait.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(refining_impl_trait)]
    ///
    /// use std::fmt::Display;
    ///
    /// pub trait AsDisplay {
    ///     fn as_display(&self) -> impl Display;
    /// }
    ///
    /// impl<'s> AsDisplay for &'s str {
    ///     fn as_display(&self) -> Self {
    ///         *self
    ///     }
    /// }
    ///
    /// fn main() {
    ///     // users can observe that the return type of
    ///     // `<&str as AsDisplay>::as_display()` is `&str`.
    ///     let _x: &str = "".as_display();
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Callers of methods for types where the implementation is known are
    /// able to observe the types written in the impl signature. This may be
    /// intended behavior, but may also lead to implementation details being
    /// revealed unintentionally. In particular, it may pose a semver hazard
    /// for authors of libraries who do not wish to make stronger guarantees
    /// about the types than what is written in the trait signature.
    ///
    /// `refining_impl_trait` is a lint group composed of two lints:
    ///
    /// * `refining_impl_trait_reachable`, for refinements that are publically
    ///   reachable outside a crate, and
    /// * `refining_impl_trait_internal`, for refinements that are only visible
    ///    within a crate.
    ///
    /// We are seeking feedback on each of these lints; see issue
    /// [#121718](https://github.com/rust-lang/rust/issues/121718) for more
    /// information.
    pub REFINING_IMPL_TRAIT_REACHABLE,
    Warn,
    "impl trait in impl method signature does not match trait method signature",
}

declare_lint! {
    /// The `renamed_and_removed_lints` lint detects lints that have been
    /// renamed or removed.
    ///
    /// ### Example
    ///
    /// ```rust
    /// #![deny(raw_pointer_derive)]
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// To fix this, either remove the lint or use the new name. This can help
    /// avoid confusion about lints that are no longer valid, and help
    /// maintain consistency for renamed lints.
    pub RENAMED_AND_REMOVED_LINTS,
    Warn,
    "lints that have been renamed or removed"
}

declare_lint! {
    /// The `repr_c_enums_larger_than_int` lint detects `repr(C)` enums with discriminant
    /// values that do not fit into a C `int` or `unsigned int`.
    ///
    /// ### Example
    ///
    /// ```rust,ignore (only errors on 64bit)
    /// #[repr(C)]
    /// enum E {
    ///     V = 9223372036854775807, // i64::MAX
    /// }
    /// ```
    ///
    /// This will produce:
    ///
    /// ```text
    /// error: `repr(C)` enum discriminant does not fit into C `int` nor into C `unsigned int`
    ///   --> $DIR/repr-c-big-discriminant1.rs:16:5
    ///    |
    /// LL |     A = 9223372036854775807, // i64::MAX
    ///    |     ^
    ///    |
    ///    = note: `repr(C)` enums with big discriminants are non-portable, and their size in Rust might not match their size in C
    ///    = help: use `repr($int_ty)` instead to explicitly set the size of this enum
    /// ```
    ///
    /// ### Explanation
    ///
    /// In C, enums with discriminants that do not all fit into an `int` or all fit into an
    /// `unsigned int` are a portability hazard: such enums are only permitted since C23, and not
    /// supported e.g. by MSVC.
    ///
    /// Furthermore, Rust interprets the discriminant values of `repr(C)` enums as expressions of
    /// type `isize`. This makes it impossible to implement the C23 behavior of enums where the enum
    /// discriminants have no predefined type and instead the enum uses a type large enough to hold
    /// all discriminants.
    ///
    /// Therefore, `repr(C)` enums in Rust require that either all discriminants to fit into a C
    /// `int` or they all fit into an `unsigned int`.
    pub REPR_C_ENUMS_LARGER_THAN_INT,
    Warn,
    "repr(C) enums with discriminant values that do not fit into a C int",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #124403),
        report_in_deps: false,
    };
}

declare_lint! {
    /// The `repr_transparent_non_zst_fields` lint
    /// detects types marked `#[repr(transparent)]` that (transitively)
    /// contain a type that is not guaranteed to remain a ZST type under all configurations.
    ///
    /// ### Example
    ///
    /// ```rust,ignore (needs external crate)
    /// #![deny(repr_transparent_external_private_fields)]
    /// use foo::NonExhaustiveZst;
    ///
    /// #[repr(C)]
    /// struct CZst([u8; 0]);
    ///
    /// #[repr(transparent)]
    /// struct Bar(u32, ([u32; 0], NonExhaustiveZst));
    /// #[repr(transparent)]
    /// struct Baz(u32, CZst);
    /// ```
    ///
    /// This will produce:
    ///
    /// ```text
    /// error: zero-sized fields in repr(transparent) cannot contain external non-exhaustive types
    ///  --> src/main.rs:5:28
    ///   |
    /// 5 | struct Bar(u32, ([u32; 0], NonExhaustiveZst));
    ///   |                            ^^^^^^^^^^^^^^^^
    ///   |
    /// note: the lint level is defined here
    ///  --> src/main.rs:1:9
    ///   |
    /// 1 | #![deny(repr_transparent_external_private_fields)]
    ///   |         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    ///   = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
    ///   = note: for more information, see issue #78586 <https://github.com/rust-lang/rust/issues/78586>
    ///   = note: this field contains `NonExhaustiveZst`, which is marked with `#[non_exhaustive]`, so it could become non-zero-sized in the future.
    ///
    /// error: zero-sized fields in repr(transparent) cannot contain `#[repr(C)]` types
    ///  --> src/main.rs:5:28
    ///   |
    /// 5 | struct Baz(u32, CZst);
    ///   |                 ^^^^
    ///   = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
    ///   = note: for more information, see issue #78586 <https://github.com/rust-lang/rust/issues/78586>
    ///   = note: this field contains `CZst`, which is a `#[repr(C)]` type, so it is not guaranteed to be zero-sized on all targets.
    /// ```
    ///
    /// ### Explanation
    ///
    /// Previous, Rust accepted fields that contain external private zero-sized types, even though
    /// those types could gain a non-zero-sized field in a future, semver-compatible update.
    ///
    /// Rust also accepted fields that contain `repr(C)` zero-sized types, even though those types
    /// are not guaranteed to be zero-sized on all targets, and even though those types can
    /// make a difference for the ABI (and therefore cannot be ignored by `repr(transparent)`).
    ///
    /// This is a [future-incompatible] lint to transition this
    /// to a hard error in the future. See [issue #78586] for more details.
    ///
    /// [issue #78586]: https://github.com/rust-lang/rust/issues/78586
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub REPR_TRANSPARENT_NON_ZST_FIELDS,
    Deny,
    "transparent type contains an external ZST that is marked #[non_exhaustive] or contains private fields",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #78586),
        report_in_deps: true,
    };
}
