//! Built-in lint definitions (R-U).
//!
//! This file is part of the `builtin` module split. See `mod.rs` for the
//! `declare_lint_pass!` that registers these lints.

// tRust: split from builtin.rs for file size reduction
use crate::{declare_lint, fcw};

declare_lint! {
    /// The `resolving_to_items_shadowing_supertrait_items` lint detects when the
    /// usage of an item that is provided by both a subtrait and supertrait
    /// is shadowed, preferring the subtrait.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![feature(supertrait_item_shadowing)]
    /// #![deny(resolving_to_items_shadowing_supertrait_items)]
    ///
    /// trait Upstream {
    ///     fn hello(&self) {}
    /// }
    /// impl<T> Upstream for T {}
    ///
    /// trait Downstream: Upstream {
    ///     fn hello(&self) {}
    /// }
    /// impl<T> Downstream for T {}
    ///
    /// struct MyType;
    /// MyType.hello();
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// RFC 3624 specified a heuristic in which a supertrait item would be
    /// shadowed by a subtrait item when ambiguity occurs during item
    /// selection. In order to mitigate side-effects of this happening
    /// silently, this lint detects these cases when users want to deny them
    /// or fix the call sites.
    pub RESOLVING_TO_ITEMS_SHADOWING_SUPERTRAIT_ITEMS,
    // tRust: known issue (supertrait_item_shadowing) — It is not decided if this should
    // warn by default at the call site.
    Allow,
    "detects when a supertrait item is shadowed by a subtrait item",
    @feature_gate = supertrait_item_shadowing;
}

declare_lint! {
    /// The `rtsan_nonblocking_async` lint detects incompatible use of
    /// [`#[sanitize(realtime = "nonblocking")]`][sanitize] on async functions.
    ///
    /// [sanitize]: https://doc.rust-lang.org/nightly/unstable-book/language-features/no-sanitize.html
    /// ### Example
    ///
    /// ```rust,no_run
    /// #![feature(sanitize)]
    ///
    /// #[sanitize(realtime = "nonblocking")]
    /// async fn x() {}
    ///
    /// fn main() {
    ///     x();
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// The sanitizer only considers the async function body nonblocking. The executor, which runs on
    /// every `.await` point can run non-realtime code, without the sanitizer catching it.
    pub RTSAN_NONBLOCKING_ASYNC,
    Warn,
    r#"detects incompatible uses of `#[sanitize(realtime = "nonblocking")]` on async functions"#,
}

declare_lint! {
    /// The `rust_2021_incompatible_closure_captures` lint detects variables that aren't completely
    /// captured in Rust 2021, such that the `Drop` order of their fields may differ between
    /// Rust 2018 and 2021.
    ///
    /// It can also detect when a variable implements a trait like `Send`, but one of its fields does not,
    /// and the field is captured by a closure and used with the assumption that said field implements
    /// the same trait as the root variable.
    ///
    /// ### Example of drop reorder
    ///
    /// ```rust,edition2018,compile_fail
    /// #![deny(rust_2021_incompatible_closure_captures)]
    /// # #![allow(unused)]
    ///
    /// struct FancyInteger(i32);
    ///
    /// impl Drop for FancyInteger {
    ///     fn drop(&mut self) {
    ///         println!("Just dropped {}", self.0);
    ///     }
    /// }
    ///
    /// struct Point { x: FancyInteger, y: FancyInteger }
    ///
    /// fn main() {
    ///   let p = Point { x: FancyInteger(10), y: FancyInteger(20) };
    ///
    ///   let c = || {
    ///      let x = p.x;
    ///   };
    ///
    ///   c();
    ///
    ///   // ... More code ...
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// In the above example, `p.y` will be dropped at the end of `f` instead of
    /// with `c` in Rust 2021.
    ///
    /// ### Example of auto-trait
    ///
    /// ```rust,edition2018,compile_fail
    /// #![deny(rust_2021_incompatible_closure_captures)]
    /// use std::thread;
    ///
    /// struct Pointer(*mut i32);
    /// unsafe impl Send for Pointer {}
    ///
    /// fn main() {
    ///     let mut f = 10;
    ///     let fptr = Pointer(&mut f as *mut i32);
    ///     // SAFETY: Illustrative example in lint documentation; not executed.
    ///     thread::spawn(move || unsafe {
    ///         *fptr.0 = 20;
    ///     });
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// In the above example, only `fptr.0` is captured in Rust 2021.
    /// The field is of type `*mut i32`, which doesn't implement `Send`,
    /// making the code invalid as the field cannot be sent between threads safely.
    pub RUST_2021_INCOMPATIBLE_CLOSURE_CAPTURES,
    Allow,
    "detects closures affected by Rust 2021 changes",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(EditionSemanticsChange 2021 "disjoint-capture-in-closures"),
        explain_reason: false,
    };
}

declare_lint! {
    /// The `rust_2021_incompatible_or_patterns` lint detects usage of old versions of or-patterns.
    ///
    /// ### Example
    ///
    /// ```rust,edition2018,compile_fail
    /// #![deny(rust_2021_incompatible_or_patterns)]
    ///
    /// macro_rules! match_any {
    ///     ( $expr:expr , $( $( $pat:pat )|+ => $expr_arm:expr ),+ ) => {
    ///         match $expr {
    ///             $(
    ///                 $( $pat => $expr_arm, )+
    ///             )+
    ///         }
    ///     };
    /// }
    ///
    /// fn main() {
    ///     let result: Result<i64, i32> = Err(42);
    ///     let int: i64 = match_any!(result, Ok(i) | Err(i) => i.into());
    ///     assert_eq!(int, 42);
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// In Rust 2021, the `pat` matcher will match additional patterns, which include the `|` character.
    pub RUST_2021_INCOMPATIBLE_OR_PATTERNS,
    Allow,
    "detects usage of old versions of or-patterns",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(EditionError 2021 "or-patterns-macro-rules"),
    };
}

declare_lint! {
    /// The `rust_2021_prefixes_incompatible_syntax` lint detects identifiers that will be parsed as a
    /// prefix instead in Rust 2021.
    ///
    /// ### Example
    ///
    /// ```rust,edition2018,compile_fail
    /// #![deny(rust_2021_prefixes_incompatible_syntax)]
    ///
    /// macro_rules! m {
    ///     (z $x:expr) => ();
    /// }
    ///
    /// m!(z"hey");
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// In Rust 2015 and 2018, `z"hey"` is two tokens: the identifier `z`
    /// followed by the string literal `"hey"`. In Rust 2021, the `z` is
    /// considered a prefix for `"hey"`.
    ///
    /// This lint suggests to add whitespace between the `z` and `"hey"` tokens
    /// to keep them separated in Rust 2021.
    // Allow this lint -- rustdoc doesn't yet support threading edition into this lint's parser.
    #[allow(rustdoc::invalid_rust_codeblocks)]
    pub RUST_2021_PREFIXES_INCOMPATIBLE_SYNTAX,
    Allow,
    "identifiers that will be parsed as a prefix in Rust 2021",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(EditionError 2021 "reserving-syntax"),
    };
    crate_level_only
}

declare_lint! {
    /// The `rust_2021_prelude_collisions` lint detects the usage of trait methods which are ambiguous
    /// with traits added to the prelude in future editions.
    ///
    /// ### Example
    ///
    /// ```rust,edition2018,compile_fail
    /// #![deny(rust_2021_prelude_collisions)]
    ///
    /// trait Foo {
    ///     fn try_into(self) -> Result<String, !>;
    /// }
    ///
    /// impl Foo for &str {
    ///     fn try_into(self) -> Result<String, !> {
    ///         Ok(String::from(self))
    ///     }
    /// }
    ///
    /// fn main() {
    ///     let x: String = "3".try_into().unwrap();
    ///     //                  ^^^^^^^^
    ///     // This call to try_into matches both Foo::try_into and TryInto::try_into as
    ///     // `TryInto` has been added to the Rust prelude in 2021 edition.
    ///     println!("{x}");
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// In Rust 2021, one of the important introductions is the [prelude changes], which add
    /// `TryFrom`, `TryInto`, and `FromIterator` into the standard library's prelude. Since this
    /// results in an ambiguity as to which method/function to call when an existing `try_into`
    /// method is called via dot-call syntax or a `try_from`/`from_iter` associated function
    /// is called directly on a type.
    ///
    /// [prelude changes]: https://blog.rust-lang.org/inside-rust/2021/03/04/planning-rust-2021.html#prelude-changes
    pub RUST_2021_PRELUDE_COLLISIONS,
    Allow,
    "detects the usage of trait methods which are ambiguous with traits added to the \
        prelude in future editions",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(EditionError 2021 "prelude"),
    };
}

declare_lint! {
    /// The `rust_2024_guarded_string_incompatible_syntax` lint detects `#` tokens
    /// that will be parsed as part of a guarded string literal in Rust 2024.
    ///
    /// ### Example
    ///
    /// ```rust,edition2021,compile_fail
    /// #![deny(rust_2024_guarded_string_incompatible_syntax)]
    ///
    /// macro_rules! m {
    ///     (# $x:expr #) => ();
    ///     (# $x:expr) => ();
    /// }
    ///
    /// m!(#"hey"#);
    /// m!(#"hello");
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Prior to Rust 2024, `#"hey"#` is three tokens: the first `#`
    /// followed by the string literal `"hey"` then the final `#`.
    /// In Rust 2024, the whole sequence is considered a single token.
    ///
    /// This lint suggests to add whitespace between the leading `#`
    /// and the string to keep them separated in Rust 2024.
    // Allow this lint -- rustdoc doesn't yet support threading edition into this lint's parser.
    #[allow(rustdoc::invalid_rust_codeblocks)]
    pub RUST_2024_GUARDED_STRING_INCOMPATIBLE_SYNTAX,
    Allow,
    "will be parsed as a guarded string in Rust 2024",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(EditionError 2024 "reserved-syntax"),
    };
    crate_level_only
}

declare_lint! {
    /// The `rust_2024_incompatible_pat` lint
    /// detects patterns whose meaning will change in the Rust 2024 edition.
    ///
    /// ### Example
    ///
    /// ```rust,edition2021
    /// #![warn(rust_2024_incompatible_pat)]
    ///
    /// if let Some(&a) = &Some(&0u8) {
    ///     let _: u8 = a;
    /// }
    /// if let Some(mut _a) = &mut Some(0u8) {
    ///     _a = 7u8;
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// In Rust 2024 and above, the `mut` keyword does not reset the pattern binding mode,
    /// and nor do `&` or `&mut` patterns. The lint will suggest code that
    /// has the same meaning in all editions.
    pub RUST_2024_INCOMPATIBLE_PAT,
    Allow,
    "detects patterns whose meaning will change in Rust 2024",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(EditionSemanticsChange 2024 "match-ergonomics"),
    };
}

declare_lint! {
    /// The `rust_2024_prelude_collisions` lint detects the usage of trait methods which are ambiguous
    /// with traits added to the prelude in future editions.
    ///
    /// ### Example
    ///
    /// ```rust,edition2021,compile_fail
    /// #![deny(rust_2024_prelude_collisions)]
    /// trait Meow {
    ///     fn poll(&self) {}
    /// }
    /// impl<T> Meow for T {}
    ///
    /// fn main() {
    ///     core::pin::pin!(async {}).poll();
    ///     //                        ^^^^^^
    ///     // This call to try_into matches both Future::poll and Meow::poll as
    ///     // `Future` has been added to the Rust prelude in 2024 edition.
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Rust 2024, introduces two new additions to the standard library's prelude:
    /// `Future` and `IntoFuture`. This results in an ambiguity as to which method/function
    /// to call when an existing `poll`/`into_future` method is called via dot-call syntax or
    /// a `poll`/`into_future` associated function is called directly on a type.
    ///
    pub RUST_2024_PRELUDE_COLLISIONS,
    Allow,
    "detects the usage of trait methods which are ambiguous with traits added to the \
        prelude in future editions",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(EditionError 2024 "prelude"),
    };
}

declare_lint! {
    /// The `self_constructor_from_outer_item` lint detects cases where the `Self` constructor
    /// was silently allowed due to a bug in the resolver, and which may produce surprising
    /// and unintended behavior.
    ///
    /// Using a `Self` type alias from an outer item was never intended, but was silently allowed.
    /// This is deprecated -- and is a hard error when the `Self` type alias references generics
    /// that are not in scope.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(self_constructor_from_outer_item)]
    ///
    /// struct S0(usize);
    ///
    /// impl S0 {
    ///     fn foo() {
    ///         const C: S0 = Self(0);
    ///         fn bar() -> S0 {
    ///             Self(0)
    ///         }
    ///     }
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// The `Self` type alias should not be reachable because nested items are not associated with
    /// the scope of the parameters from the parent item.
    pub SELF_CONSTRUCTOR_FROM_OUTER_ITEM,
    Warn,
    "detect unsupported use of `Self` from outer item",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #124186),
    };
}

declare_lint! {
    /// The `semicolon_in_expressions_from_macros` lint detects trailing semicolons
    /// in macro bodies when the macro is invoked in expression position.
    /// This was previous accepted, but is being phased out.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(semicolon_in_expressions_from_macros)]
    /// macro_rules! foo {
    ///     () => { true; }
    /// }
    ///
    /// fn main() {
    ///     let val = match true {
    ///         true => false,
    ///         _ => foo!()
    ///     };
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Previous, Rust ignored trailing semicolon in a macro
    /// body when a macro was invoked in expression position.
    /// However, this makes the treatment of semicolons in the language
    /// inconsistent, and could lead to unexpected runtime behavior
    /// in some circumstances (e.g. if the macro author expects
    /// a value to be dropped).
    ///
    /// This is a [future-incompatible] lint to transition this
    /// to a hard error in the future. See [issue #79813] for more details.
    ///
    /// [issue #79813]: https://github.com/rust-lang/rust/issues/79813
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub SEMICOLON_IN_EXPRESSIONS_FROM_MACROS,
    Deny,
    "trailing semicolon in macro body used as expression",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #79813),
        report_in_deps: true,
    };
}

declare_lint! {
    /// The `shadowing_supertrait_items` lint detects when the
    /// definition of an item that is provided by both a subtrait and
    /// supertrait is shadowed, preferring the subtrait.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![feature(supertrait_item_shadowing)]
    /// #![deny(shadowing_supertrait_items)]
    ///
    /// trait Upstream {
    ///     fn hello(&self) {}
    /// }
    /// impl<T> Upstream for T {}
    ///
    /// trait Downstream: Upstream {
    ///     fn hello(&self) {}
    /// }
    /// impl<T> Downstream for T {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// RFC 3624 specified a heuristic in which a supertrait item would be
    /// shadowed by a subtrait item when ambiguity occurs during item
    /// selection. In order to mitigate side-effects of this happening
    /// silently, this lint detects these cases when users want to deny them
    /// or fix their trait definitions.
    pub SHADOWING_SUPERTRAIT_ITEMS,
    // tRust: known issue (supertrait_item_shadowing) — It is not decided if this should
    // warn by default at the usage site.
    Allow,
    "detects when a supertrait item is shadowed by a subtrait item",
    @feature_gate = supertrait_item_shadowing;
}

declare_lint! {
    /// The `single_use_lifetimes` lint detects lifetimes that are only used
    /// once.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(single_use_lifetimes)]
    ///
    /// fn foo<'a>(x: &'a u32) {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Specifying an explicit lifetime like `'a` in a function or `impl`
    /// should only be used to link together two things. Otherwise, you should
    /// just use `'_` to indicate that the lifetime is not linked to anything,
    /// or elide the lifetime altogether if possible.
    ///
    /// This lint is "allow" by default because it was introduced at a time
    /// when `'_` and elided lifetimes were first being introduced, and this
    /// lint would be too noisy. Also, there are some known false positives
    /// that it produces. See [RFC 2115] for historical context, and [issue
    /// #44752] for more details.
    ///
    /// [RFC 2115]: https://github.com/rust-lang/rfcs/blob/master/text/2115-argument-lifetimes.md
    /// [issue #44752]: https://github.com/rust-lang/rust/issues/44752
    pub SINGLE_USE_LIFETIMES,
    Allow,
    "detects lifetime parameters that are only used once"
}

declare_lint! {
    /// The `stable_features` lint detects a [`feature` attribute] that
    /// has since been made stable.
    ///
    /// [`feature` attribute]: https://doc.rust-lang.org/nightly/unstable-book/
    ///
    /// ### Example
    ///
    /// ```rust
    /// #![feature(test_accepted_feature)]
    /// fn main() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// When a feature is stabilized, it is no longer necessary to include a
    /// `#![feature]` attribute for it. To fix, simply remove the
    /// `#![feature]` attribute.
    pub STABLE_FEATURES,
    Warn,
    "stable features found in `#[feature]` directive"
}

declare_lint! {
    /// The `tail_call_track_caller` lint detects usage of `become` attempting to tail call
    /// a function marked with `#[track_caller]`.
    ///
    /// ### Example
    ///
    /// ```rust
    /// #![feature(explicit_tail_calls)]
    /// #![expect(incomplete_features)]
    ///
    /// #[track_caller]
    /// fn f() {}
    ///
    /// fn g() {
    ///     become f();
    /// }
    ///
    /// g();
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Due to implementation details of tail calls and `#[track_caller]` attribute, calls to
    /// functions marked with `#[track_caller]` cannot become tail calls. As such using `become`
    /// is no different than a normal call (except for changes in drop order).
    pub TAIL_CALL_TRACK_CALLER,
    Warn,
    "detects tail calls of functions marked with `#[track_caller]`",
    @feature_gate = explicit_tail_calls;
}

declare_lint! {
    /// The `tail_expr_drop_order` lint looks for those values generated at the tail expression location,
    /// that runs a custom `Drop` destructor.
    /// Some of them may be dropped earlier in Edition 2024 that they used to in Edition 2021 and prior.
    /// This lint detects those cases and provides you information on those values and their custom destructor implementations.
    /// Your discretion on this information is required.
    ///
    /// ### Example
    /// ```rust,edition2021
    /// #![warn(tail_expr_drop_order)]
    /// struct Droppy(i32);
    /// impl Droppy {
    ///     fn get(&self) -> i32 {
    ///         self.0
    ///     }
    /// }
    /// impl Drop for Droppy {
    ///     fn drop(&mut self) {
    ///         // This is a custom destructor and it induces side-effects that is observable
    ///         // especially when the drop order at a tail expression changes.
    ///         println!("loud drop {}", self.0);
    ///     }
    /// }
    /// fn edition_2021() -> i32 {
    ///     let another_droppy = Droppy(0);
    ///     Droppy(1).get()
    /// }
    /// fn main() {
    ///     edition_2021();
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// In tail expression of blocks or function bodies,
    /// values of type with significant `Drop` implementation has an ill-specified drop order
    /// before Edition 2024 so that they are dropped only after dropping local variables.
    /// Edition 2024 introduces a new rule with drop orders for them,
    /// so that they are dropped first before dropping local variables.
    ///
    /// A significant `Drop::drop` destructor here refers to an explicit, arbitrary
    /// implementation of the `Drop` trait on the type, with exceptions including `Vec`,
    /// `Box`, `Rc`, `BTreeMap` and `HashMap` that are marked by the compiler otherwise
    /// so long that the generic types have no significant destructor recursively.
    /// In other words, a type has a significant drop destructor when it has a `Drop` implementation
    /// or its destructor invokes a significant destructor on a type.
    /// Since we cannot completely reason about the change by just inspecting the existence of
    /// a significant destructor, this lint remains only a suggestion and is set to `allow` by default.
    ///
    /// This lint only points out the issue with `Droppy`, which will be dropped before `another_droppy`
    /// does in Edition 2024.
    /// No fix will be proposed by this lint.
    /// However, the most probable fix is to hoist `Droppy` into its own local variable binding.
    /// ```rust
    /// struct Droppy(i32);
    /// impl Droppy {
    ///     fn get(&self) -> i32 {
    ///         self.0
    ///     }
    /// }
    /// fn edition_2024() -> i32 {
    ///     let value = Droppy(0);
    ///     let another_droppy = Droppy(1);
    ///     value.get()
    /// }
    /// ```
    pub TAIL_EXPR_DROP_ORDER,
    Allow,
    "Detect and warn on significant change in drop order in tail expression location",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(EditionSemanticsChange 2024 "temporary-tail-expr-scope"),
    };
}

declare_lint! {
    /// The `test_unstable_lint` lint tests unstable lints and is perma-unstable.
    ///
    /// ### Example
    ///
    /// ```rust
    /// // This lint is intentionally used to test the compiler's behavior
    /// // when an unstable lint is enabled without the corresponding feature gate.
    /// #![allow(test_unstable_lint)]
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// In order to test the behavior of unstable lints, a permanently-unstable
    /// lint is required. This lint can be used to trigger warnings and errors
    /// from the compiler related to unstable lints.
    pub TEST_UNSTABLE_LINT,
    Deny,
    "this unstable lint is only for testing",
    @feature_gate = test_unstable_lint;
}

declare_lint! {
    /// The `text_direction_codepoint_in_comment` lint detects Unicode codepoints in comments that
    /// change the visual representation of text on screen in a way that does not correspond to
    /// their on memory representation.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(text_direction_codepoint_in_comment)]
    /// fn main() {
    #[doc = "    println!(\"{:?}\"); // '\u{202E}');"]
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Unicode allows changing the visual flow of text on screen in order to support scripts that
    /// are written right-to-left, but a specially crafted comment can make code that will be
    /// compiled appear to be part of a comment, depending on the software used to read the code.
    /// To avoid potential problems or confusion, such as in CVE-2021-42574, by default we deny
    /// their use.
    pub TEXT_DIRECTION_CODEPOINT_IN_COMMENT,
    Deny,
    "invisible directionality-changing codepoints in comment",
    crate_level_only
}

declare_lint! {
    /// The `text_direction_codepoint_in_literal` lint detects Unicode codepoints that change the
    /// visual representation of text on screen in a way that does not correspond to their on
    /// memory representation.
    ///
    /// ### Explanation
    ///
    /// The unicode characters `\u{202A}`, `\u{202B}`, `\u{202D}`, `\u{202E}`, `\u{2066}`,
    /// `\u{2067}`, `\u{2068}`, `\u{202C}` and `\u{2069}` make the flow of text on screen change
    /// its direction on software that supports these codepoints. This makes the text "abc" display
    /// as "cba" on screen. By leveraging software that supports these, people can write specially
    /// crafted literals that make the surrounding code seem like it's performing one action, when
    /// in reality it is performing another. Because of this, we proactively lint against their
    /// presence to avoid surprises.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(text_direction_codepoint_in_literal)]
    /// fn main() {
    // ` - convince tidy that backticks match
    #[doc = "    println!(\"{:?}\", '\u{202E}');"]
    // `
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    pub TEXT_DIRECTION_CODEPOINT_IN_LITERAL,
    Deny,
    "detect special Unicode codepoints that affect the visual representation of text on screen, \
     changing the direction in which text flows",
    crate_level_only
}

declare_lint! {
    /// The `trivial_casts` lint detects trivial casts which could be replaced
    /// with coercion, which may require a temporary variable.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(trivial_casts)]
    /// let x: &u32 = &42;
    /// let y = x as *const u32;
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// A trivial cast is a cast `e as T` where `e` has type `U` and `U` is a
    /// subtype of `T`. This type of cast is usually unnecessary, as it can be
    /// usually be inferred.
    ///
    /// This lint is "allow" by default because there are situations, such as
    /// with FFI interfaces or complex type aliases, where it triggers
    /// incorrectly, or in situations where it will be more difficult to
    /// clearly express the intent. It may be possible that this will become a
    /// warning in the future, possibly with an explicit syntax for coercions
    /// providing a convenient way to work around the current issues.
    /// See [RFC 401 (coercions)][rfc-401], [RFC 803 (type ascription)][rfc-803] and
    /// [RFC 3307 (remove type ascription)][rfc-3307] for historical context.
    ///
    /// [rfc-401]: https://github.com/rust-lang/rfcs/blob/master/text/0401-coercions.md
    /// [rfc-803]: https://github.com/rust-lang/rfcs/blob/master/text/0803-type-ascription.md
    /// [rfc-3307]: https://github.com/rust-lang/rfcs/blob/master/text/3307-de-rfc-type-ascription.md
    pub TRIVIAL_CASTS,
    Allow,
    "detects trivial casts which could be removed"
}

declare_lint! {
    /// The `trivial_numeric_casts` lint detects trivial numeric casts of types
    /// which could be removed.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(trivial_numeric_casts)]
    /// let x = 42_i32 as i32;
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// A trivial numeric cast is a cast of a numeric type to the same numeric
    /// type. This type of cast is usually unnecessary.
    ///
    /// This lint is "allow" by default because there are situations, such as
    /// with FFI interfaces or complex type aliases, where it triggers
    /// incorrectly, or in situations where it will be more difficult to
    /// clearly express the intent. It may be possible that this will become a
    /// warning in the future, possibly with an explicit syntax for coercions
    /// providing a convenient way to work around the current issues.
    /// See [RFC 401 (coercions)][rfc-401], [RFC 803 (type ascription)][rfc-803] and
    /// [RFC 3307 (remove type ascription)][rfc-3307] for historical context.
    ///
    /// [rfc-401]: https://github.com/rust-lang/rfcs/blob/master/text/0401-coercions.md
    /// [rfc-803]: https://github.com/rust-lang/rfcs/blob/master/text/0803-type-ascription.md
    /// [rfc-3307]: https://github.com/rust-lang/rfcs/blob/master/text/3307-de-rfc-type-ascription.md
    pub TRIVIAL_NUMERIC_CASTS,
    Allow,
    "detects trivial casts of numeric types which could be removed"
}

declare_lint! {
    /// The `tyvar_behind_raw_pointer` lint detects raw pointer to an
    /// inference variable.
    ///
    /// ### Example
    ///
    /// ```rust,edition2015
    /// // edition 2015
    /// let data = std::ptr::null();
    /// let _ = &data as *const *const ();
    ///
    /// if data.is_null() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// This kind of inference was previously allowed, but with the future
    /// arrival of [arbitrary self types], this can introduce ambiguity. To
    /// resolve this, use an explicit type instead of relying on type
    /// inference.
    ///
    /// This is a [future-incompatible] lint to transition this to a hard
    /// error in the 2018 edition. See [issue #46906] for more details. This
    /// is currently a hard-error on the 2018 edition, and is "warn" by
    /// default in the 2015 edition.
    ///
    /// [arbitrary self types]: https://github.com/rust-lang/rust/issues/44874
    /// [issue #46906]: https://github.com/rust-lang/rust/issues/46906
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub TYVAR_BEHIND_RAW_POINTER,
    Warn,
    "raw pointer to an inference variable",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(EditionError 2018 "tyvar-behind-raw-pointer"),
    };
}

declare_lint! {
    /// The `unconditional_panic` lint detects an operation that will cause a
    /// panic at runtime.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// # #![allow(unused)]
    /// let x = 1 / 0;
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// This lint detects code that is very likely incorrect because it will
    /// always panic, such as division by zero and out-of-bounds array
    /// accesses. Consider adjusting your code if this is a bug, or using the
    /// `panic!` or `unreachable!` macro instead in case the panic is intended.
    pub UNCONDITIONAL_PANIC,
    Deny,
    "operation will cause a panic at runtime",
    @eval_always = true
}

declare_lint! {
    /// The `unconditional_recursion` lint detects functions that cannot
    /// return without calling themselves.
    ///
    /// ### Example
    ///
    /// ```rust
    /// fn foo() {
    ///     foo();
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// It is usually a mistake to have a recursive call that does not have
    /// some condition to cause it to terminate. If you really intend to have
    /// an infinite loop, using a `loop` expression is recommended.
    pub UNCONDITIONAL_RECURSION,
    Warn,
    "functions that cannot return without calling themselves"
}

declare_lint! {
    /// The `uncovered_param_in_projection` lint detects a violation of one of Rust's orphan rules for
    /// foreign trait implementations that concerns the use of type parameters inside trait associated
    /// type paths ("projections") whose output may not be a local type that is mistakenly considered
    /// to "cover" said parameters which is **unsound** and which may be rejected by a future version
    /// of the compiler.
    ///
    /// Originally reported in [#99554].
    ///
    /// [#99554]: https://github.com/rust-lang/rust/issues/99554
    ///
    /// ### Example
    ///
    /// ```rust,ignore (dependent)
    /// // dependency.rs
    /// #![crate_type = "lib"]
    ///
    /// pub trait Trait<T, U> {}
    /// ```
    ///
    /// ```edition2021,ignore (needs dependency)
    /// // dependent.rs
    /// trait Identity {
    ///     type Output;
    /// }
    ///
    /// impl<T> Identity for T {
    ///     type Output = T;
    /// }
    ///
    /// struct Local;
    ///
    /// impl<T> dependency::Trait<Local, T> for <T as Identity>::Output {}
    ///
    /// fn main() {}
    /// ```
    ///
    /// This will produce:
    ///
    /// ```text
    /// warning[E0210]: type parameter `T` must be covered by another type when it appears before the first local type (`Local`)
    ///   --> dependent.rs:11:6
    ///    |
    /// 11 | impl<T> dependency::Trait<Local, T> for <T as Identity>::Output {}
    ///    |      ^ type parameter `T` must be covered by another type when it appears before the first local type (`Local`)
    ///    |
    ///    = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
    ///    = note: for more information, see issue #124559 <https://github.com/rust-lang/rust/issues/124559>
    ///    = note: implementing a foreign trait is only possible if at least one of the types for which it is implemented is local, and no uncovered type parameters appear before that first local type
    ///    = note: in this case, 'before' refers to the following order: `impl<..> ForeignTrait<T1, ..., Tn> for T0`, where `T0` is the first and `Tn` is the last
    ///    = note: `#[warn(uncovered_param_in_projection)]` on by default
    /// ```
    ///
    /// ### Explanation
    ///
    /// tRust: known issue (fmease) — Write explainer.
    pub UNCOVERED_PARAM_IN_PROJECTION,
    Warn,
    "impl contains type parameters that are not covered",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #124559),
    };
}

declare_lint! {
    /// The `unexpected_cfgs` lint detects unexpected conditional compilation conditions.
    ///
    /// ### Example
    ///
    /// ```text
    /// rustc --check-cfg 'cfg()'
    /// ```
    ///
    /// ```rust,ignore (needs command line option)
    /// #[cfg(widnows)]
    /// fn foo() {}
    /// ```
    ///
    /// This will produce:
    ///
    /// ```text
    /// warning: unexpected `cfg` condition name: `widnows`
    ///  --> lint_example.rs:1:7
    ///   |
    /// 1 | #[cfg(widnows)]
    ///   |       ^^^^^^^
    ///   |
    ///   = note: `#[warn(unexpected_cfgs)]` on by default
    /// ```
    ///
    /// ### Explanation
    ///
    /// This lint is only active when [`--check-cfg`][check-cfg] arguments are being
    /// passed to the compiler and triggers whenever an unexpected condition name or value is
    /// used.
    ///
    /// See the [Checking Conditional Configurations][check-cfg] section for more
    /// details.
    ///
    /// See the [Cargo Specifics][unexpected_cfgs_lint_config] section for configuring this lint in
    /// `Cargo.toml`.
    ///
    /// [check-cfg]: https://doc.rust-lang.org/nightly/rustc/check-cfg.html
    /// [unexpected_cfgs_lint_config]: https://doc.rust-lang.org/nightly/rustc/check-cfg/cargo-specifics.html#check-cfg-in-lintsrust-table
    pub UNEXPECTED_CFGS,
    Warn,
    "detects unexpected names and values in `#[cfg]` conditions",
    report_in_external_macro
}

declare_lint! {
    /// The `unfulfilled_lint_expectations` lint detects when a lint expectation is
    /// unfulfilled.
    ///
    /// ### Example
    ///
    /// ```rust
    /// #[expect(unused_variables)]
    /// let x = 10;
    /// println!("{}", x);
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// The `#[expect]` attribute can be used to create a lint expectation. The
    /// expectation is fulfilled, if a `#[warn]` attribute at the same location
    /// would result in a lint emission. If the expectation is unfulfilled,
    /// because no lint was emitted, this lint will be emitted on the attribute.
    ///
    pub UNFULFILLED_LINT_EXPECTATIONS,
    Warn,
    "unfulfilled lint expectation"
}

declare_lint! {
    /// The `uninhabited_static` lint detects uninhabited statics.
    ///
    /// ### Example
    ///
    /// ```rust
    /// enum Void {}
    /// unsafe extern {
    ///     static EXTERN: Void;
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Statics with an uninhabited type can never be initialized, so they are impossible to define.
    /// However, this can be side-stepped with an `extern static`, leading to problems later in the
    /// compiler which assumes that there are no initialized uninhabited places (such as locals or
    /// statics). This was accidentally allowed, but is being phased out.
    pub UNINHABITED_STATIC,
    Warn,
    "uninhabited static",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #74840),
    };
}
