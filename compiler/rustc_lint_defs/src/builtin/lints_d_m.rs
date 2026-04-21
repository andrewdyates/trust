//! Built-in lint definitions (D-M).
//!
//! This file is part of the `builtin` module split. See `mod.rs` for the
//! `declare_lint_pass!` that registers these lints.

// tRust: split from builtin.rs for file size reduction
use crate::{declare_lint, fcw};

declare_lint! {
    /// The `duplicate_macro_attributes` lint detects when a `#[test]`-like built-in macro
    /// attribute is duplicated on an item. This lint may trigger on `bench`, `cfg_eval`, `test`
    /// and `test_case`.
    ///
    /// ### Example
    ///
    /// ```rust,ignore (needs --test)
    /// #[test]
    /// #[test]
    /// fn foo() {}
    /// ```
    ///
    /// This will produce:
    ///
    /// ```text
    /// warning: duplicated attribute
    ///  --> src/lib.rs:2:1
    ///   |
    /// 2 | #[test]
    ///   | ^^^^^^^
    ///   |
    ///   = note: `#[warn(duplicate_macro_attributes)]` on by default
    /// ```
    ///
    /// ### Explanation
    ///
    /// A duplicated attribute may erroneously originate from a copy-paste and the effect of it
    /// being duplicated may not be obvious or desirable.
    ///
    /// For instance, doubling the `#[test]` attributes registers the test to be run twice with no
    /// change to its environment.
    ///
    /// [issue #90979]: https://github.com/rust-lang/rust/issues/90979
    pub DUPLICATE_MACRO_ATTRIBUTES,
    Warn,
    "duplicated attribute"
}

declare_lint! {
    /// The `elided_lifetimes_in_associated_constant` lint detects elided lifetimes
    /// in associated constants when there are other lifetimes in scope. This was
    /// accidentally supported, and this lint was later relaxed to allow eliding
    /// lifetimes to `'static` when there are no lifetimes in scope.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(elided_lifetimes_in_associated_constant)]
    ///
    /// struct Foo<'a>(&'a ());
    ///
    /// impl<'a> Foo<'a> {
    ///     const STR: &str = "hello, world";
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Previous version of Rust
    ///
    /// Implicit static-in-const behavior was decided [against] for associated
    /// constants because of ambiguity. This, however, regressed and the compiler
    /// erroneously treats elided lifetimes in associated constants as lifetime
    /// parameters on the impl.
    ///
    /// This is a [future-incompatible] lint to transition this to a
    /// hard error in the future.
    ///
    /// [against]: https://github.com/rust-lang/rust/issues/38831
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub ELIDED_LIFETIMES_IN_ASSOCIATED_CONSTANT,
    Deny,
    "elided lifetimes cannot be used in associated constants in impls",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #115010),
    };
}

declare_lint! {
    /// The `elided_lifetimes_in_paths` lint detects the use of hidden
    /// lifetime parameters.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(elided_lifetimes_in_paths)]
    /// #![deny(warnings)]
    /// struct Foo<'a> {
    ///     x: &'a u32
    /// }
    ///
    /// fn foo(x: &Foo) {
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Elided lifetime parameters can make it difficult to see at a glance
    /// that borrowing is occurring. This lint ensures that lifetime
    /// parameters are always explicitly stated, even if it is the `'_`
    /// [placeholder lifetime].
    ///
    /// This lint is "allow" by default because it has some known issues, and
    /// may require a significant transition for old code.
    ///
    /// [placeholder lifetime]: https://doc.rust-lang.org/reference/lifetime-elision.html#lifetime-elision-in-functions
    pub ELIDED_LIFETIMES_IN_PATHS,
    Allow,
    "hidden lifetime parameters in types are deprecated"
}

declare_lint! {
    /// The `explicit_builtin_cfgs_in_flags` lint detects builtin cfgs set via the `--cfg` flag.
    ///
    /// ### Example
    ///
    /// ```text
    /// rustc --cfg unix
    /// ```
    ///
    /// ```rust,ignore (needs command line option)
    /// fn main() {}
    /// ```
    ///
    /// This will produce:
    ///
    /// ```text
    /// error: unexpected `--cfg unix` flag
    ///   |
    ///   = note: config `unix` is only supposed to be controlled by `--target`
    ///   = note: manually setting a built-in cfg can and does create incoherent behaviors
    ///   = note: `#[deny(explicit_builtin_cfgs_in_flags)]` on by default
    /// ```
    ///
    /// ### Explanation
    ///
    /// Setting builtin cfgs can and does produce incoherent behavior, it's better to the use
    /// the appropriate `rustc` flag that controls the config. For example setting the `windows`
    /// cfg but on Linux based target.
    pub EXPLICIT_BUILTIN_CFGS_IN_FLAGS,
    Deny,
    "detects builtin cfgs set via the `--cfg`"
}

declare_lint! {
    /// The `explicit_outlives_requirements` lint detects unnecessary
    /// lifetime bounds that can be inferred.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// # #![allow(unused)]
    /// #![deny(explicit_outlives_requirements)]
    /// #![deny(warnings)]
    ///
    /// struct SharedRef<'a, T>
    /// where
    ///     T: 'a,
    /// {
    ///     data: &'a T,
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// If a `struct` contains a reference, such as `&'a T`, the compiler
    /// requires that `T` outlives the lifetime `'a`. This historically
    /// required writing an explicit lifetime bound to indicate this
    /// requirement. However, this can be overly explicit, causing clutter and
    /// unnecessary complexity. The language was changed to automatically
    /// infer the bound if it is not specified. Specifically, if the struct
    /// contains a reference, directly or indirectly, to `T` with lifetime
    /// `'x`, then it will infer that `T: 'x` is a requirement.
    ///
    /// This lint is "allow" by default because it can be noisy for existing
    /// code that already had these requirements. This is a stylistic choice,
    /// as it is still valid to explicitly state the bound. It also has some
    /// false positives that can cause confusion.
    ///
    /// See [RFC 2093] for more details.
    ///
    /// [RFC 2093]: https://github.com/rust-lang/rfcs/blob/master/text/2093-infer-outlives.md
    pub EXPLICIT_OUTLIVES_REQUIREMENTS,
    Allow,
    "outlives requirements can be inferred"
}

declare_lint! {
    /// The `exported_private_dependencies` lint detects private dependencies
    /// that are exposed in a public interface.
    ///
    /// ### Example
    ///
    /// ```rust,ignore (needs-dependency)
    /// pub fn foo() -> Option<some_private_dependency::Thing> {
    ///     None
    /// }
    /// ```
    ///
    /// This will produce:
    ///
    /// ```text
    /// warning: type `bar::Thing` from private dependency 'bar' in public interface
    ///  --> src/lib.rs:3:1
    ///   |
    /// 3 | pub fn foo() -> Option<bar::Thing> {
    ///   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    ///   |
    ///   = note: `#[warn(exported_private_dependencies)]` on by default
    /// ```
    ///
    /// ### Explanation
    ///
    /// Dependencies can be marked as "private" to indicate that they are not
    /// exposed in the public interface of a crate. This can be used by Cargo
    /// to independently resolve those dependencies because it can assume it
    /// does not need to unify them with other packages using that same
    /// dependency. This lint is an indication of a violation of that
    /// contract.
    ///
    /// To fix this, avoid exposing the dependency in your public interface.
    /// Or, switch the dependency to a public dependency.
    ///
    /// Note that support for this is only available on the nightly channel.
    /// See [RFC 1977] for more details, as well as the [Cargo documentation].
    ///
    /// [RFC 1977]: https://github.com/rust-lang/rfcs/blob/master/text/1977-public-private-dependencies.md
    /// [Cargo documentation]: https://doc.rust-lang.org/nightly/cargo/reference/unstable.html#public-dependency
    pub EXPORTED_PRIVATE_DEPENDENCIES,
    Warn,
    "public interface leaks type from a private dependency"
}

declare_lint! {
    /// The `ffi_unwind_calls` lint detects calls to foreign functions or function pointers with
    /// `C-unwind` or other FFI-unwind ABIs.
    ///
    /// ### Example
    ///
    /// ```rust
    /// #![warn(ffi_unwind_calls)]
    ///
    /// unsafe extern "C-unwind" {
    ///     fn foo();
    /// }
    ///
    /// fn bar() {
    ///     // SAFETY: Illustrative example in lint documentation; not executed.
    ///     unsafe { foo(); }
    ///     let ptr: unsafe extern "C-unwind" fn() = foo;
    ///     // SAFETY: Illustrative example in lint documentation; not executed.
    ///     unsafe { ptr(); }
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// For crates containing such calls, if they are compiled with `-C panic=unwind` then the
    /// produced library cannot be linked with crates compiled with `-C panic=abort`. For crates
    /// that desire this ability it is therefore necessary to avoid such calls.
    pub FFI_UNWIND_CALLS,
    Allow,
    "call to foreign functions or function pointers with FFI-unwind ABI"
}

declare_lint! {
    /// The `forbidden_lint_groups` lint detects violations of
    /// `forbid` applied to a lint group. Due to a bug in the compiler,
    /// these used to be overlooked entirely. They now generate a warning.
    ///
    /// ### Example
    ///
    /// ```rust
    /// #![forbid(warnings)]
    /// #![warn(bad_style)]
    ///
    /// fn main() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Recommended fix
    ///
    /// If your crate is using `#![forbid(warnings)]`,
    /// we recommend that you change to `#![deny(warnings)]`.
    ///
    /// ### Explanation
    ///
    /// Due to a compiler bug, applying `forbid` to lint groups
    /// previously had no effect. The bug is now fixed but instead of
    /// enforcing `forbid` we issue this future-compatibility warning
    /// to avoid breaking existing crates.
    pub FORBIDDEN_LINT_GROUPS,
    Warn,
    "applying forbid to lint-groups",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #81670),
        report_in_deps: true,
    };
}

declare_lint! {
    /// The `function_item_references` lint detects function references that are
    /// formatted with [`fmt::Pointer`] or transmuted.
    ///
    /// [`fmt::Pointer`]: https://doc.rust-lang.org/std/fmt/trait.Pointer.html
    ///
    /// ### Example
    ///
    /// ```rust
    /// fn foo() { }
    ///
    /// fn main() {
    ///     println!("{:p}", &foo);
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Taking a reference to a function may be mistaken as a way to obtain a
    /// pointer to that function. This can give unexpected results when
    /// formatting the reference as a pointer or transmuting it. This lint is
    /// issued when function references are formatted as pointers, passed as
    /// arguments bound by [`fmt::Pointer`] or transmuted.
    pub FUNCTION_ITEM_REFERENCES,
    Warn,
    "suggest casting to a function pointer when attempting to take references to function items",
}

declare_lint! {
    /// The `fuzzy_provenance_casts` lint detects an `as` cast between an integer
    /// and a pointer.
    ///
    /// ### Example
    ///
    /// ```rust
    /// #![feature(strict_provenance_lints)]
    /// #![warn(fuzzy_provenance_casts)]
    ///
    /// fn main() {
    ///     let _dangling = 16_usize as *const u8;
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// This lint is part of the strict provenance effort, see [issue #95228].
    /// Casting an integer to a pointer is considered bad style, as a pointer
    /// contains, besides the *address* also a *provenance*, indicating what
    /// memory the pointer is allowed to read/write. Casting an integer, which
    /// doesn't have provenance, to a pointer requires the compiler to assign
    /// (guess) provenance. The compiler assigns "all exposed valid" (see the
    /// docs of [`ptr::with_exposed_provenance`] for more information about this
    /// "exposing"). This penalizes the optimiser and is not well suited for
    /// dynamic analysis/dynamic program verification (e.g. Miri or CHERI
    /// platforms).
    ///
    /// It is much better to use [`ptr::with_addr`] instead to specify the
    /// provenance you want. If using this function is not possible because the
    /// code relies on exposed provenance then there is as an escape hatch
    /// [`ptr::with_exposed_provenance`].
    ///
    /// [issue #95228]: https://github.com/rust-lang/rust/issues/95228
    /// [`ptr::with_addr`]: https://doc.rust-lang.org/core/primitive.pointer.html#method.with_addr
    /// [`ptr::with_exposed_provenance`]: https://doc.rust-lang.org/core/ptr/fn.with_exposed_provenance.html
    pub FUZZY_PROVENANCE_CASTS,
    Allow,
    "a fuzzy integer to pointer cast is used",
    @feature_gate = strict_provenance_lints;
}

declare_lint! {
    /// The `hidden_glob_reexports` lint detects cases where glob re-export items are shadowed by
    /// private items.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(hidden_glob_reexports)]
    ///
    /// pub mod upstream {
    ///     mod inner { pub struct Foo {}; pub struct Bar {}; }
    ///     pub use self::inner::*;
    ///     struct Foo {} // private item shadows `inner::Foo`
    /// }
    ///
    /// // mod downstream {
    /// //     fn test() {
    /// //         let _ = crate::upstream::Foo; // inaccessible
    /// //     }
    /// // }
    ///
    /// pub fn main() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// This was previously accepted without any errors or warnings but it could silently break a
    /// crate's downstream user code. If the `struct Foo` was added, `dep::inner::Foo` would
    /// silently become inaccessible and trigger a "`struct `Foo` is private`" visibility error at
    /// the downstream use site.
    pub HIDDEN_GLOB_REEXPORTS,
    Warn,
    "name introduced by a private item shadows a name introduced by a public glob re-export",
}

declare_lint! {
    /// The `ill_formed_attribute_input` lint detects ill-formed attribute
    /// inputs that were previously accepted and used in practice.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #[inline = "this is not valid"]
    /// fn foo() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Previously, inputs for many built-in attributes weren't validated and
    /// nonsensical attribute inputs were accepted. After validation was
    /// added, it was determined that some existing projects made use of these
    /// invalid forms. This is a [future-incompatible] lint to transition this
    /// to a hard error in the future. See [issue #57571] for more details.
    ///
    /// Check the [attribute reference] for details on the valid inputs for
    /// attributes.
    ///
    /// [issue #57571]: https://github.com/rust-lang/rust/issues/57571
    /// [attribute reference]: https://doc.rust-lang.org/nightly/reference/attributes.html
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub ILL_FORMED_ATTRIBUTE_INPUT,
    Deny,
    "ill-formed attribute inputs that were previously accepted and used in practice",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #57571),
        report_in_deps: true,
    };
    crate_level_only
}

declare_lint! {
    /// The `incomplete_include` lint detects the use of the [`include!`]
    /// macro with a file that contains more than one expression.
    ///
    /// [`include!`]: https://doc.rust-lang.org/std/macro.include.html
    ///
    /// ### Example
    ///
    /// ```rust,ignore (needs separate file)
    /// fn main() {
    ///     include!("foo.txt");
    /// }
    /// ```
    ///
    /// where the file `foo.txt` contains:
    ///
    /// ```text
    /// println!("hi!");
    /// ```
    ///
    /// produces:
    ///
    /// ```text
    /// error: include macro expected single expression in source
    ///  --> foo.txt:1:14
    ///   |
    /// 1 | println!("1");
    ///   |              ^
    ///   |
    ///   = note: `#[deny(incomplete_include)]` on by default
    /// ```
    ///
    /// ### Explanation
    ///
    /// The [`include!`] macro is currently only intended to be used to
    /// include a single [expression] or multiple [items]. Historically it
    /// would ignore any contents after the first expression, but that can be
    /// confusing. In the example above, the `println!` expression ends just
    /// before the semicolon, making the semicolon "extra" information that is
    /// ignored. Perhaps even more surprising, if the included file had
    /// multiple print statements, the subsequent ones would be ignored!
    ///
    /// One workaround is to place the contents in braces to create a [block
    /// expression]. Also consider alternatives, like using functions to
    /// encapsulate the expressions, or use [proc-macros].
    ///
    /// This is a lint instead of a hard error because existing projects were
    /// found to hit this error. To be cautious, it is a lint for now. The
    /// future semantics of the `include!` macro are also uncertain, see
    /// [issue #35560].
    ///
    /// [items]: https://doc.rust-lang.org/reference/items.html
    /// [expression]: https://doc.rust-lang.org/reference/expressions.html
    /// [block expression]: https://doc.rust-lang.org/reference/expressions/block-expr.html
    /// [proc-macros]: https://doc.rust-lang.org/reference/procedural-macros.html
    /// [issue #35560]: https://github.com/rust-lang/rust/issues/35560
    pub INCOMPLETE_INCLUDE,
    Deny,
    "trailing content in included file"
}

declare_lint! {
    /// The `ineffective_unstable_trait_impl` lint detects `#[unstable]` attributes which are not used.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![feature(staged_api)]
    ///
    /// #[derive(Clone)]
    /// #[stable(feature = "x", since = "1")]
    /// struct S {}
    ///
    /// #[unstable(feature = "y", issue = "none")]
    /// impl Copy for S {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// `staged_api` does not currently support using a stability attribute on `impl` blocks.
    /// `impl`s are always stable if both the type and trait are stable, and always unstable otherwise.
    pub INEFFECTIVE_UNSTABLE_TRAIT_IMPL,
    Deny,
    "detects `#[unstable]` on stable trait implementations for stable types"
}

declare_lint! {
    /// The `inline_always_mismatching_target_features` lint will trigger when a
    /// function with the `#[inline(always)]` and `#[target_feature(enable = "...")]`
    /// attributes is called and cannot be inlined due to missing target features in the caller.
    ///
    /// ### Example
    ///
    /// ```rust,ignore (fails on x86_64)
    /// #[inline(always)]
    /// #[target_feature(enable = "fp16")]
    /// unsafe fn callee() {
    ///     // operations using fp16 types
    /// }
    ///
    /// // Caller does not enable the required target feature
    /// fn caller() {
    ///     // SAFETY: Illustrative example in lint documentation; not executed.
    ///     unsafe { callee(); }
    /// }
    ///
    /// fn main() {
    ///     caller();
    /// }
    /// ```
    ///
    /// This will produce:
    ///
    /// ```text
    /// warning: call to `#[inline(always)]`-annotated `callee` requires the same target features. Function will not have `alwaysinline` attribute applied
    ///   --> $DIR/builtin.rs:5192:14
    ///    |
    /// 10 |     unsafe { callee(); }
    ///    |              ^^^^^^^^
    ///    |
    /// note: `fp16` target feature enabled in `callee` here but missing from `caller`
    ///   --> $DIR/builtin.rs:5185:1
    ///    |
    /// 3  | #[target_feature(enable = "fp16")]
    ///    | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    /// 4  | unsafe fn callee() {
    ///    | ------------------
    ///    = note: `#[warn(inline_always_mismatching_target_features)]` on by default
    /// warning: 1 warning emitted
    /// ```
    ///
    /// ### Explanation
    ///
    /// Inlining a function with a target feature attribute into a caller that
    /// lacks the corresponding target feature can lead to unsound behavior.
    /// LLVM may select the wrong instructions or registers, or reorder
    /// operations, potentially resulting in runtime errors.
    pub INLINE_ALWAYS_MISMATCHING_TARGET_FEATURES,
    Warn,
    r#"detects when a function annotated with `#[inline(always)]` and `#[target_feature(enable = "..")]` is inlined into a caller without the required target feature"#,
}

declare_lint! {
    /// The `inline_no_sanitize` lint detects incompatible use of
    /// [`#[inline(always)]`][inline] and [`#[sanitize(xyz = "off")]`][sanitize].
    ///
    /// [inline]: https://doc.rust-lang.org/reference/attributes/codegen.html#the-inline-attribute
    /// [sanitize]: https://doc.rust-lang.org/nightly/unstable-book/language-features/no-sanitize.html
    ///
    /// ### Example
    ///
    /// ```rust
    /// #![feature(sanitize)]
    ///
    /// #[inline(always)]
    /// #[sanitize(address = "off")]
    /// fn x() {}
    ///
    /// fn main() {
    ///     x()
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// The use of the [`#[inline(always)]`][inline] attribute prevents the
    /// the [`#[sanitize(xyz = "off")]`][sanitize] attribute from working.
    /// Consider temporarily removing `inline` attribute.
    pub INLINE_NO_SANITIZE,
    Warn,
    r#"detects incompatible use of `#[inline(always)]` and `#[sanitize(... = "off")]`"#,
}

declare_lint! {
    /// The `invalid_doc_attributes` lint detects when the `#[doc(...)]` is
    /// misused.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(warnings)]
    ///
    /// pub mod submodule {
    ///     #![doc(test(no_crate_inject))]
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Previously, incorrect usage of the `#[doc(..)]` attribute was not
    /// being validated. Usually these should be rejected as a hard error,
    /// but this lint was introduced to avoid breaking any existing
    /// crates which included them.
    pub INVALID_DOC_ATTRIBUTES,
    Warn,
    "detects invalid `#[doc(...)]` attributes",
}

declare_lint! {
    /// The `invalid_macro_export_arguments` lint detects cases where `#[macro_export]` is being used with invalid arguments.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(invalid_macro_export_arguments)]
    ///
    /// #[macro_export(invalid_parameter)]
    /// macro_rules! myMacro {
    ///    () => {
    ///         // [...]
    ///    }
    /// }
    ///
    /// #[macro_export(too, many, items)]
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// The only valid argument is `#[macro_export(local_inner_macros)]` or no argument (`#[macro_export]`).
    /// You can't have multiple arguments in a `#[macro_export(..)]`, or mention arguments other than `local_inner_macros`.
    ///
    pub INVALID_MACRO_EXPORT_ARGUMENTS,
    Deny,
    "\"invalid_parameter\" isn't a valid argument for `#[macro_export]`",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #57571),
        report_in_deps: true,
    };
}

declare_lint! {
    /// The `invalid_type_param_default` lint detects type parameter defaults
    /// erroneously allowed in an invalid location.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// fn foo<T=i32>(t: T) {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Default type parameters were only intended to be allowed in certain
    /// situations, but historically the compiler allowed them everywhere.
    /// This is a [future-incompatible] lint to transition this to a hard
    /// error in the future. See [issue #36887] for more details.
    ///
    /// [issue #36887]: https://github.com/rust-lang/rust/issues/36887
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub INVALID_TYPE_PARAM_DEFAULT,
    Deny,
    "type parameter default erroneously allowed in invalid location",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #36887),
        report_in_deps: true,
    };
}

declare_lint! {
    /// The `irrefutable_let_patterns` lint detects [irrefutable patterns]
    /// in [`if let`]s, [`while let`]s, and `if let` guards.
    ///
    /// ### Example
    ///
    /// ```rust
    /// if let _ = 123 {
    ///     println!("always runs!");
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// There usually isn't a reason to have an irrefutable pattern in an
    /// `if let` or `while let` statement, because the pattern will always match
    /// successfully. A [`let`] or [`loop`] statement will suffice. However,
    /// when generating code with a macro, forbidding irrefutable patterns
    /// would require awkward workarounds in situations where the macro
    /// doesn't know if the pattern is refutable or not. This lint allows
    /// macros to accept this form, while alerting for a possibly incorrect
    /// use in normal code.
    ///
    /// See [RFC 2086] for more details.
    ///
    /// [irrefutable patterns]: https://doc.rust-lang.org/reference/patterns.html#refutability
    /// [`if let`]: https://doc.rust-lang.org/reference/expressions/if-expr.html#if-let-expressions
    /// [`while let`]: https://doc.rust-lang.org/reference/expressions/loop-expr.html#predicate-pattern-loops
    /// [`let`]: https://doc.rust-lang.org/reference/statements.html#let-statements
    /// [`loop`]: https://doc.rust-lang.org/reference/expressions/loop-expr.html#infinite-loops
    /// [RFC 2086]: https://github.com/rust-lang/rfcs/blob/master/text/2086-allow-if-let-irrefutables.md
    pub IRREFUTABLE_LET_PATTERNS,
    Warn,
    "detects irrefutable patterns in `if let` and `while let` statements"
}

declare_lint! {
    /// The `large_assignments` lint detects when objects of large
    /// types are being moved around.
    ///
    /// ### Example
    ///
    /// ```rust,ignore (can crash on some platforms)
    /// let x = [0; 50000];
    /// let y = x;
    /// ```
    ///
    /// produces:
    ///
    /// ```text
    /// warning: moving a large value
    ///   --> $DIR/move-large.rs:1:3
    ///   let y = x;
    ///           - Copied large value here
    /// ```
    ///
    /// ### Explanation
    ///
    /// When using a large type in a plain assignment or in a function
    /// argument, idiomatic code can be inefficient.
    /// Ideally appropriate optimizations would resolve this, but such
    /// optimizations are only done in a best-effort manner.
    /// This lint will trigger on all sites of large moves and thus allow the
    /// user to resolve them in code.
    pub LARGE_ASSIGNMENTS,
    Warn,
    "detects large moves or copies",
}

declare_lint! {
    /// The `late_bound_lifetime_arguments` lint detects generic lifetime
    /// arguments in path segments with late bound lifetime parameters.
    ///
    /// ### Example
    ///
    /// ```rust
    /// struct S;
    ///
    /// impl S {
    ///     fn late(self, _: &u8, _: &u8) {}
    /// }
    ///
    /// fn main() {
    ///     S.late::<'static>(&0, &0);
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// It is not clear how to provide arguments for early-bound lifetime
    /// parameters if they are intermixed with late-bound parameters in the
    /// same list. For now, providing any explicit arguments will trigger this
    /// lint if late-bound parameters are present, so in the future a solution
    /// can be adopted without hitting backward compatibility issues. This is
    /// a [future-incompatible] lint to transition this to a hard error in the
    /// future. See [issue #42868] for more details, along with a description
    /// of the difference between early and late-bound parameters.
    ///
    /// [issue #42868]: https://github.com/rust-lang/rust/issues/42868
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub LATE_BOUND_LIFETIME_ARGUMENTS,
    Warn,
    "detects generic lifetime arguments in path segments with late bound lifetime parameters",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #42868),
    };
}

declare_lint! {
    /// The `legacy_derive_helpers` lint detects derive helper attributes
    /// that are used before they are introduced.
    ///
    /// ### Example
    ///
    /// ```rust,ignore (needs extern crate)
    /// #[serde(rename_all = "camelCase")]
    /// #[derive(Deserialize)]
    /// struct S { /* fields */ }
    /// ```
    ///
    /// produces:
    ///
    /// ```text
    /// warning: derive helper attribute is used before it is introduced
    ///   --> $DIR/legacy-derive-helpers.rs:1:3
    ///    |
    ///  1 | #[serde(rename_all = "camelCase")]
    ///    |   ^^^^^
    /// ...
    ///  2 | #[derive(Deserialize)]
    ///    |          ----------- the attribute is introduced here
    /// ```
    ///
    /// ### Explanation
    ///
    /// Attributes like this work for historical reasons, but attribute expansion works in
    /// left-to-right order in general, so, to resolve `#[serde]`, compiler has to try to "look
    /// into the future" at not yet expanded part of the item , but such attempts are not always
    /// reliable.
    ///
    /// To fix the warning place the helper attribute after its corresponding derive.
    /// ```rust,ignore (needs extern crate)
    /// #[derive(Deserialize)]
    /// #[serde(rename_all = "camelCase")]
    /// struct S { /* fields */ }
    /// ```
    pub LEGACY_DERIVE_HELPERS,
    Deny,
    "detects derive helper attributes that are used before they are introduced",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #79202),
        report_in_deps: true,
    };
}

declare_lint! {
    /// The `linker_info` lint forwards warnings from the linker that are known to be informational-only.
    ///
    /// ### Example
    ///
    /// ```rust,ignore (needs CLI args, platform-specific)
    /// #[warn(linker_info)]
    /// fn main () {}
    /// ```
    ///
    /// On MacOS, using `-C link-arg=-lc` and the default linker, this will produce
    ///
    /// ```text
    /// warning: linker stderr: ld: ignoring duplicate libraries: '-lc'
    ///   |
    /// note: the lint level is defined here
    ///  --> ex.rs:1:9
    ///   |
    /// 1 | #![warn(linker_info)]
    ///   |         ^^^^^^^^^^^^^^^
    /// ```
    ///
    /// ### Explanation
    ///
    /// Many linkers are very "chatty" and print lots of information that is not necessarily
    /// indicative of an issue. This output has been ignored for many years and is often not
    /// actionable by developers. It is silenced unless the developer specifically requests for it
    /// to be printed. See this tracking issue for more details:
    /// <https://github.com/rust-lang/rust/issues/136096>.
    pub LINKER_INFO,
    Allow,
    "linker warnings known to be informational-only and not indicative of a problem"
}

declare_lint! {
    /// The `linker_messages` lint forwards warnings from the linker.
    ///
    /// ### Example
    ///
    /// ```rust,ignore (needs CLI args, platform-specific)
    /// #[warn(linker_messages)]
    /// extern "C" {
    ///   fn foo();
    /// }
    /// // SAFETY: Illustrative example in lint documentation; not executed.
    /// fn main () { unsafe { foo(); } }
    /// ```
    ///
    /// On Linux, using `gcc -Wl,--warn-unresolved-symbols` as a linker, this will produce
    ///
    /// ```text
    /// warning: linker stderr: rust-lld: undefined symbol: foo
    ///          >>> referenced by rust_out.69edbd30df4ae57d-cgu.0
    ///          >>>               rust_out.rust_out.69edbd30df4ae57d-cgu.0.rcgu.o:(rust_out::main::h3a90094b06757803)
    ///   |
    /// note: the lint level is defined here
    ///  --> warn.rs:1:9
    ///   |
    /// 1 | #![warn(linker_messages)]
    ///   |         ^^^^^^^^^^^^^^^
    /// warning: 1 warning emitted
    /// ```
    ///
    /// ### Explanation
    ///
    /// Linkers emit platform-specific and program-specific warnings that cannot be predicted in
    /// advance by the Rust compiler. Such messages are ignored by default for now. While linker
    /// warnings could be very useful they have been ignored for many years by essentially all
    /// users, so we need to do a bit more work than just surfacing their text to produce a clear
    /// and actionable warning of similar quality to our other diagnostics. See this tracking
    /// issue for more details: <https://github.com/rust-lang/rust/issues/136096>.
    pub LINKER_MESSAGES,
    Allow,
    "warnings emitted at runtime by the target-specific linker program"
}

declare_lint! {
    /// The `long_running_const_eval` lint is emitted when const
    /// eval is running for a long time to ensure rustc terminates
    /// even if you accidentally wrote an infinite loop.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// const FOO: () = loop {};
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Loops allow const evaluation to compute arbitrary code, but may also
    /// cause infinite loops or just very long running computations.
    /// Users can enable long running computations by allowing the lint
    /// on individual constants or for entire crates.
    ///
    /// ### Unconditional warnings
    ///
    /// Note that regardless of whether the lint is allowed or set to warn,
    /// the compiler will issue warnings if constant evaluation runs significantly
    /// longer than this lint's limit. These warnings are also shown to downstream
    /// users from crates.io or similar registries. If you are above the lint's limit,
    /// both you and downstream users might be exposed to these warnings.
    /// They might also appear on compiler updates, as the compiler makes minor changes
    /// about how complexity is measured: staying below the limit ensures that there
    /// is enough room, and given that the lint is disabled for people who use your
    /// dependency it means you will be the only one to get the warning and can put
    /// out an update in your own time.
    pub LONG_RUNNING_CONST_EVAL,
    Deny,
    "detects long const eval operations",
    report_in_external_macro
}

declare_lint! {
    /// The `lossy_provenance_casts` lint detects an `as` cast between a pointer
    /// and an integer.
    ///
    /// ### Example
    ///
    /// ```rust
    /// #![feature(strict_provenance_lints)]
    /// #![warn(lossy_provenance_casts)]
    ///
    /// fn main() {
    ///     let x: u8 = 37;
    ///     let _addr: usize = &x as *const u8 as usize;
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// This lint is part of the strict provenance effort, see [issue #95228].
    /// Casting a pointer to an integer is a lossy operation, because beyond
    /// just an *address* a pointer may be associated with a particular
    /// *provenance*. This information is used by the optimiser and for dynamic
    /// analysis/dynamic program verification (e.g. Miri or CHERI platforms).
    ///
    /// Since this cast is lossy, it is considered good style to use the
    /// [`ptr::addr`] method instead, which has a similar effect, but doesn't
    /// "expose" the pointer provenance. This improves optimisation potential.
    /// See the docs of [`ptr::addr`] and [`ptr::expose_provenance`] for more information
    /// about exposing pointer provenance.
    ///
    /// If your code can't comply with strict provenance and needs to expose
    /// the provenance, then there is [`ptr::expose_provenance`] as an escape hatch,
    /// which preserves the behaviour of `as usize` casts while being explicit
    /// about the semantics.
    ///
    /// [issue #95228]: https://github.com/rust-lang/rust/issues/95228
    /// [`ptr::addr`]: https://doc.rust-lang.org/core/primitive.pointer.html#method.addr
    /// [`ptr::expose_provenance`]: https://doc.rust-lang.org/core/primitive.pointer.html#method.expose_provenance
    pub LOSSY_PROVENANCE_CASTS,
    Allow,
    "a lossy pointer to integer cast is used",
    @feature_gate = strict_provenance_lints;
}

declare_lint! {
    /// The `macro_expanded_macro_exports_accessed_by_absolute_paths` lint
    /// detects macro-expanded [`macro_export`] macros from the current crate
    /// that cannot be referred to by absolute paths.
    ///
    /// [`macro_export`]: https://doc.rust-lang.org/reference/macros-by-example.html#path-based-scope
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// macro_rules! define_exported {
    ///     () => {
    ///         #[macro_export]
    ///         macro_rules! exported {
    ///             () => {};
    ///         }
    ///     };
    /// }
    ///
    /// define_exported!();
    ///
    /// fn main() {
    ///     crate::exported!();
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// The intent is that all macros marked with the `#[macro_export]`
    /// attribute are made available in the root of the crate. However, when a
    /// `macro_rules!` definition is generated by another macro, the macro
    /// expansion is unable to uphold this rule. This is a
    /// [future-incompatible] lint to transition this to a hard error in the
    /// future. See [issue #53495] for more details.
    ///
    /// [issue #53495]: https://github.com/rust-lang/rust/issues/53495
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub MACRO_EXPANDED_MACRO_EXPORTS_ACCESSED_BY_ABSOLUTE_PATHS,
    Deny,
    "macro-expanded `macro_export` macros from the current crate \
     cannot be referred to by absolute paths",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #52234),
        report_in_deps: true,
    };
    crate_level_only
}
