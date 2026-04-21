//! Built-in lint definitions (U-W).
//!
//! This file is part of the `builtin` module split. See `mod.rs` for the
//! `declare_lint_pass!` that registers these lints.

// tRust: split from builtin.rs for file size reduction
use crate::{declare_lint, fcw};

declare_lint! {
    /// The `unknown_crate_types` lint detects an unknown crate type found in
    /// a [`crate_type` attribute].
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![crate_type="lol"]
    /// fn main() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// An unknown value give to the `crate_type` attribute is almost
    /// certainly a mistake.
    ///
    /// [`crate_type` attribute]: https://doc.rust-lang.org/reference/linkage.html
    pub UNKNOWN_CRATE_TYPES,
    Deny,
    "unknown crate type found in `#[crate_type]` directive",
    crate_level_only
}

declare_lint! {
    /// The `unknown_diagnostic_attributes` lint detects unknown diagnostic attributes.
    ///
    /// ### Example
    ///
    /// ```rust
    /// #[diagnostic::does_not_exist]
    /// struct Thing;
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// It is usually a mistake to specify a diagnostic attribute that does not exist. Check the
    /// spelling, and check the diagnostic attribute listing for the correct name. Also consider if
    /// you are using an old version of the compiler and the attribute is only available in a newer
    /// version. See the [reference] for the list of diagnostic attributes.
    ///
    /// [reference]: https://doc.rust-lang.org/nightly/reference/attributes/diagnostics.html#the-diagnostic-tool-attribute-namespace
    pub UNKNOWN_DIAGNOSTIC_ATTRIBUTES,
    Warn,
    "detects unknown diagnostic attributes",
}

declare_lint! {
    /// The `unknown_lints` lint detects unrecognized lint attributes.
    ///
    /// ### Example
    ///
    /// ```rust
    /// #![allow(not_a_real_lint)]
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// It is usually a mistake to specify a lint that does not exist. Check
    /// the spelling, and check the lint listing for the correct name. Also
    /// consider if you are using an old version of the compiler, and the lint
    /// is only available in a newer version.
    pub UNKNOWN_LINTS,
    Warn,
    "unrecognized lint attribute",
    @eval_always = true
}

declare_lint! {
    /// The `unnameable_test_items` lint detects [`#[test]`][test] functions
    /// that are not able to be run by the test harness because they are in a
    /// position where they are not nameable.
    ///
    /// [test]: https://doc.rust-lang.org/reference/attributes/testing.html#the-test-attribute
    ///
    /// ### Example
    ///
    /// ```rust,test
    /// fn main() {
    ///     #[test]
    ///     fn foo() {
    ///         // This test will not fail because it does not run.
    ///         assert_eq!(1, 2);
    ///     }
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// In order for the test harness to run a test, the test function must be
    /// located in a position where it can be accessed from the crate root.
    /// This generally means it must be defined in a module, and not anywhere
    /// else such as inside another function. The compiler previously allowed
    /// this without an error, so a lint was added as an alert that a test is
    /// not being used. Whether or not this should be allowed has not yet been
    /// decided, see [RFC 2471] and [issue #36629].
    ///
    /// [RFC 2471]: https://github.com/rust-lang/rfcs/pull/2471#issuecomment-397414443
    /// [issue #36629]: https://github.com/rust-lang/rust/issues/36629
    pub UNNAMEABLE_TEST_ITEMS,
    Warn,
    "detects an item that cannot be named being marked as `#[test_case]`",
    report_in_external_macro
}

declare_lint! {
    /// The `unnameable_types` lint detects types for which you can get objects of that type,
    /// but cannot name the type itself.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// # #![allow(unused)]
    /// #![deny(unnameable_types)]
    /// mod m {
    ///     pub struct S;
    /// }
    ///
    /// pub fn get_unnameable() -> m::S { m::S }
    /// # fn main() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// It is often expected that if you can obtain an object of type `T`, then
    /// you can name the type `T` as well; this lint attempts to enforce this rule.
    /// The recommended action is to either reexport the type properly to make it nameable,
    /// or document that users are not supposed to be able to name it for one reason or another.
    ///
    /// Besides types, this lint applies to traits because traits can also leak through signatures,
    /// and you may obtain objects of their `dyn Trait` or `impl Trait` types.
    pub UNNAMEABLE_TYPES,
    Allow,
    "effective visibility of a type is larger than the area in which it can be named",
}

declare_lint! {
    /// The `unreachable_cfg_select_predicates` lint detects unreachable configuration
    /// predicates in the `cfg_select!` macro.
    ///
    /// ### Example
    ///
    /// ```rust
    /// cfg_select! {
    ///     _ => (),
    ///     windows => (),
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// This usually indicates a mistake in how the predicates are specified or
    /// ordered. In this example, the `_` predicate will always match, so the
    /// `windows` is impossible to reach. Remember, arms match in order, you
    /// probably wanted to put the `windows` case above the `_` case.
    pub UNREACHABLE_CFG_SELECT_PREDICATES,
    Warn,
    "detects unreachable configuration predicates in the cfg_select macro",
}

declare_lint! {
    /// The `unreachable_code` lint detects unreachable code paths.
    ///
    /// ### Example
    ///
    /// ```rust,no_run
    /// panic!("we never go past here!");
    ///
    /// let x = 5;
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Unreachable code may signal a mistake or unfinished code. If the code
    /// is no longer in use, consider removing it.
    pub UNREACHABLE_CODE,
    Warn,
    "detects unreachable code paths",
    report_in_external_macro
}

declare_lint! {
    /// The `unreachable_patterns` lint detects unreachable patterns.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let x = 5;
    /// match x {
    ///     y => (),
    ///     5 => (),
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// This usually indicates a mistake in how the patterns are specified or
    /// ordered. In this example, the `y` pattern will always match, so the
    /// five is impossible to reach. Remember, match arms match in order, you
    /// probably wanted to put the `5` case above the `y` case.
    pub UNREACHABLE_PATTERNS,
    Warn,
    "detects unreachable patterns"
}

declare_lint! {
    /// The `unsafe_attr_outside_unsafe` lint detects a missing unsafe keyword
    /// on attributes considered unsafe.
    ///
    /// ### Example
    ///
    /// ```rust,edition2021
    /// #![warn(unsafe_attr_outside_unsafe)]
    ///
    /// #[no_mangle]
    /// extern "C" fn foo() {}
    ///
    /// fn main() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Some attributes (e.g. `no_mangle`, `export_name`, `link_section` -- see
    /// [issue #82499] for a more complete list) are considered "unsafe" attributes.
    /// An unsafe attribute must only be used inside unsafe(...).
    ///
    /// This lint can automatically wrap the attributes in `unsafe(...)` , but this
    /// obviously cannot verify that the preconditions of the `unsafe`
    /// attributes are fulfilled, so that is still up to the user.
    ///
    /// The lint is currently "allow" by default, but that might change in the
    /// future.
    ///
    /// [editions]: https://doc.rust-lang.org/edition-guide/
    /// [issue #82499]: https://github.com/rust-lang/rust/issues/82499
    pub UNSAFE_ATTR_OUTSIDE_UNSAFE,
    Allow,
    "detects unsafe attributes outside of unsafe",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(EditionError 2024 "unsafe-attributes"),
    };
}

declare_lint! {
    /// The `unsafe_op_in_unsafe_fn` lint detects unsafe operations in unsafe
    /// functions without an explicit unsafe block.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(unsafe_op_in_unsafe_fn)]
    ///
    /// unsafe fn foo() {}
    ///
    /// unsafe fn bar() {
    ///     foo();
    /// }
    ///
    /// fn main() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Currently, an [`unsafe fn`] allows any [unsafe] operation within its
    /// body. However, this can increase the surface area of code that needs
    /// to be scrutinized for proper behavior. The [`unsafe` block] provides a
    /// convenient way to make it clear exactly which parts of the code are
    /// performing unsafe operations. In the future, it is desired to change
    /// it so that unsafe operations cannot be performed in an `unsafe fn`
    /// without an `unsafe` block.
    ///
    /// The fix to this is to wrap the unsafe code in an `unsafe` block.
    ///
    /// This lint is "allow" by default on editions up to 2021, from 2024 it is
    /// "warn" by default; the plan for increasing severity further is
    /// still being considered. See [RFC #2585] and [issue #71668] for more
    /// details.
    ///
    /// [`unsafe fn`]: https://doc.rust-lang.org/reference/unsafe-functions.html
    /// [`unsafe` block]: https://doc.rust-lang.org/reference/expressions/block-expr.html#unsafe-blocks
    /// [unsafe]: https://doc.rust-lang.org/reference/unsafety.html
    /// [RFC #2585]: https://github.com/rust-lang/rfcs/blob/master/text/2585-unsafe-block-in-unsafe-fn.md
    /// [issue #71668]: https://github.com/rust-lang/rust/issues/71668
    pub UNSAFE_OP_IN_UNSAFE_FN,
    Allow,
    "unsafe operations in unsafe functions without an explicit unsafe block are deprecated",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(EditionError 2024 "unsafe-op-in-unsafe-fn"),
        explain_reason: false
    };
    @edition Edition2024 => Warn;
}

declare_lint! {
    /// The `unstable_name_collisions` lint detects that you have used a name
    /// that the standard library plans to add in the future.
    ///
    /// ### Example
    ///
    /// ```rust
    /// trait MyIterator : Iterator {
    ///     // is_partitioned is an unstable method that already exists on the Iterator trait
    ///     fn is_partitioned<P>(self, predicate: P) -> bool
    ///     where
    ///         Self: Sized,
    ///         P: FnMut(Self::Item) -> bool,
    ///     {true}
    /// }
    ///
    /// impl<T: ?Sized> MyIterator for T where T: Iterator { }
    ///
    /// let x = vec![1, 2, 3];
    /// let _ = x.iter().is_partitioned(|_| true);
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// When new methods are added to traits in the standard library, they are
    /// usually added in an "unstable" form which is only available on the
    /// [nightly channel] with a [`feature` attribute]. If there is any
    /// preexisting code which extends a trait to have a method with the same
    /// name, then the names will collide. In the future, when the method is
    /// stabilized, this will cause an error due to the ambiguity. This lint
    /// is an early-warning to let you know that there may be a collision in
    /// the future. This can be avoided by adding type annotations to
    /// disambiguate which trait method you intend to call, such as
    /// `MyIterator::is_partitioned(my_iter, my_predicate)` or renaming or removing the method.
    ///
    /// [nightly channel]: https://doc.rust-lang.org/book/appendix-07-nightly-rust.html
    /// [`feature` attribute]: https://doc.rust-lang.org/nightly/unstable-book/
    pub UNSTABLE_NAME_COLLISIONS,
    Warn,
    "detects name collision with an existing but unstable method",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(
            "once this associated item is added to the standard library, \
             the ambiguity may cause an error or change in behavior!"
             #48919
        ),
        // Note: this item represents future incompatibility of all unstable functions in the
        //       standard library, and thus should never be removed or changed to an error.
    };
}

declare_lint! {
    /// The `unstable_syntax_pre_expansion` lint detects the use of unstable
    /// syntax that is discarded during attribute expansion.
    ///
    /// ### Example
    ///
    /// ```rust
    /// #[cfg(FALSE)]
    /// macro foo() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// The input to active attributes such as `#[cfg]` or procedural macro
    /// attributes is required to be valid syntax. Previously, the compiler only
    /// gated the use of unstable syntax features after resolving `#[cfg]` gates
    /// and expanding procedural macros.
    ///
    /// To avoid relying on unstable syntax, move the use of unstable syntax
    /// into a position where the compiler does not parse the syntax, such as a
    /// functionlike macro.
    ///
    /// ```rust
    /// # #![deny(unstable_syntax_pre_expansion)]
    ///
    /// macro_rules! identity {
    ///    ( $($tokens:tt)* ) => { $($tokens)* }
    /// }
    ///
    /// #[cfg(FALSE)]
    /// identity! {
    ///    macro foo() {}
    /// }
    /// ```
    ///
    /// This is a [future-incompatible] lint to transition this
    /// to a hard error in the future. See [issue #65860] for more details.
    ///
    /// [issue #65860]: https://github.com/rust-lang/rust/issues/65860
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub UNSTABLE_SYNTAX_PRE_EXPANSION,
    Warn,
    "unstable syntax can change at any point in the future, causing a hard error!",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #65860),
    };
}

declare_lint! {
    /// The `unsupported_calling_conventions` lint is output whenever there is a use of the
    /// `stdcall`, `fastcall`, and `cdecl` calling conventions (or their unwind
    /// variants) on targets that cannot meaningfully be supported for the requested target.
    ///
    /// For example, `stdcall` does not make much sense for a x86_64 or, more apparently, powerpc
    /// code, because this calling convention was never specified for those targets.
    ///
    /// Historically, MSVC toolchains have fallen back to the regular C calling convention for
    /// targets other than x86, but Rust doesn't really see a similar need to introduce a similar
    /// hack across many more targets.
    ///
    /// ### Example
    ///
    /// ```rust,ignore (needs specific targets)
    /// extern "stdcall" fn stdcall() {}
    /// ```
    ///
    /// This will produce:
    ///
    /// ```text
    /// warning: use of calling convention not supported on this target
    ///   --> $DIR/unsupported.rs:39:1
    ///    |
    /// LL | extern "stdcall" fn stdcall() {}
    ///    | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    ///    |
    ///    = note: `#[warn(unsupported_calling_conventions)]` on by default
    ///    = warning: this was previously accepted by the compiler but is being phased out;
    ///               it will become a hard error in a future release!
    ///    = note: for more information, see issue ...
    /// ```
    ///
    /// ### Explanation
    ///
    /// On most of the targets, the behaviour of `stdcall` and similar calling conventions is not
    /// defined at all, but was previously accepted due to a bug in the implementation of the
    /// compiler.
    pub UNSUPPORTED_CALLING_CONVENTIONS,
    Warn,
    "use of unsupported calling convention",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #137018),
        report_in_deps: false,
    };
}

declare_lint! {
    /// The `unsupported_fn_ptr_calling_conventions` lint is output whenever there is a use of
    /// a target dependent calling convention on a target that does not support this calling
    /// convention on a function pointer.
    ///
    /// For example `stdcall` does not make much sense for a x86_64 or, more apparently, powerpc
    /// code, because this calling convention was never specified for those targets.
    ///
    /// ### Example
    ///
    /// ```rust,ignore (needs specific targets)
    /// fn stdcall_ptr(f: extern "stdcall" fn ()) {
    ///     f()
    /// }
    /// ```
    ///
    /// This will produce:
    ///
    /// ```text
    /// warning: the calling convention `"stdcall"` is not supported on this target
    ///   --> $DIR/unsupported.rs:34:15
    ///    |
    /// LL | fn stdcall_ptr(f: extern "stdcall" fn()) {
    ///    |               ^^^^^^^^^^^^^^^^^^^^^^^^
    ///    |
    ///    = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
    ///    = note: for more information, see issue #130260 <https://github.com/rust-lang/rust/issues/130260>
    ///    = note: `#[warn(unsupported_fn_ptr_calling_conventions)]` on by default
    /// ```
    ///
    /// ### Explanation
    ///
    /// On most of the targets the behaviour of `stdcall` and similar calling conventions is not
    /// defined at all, but was previously accepted due to a bug in the implementation of the
    /// compiler.
    pub UNSUPPORTED_FN_PTR_CALLING_CONVENTIONS,
    Warn,
    "use of unsupported calling convention for function pointer",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #130260),
        report_in_deps: true,
    };
}

declare_lint! {
    /// The `unused_assignments` lint detects assignments that will never be read.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let mut x = 5;
    /// x = 6;
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Unused assignments may signal a mistake or unfinished code. If the
    /// variable is never used after being assigned, then the assignment can
    /// be removed. Variables with an underscore prefix such as `_x` will not
    /// trigger this lint.
    pub UNUSED_ASSIGNMENTS,
    Warn,
    "detect assignments that will never be read"
}

declare_lint! {
    /// The `unused_associated_type_bounds` lint is emitted when an
    /// associated type bound is added to a trait object, but the associated
    /// type has a `where Self: Sized` bound, and is thus unavailable on the
    /// trait object anyway.
    ///
    /// ### Example
    ///
    /// ```rust
    /// trait Foo {
    ///     type Bar where Self: Sized;
    /// }
    /// type Mop = dyn Foo<Bar = ()>;
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Just like methods with `Self: Sized` bounds are unavailable on trait
    /// objects, associated types can be removed from the trait object.
    pub UNUSED_ASSOCIATED_TYPE_BOUNDS,
    Warn,
    "detects unused `Foo = Bar` bounds in `dyn Trait<Foo = Bar>`"
}

declare_lint! {
    /// The `unused_attributes` lint detects attributes that were not used by
    /// the compiler.
    ///
    /// ### Example
    ///
    /// ```rust
    /// #![ignore]
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Unused [attributes] may indicate the attribute is placed in the wrong
    /// position. Consider removing it, or placing it in the correct position.
    /// Also consider if you intended to use an _inner attribute_ (with a `!`
    /// such as `#![allow(unused)]`) which applies to the item the attribute
    /// is within, or an _outer attribute_ (without a `!` such as
    /// `#[allow(unused)]`) which applies to the item *following* the
    /// attribute.
    ///
    /// [attributes]: https://doc.rust-lang.org/reference/attributes.html
    pub UNUSED_ATTRIBUTES,
    Warn,
    "detects attributes that were not used by the compiler"
}

declare_lint! {
    /// The `unused_crate_dependencies` lint detects crate dependencies that
    /// are never used.
    ///
    /// ### Example
    ///
    /// ```rust,ignore (needs extern crate)
    /// #![deny(unused_crate_dependencies)]
    /// ```
    ///
    /// This will produce:
    ///
    /// ```text
    /// error: extern crate `regex` is unused in crate `lint_example`
    ///   |
    ///   = help: remove the dependency or add `use regex as _;` to the crate root
    /// note: the lint level is defined here
    ///  --> src/lib.rs:1:9
    ///   |
    /// 1 | #![deny(unused_crate_dependencies)]
    ///   |         ^^^^^^^^^^^^^^^^^^^^^^^^^
    /// ```
    ///
    /// ### Explanation
    ///
    /// After removing the code that uses a dependency, this usually also
    /// requires removing the dependency from the build configuration.
    /// However, sometimes that step can be missed, which leads to time wasted
    /// building dependencies that are no longer used. This lint can be
    /// enabled to detect dependencies that are never used (more specifically,
    /// any dependency passed with the `--extern` command-line flag that is
    /// never referenced via [`use`], [`extern crate`], or in any [path]).
    ///
    /// This lint is "allow" by default because it can provide false positives
    /// depending on how the build system is configured. For example, when
    /// using Cargo, a "package" consists of multiple crates (such as a
    /// library and a binary), but the dependencies are defined for the
    /// package as a whole. If there is a dependency that is only used in the
    /// binary, but not the library, then the lint will be incorrectly issued
    /// in the library.
    ///
    /// [path]: https://doc.rust-lang.org/reference/paths.html
    /// [`use`]: https://doc.rust-lang.org/reference/items/use-declarations.html
    /// [`extern crate`]: https://doc.rust-lang.org/reference/items/extern-crates.html
    pub UNUSED_CRATE_DEPENDENCIES,
    Allow,
    "crate dependencies that are never used",
    crate_level_only
}

declare_lint! {
    /// The `unused_doc_comments` lint detects doc comments that aren't used
    /// by `rustdoc`.
    ///
    /// ### Example
    ///
    /// ```rust
    /// /// docs for x
    /// let x = 12;
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// `rustdoc` does not use doc comments in all positions, and so the doc
    /// comment will be ignored. Try changing it to a normal comment with `//`
    /// to avoid the warning.
    pub UNUSED_DOC_COMMENTS,
    Warn,
    "detects doc comments that aren't used by rustdoc"
}

declare_lint! {
    /// The `unused_extern_crates` lint guards against `extern crate` items
    /// that are never used.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(unused_extern_crates)]
    /// #![deny(warnings)]
    /// extern crate proc_macro;
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// `extern crate` items that are unused have no effect and should be
    /// removed. Note that there are some cases where specifying an `extern
    /// crate` is desired for the side effect of ensuring the given crate is
    /// linked, even though it is not otherwise directly referenced. The lint
    /// can be silenced by aliasing the crate to an underscore, such as
    /// `extern crate foo as _`. Also note that it is no longer idiomatic to
    /// use `extern crate` in the [2018 edition], as extern crates are now
    /// automatically added in scope.
    ///
    /// This lint is "allow" by default because it can be noisy, and produce
    /// false-positives. If a dependency is being removed from a project, it
    /// is recommended to remove it from the build configuration (such as
    /// `Cargo.toml`) to ensure stale build entries aren't left behind.
    ///
    /// [2018 edition]: https://doc.rust-lang.org/edition-guide/rust-2018/module-system/path-clarity.html#no-more-extern-crate
    pub UNUSED_EXTERN_CRATES,
    Allow,
    "extern crates that are never used"
}

declare_lint! {
    /// The `unused_features` lint detects unused or unknown features found in
    /// crate-level [`feature` attributes].
    ///
    /// [`feature` attributes]: https://doc.rust-lang.org/nightly/unstable-book/
    pub UNUSED_FEATURES,
    Warn,
    "unused features found in crate-level `#[feature]` directives"
}

declare_lint! {
    /// The `unused_imports` lint detects imports that are never used.
    ///
    /// ### Example
    ///
    /// ```rust
    /// use std::collections::HashMap;
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Unused imports may signal a mistake or unfinished code, and clutter
    /// the code, and should be removed. If you intended to re-export the item
    /// to make it available outside of the module, add a visibility modifier
    /// like `pub`.
    pub UNUSED_IMPORTS,
    Warn,
    "imports that are never used"
}

declare_lint! {
    /// The `unused_labels` lint detects [labels] that are never used.
    ///
    /// [labels]: https://doc.rust-lang.org/reference/expressions/loop-expr.html#loop-labels
    ///
    /// ### Example
    ///
    /// ```rust,no_run
    /// 'unused_label: loop {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Unused labels may signal a mistake or unfinished code. To silence the
    /// warning for the individual label, prefix it with an underscore such as
    /// `'_my_label:`.
    pub UNUSED_LABELS,
    Warn,
    "detects labels that are never used"
}

declare_lint! {
    /// The `unused_lifetimes` lint detects lifetime parameters that are never
    /// used.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #[deny(unused_lifetimes)]
    ///
    /// pub fn foo<'a>() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Unused lifetime parameters may signal a mistake or unfinished code.
    /// Consider removing the parameter.
    pub UNUSED_LIFETIMES,
    Allow,
    "detects lifetime parameters that are never used"
}

declare_lint! {
    /// The `unused_macros` lint detects macros that were not used.
    ///
    /// Note that this lint is distinct from the `unused_macro_rules` lint,
    /// which checks for single rules that never match of an otherwise used
    /// macro, and thus never expand.
    ///
    /// ### Example
    ///
    /// ```rust
    /// macro_rules! unused {
    ///     () => {};
    /// }
    ///
    /// fn main() {
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Unused macros may signal a mistake or unfinished code. To silence the
    /// warning for the individual macro, prefix the name with an underscore
    /// such as `_my_macro`. If you intended to export the macro to make it
    /// available outside of the crate, use the [`macro_export` attribute].
    ///
    /// [`macro_export` attribute]: https://doc.rust-lang.org/reference/macros-by-example.html#path-based-scope
    pub UNUSED_MACROS,
    Warn,
    "detects macros that were not used"
}

declare_lint! {
    /// The `unused_macro_rules` lint detects macro rules that were not used.
    ///
    /// Note that the lint is distinct from the `unused_macros` lint, which
    /// fires if the entire macro is never called, while this lint fires for
    /// single unused rules of the macro that is otherwise used.
    /// `unused_macro_rules` fires only if `unused_macros` wouldn't fire.
    ///
    /// ### Example
    ///
    /// ```rust
    /// #[warn(unused_macro_rules)]
    /// macro_rules! unused_empty {
    ///     (hello) => { println!("Hello, world!") }; // This rule is used
    ///     () => { println!("empty") }; // This rule is unused
    /// }
    ///
    /// fn main() {
    ///     unused_empty!(hello);
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Unused macro rules may signal a mistake or unfinished code. Furthermore,
    /// they slow down compilation. Right now, silencing the warning is not
    /// supported on a single rule level, so you have to add an allow to the
    /// entire macro definition.
    ///
    /// If you intended to export the macro to make it
    /// available outside of the crate, use the [`macro_export` attribute].
    ///
    /// [`macro_export` attribute]: https://doc.rust-lang.org/reference/macros-by-example.html#path-based-scope
    pub UNUSED_MACRO_RULES,
    Allow,
    "detects macro rules that were not used"
}

declare_lint! {
    /// The `unused_mut` lint detects mut variables which don't need to be
    /// mutable.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let mut x = 5;
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// The preferred style is to only mark variables as `mut` if it is
    /// required.
    pub UNUSED_MUT,
    Warn,
    "detect mut variables which don't need to be mutable"
}

declare_lint! {
    /// The `unused_qualifications` lint detects unnecessarily qualified
    /// names.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(unused_qualifications)]
    /// mod foo {
    ///     pub fn bar() {}
    /// }
    ///
    /// fn main() {
    ///     use foo::bar;
    ///     foo::bar();
    ///     bar();
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// If an item from another module is already brought into scope, then
    /// there is no need to qualify it in this case. You can call `bar()`
    /// directly, without the `foo::`.
    ///
    /// This lint is "allow" by default because it is somewhat pedantic, and
    /// doesn't indicate an actual problem, but rather a stylistic choice, and
    /// can be noisy when refactoring or moving around code.
    pub UNUSED_QUALIFICATIONS,
    Allow,
    "detects unnecessarily qualified names"
}

declare_lint! {
    /// The `unused_unsafe` lint detects unnecessary use of an `unsafe` block.
    ///
    /// ### Example
    ///
    /// ```rust
    /// // SAFETY: Illustrative example in lint documentation; not executed.
    /// unsafe {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// If nothing within the block requires `unsafe`, then remove the
    /// `unsafe` marker because it is not required and may cause confusion.
    pub UNUSED_UNSAFE,
    Warn,
    "unnecessary use of an `unsafe` block"
}

declare_lint! {
    /// The `unused_variables` lint detects variables which are not used in
    /// any way.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let x = 5;
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Unused variables may signal a mistake or unfinished code. To silence
    /// the warning for the individual variable, prefix it with an underscore
    /// such as `_x`.
    pub UNUSED_VARIABLES,
    Warn,
    "detect variables which are not used in any way"
}

declare_lint! {
    /// The `unused_visibilities` lint detects visibility qualifiers (like `pub`)
    /// on a `const _` item.
    ///
    /// ### Example
    ///
    /// ```rust
    /// pub const _: () = {};
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// These qualifiers have no effect, as `const _` items are unnameable.
    pub UNUSED_VISIBILITIES,
    Warn,
    "detect visibility qualifiers on `const _` items"
}

declare_lint! {
    /// The `useless_deprecated` lint detects deprecation attributes with no effect.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// struct X;
    ///
    /// #[deprecated = "message"]
    /// impl Default for X {
    ///     fn default() -> Self {
    ///         X
    ///     }
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Deprecation attributes have no effect on trait implementations.
    pub USELESS_DEPRECATED,
    Deny,
    "detects deprecation attributes with no effect",
}

declare_lint! {
    /// The `varargs_without_pattern` lint detects when `...` is used as an argument to a
    /// non-foreign function without any pattern being specified.
    ///
    /// ### Example
    ///
    /// ```rust
    /// // Using `...` in non-foreign function definitions is unstable, however stability is
    /// // currently only checked after attributes are expanded, so using `#[cfg(false)]` here will
    /// // allow this to compile on stable Rust.
    /// #[cfg(false)]
    /// fn foo(...) {
    ///
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Patterns are currently required for all non-`...` arguments in function definitions (with
    /// some exceptions in the 2015 edition). Requiring `...` arguments to have patterns in
    /// non-foreign function definitions makes the language more consistent, and removes a source of
    /// confusion for the unstable C variadic feature. `...` arguments without a pattern are already
    /// stable and widely used in foreign function definitions; this lint only affects non-foreign
    /// function definitions.
    ///
    /// Using `...` (C varargs) in a non-foreign function definition is currently unstable. However,
    /// stability checking for the `...` syntax in non-foreign function definitions is currently
    /// implemented after attributes have been expanded, meaning that if the attribute removes the
    /// use of the unstable syntax (e.g. `#[cfg(false)]`, or a procedural macro), the code will
    /// compile on stable Rust; this is the only situation where this lint affects code that
    /// compiles on stable Rust.
    ///
    /// This is a [future-incompatible] lint to transition this to a hard error in the future.
    ///
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub VARARGS_WITHOUT_PATTERN,
    Warn,
    "detects usage of `...` arguments without a pattern in non-foreign items",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #145544),
        report_in_deps: false,
    };
}

declare_lint! {
    /// The `warnings` lint allows you to change the level of other
    /// lints which produce warnings.
    ///
    /// ### Example
    ///
    /// ```rust
    /// #![deny(warnings)]
    /// fn foo() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// The `warnings` lint is a bit special; by changing its level, you
    /// change every other warning that would produce a warning to whatever
    /// value you'd like. As such, you won't ever trigger this lint in your
    /// code directly.
    pub WARNINGS,
    Warn,
    "mass-change the level for lints which produce warnings"
}
