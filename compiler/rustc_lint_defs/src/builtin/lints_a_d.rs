//! Built-in lint definitions (A-D).
//!
//! This file is part of the `builtin` module split. See `mod.rs` for the
//! `declare_lint_pass!` that registers these lints.

// tRust: split from builtin.rs for file size reduction
use crate::{declare_lint, fcw};

declare_lint! {
    /// The `aarch64_softfloat_neon` lint detects usage of `#[target_feature(enable = "neon")]` on
    /// softfloat aarch64 targets. Enabling this target feature causes LLVM to alter the ABI of
    /// function calls, making this attribute unsound to use.
    ///
    /// ### Example
    ///
    /// ```rust,ignore (needs aarch64-unknown-none-softfloat)
    /// #[target_feature(enable = "neon")]
    /// fn with_neon() {}
    /// ```
    ///
    /// This will produce:
    ///
    /// ```text
    /// error: enabling the `neon` target feature on the current target is unsound due to ABI issues
    ///   --> $DIR/abi-incompatible-target-feature-attribute-fcw.rs:11:18
    ///    |
    ///    | #[target_feature(enable = "neon")]
    ///    |                  ^^^^^^^^^^^^^^^
    ///    |
    ///    = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
    ///    = note: for more information, see issue #134375 <https://github.com/rust-lang/rust/issues/134375>
    /// ```
    ///
    /// ### Explanation
    ///
    /// If a function like `with_neon` above ends up containing calls to LLVM builtins, those will
    /// not use the correct ABI. This is caused by a lack of support in LLVM for mixing code with
    /// and without the `neon` target feature. The target feature should never have been stabilized
    /// on this target due to this issue, but the problem was not known at the time of
    /// stabilization.
    pub AARCH64_SOFTFLOAT_NEON,
    Warn,
    "detects code that could be affected by ABI issues on aarch64 softfloat targets",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #134375),
        report_in_deps: true,
    };
}

declare_lint! {
    /// The `absolute_paths_not_starting_with_crate` lint detects fully
    /// qualified paths that start with a module name instead of `crate`,
    /// `self`, or an extern crate name
    ///
    /// ### Example
    ///
    /// ```rust,edition2015,compile_fail
    /// #![deny(absolute_paths_not_starting_with_crate)]
    ///
    /// mod foo {
    ///     pub fn bar() {}
    /// }
    ///
    /// fn main() {
    ///     ::foo::bar();
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Rust [editions] allow the language to evolve without breaking
    /// backwards compatibility. This lint catches code that uses absolute
    /// paths in the style of the 2015 edition. In the 2015 edition, absolute
    /// paths (those starting with `::`) refer to either the crate root or an
    /// external crate. In the 2018 edition it was changed so that they only
    /// refer to external crates. The path prefix `crate::` should be used
    /// instead to reference items from the crate root.
    ///
    /// If you switch the compiler from the 2015 to 2018 edition without
    /// updating the code, then it will fail to compile if the old style paths
    /// are used. You can manually change the paths to use the `crate::`
    /// prefix to transition to the 2018 edition.
    ///
    /// This lint solves the problem automatically. It is "allow" by default
    /// because the code is perfectly valid in the 2015 edition. The [`cargo
    /// fix`] tool with the `--edition` flag will switch this lint to "warn"
    /// and automatically apply the suggested fix from the compiler. This
    /// provides a completely automated way to update old code to the 2018
    /// edition.
    ///
    /// [editions]: https://doc.rust-lang.org/edition-guide/
    /// [`cargo fix`]: https://doc.rust-lang.org/cargo/commands/cargo-fix.html
    pub ABSOLUTE_PATHS_NOT_STARTING_WITH_CRATE,
    Allow,
    "fully qualified paths that start with a module name \
     instead of `crate`, `self`, or an extern crate name",
     @future_incompatible = FutureIncompatibleInfo {
         reason: fcw!(EditionError 2018 "path-changes"),
     };
}

declare_lint! {
    /// The `ambiguous_associated_items` lint detects ambiguity between
    /// [associated items] and [enum variants].
    ///
    /// [associated items]: https://doc.rust-lang.org/reference/items/associated-items.html
    /// [enum variants]: https://doc.rust-lang.org/reference/items/enumerations.html
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// enum E {
    ///     V
    /// }
    ///
    /// trait Tr {
    ///     type V;
    ///     fn foo() -> Self::V;
    /// }
    ///
    /// impl Tr for E {
    ///     type V = u8;
    ///     // `Self::V` is ambiguous because it may refer to the associated type or
    ///     // the enum variant.
    ///     fn foo() -> Self::V { 0 }
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Previous versions of Rust did not allow accessing enum variants
    /// through [type aliases]. When this ability was added (see [RFC 2338]), this
    /// introduced some situations where it can be ambiguous what a type
    /// was referring to.
    ///
    /// To fix this ambiguity, you should use a [qualified path] to explicitly
    /// state which type to use. For example, in the above example the
    /// function can be written as `fn f() -> <Self as Tr>::V { 0 }` to
    /// specifically refer to the associated type.
    ///
    /// This is a [future-incompatible] lint to transition this to a hard
    /// error in the future. See [issue #57644] for more details.
    ///
    /// [issue #57644]: https://github.com/rust-lang/rust/issues/57644
    /// [type aliases]: https://doc.rust-lang.org/reference/items/type-aliases.html#type-aliases
    /// [RFC 2338]: https://github.com/rust-lang/rfcs/blob/master/text/2338-type-alias-enum-variants.md
    /// [qualified path]: https://doc.rust-lang.org/reference/paths.html#qualified-paths
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub AMBIGUOUS_ASSOCIATED_ITEMS,
    Deny,
    "ambiguous associated items",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #57644),
    };
}

declare_lint! {
    /// The `ambiguous_derive_helpers` lint detects cases where a derive macro's helper attribute
    /// is the same name as that of a built-in attribute.
    ///
    /// ### Example
    ///
    /// ```rust,ignore (proc-macro)
    /// #![crate_type = "proc-macro"]
    /// #![deny(ambiguous_derive_helpers)]
    ///
    /// use proc_macro::TokenStream;
    ///
    /// #[proc_macro_derive(Trait, attributes(ignore))]
    /// pub fn example(input: TokenStream) -> TokenStream {
    ///     TokenStream::new()
    /// }
    /// ```
    ///
    /// Produces:
    ///
    /// ```text
    /// warning: there exists a built-in attribute with the same name
    ///   --> file.rs:5:39
    ///    |
    ///  5 | #[proc_macro_derive(Trait, attributes(ignore))]
    ///    |                                       ^^^^^^
    ///    |
    ///    = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
    ///    = note: for more information, see issue #151152 <https://github.com/rust-lang/rust/issues/151152>
    ///    = note: `#[deny(ambiguous_derive_helpers)]` (part of `#[deny(future_incompatible)]`) on by default
    /// ```
    ///
    /// ### Explanation
    ///
    /// Attempting to use this helper attribute will throw an error:
    ///
    /// ```rust,ignore (needs-dependency)
    /// #[derive(Trait)]
    /// struct Example {
    ///     #[ignore]
    ///     fields: ()
    /// }
    /// ```
    ///
    /// Produces:
    ///
    /// ```text
    /// error[E0659]: `ignore` is ambiguous
    ///  --> src/lib.rs:5:7
    ///   |
    /// 5 |     #[ignore]
    ///   |       ^^^^^^ ambiguous name
    ///   |
    ///   = note: ambiguous because of a name conflict with a builtin attribute
    ///   = note: `ignore` could refer to a built-in attribute
    /// note: `ignore` could also refer to the derive helper attribute defined here
    ///  --> src/lib.rs:3:10
    ///   |
    /// 3 | #[derive(Trait)]
    ///   |          ^^^^^
    /// ```
    pub AMBIGUOUS_DERIVE_HELPERS,
    Warn,
    "detects derive helper attributes that are ambiguous with built-in attributes",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #151276),
    };
}

declare_lint! {
    /// The `ambiguous_glob_imported_traits` lint reports uses of traits that are
    /// imported ambiguously via glob imports. Previously, this was not enforced
    /// due to a bug in rustc.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(ambiguous_glob_imported_traits)]
    /// mod m1 {
    ///    pub trait Trait {
    ///            fn method1(&self) {}
    ///        }
    ///        impl Trait for u8 {}
    ///    }
    ///    mod m2 {
    ///        pub trait Trait {
    ///            fn method2(&self) {}
    ///        }
    ///        impl Trait for u8 {}
    ///    }
    ///
    ///  fn main() {
    ///      use m1::*;
    ///      use m2::*;
    ///      0u8.method1();
    ///      0u8.method2();
    ///  }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// When multiple traits with the same name are brought into scope through glob imports,
    /// one trait becomes the "primary" one while the others are shadowed. Methods from the
    /// shadowed traits (e.g. `method2`) become inaccessible, while methods from the "primary"
    /// trait (e.g. `method1`) still resolve. Ideally, none of the ambiguous traits would be in scope,
    /// but we have to allow this for now because of backwards compatibility.
    /// This lint reports uses of these "primary" traits that are ambiguous.
    ///
    /// This is a [future-incompatible] lint to transition this to a
    /// hard error in the future.
    ///
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub AMBIGUOUS_GLOB_IMPORTED_TRAITS,
    Warn,
    "detects uses of ambiguously glob imported traits",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #147992),
        report_in_deps: false,
    };
}

declare_lint! {
    /// The `ambiguous_glob_imports` lint detects glob imports that should report ambiguity
    /// errors, but previously didn't do that due to rustc bugs.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(ambiguous_glob_imports)]
    /// pub fn foo() -> u32 {
    ///     use sub::*;
    ///     C
    /// }
    ///
    /// mod sub {
    ///     mod mod1 { pub const C: u32 = 1; }
    ///     mod mod2 { pub const C: u32 = 2; }
    ///
    ///     pub use mod1::*;
    ///     pub use mod2::*;
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Previous versions of Rust compile it successfully because it
    /// had lost the ambiguity error when resolve `use sub::mod2::*`.
    ///
    /// This is a [future-incompatible] lint to transition this to a
    /// hard error in the future.
    ///
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub AMBIGUOUS_GLOB_IMPORTS,
    Deny,
    "detects certain glob imports that require reporting an ambiguity error",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #114095),
        report_in_deps: true,
    };
}

declare_lint! {
    /// The `ambiguous_glob_reexports` lint detects cases where names re-exported via globs
    /// collide. Downstream users trying to use the same name re-exported from multiple globs
    /// will receive a warning pointing out redefinition of the same name.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(ambiguous_glob_reexports)]
    /// pub mod foo {
    ///     pub type X = u8;
    /// }
    ///
    /// pub mod bar {
    ///     pub type Y = u8;
    ///     pub type X = u8;
    /// }
    ///
    /// pub use foo::*;
    /// pub use bar::*;
    ///
    ///
    /// pub fn main() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// This was previously accepted but it could silently break a crate's downstream users code.
    /// For example, if `foo::*` and `bar::*` were re-exported before `bar::X` was added to the
    /// re-exports, down stream users could use `this_crate::X` without problems. However, adding
    /// `bar::X` would cause compilation errors in downstream crates because `X` is defined
    /// multiple times in the same namespace of `this_crate`.
    pub AMBIGUOUS_GLOB_REEXPORTS,
    Warn,
    "ambiguous glob re-exports",
}

declare_lint! {
    /// The `ambiguous_import_visibilities` lint detects imports that should report ambiguity
    /// errors, but previously didn't do that due to rustc bugs.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(unknown_lints)]
    /// #![deny(ambiguous_import_visibilities)]
    /// mod reexport {
    ///     mod m {
    ///         pub struct S {}
    ///     }
    ///
    ///     macro_rules! mac {
    ///         () => { use m::S; }
    ///     }
    ///
    ///     pub use m::*;
    ///     mac!();
    ///
    ///     pub use S as Z; // ambiguous visibility
    /// }
    ///
    /// fn main() {
    ///     reexport::Z {};
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Previous versions of Rust compile it successfully because it
    /// fetched the glob import's visibility for `pub use S as Z` import, and ignored the private
    /// `use m::S` import that appeared later.
    ///
    /// This is a [future-incompatible] lint to transition this to a
    /// hard error in the future.
    ///
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub AMBIGUOUS_IMPORT_VISIBILITIES,
    Warn,
    "detects certain glob imports that require reporting an ambiguity error",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #149145),
    };
}

declare_lint! {
    /// The `ambiguous_panic_imports` lint detects ambiguous core and std panic imports, but
    /// previously didn't do that due to `#[macro_use]` prelude macro import.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #![deny(ambiguous_panic_imports)]
    /// #![no_std]
    ///
    /// extern crate std;
    /// use std::prelude::v1::*;
    ///
    /// fn xx() {
    ///     panic!(); // resolves to core::panic
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Future versions of Rust will no longer accept the ambiguous resolution.
    ///
    /// This is a [future-incompatible] lint to transition this to a hard error in the future.
    ///
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub AMBIGUOUS_PANIC_IMPORTS,
    Warn,
    "detects ambiguous core and std panic imports",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #147319),
        report_in_deps: false,
    };
}

declare_lint! {
    /// The `arithmetic_overflow` lint detects that an arithmetic operation
    /// will [overflow].
    ///
    /// [overflow]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#overflow
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// 1_i32 << 32;
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// It is very likely a mistake to perform an arithmetic operation that
    /// overflows its value. If the compiler is able to detect these kinds of
    /// overflows at compile-time, it will trigger this lint. Consider
    /// adjusting the expression to avoid overflow, or use a data type that
    /// will not overflow.
    pub ARITHMETIC_OVERFLOW,
    Deny,
    "arithmetic operation overflows",
    @eval_always = true
}

declare_lint! {
    /// The `asm_sub_register` lint detects using only a subset of a register
    /// for inline asm inputs.
    ///
    /// ### Example
    ///
    /// ```rust,ignore (fails on non-x86_64)
    /// #[cfg(target_arch="x86_64")]
    /// use std::arch::asm;
    ///
    /// fn main() {
    ///     #[cfg(target_arch="x86_64")]
    ///     // SAFETY: Illustrative example in lint documentation; not executed.
    ///     unsafe {
    ///         asm!("mov {0}, {0}", in(reg) 0i16);
    ///     }
    /// }
    /// ```
    ///
    /// This will produce:
    ///
    /// ```text
    /// warning: formatting may not be suitable for sub-register argument
    ///  --> src/main.rs:7:19
    ///   |
    /// 7 |         asm!("mov {0}, {0}", in(reg) 0i16);
    ///   |                   ^^^  ^^^           ---- for this argument
    ///   |
    ///   = note: `#[warn(asm_sub_register)]` on by default
    ///   = help: use the `x` modifier to have the register formatted as `ax`
    ///   = help: or use the `r` modifier to keep the default formatting of `rax`
    /// ```
    ///
    /// ### Explanation
    ///
    /// Registers on some architectures can use different names to refer to a
    /// subset of the register. By default, the compiler will use the name for
    /// the full register size. To explicitly use a subset of the register,
    /// you can override the default by using a modifier on the template
    /// string operand to specify when subregister to use. This lint is issued
    /// if you pass in a value with a smaller data type than the default
    /// register size, to alert you of possibly using the incorrect width. To
    /// fix this, add the suggested modifier to the template, or cast the
    /// value to the correct size.
    ///
    /// See [register template modifiers] in the reference for more details.
    ///
    /// [register template modifiers]: https://doc.rust-lang.org/nightly/reference/inline-assembly.html#template-modifiers
    pub ASM_SUB_REGISTER,
    Warn,
    "using only a subset of a register for inline asm inputs",
}

declare_lint! {
    /// The `bad_asm_style` lint detects the use of the `.intel_syntax` and
    /// `.att_syntax` directives.
    ///
    /// ### Example
    ///
    /// ```rust,ignore (fails on non-x86_64)
    /// #[cfg(target_arch="x86_64")]
    /// use std::arch::asm;
    ///
    /// fn main() {
    ///     #[cfg(target_arch="x86_64")]
    ///     // SAFETY: Illustrative example in lint documentation; not executed.
    ///     unsafe {
    ///         asm!(
    ///             ".att_syntax",
    ///             "movq %{0}, %{0}", in(reg) 0usize
    ///         );
    ///     }
    /// }
    /// ```
    ///
    /// This will produce:
    ///
    /// ```text
    /// warning: avoid using `.att_syntax`, prefer using `options(att_syntax)` instead
    ///  --> src/main.rs:8:14
    ///   |
    /// 8 |             ".att_syntax",
    ///   |              ^^^^^^^^^^^
    ///   |
    ///   = note: `#[warn(bad_asm_style)]` on by default
    /// ```
    ///
    /// ### Explanation
    ///
    /// On x86, `asm!` uses the intel assembly syntax by default. While this
    /// can be switched using assembler directives like `.att_syntax`, using the
    /// `att_syntax` option is recommended instead because it will also properly
    /// prefix register placeholders with `%` as required by AT&T syntax.
    pub BAD_ASM_STYLE,
    Warn,
    "incorrect use of inline assembly",
}

declare_lint! {
    /// The `bare_trait_objects` lint suggests using `dyn Trait` for trait
    /// objects.
    ///
    /// ### Example
    ///
    /// ```rust,edition2018
    /// trait Trait { }
    ///
    /// fn takes_trait_object(_: Box<Trait>) {
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Without the `dyn` indicator, it can be ambiguous or confusing when
    /// reading code as to whether or not you are looking at a trait object.
    /// The `dyn` keyword makes it explicit, and adds a symmetry to contrast
    /// with [`impl Trait`].
    ///
    /// [`impl Trait`]: https://doc.rust-lang.org/book/ch10-02-traits.html#traits-as-parameters
    pub BARE_TRAIT_OBJECTS,
    Warn,
    "suggest using `dyn Trait` for trait objects",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(EditionError 2021 "warnings-promoted-to-error"),
    };
}

declare_lint! {
    /// The `bindings_with_variant_name` lint detects pattern bindings with
    /// the same name as one of the matched variants.
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// pub enum Enum {
    ///     Foo,
    ///     Bar,
    /// }
    ///
    /// pub fn foo(x: Enum) {
    ///     match x {
    ///         Foo => {}
    ///         Bar => {}
    ///     }
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// It is usually a mistake to specify an enum variant name as an
    /// [identifier pattern]. In the example above, the `match` arms are
    /// specifying a variable name to bind the value of `x` to. The second arm
    /// is ignored because the first one matches *all* values. The likely
    /// intent is that the arm was intended to match on the enum variant.
    ///
    /// Two possible solutions are:
    ///
    /// * Specify the enum variant using a [path pattern], such as
    ///   `Enum::Foo`.
    /// * Bring the enum variants into local scope, such as adding `use
    ///   Enum::*;` to the beginning of the `foo` function in the example
    ///   above.
    ///
    /// [identifier pattern]: https://doc.rust-lang.org/reference/patterns.html#identifier-patterns
    /// [path pattern]: https://doc.rust-lang.org/reference/patterns.html#path-patterns
    pub BINDINGS_WITH_VARIANT_NAME,
    Deny,
    "detects pattern bindings with the same name as one of the matched variants"
}

declare_lint! {
    /// The `break_with_label_and_loop` lint detects labeled `break` expressions with
    /// an unlabeled loop as their value expression.
    ///
    /// ### Example
    ///
    /// ```rust
    /// 'label: loop {
    ///     break 'label loop { break 42; };
    /// };
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// In Rust, loops can have a label, and `break` expressions can refer to that label to
    /// break out of specific loops (and not necessarily the innermost one). `break` expressions
    /// can also carry a value expression, which can be another loop. A labeled `break` with an
    /// unlabeled loop as its value expression is easy to confuse with an unlabeled break with
    /// a labeled loop and is thus discouraged (but allowed for compatibility); use parentheses
    /// around the loop expression to silence this warning. Unlabeled `break` expressions with
    /// labeled loops yield a hard error, which can also be silenced by wrapping the expression
    /// in parentheses.
    pub BREAK_WITH_LABEL_AND_LOOP,
    Warn,
    "`break` expression with label and unlabeled loop as value expression"
}

declare_lint! {
    /// The `coherence_leak_check` lint detects conflicting implementations of
    /// a trait that are only distinguished by the old leak-check code.
    ///
    /// ### Example
    ///
    /// ```rust
    /// trait SomeTrait { }
    /// impl SomeTrait for for<'a> fn(&'a u8) { }
    /// impl<'a> SomeTrait for fn(&'a u8) { }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// In the past, the compiler would accept trait implementations for
    /// identical functions that differed only in where the lifetime binder
    /// appeared. Due to a change in the borrow checker implementation to fix
    /// several bugs, this is no longer allowed. However, since this affects
    /// existing code, this is a [future-incompatible] lint to transition this
    /// to a hard error in the future.
    ///
    /// Code relying on this pattern should introduce "[newtypes]",
    /// like `struct Foo(for<'a> fn(&'a u8))`.
    ///
    /// See [issue #56105] for more details.
    ///
    /// [issue #56105]: https://github.com/rust-lang/rust/issues/56105
    /// [newtypes]: https://doc.rust-lang.org/book/ch19-04-advanced-types.html#using-the-newtype-pattern-for-type-safety-and-abstraction
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub COHERENCE_LEAK_CHECK,
    Warn,
    "distinct impls distinguished only by the leak-check code",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!("the behavior may change in a future release" #56105),
    };
}

declare_lint! {
    /// The `conflicting_repr_hints` lint detects [`repr` attributes] with
    /// conflicting hints.
    ///
    /// [`repr` attributes]: https://doc.rust-lang.org/reference/type-layout.html#representations
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// #[repr(u32, u64)]
    /// enum Foo {
    ///     Variant1,
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// The compiler incorrectly accepted these conflicting representations in
    /// the past. This is a [future-incompatible] lint to transition this to a
    /// hard error in the future. See [issue #68585] for more details.
    ///
    /// To correct the issue, remove one of the conflicting hints.
    ///
    /// [issue #68585]: https://github.com/rust-lang/rust/issues/68585
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    pub CONFLICTING_REPR_HINTS,
    Deny,
    "conflicts between `#[repr(..)]` hints that were previously accepted and used in practice",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #68585),
        report_in_deps: true,
    };
}

declare_lint! {
    /// The `const_evaluatable_unchecked` lint detects a generic constant used
    /// in a type.
    ///
    /// ### Example
    ///
    /// ```rust
    /// const fn foo<T>() -> usize {
    ///     if size_of::<*mut T>() < 8 { // size of *mut T does not depend on T
    ///         4
    ///     } else {
    ///         8
    ///     }
    /// }
    ///
    /// fn test<T>() {
    ///     let _ = [0; foo::<T>()];
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// In the 1.43 release, some uses of generic parameters in array repeat
    /// expressions were accidentally allowed. This is a [future-incompatible]
    /// lint to transition this to a hard error in the future. See [issue
    /// #76200] for a more detailed description and possible fixes.
    ///
    /// [future-incompatible]: ../index.md#future-incompatible-lints
    /// [issue #76200]: https://github.com/rust-lang/rust/issues/76200
    pub CONST_EVALUATABLE_UNCHECKED,
    Warn,
    "detects a generic constant is used in a type without a emitting a warning",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(FutureReleaseError #76200),
    };
}

declare_lint! {
    /// The `const_item_mutation` lint detects attempts to mutate a `const`
    /// item.
    ///
    /// ### Example
    ///
    /// ```rust
    /// const FOO: [i32; 1] = [0];
    ///
    /// fn main() {
    ///     FOO[0] = 1;
    ///     // This will print "[0]".
    ///     println!("{:?}", FOO);
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Trying to directly mutate a `const` item is almost always a mistake.
    /// What is happening in the example above is that a temporary copy of the
    /// `const` is mutated, but the original `const` is not. Each time you
    /// refer to the `const` by name (such as `FOO` in the example above), a
    /// separate copy of the value is inlined at that location.
    ///
    /// This lint checks for writing directly to a field (`FOO.field =
    /// some_value`) or array entry (`FOO[0] = val`), or taking a mutable
    /// reference to the const item (`&mut FOO`), including through an
    /// autoderef (`FOO.some_mut_self_method()`).
    ///
    /// There are various alternatives depending on what you are trying to
    /// accomplish:
    ///
    /// * First, always reconsider using mutable globals, as they can be
    ///   difficult to use correctly, and can make the code more difficult to
    ///   use or understand.
    /// * If you are trying to perform a one-time initialization of a global:
    ///     * If the value can be computed at compile-time, consider using
    ///       const-compatible values (see [Constant Evaluation]).
    ///     * For more complex single-initialization cases, consider using
    ///       [`std::sync::LazyLock`].
    /// * If you truly need a mutable global, consider using a [`static`],
    ///   which has a variety of options:
    ///   * Simple data types can be directly defined and mutated with an
    ///     [`atomic`] type.
    ///   * More complex types can be placed in a synchronization primitive
    ///     like a [`Mutex`], which can be initialized with one of the options
    ///     listed above.
    ///   * A [mutable `static`] is a low-level primitive, requiring unsafe.
    ///     Typically This should be avoided in preference of something
    ///     higher-level like one of the above.
    ///
    /// [Constant Evaluation]: https://doc.rust-lang.org/reference/const_eval.html
    /// [`static`]: https://doc.rust-lang.org/reference/items/static-items.html
    /// [mutable `static`]: https://doc.rust-lang.org/reference/items/static-items.html#mutable-statics
    /// [`std::sync::LazyLock`]: https://doc.rust-lang.org/stable/std/sync/struct.LazyLock.html
    /// [`atomic`]: https://doc.rust-lang.org/std/sync/atomic/index.html
    /// [`Mutex`]: https://doc.rust-lang.org/std/sync/struct.Mutex.html
    pub CONST_ITEM_MUTATION,
    Warn,
    "detects attempts to mutate a `const` item",
}

declare_lint! {
    /// The `dead_code` lint detects unused, unexported items.
    ///
    /// ### Example
    ///
    /// ```rust
    /// fn foo() {}
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Dead code may signal a mistake or unfinished code. To silence the
    /// warning for individual items, prefix the name with an underscore such
    /// as `_foo`. If it was intended to expose the item outside of the crate,
    /// consider adding a visibility modifier like `pub`.
    ///
    /// To preserve the numbering of tuple structs with unused fields,
    /// change the unused fields to have unit type or use
    /// `PhantomData`.
    ///
    /// Otherwise consider removing the unused code.
    ///
    /// ### Limitations
    ///
    /// Removing fields that are only used for side-effects and never
    /// read will result in behavioral changes. Examples of this
    /// include:
    ///
    /// - If a field's value performs an action when it is dropped.
    /// - If a field's type does not implement an auto trait
    ///   (e.g. `Send`, `Sync`, `Unpin`).
    ///
    /// For side-effects from dropping field values, this lint should
    /// be allowed on those fields. For side-effects from containing
    /// field types, `PhantomData` should be used.
    pub DEAD_CODE,
    Warn,
    "detect unused, unexported items"
}

declare_lint! {
    /// The `dependency_on_unit_never_type_fallback` lint detects cases where code compiles with
    /// [never type fallback] being [`()`], but will stop compiling with fallback being [`!`].
    ///
    /// [never type fallback]: https://doc.rust-lang.org/nightly/core/primitive.never.html#never-type-fallback
    /// [`!`]: https://doc.rust-lang.org/core/primitive.never.html
    /// [`()`]: https://doc.rust-lang.org/core/primitive.unit.html
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail,edition2021
    /// # #![deny(dependency_on_unit_never_type_fallback)]
    /// fn main() {
    ///     if true {
    ///         // return has type `!` which, is some cases, causes never type fallback
    ///         return
    ///     } else {
    ///         // the type produced by this call is not specified explicitly,
    ///         // so it will be inferred from the previous branch
    ///         Default::default()
    ///     };
    ///     // depending on the fallback, this may compile (because `()` implements `Default`),
    ///     // or it may not (because `!` does not implement `Default`)
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Due to historic reasons never type fallback was `()`, meaning that `!` got spontaneously
    /// coerced to `()`. There are plans to change that, but they may make the code such as above
    /// not compile. Instead of depending on the fallback, you should specify the type explicitly:
    /// ```
    /// if true {
    ///     return
    /// } else {
    ///     // type is explicitly specified, fallback can't hurt us no more
    ///     <() as Default>::default()
    /// };
    /// ```
    ///
    /// See [Tracking Issue for making `!` fall back to `!`](https://github.com/rust-lang/rust/issues/123748).
    pub DEPENDENCY_ON_UNIT_NEVER_TYPE_FALLBACK,
    Deny,
    "never type fallback affecting unsafe function calls",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(EditionAndFutureReleaseError 2024 "never-type-fallback"),
        report_in_deps: true,
    };
    report_in_external_macro
}

declare_lint! {
    /// The `deprecated` lint detects use of deprecated items.
    ///
    /// ### Example
    ///
    /// ```rust
    /// #[deprecated]
    /// fn foo() {}
    ///
    /// fn bar() {
    ///     foo();
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Items may be marked "deprecated" with the [`deprecated` attribute] to
    /// indicate that they should no longer be used. Usually the attribute
    /// should include a note on what to use instead, or check the
    /// documentation.
    ///
    /// [`deprecated` attribute]: https://doc.rust-lang.org/reference/attributes/diagnostics.html#the-deprecated-attribute
    pub DEPRECATED,
    Warn,
    "detects use of deprecated items",
    report_in_external_macro
}

declare_lint! {
    /// The `deprecated_in_future` lint is internal to rustc and should not be
    /// used by user code.
    ///
    /// This lint is only enabled in the standard library. It works with the
    /// use of `#[deprecated]` with a `since` field of a version in the future.
    /// This allows something to be marked as deprecated in a future version,
    /// and then this lint will ensure that the item is no longer used in the
    /// standard library. See the [stability documentation] for more details.
    ///
    /// [stability documentation]: https://rustc-dev-guide.rust-lang.org/stability.html#deprecated
    pub DEPRECATED_IN_FUTURE,
    Allow,
    "detects use of items that will be deprecated in a future version",
    report_in_external_macro
}

declare_lint! {
    /// The `deprecated_safe_2024` lint detects unsafe functions being used as
    /// safe functions.
    ///
    /// ### Example
    ///
    /// ```rust,edition2021,compile_fail
    /// #![deny(deprecated_safe)]
    /// // edition 2021
    /// use std::env;
    /// fn enable_backtrace() {
    ///     env::set_var("RUST_BACKTRACE", "1");
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Rust [editions] allow the language to evolve without breaking backward
    /// compatibility. This lint catches code that uses `unsafe` functions that
    /// were declared as safe (non-`unsafe`) in editions prior to Rust 2024. If
    /// you switch the compiler to Rust 2024 without updating the code, then it
    /// will fail to compile if you are using a function previously marked as
    /// safe.
    ///
    /// You can audit the code to see if it suffices the preconditions of the
    /// `unsafe` code, and if it does, you can wrap it in an `unsafe` block. If
    /// you can't fulfill the preconditions, you probably need to switch to a
    /// different way of doing what you want to achieve.
    ///
    /// This lint can automatically wrap the calls in `unsafe` blocks, but this
    /// obviously cannot verify that the preconditions of the `unsafe`
    /// functions are fulfilled, so that is still up to the user.
    ///
    /// The lint is currently "allow" by default, but that might change in the
    /// future.
    ///
    /// [editions]: https://doc.rust-lang.org/edition-guide/
    pub DEPRECATED_SAFE_2024,
    Allow,
    "detects unsafe functions being used as safe functions",
    @future_incompatible = FutureIncompatibleInfo {
        reason: fcw!(EditionError 2024 "newly-unsafe-functions"),
    };
}

declare_lint! {
    /// The `deprecated_where_clause_location` lint detects when a where clause in front of the equals
    /// in an associated type.
    ///
    /// ### Example
    ///
    /// ```rust
    /// trait Trait {
    ///   type Assoc<'a> where Self: 'a;
    /// }
    ///
    /// impl Trait for () {
    ///   type Assoc<'a> where Self: 'a = ();
    /// }
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// The preferred location for where clauses on associated types
    /// is after the type. However, for most of generic associated types development,
    /// it was only accepted before the equals. To provide a transition period and
    /// further evaluate this change, both are currently accepted. At some point in
    /// the future, this may be disallowed at an edition boundary; but, that is
    /// undecided currently.
    pub DEPRECATED_WHERE_CLAUSE_LOCATION,
    Warn,
    "deprecated where clause location"
}

declare_lint! {
    /// The `duplicate_features` lint detects duplicate features found in
    /// crate-level [`feature` attributes].
    ///
    /// Note: This lint used to be a hard error (E0636).
    ///
    /// [`feature` attributes]: https://doc.rust-lang.org/nightly/unstable-book/
    ///
    /// ### Example
    ///
    /// ```rust,compile_fail
    /// # #![allow(internal_features)]
    /// #![feature(rustc_attrs)]
    /// #![feature(rustc_attrs)]
    /// ```
    ///
    /// {{produces}}
    ///
    /// ### Explanation
    ///
    /// Enabling a feature more than once is a no-op.
    /// To avoid this warning, remove the second `feature()` attribute.
    pub DUPLICATE_FEATURES,
    Deny,
    "duplicate features found in crate-level `#[feature]` directives"
}
