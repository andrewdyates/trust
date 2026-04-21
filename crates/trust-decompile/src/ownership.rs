// trust-decompile: Ownership inference for unsafe Rust reconstruction
//
// Analyzes MIR-level pointer patterns to infer Rust ownership:
//   - alloc/free pairs -> Box<T>
//   - address-of without free (immutable) -> &T
//   - address-of without free (mutable) -> &mut T
//   - unclassifiable raw pointer ops -> wrapped in unsafe blocks
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Operand, Rvalue, Statement, Terminator, Ty, VerifiableFunction};

/// The inferred ownership kind for a pointer-typed local variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OwnershipKind {
    /// Heap-allocated, owned value (alloc + free pair detected). Maps to `Box<T>`.
    Owned,
    /// Immutable borrow (address-of without free, not mutable). Maps to `&T`.
    SharedBorrow,
    /// Mutable borrow (address-of without free, mutable). Maps to `&mut T`.
    MutBorrow,
    /// Raw pointer that could not be classified. Stays as `*const T` / `*mut T`
    /// and operations are wrapped in `unsafe` blocks.
    RawPtr,
}

/// A record of how a pointer-typed local is created and destroyed.
#[derive(Debug, Clone)]
pub(crate) struct PointerInfo {
    /// The local variable index.
    pub(crate) local: usize,
    /// How the pointer was created.
    pub(crate) creation: PointerCreation,
    /// Whether a corresponding drop/dealloc was found.
    pub(crate) has_free: bool,
    /// Whether the pointer is mutable.
    pub(crate) mutable: bool,
    /// The inferred ownership kind.
    pub(crate) kind: OwnershipKind,
}

/// How a pointer was created in the MIR.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PointerCreation {
    /// Created via `Rvalue::AddressOf` (`&raw const`/`&raw mut`).
    AddressOf,
    /// Created via `Rvalue::Ref` (borrow).
    Ref,
    /// Created via a call to an allocator function (e.g., `__rust_alloc`, `alloc::alloc`).
    AllocCall,
    /// Created via cast from integer or other pointer.
    Cast,
    /// Unknown or unrecognized creation pattern.
    Unknown,
}

/// Analyze a `VerifiableFunction` to identify pointer-typed locals and infer ownership.
///
/// Returns a vector of `PointerInfo` for each local that has a pointer-like type
/// (`RawPtr` or `Ref`).
pub(crate) fn analyze_ownership(func: &VerifiableFunction) -> Vec<PointerInfo> {
    let body = &func.body;
    let mut infos: Vec<PointerInfo> = Vec::new();

    // Phase 1: Identify pointer-typed locals and their creation patterns.
    for decl in &body.locals {
        if !decl.ty.is_pointer_like() && !decl.ty.is_raw_ptr() {
            continue;
        }

        let mutable = match &decl.ty {
            Ty::RawPtr { mutable, .. } => *mutable,
            Ty::Ref { mutable, .. } => *mutable,
            _ => false,
        };

        let creation = find_creation_pattern(decl.index, body);
        infos.push(PointerInfo {
            local: decl.index,
            creation,
            has_free: false,
            mutable,
            kind: OwnershipKind::RawPtr, // default, refined below
        });
    }

    // Phase 2: Scan for drop/dealloc terminators to detect frees.
    for bb in &body.blocks {
        match &bb.terminator {
            Terminator::Drop { place, .. } => {
                if let Some(info) = infos.iter_mut().find(|i| i.local == place.local) {
                    info.has_free = true;
                }
            }
            Terminator::Call { func: fn_name, args, .. } => {
                if is_dealloc_function(fn_name) {
                    // First argument to dealloc is typically the pointer.
                    if let Some(local_idx) = first_arg_local(args)
                        && let Some(info) = infos.iter_mut().find(|i| i.local == local_idx) {
                            info.has_free = true;
                        }
                }
            }
            _ => {}
        }
    }

    // Phase 3: Classify ownership based on creation + free patterns.
    for info in &mut infos {
        info.kind = classify_ownership(info);
    }

    infos
}

/// Scan all blocks to determine how a given local is first assigned.
fn find_creation_pattern(
    local_idx: usize,
    body: &trust_types::VerifiableBody,
) -> PointerCreation {
    for bb in &body.blocks {
        for stmt in &bb.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt
                && place.local == local_idx && place.projections.is_empty() {
                    return match rvalue {
                        Rvalue::AddressOf(_, _) => PointerCreation::AddressOf,
                        Rvalue::Ref { .. } => PointerCreation::Ref,
                        Rvalue::Cast(_, _) => PointerCreation::Cast,
                        _ => PointerCreation::Unknown,
                    };
                }
        }

        // Check if created by a call (allocator).
        if let Terminator::Call { func, dest, .. } = &bb.terminator
            && dest.local == local_idx && dest.projections.is_empty() && is_alloc_function(func) {
                return PointerCreation::AllocCall;
            }
    }

    PointerCreation::Unknown
}

/// Determine if a function name is a known allocator.
fn is_alloc_function(name: &str) -> bool {
    name.contains("__rust_alloc")
        || name.contains("alloc::alloc::alloc")
        || name.contains("alloc::alloc::Global")
        || name.contains("Box::new")
        || name.contains("alloc::boxed::Box")
}

/// Determine if a function name is a known deallocator.
fn is_dealloc_function(name: &str) -> bool {
    name.contains("__rust_dealloc")
        || name.contains("alloc::alloc::dealloc")
        || name.contains("alloc::alloc::Global")
}

/// Extract the local index from the first argument of a call, if it is a simple local.
fn first_arg_local(args: &[Operand]) -> Option<usize> {
    match args.first() {
        Some(Operand::Copy(place) | Operand::Move(place)) if place.projections.is_empty() => {
            Some(place.local)
        }
        _ => None,
    }
}

/// Classify ownership based on creation pattern and whether a free exists.
fn classify_ownership(info: &PointerInfo) -> OwnershipKind {
    match (&info.creation, info.has_free) {
        // alloc + free = Box<T>
        (PointerCreation::AllocCall, true) => OwnershipKind::Owned,
        // Ref without free = borrow
        (PointerCreation::Ref, false) => {
            if info.mutable {
                OwnershipKind::MutBorrow
            } else {
                OwnershipKind::SharedBorrow
            }
        }
        // AddressOf without free = borrow (from raw)
        (PointerCreation::AddressOf, false) => {
            if info.mutable {
                OwnershipKind::MutBorrow
            } else {
                OwnershipKind::SharedBorrow
            }
        }
        // Everything else stays as raw pointer
        _ => OwnershipKind::RawPtr,
    }
}

/// Apply ownership inference to decompiled source code.
///
/// Uses the analysis results to:
/// 1. Replace raw pointer type annotations with inferred ownership types.
/// 2. Replace alloc/free patterns with `Box::new(...)` / implicit drop.
/// 3. Replace `&raw const`/`&raw mut` with `&` / `&mut` for borrows.
/// 4. Wrap remaining raw pointer operations in `unsafe { ... }` blocks.
///
/// Returns the transformed source and a confidence boost.
pub(crate) fn apply_ownership_inference(
    source: &str,
    infos: &[PointerInfo],
) -> (String, f64) {
    let mut result = source.to_string();
    let mut boost = 0.0;

    for info in infos {
        let local_name = format!("_{}", info.local);
        match info.kind {
            OwnershipKind::Owned => {
                // Replace raw pointer type with Box<T>
                let (s, b) = rewrite_owned_pattern(&result, &local_name);
                result = s;
                boost += b;
            }
            OwnershipKind::SharedBorrow => {
                // Replace &raw const with & for this local
                let (s, b) = rewrite_borrow_pattern(&result, &local_name, false);
                result = s;
                boost += b;
            }
            OwnershipKind::MutBorrow => {
                // Replace &raw mut with &mut for this local
                let (s, b) = rewrite_borrow_pattern(&result, &local_name, true);
                result = s;
                boost += b;
            }
            OwnershipKind::RawPtr => {
                // Wrap raw pointer dereferences in unsafe blocks
                let (s, b) = wrap_unsafe_operations(&result, &local_name);
                result = s;
                boost += b;
            }
        }
    }

    (result, boost)
}

/// Rewrite alloc/free patterns to Box::new / implicit drop for a given local.
fn rewrite_owned_pattern(source: &str, local_name: &str) -> (String, f64) {
    let mut result = source.to_string();
    let mut boost = 0.0;

    // Replace type annotation: *mut T -> Box<T> or *const T -> Box<T>
    let patterns = [
        (format!("{local_name}: *mut "), format!("{local_name}: Box<")),
        (format!("{local_name}: *const "), format!("{local_name}: Box<")),
    ];

    for (old, new) in &patterns {
        if result.contains(old.as_str()) {
            // Find the type after the pointer and wrap with Box<...>
            result = rewrite_ptr_type_to_box(&result, old, new);
            boost += 0.05;
        }
    }

    // Replace dealloc calls involving this local with a comment
    let dealloc_patterns = [
        format!("drop(Box::from_raw({local_name}))"),
        // legacy __rust_dealloc patterns are handled by the pattern recovery pass
    ];
    for pat in &dealloc_patterns {
        if result.contains(pat.as_str()) {
            result = result.replace(pat.as_str(), &format!("// ownership: {local_name} dropped implicitly"));
            boost += 0.02;
        }
    }

    // Replace explicit drop of an owned pointer with comment
    let drop_pattern = format!("drop({local_name});");
    if result.contains(&drop_pattern) {
        result = result.replace(
            &drop_pattern,
            &format!("// ownership: {local_name} dropped (Box)"),
        );
        boost += 0.02;
    }

    (result, boost)
}

/// Replace a `*mut T`/`*const T` annotation with `Box<T>` in a type position.
fn rewrite_ptr_type_to_box(source: &str, old_prefix: &str, new_prefix: &str) -> String {
    // Simple approach: find the line containing old_prefix and replace
    // the raw pointer type with Box<type_name>
    let mut lines: Vec<String> = source.lines().map(|l| l.to_string()).collect();

    for line in &mut lines {
        if let Some(start) = line.find(old_prefix) {
            let after_prefix = start + old_prefix.len();
            // Find the end of the type (`;` or `,` or `>`)
            let rest = &line[after_prefix..];
            let type_end = rest
                .find([';', ',', '>'])
                .unwrap_or(rest.len());
            let type_name = rest[..type_end].trim();
            let replacement = format!("{new_prefix}{type_name}>");
            let old_full = format!("{old_prefix}{type_name}");
            *line = line.replace(&old_full, &replacement);
        }
    }

    lines.join("\n")
}

/// Rewrite AddressOf/Ref patterns for borrows.
fn rewrite_borrow_pattern(source: &str, local_name: &str, mutable: bool) -> (String, f64) {
    let mut result = source.to_string();
    let mut boost = 0.0;

    if mutable {
        // &raw mut -> &mut
        let raw_pattern = format!("{local_name} = &raw mut ");
        let safe_pattern = format!("{local_name} = &mut ");
        if result.contains(&raw_pattern) {
            result = result.replace(&raw_pattern, &safe_pattern);
            boost += 0.04;
        }

        // Rewrite type annotation: *mut T -> &mut T
        let type_old = format!("{local_name}: *mut ");
        let type_new = format!("{local_name}: &mut ");
        if result.contains(&type_old) {
            result = result.replace(&type_old, &type_new);
            boost += 0.03;
        }
    } else {
        // &raw const -> &
        let raw_pattern = format!("{local_name} = &raw const ");
        let safe_pattern = format!("{local_name} = &");
        if result.contains(&raw_pattern) {
            result = result.replace(&raw_pattern, &safe_pattern);
            boost += 0.04;
        }

        // Rewrite type annotation: *const T -> &T
        let type_old = format!("{local_name}: *const ");
        let type_new = format!("{local_name}: &");
        if result.contains(&type_old) {
            result = result.replace(&type_old, &type_new);
            boost += 0.03;
        }
    }

    (result, boost)
}

/// Wrap raw pointer dereferences in unsafe blocks.
fn wrap_unsafe_operations(source: &str, local_name: &str) -> (String, f64) {
    let mut result = source.to_string();
    let mut boost = 0.0;

    // Pattern: (*local_name) used in an assignment
    let deref_pattern = format!("(*{local_name})");
    if result.contains(&deref_pattern) {
        // Find lines with the dereference and wrap in unsafe
        let lines: Vec<String> = result
            .lines()
            .map(|line| {
                if line.contains(&deref_pattern) && !line.trim_start().starts_with("unsafe") {
                    let trimmed = line.trim_start();
                    let indent = &line[..line.len() - trimmed.len()];
                    format!("{indent}unsafe {{ {trimmed} }}")
                } else {
                    line.to_string()
                }
            })
            .collect();
        result = lines.join("\n");
        boost += 0.02;
    }

    (result, boost)
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{
        BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
        Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
    };

    /// Helper to create a minimal VerifiableFunction with the given locals, blocks,
    /// and arg_count.
    fn make_func(
        locals: Vec<LocalDecl>,
        blocks: Vec<BasicBlock>,
        arg_count: usize,
    ) -> VerifiableFunction {
        VerifiableFunction {
            name: "test_fn".to_string(),
            def_path: "m::test_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals,
                blocks,
                arg_count,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    // -- analyze_ownership tests --

    #[test]
    fn test_alloc_free_pair_infers_owned() {
        // Local _1 is *mut u8, created by alloc call, freed by dealloc call.
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                    name: Some("ptr".into()),
                },
            ],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "__rust_alloc".to_string(),
                        args: vec![Operand::Constant(ConstValue::Uint(8, 64))],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "__rust_dealloc".to_string(),
                        args: vec![Operand::Move(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Return,
                },
            ],
            0,
        );

        let infos = analyze_ownership(&func);
        assert_eq!(infos.len(), 1);
        assert_eq!(infos[0].local, 1);
        assert_eq!(infos[0].kind, OwnershipKind::Owned);
        assert_eq!(infos[0].creation, PointerCreation::AllocCall);
        assert!(infos[0].has_free);
    }

    #[test]
    fn test_address_of_immutable_without_free_infers_shared_borrow() {
        // Local _1 is *const u32, created by AddressOf(false, ...), no free.
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) },
                    name: Some("p".into()),
                },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("x".into()) },
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::AddressOf(false, Place::local(2)),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            1, // _2 (x) is the argument
        );

        let infos = analyze_ownership(&func);
        assert_eq!(infos.len(), 1);
        assert_eq!(infos[0].local, 1);
        assert_eq!(infos[0].kind, OwnershipKind::SharedBorrow);
        assert!(!infos[0].has_free);
    }

    #[test]
    fn test_address_of_mutable_without_free_infers_mut_borrow() {
        // Local _1 is *mut i32, created by AddressOf(true, ...), no free.
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::i32()) },
                    name: Some("p".into()),
                },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("x".into()) },
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::AddressOf(true, Place::local(2)),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            1,
        );

        let infos = analyze_ownership(&func);
        assert_eq!(infos.len(), 1);
        assert_eq!(infos[0].local, 1);
        assert_eq!(infos[0].kind, OwnershipKind::MutBorrow);
        assert!(!infos[0].has_free);
    }

    #[test]
    fn test_ref_without_free_infers_shared_borrow() {
        // Local _1 is &u64, created by Ref { mutable: false }, no free.
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::usize()) },
                    name: None,
                },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("val".into()) },
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Ref { mutable: false, place: Place::local(2) },
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            1,
        );

        let infos = analyze_ownership(&func);
        assert_eq!(infos.len(), 1);
        assert_eq!(infos[0].local, 1);
        assert_eq!(infos[0].kind, OwnershipKind::SharedBorrow);
        assert_eq!(infos[0].creation, PointerCreation::Ref);
    }

    #[test]
    fn test_raw_ptr_with_drop_stays_raw() {
        // Local _1 is *const u8, created by AddressOf (immutable), but has Drop.
        // AddressOf + free = unclear pattern, stays RawPtr.
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) },
                    name: Some("p".into()),
                },
                LocalDecl { index: 2, ty: Ty::u8(), name: Some("data".into()) },
            ],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::AddressOf(false, Place::local(2)),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Drop {
                        place: Place::local(1),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Return,
                },
            ],
            1,
        );

        let infos = analyze_ownership(&func);
        assert_eq!(infos.len(), 1);
        assert_eq!(infos[0].local, 1);
        // AddressOf + free = ambiguous, stays RawPtr
        assert_eq!(infos[0].kind, OwnershipKind::RawPtr);
    }

    #[test]
    fn test_no_pointer_locals_returns_empty() {
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            1,
        );

        let infos = analyze_ownership(&func);
        assert!(infos.is_empty());
    }

    #[test]
    fn test_cast_without_free_stays_raw() {
        // Local _1 is *const u8, created by Cast, no free -> RawPtr
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) },
                    name: Some("p".into()),
                },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("addr".into()) },
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Cast(
                        Operand::Copy(Place::local(2)),
                        Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) },
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            1,
        );

        let infos = analyze_ownership(&func);
        assert_eq!(infos.len(), 1);
        assert_eq!(infos[0].kind, OwnershipKind::RawPtr);
        assert_eq!(infos[0].creation, PointerCreation::Cast);
    }

    // -- apply_ownership_inference tests --

    #[test]
    fn test_apply_owned_rewrites_type() {
        let source = "    let mut _1: *mut u8;\n    _1 = __rust_alloc(8);\n    drop(_1);";
        let infos = vec![PointerInfo {
            local: 1,
            creation: PointerCreation::AllocCall,
            has_free: true,
            mutable: true,
            kind: OwnershipKind::Owned,
        }];

        let (result, boost) = apply_ownership_inference(source, &infos);
        assert!(result.contains("Box<u8>"), "Should contain Box<u8>, got: {result}");
        assert!(result.contains("dropped (Box)"), "Should have drop comment, got: {result}");
        assert!(boost > 0.0);
    }

    #[test]
    fn test_apply_shared_borrow_rewrites() {
        let source = "    let mut _1: *const u32;\n    _1 = &raw const x;";
        let infos = vec![PointerInfo {
            local: 1,
            creation: PointerCreation::AddressOf,
            has_free: false,
            mutable: false,
            kind: OwnershipKind::SharedBorrow,
        }];

        let (result, boost) = apply_ownership_inference(source, &infos);
        assert!(result.contains("&u32"), "Should contain &u32, got: {result}");
        assert!(result.contains("_1 = &x"), "Should rewrite to &x, got: {result}");
        assert!(boost > 0.0);
    }

    #[test]
    fn test_apply_mut_borrow_rewrites() {
        let source = "    let mut _1: *mut i32;\n    _1 = &raw mut y;";
        let infos = vec![PointerInfo {
            local: 1,
            creation: PointerCreation::AddressOf,
            has_free: false,
            mutable: true,
            kind: OwnershipKind::MutBorrow,
        }];

        let (result, boost) = apply_ownership_inference(source, &infos);
        assert!(result.contains("&mut i32"), "Should contain &mut i32, got: {result}");
        assert!(result.contains("_1 = &mut y"), "Should rewrite to &mut y, got: {result}");
        assert!(boost > 0.0);
    }

    #[test]
    fn test_apply_raw_ptr_wraps_unsafe() {
        let source = "    let mut _1: *const u8;\n    _2 = (*_1);";
        let infos = vec![PointerInfo {
            local: 1,
            creation: PointerCreation::Cast,
            has_free: false,
            mutable: false,
            kind: OwnershipKind::RawPtr,
        }];

        let (result, boost) = apply_ownership_inference(source, &infos);
        assert!(result.contains("unsafe {"), "Should wrap in unsafe, got: {result}");
        assert!(result.contains("(*_1)"), "Should still contain deref, got: {result}");
        assert!(boost > 0.0);
    }

    #[test]
    fn test_apply_no_pointers_unchanged() {
        let source = "unsafe fn foo() -> u32 {\n    return _0;\n}";
        let (result, boost) = apply_ownership_inference(source, &[]);
        assert_eq!(result, source);
        assert!((boost - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_classify_alloc_no_free_is_raw() {
        let info = PointerInfo {
            local: 1,
            creation: PointerCreation::AllocCall,
            has_free: false, // memory leak pattern
            mutable: true,
            kind: OwnershipKind::RawPtr,
        };
        assert_eq!(classify_ownership(&info), OwnershipKind::RawPtr);
    }

    #[test]
    fn test_classify_ref_mutable_no_free() {
        let info = PointerInfo {
            local: 1,
            creation: PointerCreation::Ref,
            has_free: false,
            mutable: true,
            kind: OwnershipKind::RawPtr,
        };
        assert_eq!(classify_ownership(&info), OwnershipKind::MutBorrow);
    }
}
