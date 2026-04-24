// trust-types/model.rs: MIR-level verification model
//
// These types represent a function extracted from rustc's MIR, simplified
// for verification. Only trust-mir-extract creates these; everything
// downstream consumes them.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;

use serde::{Deserialize, Serialize};

use crate::Formula;
use crate::spec::FunctionSpec;

/// A function extracted for verification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifiableFunction {
    pub name: String,
    pub def_path: String,
    pub span: SourceSpan,
    pub body: VerifiableBody,
    pub contracts: Vec<Contract>,
    // tRust #72: Parsed spec formulas from #[requires] and #[ensures] attributes.
    // Populated by trust-mir-extract using spec_parse::parse_spec_expr.
    #[serde(default)]
    pub preconditions: Vec<Formula>,
    #[serde(default)]
    pub postconditions: Vec<Formula>,
    // tRust #119: Structured spec representation from #[requires], #[ensures],
    // #[invariant] attributes. Bridges compiler attribute parsing to the
    // verification pipeline's FunctionSpec/ContractMetadata types.
    #[serde(default)]
    pub spec: FunctionSpec,
}

impl VerifiableFunction {
    /// Compute a stable content hash of the function body for caching.
    ///
    /// Uses SHA-256 over the serde_json serialization of the body, contracts,
    /// preconditions, postconditions, and spec. The hash is deterministic across
    /// Rust versions (unlike `DefaultHasher`). Name and span are intentionally
    /// excluded — the cache keys by def_path separately.
    ///
    /// This is the single source of truth for content hashing. The free function
    /// `trust_cache::compute_content_hash()` delegates to this method.
    #[must_use]
    pub fn content_hash(&self) -> String {
        use sha2::{Digest, Sha256};
        let body_json = serde_json::to_string(&self.body).unwrap_or_default();
        let contracts_json = serde_json::to_string(&self.contracts).unwrap_or_default();
        let pre_json = serde_json::to_string(&self.preconditions).unwrap_or_default();
        let post_json = serde_json::to_string(&self.postconditions).unwrap_or_default();
        let spec_json = serde_json::to_string(&self.spec).unwrap_or_default();
        let mut hasher = Sha256::new();
        hasher.update(body_json.as_bytes());
        hasher.update(b":");
        hasher.update(contracts_json.as_bytes());
        hasher.update(b":");
        hasher.update(pre_json.as_bytes());
        hasher.update(b":");
        hasher.update(post_json.as_bytes());
        hasher.update(b":");
        hasher.update(spec_json.as_bytes());
        format!("{:x}", hasher.finalize())
    }
}

/// MIR body simplified for verification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifiableBody {
    pub locals: Vec<LocalDecl>,
    pub blocks: Vec<BasicBlock>,
    pub arg_count: usize,
    pub return_ty: Ty,
}

impl VerifiableBody {
    /// Discover guarded clauses encoded by block terminators.
    pub fn discovered_clauses(&self) -> Vec<DiscoveredClause> {
        self.blocks.iter().flat_map(BasicBlock::discovered_clauses).collect()
    }

    /// Build a bounded path map from the entry block to each reachable block.
    ///
    /// This first slice keeps the first discovered conjunction of guards for
    /// each block instead of a full disjunction of all possible paths. That is
    /// enough to support lightweight reachability queries and proof reporting
    /// without exploding path count.
    pub fn path_map(&self) -> Vec<PathMapEntry> {
        if self.blocks.is_empty() {
            return vec![];
        }

        let mut discovered: Vec<Option<PathMapEntry>> = vec![None; self.blocks.len()];
        let mut queue = VecDeque::from([(BlockId(0), Vec::<GuardCondition>::new())]);

        while let Some((block, guards)) = queue.pop_front() {
            let Some(bb) = self.blocks.get(block.0) else {
                continue;
            };

            if discovered[block.0].is_some() {
                continue;
            }

            discovered[block.0] = Some(PathMapEntry {
                block,
                guards: guards.clone(),
                exits: bb.terminator.exit_targets(),
            });

            for guarded in bb.terminator.discovered_clauses(block) {
                if let ClauseTarget::Block(target) = guarded.target {
                    let mut next_guards = guards.clone();
                    next_guards.push(guarded.guard);
                    queue.push_back((target, next_guards));
                }
            }

            for target in bb.terminator.unguarded_successors() {
                queue.push_back((target, guards.clone()));
            }
        }

        discovered.into_iter().flatten().collect()
    }
}

/// A local variable declaration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LocalDecl {
    pub index: usize,
    pub ty: Ty,
    pub name: Option<String>,
}

/// Source location.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct SourceSpan {
    pub file: String,
    pub line_start: u32,
    pub col_start: u32,
    pub line_end: u32,
    pub col_end: u32,
}

/// A contract specification (requires/ensures).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Contract {
    pub kind: ContractKind,
    pub span: SourceSpan,
    pub body: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ContractKind {
    Requires,
    Ensures,
    Invariant,
    Decreases,
    // tRust #588: Sunder-style contract extensions for Horn clause lowering.
    /// Loop invariant that must hold at a specific loop header.
    /// Unlike `Invariant` (a general assertion), `LoopInvariant` is lowered
    /// to three CHC obligations: initiation, consecution, and sufficiency.
    LoopInvariant,
    /// Type refinement predicate constraining a variable's domain
    /// (e.g., `x: {v: i32 | v > 0}`). Lowered to Horn clause body constraints.
    TypeRefinement,
    /// Frame condition specifying which variables a function may modify.
    /// Everything not in the modifies set is implicitly preserved.
    Modifies,
}

impl ContractKind {
    /// The attribute name as it appears in source code.
    pub fn attr_name(&self) -> &'static str {
        match self {
            ContractKind::Requires => "requires",
            ContractKind::Ensures => "ensures",
            ContractKind::Invariant => "invariant",
            ContractKind::Decreases => "decreases",
            // tRust #588: Sunder contract extension attribute names.
            ContractKind::LoopInvariant => "loop_invariant",
            ContractKind::TypeRefinement => "refine",
            ContractKind::Modifies => "modifies",
        }
    }

    /// Format as a source-level attribute string, e.g. `#[requires("x > 0")]`.
    pub fn format_attr(&self, expr: &str) -> String {
        format!("#[{}(\"{}\")]", self.attr_name(), expr)
    }

    /// Parse a contract kind from an attribute name string.
    #[must_use]
    pub fn from_attr_name(name: &str) -> Option<Self> {
        match name {
            "requires" => Some(ContractKind::Requires),
            "ensures" => Some(ContractKind::Ensures),
            "invariant" => Some(ContractKind::Invariant),
            "decreases" => Some(ContractKind::Decreases),
            // tRust #588: Sunder contract extension attribute names.
            "loop_invariant" => Some(ContractKind::LoopInvariant),
            "refine" => Some(ContractKind::TypeRefinement),
            "modifies" => Some(ContractKind::Modifies),
            _ => None,
        }
    }
}

impl std::fmt::Display for ContractKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.attr_name())
    }
}

// tRust #66: Decreases clause for termination checking.

/// A decreases clause specifying a well-founded measure that must strictly
/// decrease on each loop iteration or recursive call to prove termination.
///
/// The `measure` is a Formula over function locals that maps to a natural
/// number (non-negative integer). Termination is proved by showing:
///   1. The measure is non-negative (bounded below by 0).
///   2. The measure strictly decreases on each iteration/recursive call.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DecreasesClause {
    /// The expression that must decrease (e.g., `n`, `len - i`).
    pub measure: String,
    /// Where this clause was specified or inferred.
    pub span: SourceSpan,
    /// The kind of termination argument this clause supports.
    pub kind: DecreasesKind,
}

/// Whether the decreases clause applies to a loop or a recursive function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum DecreasesKind {
    /// Loop variant: measure decreases on each iteration of the loop
    /// at the given back-edge block.
    LoopVariant { header_block: usize },
    /// Recursive function: measure decreases on each recursive call.
    Recursion,
}

/// Trust metadata extracted from local items.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct TrustMetadata {
    pub contracts: Vec<Contract>,
    pub trust_annotations: Vec<TrustAnnotation>,
    // tRust #119: Structured spec from parsed contracts.
    #[serde(default)]
    pub spec: FunctionSpec,
}

/// An explicit trust annotation extracted from source attributes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustAnnotation {
    pub kind: TrustAnnotationKind,
    pub span: SourceSpan,
    pub body: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TrustAnnotationKind {
    Boundary,
    Model,
    Assumption,
}

// tRust: #828 — function signatures need structural hashing through nested types.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FnSig {
    pub params: Vec<Ty>,
    pub ret: Box<Ty>,
}

/// Simplified type representation.
// tRust: #828 — MIR function-like types require `Ty` to participate in hashing.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Ty {
    Bool,
    Int {
        width: u32,
        signed: bool,
    },
    Float {
        width: u32,
    },
    Ref {
        mutable: bool,
        inner: Box<Ty>,
    },
    // tRust #432: Raw pointer type for provenance-aware pointer modeling.
    // Distinguishes `*const T` (mutable=false) from `*mut T` (mutable=true).
    RawPtr {
        mutable: bool,
        pointee: Box<Ty>,
    },
    Slice {
        elem: Box<Ty>,
    },
    Array {
        elem: Box<Ty>,
        len: u64,
    },
    Tuple(Vec<Ty>),
    Adt {
        name: String,
        fields: Vec<(String, Ty)>,
    },
    /// Machine bitvector of given width (for binary-lifted code before type recovery).
    // tRust: #575 — return type analysis produces Bv(32) / Bv(64) for machine registers.
    Bv(u32),
    Unit,
    Never,
    // tRust: #828 — preserve closure captures for full MIR type coverage.
    Closure {
        name: String,
        upvars: Vec<Ty>,
    },
    // tRust: #828 — model named function items with their signature.
    FnDef {
        name: String,
        sig: Box<FnSig>,
    },
    // tRust: #828 — model first-class function pointer types.
    FnPtr {
        sig: Box<FnSig>,
    },
    // tRust: #828 — represent trait objects as dynamic dispatch types.
    Dynamic {
        trait_name: String,
    },
    // tRust: #828 — preserve coroutine captures for full MIR type coverage.
    Coroutine {
        name: String,
        upvars: Vec<Ty>,
    },
}

impl Ty {
    /// Returns the bit width for integer types.
    pub fn int_width(&self) -> Option<u32> {
        match self {
            Ty::Int { width, .. } => Some(*width),
            _ => None,
        }
    }

    /// Returns true if this is a signed integer type.
    pub fn is_signed(&self) -> bool {
        matches!(self, Ty::Int { signed: true, .. })
    }

    /// Returns true if this is any integer type.
    pub fn is_integer(&self) -> bool {
        matches!(self, Ty::Int { .. })
    }

    /// Returns true if this is any floating-point type.
    pub fn is_float(&self) -> bool {
        matches!(self, Ty::Float { .. })
    }

    /// Returns true if this is a raw pointer type.
    pub fn is_raw_ptr(&self) -> bool {
        matches!(self, Ty::RawPtr { .. })
    }

    // tRust: #828 — identify closure types emitted by MIR lowering.
    pub fn is_closure(&self) -> bool {
        matches!(self, Ty::Closure { .. })
    }

    // tRust: #828 — treat function items and function pointers as callable pointer-like types.
    pub fn is_fn_ptr(&self) -> bool {
        matches!(self, Ty::FnPtr { .. } | Ty::FnDef { .. })
    }

    // tRust: #828 — detect trait object types for dynamic dispatch handling.
    pub fn is_dynamic(&self) -> bool {
        matches!(self, Ty::Dynamic { .. })
    }

    // tRust: #828 — identify coroutine types emitted by async/generator lowering.
    pub fn is_coroutine(&self) -> bool {
        matches!(self, Ty::Coroutine { .. })
    }

    /// Returns true if this is any pointer-like type (Ref or RawPtr).
    pub fn is_pointer_like(&self) -> bool {
        matches!(self, Ty::Ref { .. } | Ty::RawPtr { .. })
    }

    /// Returns the pointee type for Ref or RawPtr, None otherwise.
    pub fn pointee_ty(&self) -> Option<&Ty> {
        match self {
            Ty::Ref { inner, .. } => Some(inner),
            Ty::RawPtr { pointee, .. } => Some(pointee),
            _ => None,
        }
    }

    /// Returns the bit width for floating-point types.
    pub fn float_width(&self) -> Option<u32> {
        match self {
            Ty::Float { width } => Some(*width),
            _ => None,
        }
    }

    /// Create a usize type (64-bit on most platforms).
    pub fn usize() -> Self {
        Ty::Int { width: 64, signed: false }
    }

    /// Create an isize type (64-bit on most platforms).
    pub fn isize() -> Self {
        Ty::Int { width: 64, signed: true }
    }

    /// Create a u8 type.
    pub fn u8() -> Self {
        Ty::Int { width: 8, signed: false }
    }

    /// Create an i8 type.
    pub fn i8() -> Self {
        Ty::Int { width: 8, signed: true }
    }

    /// Create a u16 type.
    pub fn u16() -> Self {
        Ty::Int { width: 16, signed: false }
    }

    /// Create an i16 type.
    pub fn i16() -> Self {
        Ty::Int { width: 16, signed: true }
    }

    /// Create a u32 type.
    pub fn u32() -> Self {
        Ty::Int { width: 32, signed: false }
    }

    /// Create an i32 type.
    pub fn i32() -> Self {
        Ty::Int { width: 32, signed: true }
    }

    /// Create a u64 type.
    pub fn u64() -> Self {
        Ty::Int { width: 64, signed: false }
    }

    /// Create an i64 type.
    pub fn i64() -> Self {
        Ty::Int { width: 64, signed: true }
    }

    /// Create a u128 type.
    pub fn u128() -> Self {
        Ty::Int { width: 128, signed: false }
    }

    /// Create an i128 type.
    pub fn i128() -> Self {
        Ty::Int { width: 128, signed: true }
    }

    /// Create an f32 type.
    pub fn f32_ty() -> Self {
        Ty::Float { width: 32 }
    }

    /// Create an f64 type.
    pub fn f64_ty() -> Self {
        Ty::Float { width: 64 }
    }

    /// Create a bool type.
    pub fn bool_ty() -> Self {
        Ty::Bool
    }

    /// Create a unit type.
    pub fn unit_ty() -> Self {
        Ty::Unit
    }
}

/// Block identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BlockId(pub usize);

/// A basic block.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BasicBlock {
    pub id: BlockId,
    pub stmts: Vec<Statement>,
    pub terminator: Terminator,
}

impl BasicBlock {
    /// Discover guarded clauses encoded by this block's terminator.
    pub fn discovered_clauses(&self) -> Vec<DiscoveredClause> {
        self.terminator.discovered_clauses(self.id)
    }
}

/// A bounded path-map entry for one reachable block.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PathMapEntry {
    pub block: BlockId,
    pub guards: Vec<GuardCondition>,
    pub exits: Vec<ClauseTarget>,
}

/// Statements we care about for verification.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Statement {
    Assign {
        place: Place,
        rvalue: Rvalue,
        span: SourceSpan, // tRust: per-statement source location for diagnostics
    },
    // tRust: #828 — track local storage lifetime boundaries from MIR.
    StorageLive(usize),
    // tRust: #828 — track local storage lifetime boundaries from MIR.
    StorageDead(usize),
    // tRust: #828 — represent discriminant writes on enum places.
    SetDiscriminant {
        place: Place,
        variant_index: usize,
    },
    // tRust: #828 — model deinitialization effects in MIR.
    Deinit {
        place: Place,
    },
    // tRust: #828 — preserve Stacked Borrows retag statements.
    Retag {
        place: Place,
    },
    // tRust: #828 — preserve place mentions emitted as no-op statements.
    PlaceMention(Place),
    // tRust: #828 — support non-diverging intrinsic calls as statements.
    Intrinsic {
        name: String,
        args: Vec<Operand>,
    },
    // tRust: #828 — carry coverage instrumentation without semantic effect.
    Coverage,
    // tRust: #828 — carry const-eval step counters without semantic effect.
    ConstEvalCounter,
    Nop,
}

/// A place (lvalue) in MIR — a local variable possibly with projections.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Place {
    pub local: usize,
    pub projections: Vec<Projection>,
}

impl Place {
    pub fn local(index: usize) -> Self {
        Place { local: index, projections: vec![] }
    }

    pub fn field(local: usize, field: usize) -> Self {
        Place { local, projections: vec![Projection::Field(field)] }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Projection {
    Field(usize),
    Index(usize),
    Deref,
    Downcast(usize),
    /// Constant-offset indexing into a slice/array (e.g., `[2 from end]`).
    ConstantIndex {
        offset: usize,
        from_end: bool,
    },
    /// Subslice projection (e.g., `[2..5]` or `[2..-3]`).
    Subslice {
        from: usize,
        to: usize,
        from_end: bool,
    },
}

/// An operand — either a local or a constant.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(ConstValue),
    // tRust: #564 — carry SMT-level Formula values from binary lifting.
    // Lifted machine semantics produce symbolic expressions (Formula) that
    // cannot be represented as ConstValue. Downstream VC generation reads
    // these directly.
    Symbolic(crate::Formula),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ConstValue {
    Bool(bool),
    Int(i128),
    Uint(u128, u32),
    Float(f64),
    Unit,
}

/// Rvalues — computations that produce a value.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Rvalue {
    Use(Operand),
    BinaryOp(BinOp, Operand, Operand),
    CheckedBinaryOp(BinOp, Operand, Operand),
    UnaryOp(UnOp, Operand),
    Ref {
        mutable: bool,
        place: Place,
    },
    Cast(Operand, Ty),
    Aggregate(AggregateKind, Vec<Operand>),
    Discriminant(Place),
    Len(Place),
    /// Array repetition: `[operand; count]`.
    Repeat(Operand, usize),
    /// Raw pointer creation (`&raw const`/`&raw mut`). `mutable` = true for `&raw mut`.
    AddressOf(bool, Place),
    /// Copy for deref — semantically equivalent to `Use(Copy(place))` but
    /// preserved so downstream passes can distinguish compiler-inserted copies.
    CopyForDeref(Place),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    /// Three-way comparison (like `Ord::cmp`): returns -1, 0, or 1.
    // tRust: #383 — proper Cmp semantics instead of mapping to Eq.
    Cmp,
}

impl BinOp {
    /// Returns true if this operation can overflow on integer types.
    pub fn can_overflow(&self) -> bool {
        matches!(self, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Shl | BinOp::Shr)
    }

    /// Returns true if this is a division-family operation.
    pub fn is_division(&self) -> bool {
        matches!(self, BinOp::Div | BinOp::Rem)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum UnOp {
    Not,
    Neg,
    /// Extracts metadata (e.g., length) from a fat pointer.
    /// Semantically a no-op for verification: produces an unconstrained usize.
    // tRust: #386 — proper variant instead of fallback to Not.
    PtrMetadata,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AggregateKind {
    Tuple,
    Array,
    Adt { name: String, variant: usize },
    // tRust: #828 — closure aggregates materialize captured environment state.
    Closure { name: String },
    // tRust: #828 — coroutine aggregates materialize generator state.
    Coroutine { name: String },
    // tRust: #828 — async closure aggregates have distinct MIR shape.
    CoroutineClosure { name: String },
    // tRust: #828 — raw pointer aggregates combine data pointer and metadata.
    RawPtr { pointee_ty: Ty, mutable: bool },
}

/// Atomic memory ordering, following the C11/Rust memory model.
///
/// The ordering forms a lattice, NOT a total order.
/// Acquire and Release are incomparable; AcqRel and SeqCst are above both.
///
/// ```text
///        SeqCst
///          |
///        AcqRel
///        /    \
///   Acquire  Release
///        \    /
///        Relaxed
/// ```
///
/// This type deliberately does NOT derive `PartialOrd` or `Ord` because
/// derived `Ord` on an enum uses variant declaration order, which would
/// incorrectly imply a total ordering where Acquire < Release.
///
/// A manual `PartialOrd` is provided that correctly models the C11 lattice:
/// `Acquire` and `Release` are incomparable (`partial_cmp` returns `None`).
/// `Ord` is intentionally NOT implemented — this is a partial order.
// tRust: #603 — canonical ordering type replacing buggy send_sync::AtomicOrdering.
// tRust: #612 — added PartialOrd for lattice comparisons.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AtomicOrdering {
    Relaxed,
    Acquire,
    Release,
    AcqRel,
    SeqCst,
}

impl AtomicOrdering {
    /// Returns true if this ordering provides acquire semantics.
    ///
    /// Acquire semantics means that no reads or writes in the current
    /// thread can be reordered before this load/fence.
    // tRust: #612 -- ported from send_sync::AtomicOrdering for consolidation.
    #[must_use]
    pub fn is_acquire(&self) -> bool {
        matches!(self, Self::Acquire | Self::AcqRel | Self::SeqCst)
    }

    /// Returns true if this ordering provides release semantics.
    ///
    /// Release semantics means that no reads or writes in the current
    /// thread can be reordered after this store/fence.
    // tRust: #612 -- ported from send_sync::AtomicOrdering for consolidation.
    #[must_use]
    pub fn is_release(&self) -> bool {
        matches!(self, Self::Release | Self::AcqRel | Self::SeqCst)
    }

    /// Human-readable name for diagnostics.
    // tRust: #612 -- ported from send_sync::AtomicOrdering for consolidation.
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            Self::Relaxed => "Relaxed",
            Self::Acquire => "Acquire",
            Self::Release => "Release",
            Self::AcqRel => "AcqRel",
            Self::SeqCst => "SeqCst",
        }
    }

    /// Returns true if `self` is at least as strong as `other` in the
    /// memory ordering lattice.
    ///
    /// This correctly models the C11 partial order where Acquire and Release
    /// are incomparable. Neither `Acquire.is_at_least(&Release)` nor
    /// `Release.is_at_least(&Acquire)` returns true.
    #[must_use]
    pub fn is_at_least(&self, other: &AtomicOrdering) -> bool {
        use AtomicOrdering::*;
        match (self, other) {
            // Everything is at least Relaxed.
            (_, Relaxed) => true,
            // Relaxed is only at least Relaxed (handled above).
            (Relaxed, _) => false,
            // SeqCst is at least everything.
            (SeqCst, _) => true,
            // Nothing except SeqCst is at least SeqCst.
            (_, SeqCst) => false,
            // AcqRel is at least Acquire, Release, and AcqRel.
            (AcqRel, Acquire | Release | AcqRel) => true,
            // Acquire is at least Acquire but NOT Release.
            (Acquire, Acquire) => true,
            (Acquire, Release | AcqRel) => false,
            // Release is at least Release but NOT Acquire.
            (Release, Release) => true,
            (Release, Acquire | AcqRel) => false,
        }
    }

    /// Returns the join (least upper bound) of two orderings in the lattice.
    #[must_use]
    pub fn join(&self, other: &AtomicOrdering) -> AtomicOrdering {
        use AtomicOrdering::*;
        if self == other {
            return *self;
        }
        match (self, other) {
            (SeqCst, _) | (_, SeqCst) => SeqCst,
            (AcqRel, _) | (_, AcqRel) => AcqRel,
            // Acquire join Release = AcqRel (they are incomparable)
            (Acquire, Release) | (Release, Acquire) => AcqRel,
            (Acquire, Relaxed) | (Relaxed, Acquire) => Acquire,
            (Release, Relaxed) | (Relaxed, Release) => Release,
            // Remaining self==other cases handled above
            _ => {
                unreachable!("AtomicOrdering::join covers all unequal pairs in the current lattice")
            }
        }
    }

    /// Returns the meet (greatest lower bound) of two orderings in the lattice.
    #[must_use]
    pub fn meet(&self, other: &AtomicOrdering) -> AtomicOrdering {
        use AtomicOrdering::*;
        if self == other {
            return *self;
        }
        match (self, other) {
            (Relaxed, _) | (_, Relaxed) => Relaxed,
            (SeqCst, x) | (x, SeqCst) => *x,
            (AcqRel, x) | (x, AcqRel) => *x,
            // Acquire meet Release = Relaxed (they are incomparable)
            (Acquire, Release) | (Release, Acquire) => Relaxed,
            // Remaining self==other cases handled above
            _ => {
                unreachable!("AtomicOrdering::meet covers all unequal pairs in the current lattice")
            }
        }
    }
}

impl std::fmt::Display for AtomicOrdering {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AtomicOrdering::Relaxed => f.write_str("Relaxed"),
            AtomicOrdering::Acquire => f.write_str("Acquire"),
            AtomicOrdering::Release => f.write_str("Release"),
            AtomicOrdering::AcqRel => f.write_str("AcqRel"),
            AtomicOrdering::SeqCst => f.write_str("SeqCst"),
        }
    }
}

// tRust: #612 -- Manual PartialOrd for the C11 memory ordering lattice.
// Acquire and Release are incomparable, so this is a strict partial order
// (no Ord impl). Use `is_at_least()` for a bool check, or `partial_cmp()`
// for Option<Ordering> when you need the full three-way result.
impl PartialOrd for AtomicOrdering {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self == other {
            return Some(std::cmp::Ordering::Equal);
        }
        let self_ge = self.is_at_least(other);
        let other_ge = other.is_at_least(self);
        match (self_ge, other_ge) {
            (true, false) => Some(std::cmp::Ordering::Greater),
            (false, true) => Some(std::cmp::Ordering::Less),
            // Both true would mean equal, handled above.
            // Both false means incomparable.
            _ => None,
        }
    }
}

/// Atomic operation detected from MIR intrinsic calls.
// tRust: #603 — carries atomic metadata on Terminator::Call.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtomicOperation {
    /// The place being atomically accessed (first arg = raw pointer target).
    pub place: Place,
    /// Destination place for the return value (for Load, Exchange, CAS, Fetch*).
    /// None for Store and Fence.
    pub dest: Option<Place>,
    /// What kind of atomic operation this is.
    pub op_kind: AtomicOpKind,
    /// The memory ordering used (success ordering for CAS).
    pub ordering: AtomicOrdering,
    /// For CAS: the failure ordering. Must satisfy:
    /// - failure_ordering is not Release or AcqRel
    /// - failure_ordering is no stronger than success ordering
    #[serde(default)]
    pub failure_ordering: Option<AtomicOrdering>,
    /// Source span for diagnostics.
    pub span: SourceSpan,
}

/// The kind of atomic operation.
// tRust: #603 — covers all rustc atomic intrinsics including CompilerFence.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AtomicOpKind {
    Load,
    Store,
    Exchange,
    CompareExchange,
    CompareExchangeWeak,
    FetchAdd,
    FetchSub,
    FetchAnd,
    FetchOr,
    FetchXor,
    FetchNand,
    FetchMin,
    FetchMax,
    Fence,
    /// compiler_fence (singlethreadfence): prevents compiler reordering
    /// but does NOT emit a hardware fence. Relevant for signal handlers
    /// and memory-mapped I/O.
    CompilerFence,
}

impl AtomicOpKind {
    /// Returns true if this operation is a read-modify-write operation.
    ///
    /// RMW ops have combined acquire+release semantics when AcqRel is used,
    /// and they extend release sequences (relevant for Phase 2 HB analysis).
    #[must_use]
    pub fn is_rmw(&self) -> bool {
        matches!(
            self,
            AtomicOpKind::Exchange
                | AtomicOpKind::CompareExchange
                | AtomicOpKind::CompareExchangeWeak
                | AtomicOpKind::FetchAdd
                | AtomicOpKind::FetchSub
                | AtomicOpKind::FetchAnd
                | AtomicOpKind::FetchOr
                | AtomicOpKind::FetchXor
                | AtomicOpKind::FetchNand
                | AtomicOpKind::FetchMin
                | AtomicOpKind::FetchMax
        )
    }

    /// Returns true if this is a load-type operation (reads without writing).
    #[must_use]
    pub fn is_load(&self) -> bool {
        matches!(self, AtomicOpKind::Load)
    }

    /// Returns true if this is a store-type operation (writes without reading).
    #[must_use]
    pub fn is_store(&self) -> bool {
        matches!(self, AtomicOpKind::Store)
    }

    /// Returns true if this is a fence operation (no memory location accessed).
    #[must_use]
    pub fn is_fence(&self) -> bool {
        matches!(self, AtomicOpKind::Fence | AtomicOpKind::CompilerFence)
    }
}

impl std::fmt::Display for AtomicOpKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AtomicOpKind::Load => f.write_str("load"),
            AtomicOpKind::Store => f.write_str("store"),
            AtomicOpKind::Exchange => f.write_str("exchange"),
            AtomicOpKind::CompareExchange => f.write_str("compare_exchange"),
            AtomicOpKind::CompareExchangeWeak => f.write_str("compare_exchange_weak"),
            AtomicOpKind::FetchAdd => f.write_str("fetch_add"),
            AtomicOpKind::FetchSub => f.write_str("fetch_sub"),
            AtomicOpKind::FetchAnd => f.write_str("fetch_and"),
            AtomicOpKind::FetchOr => f.write_str("fetch_or"),
            AtomicOpKind::FetchXor => f.write_str("fetch_xor"),
            AtomicOpKind::FetchNand => f.write_str("fetch_nand"),
            AtomicOpKind::FetchMin => f.write_str("fetch_min"),
            AtomicOpKind::FetchMax => f.write_str("fetch_max"),
            AtomicOpKind::Fence => f.write_str("fence"),
            AtomicOpKind::CompilerFence => f.write_str("compiler_fence"),
        }
    }
}

/// The sub-operation for a read-modify-write (RMW) atomic.
///
/// RMW operations atomically read a value, apply an operation, and write back.
/// They have combined acquire+release semantics when `AcqRel` is used and
/// extend release sequences (relevant for happens-before analysis).
// tRust: #612 -- factored out of AtomicOpKind for use in data_race::AccessKind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AtomicRmwOp {
    /// Exchange (swap).
    Xchg,
    /// Addition.
    Add,
    /// Subtraction.
    Sub,
    /// Bitwise AND.
    And,
    /// Bitwise OR.
    Or,
    /// Bitwise XOR.
    Xor,
    /// Bitwise NAND.
    Nand,
    /// Signed/unsigned minimum.
    Min,
    /// Signed/unsigned maximum.
    Max,
    /// Unsigned minimum (for unsigned comparisons specifically).
    UMin,
    /// Unsigned maximum (for unsigned comparisons specifically).
    UMax,
}

impl std::fmt::Display for AtomicRmwOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AtomicRmwOp::Xchg => f.write_str("xchg"),
            AtomicRmwOp::Add => f.write_str("add"),
            AtomicRmwOp::Sub => f.write_str("sub"),
            AtomicRmwOp::And => f.write_str("and"),
            AtomicRmwOp::Or => f.write_str("or"),
            AtomicRmwOp::Xor => f.write_str("xor"),
            AtomicRmwOp::Nand => f.write_str("nand"),
            AtomicRmwOp::Min => f.write_str("min"),
            AtomicRmwOp::Max => f.write_str("max"),
            AtomicRmwOp::UMin => f.write_str("umin"),
            AtomicRmwOp::UMax => f.write_str("umax"),
        }
    }
}

impl AtomicRmwOp {
    /// Convert from an `AtomicOpKind` fetch variant.
    ///
    /// Returns `None` if the kind is not an RMW operation.
    #[must_use]
    pub fn from_op_kind(kind: AtomicOpKind) -> Option<Self> {
        match kind {
            AtomicOpKind::Exchange => Some(AtomicRmwOp::Xchg),
            AtomicOpKind::FetchAdd => Some(AtomicRmwOp::Add),
            AtomicOpKind::FetchSub => Some(AtomicRmwOp::Sub),
            AtomicOpKind::FetchAnd => Some(AtomicRmwOp::And),
            AtomicOpKind::FetchOr => Some(AtomicRmwOp::Or),
            AtomicOpKind::FetchXor => Some(AtomicRmwOp::Xor),
            AtomicOpKind::FetchNand => Some(AtomicRmwOp::Nand),
            AtomicOpKind::FetchMin => Some(AtomicRmwOp::Min),
            AtomicOpKind::FetchMax => Some(AtomicRmwOp::Max),
            _ => None,
        }
    }
}

/// High-level classification of atomic operations.
///
/// Unifies the various `AtomicOpKind` variants into four categories that
/// matter for memory ordering analysis:
/// - **Load**: read-only, may use Relaxed/Acquire/SeqCst.
/// - **Store**: write-only, may use Relaxed/Release/SeqCst.
/// - **Fence**: no memory location, establishes ordering.
/// - **CmpXchg**: compare-and-exchange with success/failure orderings.
/// - **Rmw**: read-modify-write with a sub-operation.
// tRust: #612 -- higher-level atomic op classification for data race analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AtomicOpClass {
    /// Atomic load (read-only).
    Load,
    /// Atomic store (write-only).
    Store,
    /// Memory fence (no location accessed).
    Fence,
    /// Compare-and-exchange (with weak flag).
    CmpXchg { weak: bool },
    /// Read-modify-write operation.
    Rmw(AtomicRmwOp),
}

impl AtomicOpClass {
    /// Classify an `AtomicOpKind` into its high-level class.
    #[must_use]
    pub fn from_op_kind(kind: AtomicOpKind) -> Self {
        match kind {
            AtomicOpKind::Load => AtomicOpClass::Load,
            AtomicOpKind::Store => AtomicOpClass::Store,
            AtomicOpKind::Fence | AtomicOpKind::CompilerFence => AtomicOpClass::Fence,
            AtomicOpKind::CompareExchange => AtomicOpClass::CmpXchg { weak: false },
            AtomicOpKind::CompareExchangeWeak => AtomicOpClass::CmpXchg { weak: true },
            AtomicOpKind::Exchange => AtomicOpClass::Rmw(AtomicRmwOp::Xchg),
            AtomicOpKind::FetchAdd => AtomicOpClass::Rmw(AtomicRmwOp::Add),
            AtomicOpKind::FetchSub => AtomicOpClass::Rmw(AtomicRmwOp::Sub),
            AtomicOpKind::FetchAnd => AtomicOpClass::Rmw(AtomicRmwOp::And),
            AtomicOpKind::FetchOr => AtomicOpClass::Rmw(AtomicRmwOp::Or),
            AtomicOpKind::FetchXor => AtomicOpClass::Rmw(AtomicRmwOp::Xor),
            AtomicOpKind::FetchNand => AtomicOpClass::Rmw(AtomicRmwOp::Nand),
            AtomicOpKind::FetchMin => AtomicOpClass::Rmw(AtomicRmwOp::Min),
            AtomicOpKind::FetchMax => AtomicOpClass::Rmw(AtomicRmwOp::Max),
        }
    }

    /// Returns true if this class involves a read (Load, CmpXchg, or Rmw).
    #[must_use]
    pub fn is_read(&self) -> bool {
        matches!(self, AtomicOpClass::Load | AtomicOpClass::CmpXchg { .. } | AtomicOpClass::Rmw(_))
    }

    /// Returns true if this class involves a write (Store, CmpXchg, or Rmw).
    #[must_use]
    pub fn is_write(&self) -> bool {
        matches!(self, AtomicOpClass::Store | AtomicOpClass::CmpXchg { .. } | AtomicOpClass::Rmw(_))
    }
}

impl std::fmt::Display for AtomicOpClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AtomicOpClass::Load => f.write_str("load"),
            AtomicOpClass::Store => f.write_str("store"),
            AtomicOpClass::Fence => f.write_str("fence"),
            AtomicOpClass::CmpXchg { weak: false } => f.write_str("cmpxchg"),
            AtomicOpClass::CmpXchg { weak: true } => f.write_str("cmpxchg_weak"),
            AtomicOpClass::Rmw(op) => write!(f, "rmw_{op}"),
        }
    }
}

/// How a block ends.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Terminator {
    Goto(BlockId),
    SwitchInt {
        discr: Operand,
        targets: Vec<(u128, BlockId)>,
        otherwise: BlockId,
        span: SourceSpan, // tRust: source location for diagnostics
    },
    Return,
    Call {
        func: String,
        args: Vec<Operand>,
        dest: Place,
        target: Option<BlockId>,
        span: SourceSpan, // tRust: source location for diagnostics
        /// tRust #603: Present when the call is a recognized atomic intrinsic.
        /// Downstream passes that don't care about atomics ignore this field.
        #[serde(default)]
        atomic: Option<AtomicOperation>,
    },
    Assert {
        cond: Operand,
        expected: bool,
        msg: AssertMessage,
        target: BlockId,
        span: SourceSpan, // tRust: source location for diagnostics
    },
    Drop {
        place: Place,
        target: BlockId,
        span: SourceSpan, // tRust: source location for diagnostics
    },
    Unreachable,
}

impl Terminator {
    /// Discover guarded clauses for conditional control-flow terminators.
    ///
    /// This is a bounded first slice for MIR guard extraction: only `SwitchInt`
    /// and `Assert` contribute clauses today.
    pub fn discovered_clauses(&self, source: BlockId) -> Vec<DiscoveredClause> {
        match self {
            Terminator::SwitchInt { discr, targets, otherwise, span } => {
                let mut clauses = Vec::with_capacity(targets.len() + 1);

                clauses.extend(targets.iter().map(|(value, target)| DiscoveredClause {
                    source,
                    target: ClauseTarget::Block(*target),
                    guard: GuardCondition::SwitchIntMatch { discr: discr.clone(), value: *value },
                    span: span.clone(),
                }));

                clauses.push(DiscoveredClause {
                    source,
                    target: ClauseTarget::Block(*otherwise),
                    guard: GuardCondition::SwitchIntOtherwise {
                        discr: discr.clone(),
                        excluded_values: targets.iter().map(|(value, _)| *value).collect(),
                    },
                    span: span.clone(),
                });

                clauses
            }
            Terminator::Assert { cond, expected, msg, target, span } => vec![
                DiscoveredClause {
                    source,
                    target: ClauseTarget::Block(*target),
                    guard: GuardCondition::AssertHolds { cond: cond.clone(), expected: *expected },
                    span: span.clone(),
                },
                DiscoveredClause {
                    source,
                    target: ClauseTarget::Panic,
                    guard: GuardCondition::AssertFails {
                        cond: cond.clone(),
                        expected: *expected,
                        msg: msg.clone(),
                    },
                    span: span.clone(),
                },
            ],
            _ => vec![],
        }
    }

    /// Plain successor blocks that do not add a new guard condition.
    pub fn unguarded_successors(&self) -> Vec<BlockId> {
        match self {
            Terminator::Goto(target) => vec![*target],
            Terminator::Call { target, .. } => target.iter().copied().collect(),
            Terminator::Drop { target, .. } => vec![*target],
            Terminator::SwitchInt { .. }
            | Terminator::Return
            | Terminator::Assert { .. }
            | Terminator::Unreachable => vec![],
        }
    }

    /// Exit categories directly reachable from this terminator.
    pub fn exit_targets(&self) -> Vec<ClauseTarget> {
        match self {
            Terminator::Return => vec![ClauseTarget::Return],
            Terminator::Unreachable => vec![ClauseTarget::Unreachable],
            // tRust #804 (P1-16): Assert has both a normal target (condition holds)
            // and a panic target (condition violated).
            Terminator::Assert { target, .. } => {
                vec![ClauseTarget::Block(*target), ClauseTarget::Panic]
            }
            Terminator::SwitchInt { targets, otherwise, .. } => {
                let mut exits = targets
                    .iter()
                    .map(|(_, block)| ClauseTarget::Block(*block))
                    .collect::<Vec<_>>();
                exits.push(ClauseTarget::Block(*otherwise));
                exits
            }
            Terminator::Goto(target) | Terminator::Drop { target, .. } => {
                vec![ClauseTarget::Block(*target)]
            }
            Terminator::Call { target, .. } => {
                target.iter().map(|block| ClauseTarget::Block(*block)).collect()
            }
        }
    }
}

/// A discovered guarded clause from MIR control flow.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DiscoveredClause {
    pub source: BlockId,
    pub target: ClauseTarget,
    pub guard: GuardCondition,
    pub span: SourceSpan,
}

/// Successor category for a discovered clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ClauseTarget {
    Block(BlockId),
    Panic,
    Return,
    Unreachable,
}

/// Guard condition recovered from a conditional MIR terminator.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum GuardCondition {
    SwitchIntMatch { discr: Operand, value: u128 },
    SwitchIntOtherwise { discr: Operand, excluded_values: Vec<u128> },
    AssertHolds { cond: Operand, expected: bool },
    AssertFails { cond: Operand, expected: bool, msg: AssertMessage },
}

// tRust: State machine extraction types for TLA2 temporal verification (#46)

/// A state machine extracted from enum + match patterns in MIR.
///
/// Represents the transition system: states (enum variants), transitions
/// (match arms that assign new enum values), and initial state. This is
/// the bridge between Rust code and temporal model checking (TLA2).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StateMachine {
    /// Name of the enum type used as state variable.
    pub enum_name: String,
    /// Local variable index holding the state enum.
    pub state_local: usize,
    /// All discovered states (enum variants).
    pub states: Vec<StateInfo>,
    /// Transitions between states discovered from match arms.
    pub transitions: Vec<Transition>,
    /// Discriminant value of the initial state (first assigned variant), if known.
    pub initial_state: Option<u128>,
}

impl StateMachine {
    /// Number of unique states.
    pub fn state_count(&self) -> usize {
        self.states.len()
    }

    /// Number of transitions.
    pub fn transition_count(&self) -> usize {
        self.transitions.len()
    }

    /// Look up a state name by its discriminant value.
    pub fn state_name(&self, discriminant: u128) -> Option<&str> {
        self.states.iter().find(|s| s.discriminant == discriminant).map(|s| s.name.as_str())
    }
}

/// A single state (enum variant) in a state machine.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StateInfo {
    /// Variant name (e.g., "Idle", "Connected").
    pub name: String,
    /// Discriminant value used in SwitchInt.
    pub discriminant: u128,
}

/// A transition between two states, discovered from a match arm.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Transition {
    /// Discriminant of the source state (matched variant).
    pub from: u128,
    /// Discriminant of the target state (assigned variant).
    pub to: u128,
    /// Block where the match arm lives.
    pub source_block: BlockId,
    /// Block where the state assignment happens.
    pub target_block: BlockId,
}

/// Assert failure messages (mirrors rustc's AssertKind).
// tRust: #413 — added NullPointerDereference, InvalidEnumConstruction,
// ResumedAfterDrop to match rustc's AssertKind variants.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AssertMessage {
    BoundsCheck,
    Overflow(BinOp),
    OverflowNeg,
    DivisionByZero,
    RemainderByZero,
    ResumedAfterReturn,
    ResumedAfterPanic,
    ResumedAfterDrop,
    MisalignedPointerDereference,
    NullPointerDereference,
    InvalidEnumConstruction,
    Custom(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_midpoint_function() {
        // Hand-build the MIR for: fn get_midpoint(a: usize, b: usize) -> usize { (a + b) / 2 }
        //
        // MIR (simplified):
        //   _0: usize (return)
        //   _1: usize (a)
        //   _2: usize (b)
        //   _3: (usize, bool) (checked add result)
        //   _4: usize (add result)
        //   _5: usize (final result)
        //
        //   bb0:
        //     _3 = CheckedAdd(_1, _2)
        //     assert(!(_3.1), "overflow") -> bb1
        //   bb1:
        //     _4 = (_3.0)
        //     _5 = Div(_4, const 2)
        //     _0 = _5
        //     return

        let func = VerifiableFunction {
            name: "get_midpoint".to_string(),
            def_path: "midpoint::get_midpoint".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None }, // _0 return
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) }, // _1
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) }, // _2
                    LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None }, // _3 checked result
                    LocalDecl { index: 4, ty: Ty::usize(), name: None }, // _4
                    LocalDecl { index: 5, ty: Ty::usize(), name: None }, // _5
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            cond: Operand::Copy(Place::field(3, 1)),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(4),
                                rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(5),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Div,
                                    Operand::Copy(Place::local(4)),
                                    Operand::Constant(ConstValue::Uint(2, 64)),
                                ),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(0),
                                rvalue: Rvalue::Use(Operand::Copy(Place::local(5))),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 2,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        assert_eq!(func.name, "get_midpoint");
        assert_eq!(func.body.locals.len(), 6);
        assert_eq!(func.body.blocks.len(), 2);
        assert_eq!(func.body.arg_count, 2);

        // Verify we can find the overflow assert
        let has_overflow_assert = func.body.blocks.iter().any(|bb| {
            matches!(
                &bb.terminator,
                Terminator::Assert { msg: AssertMessage::Overflow(BinOp::Add), .. }
            )
        });
        assert!(has_overflow_assert, "must have overflow assert for checked add");

        // Verify we can find the division
        let has_div = func.body.blocks.iter().any(|bb| {
            bb.stmts.iter().any(|stmt| {
                matches!(stmt, Statement::Assign { rvalue: Rvalue::BinaryOp(BinOp::Div, ..), .. })
            })
        });
        assert!(has_div, "must have division operation");

        let clauses = func.body.discovered_clauses();
        assert_eq!(clauses.len(), 2);
        assert!(clauses.iter().any(|clause| {
            matches!(clause.target, ClauseTarget::Block(BlockId(1)))
                && matches!(&clause.guard, GuardCondition::AssertHolds { expected: false, .. })
        }));
        assert!(clauses.iter().any(|clause| {
            matches!(clause.target, ClauseTarget::Panic)
                && matches!(
                    &clause.guard,
                    GuardCondition::AssertFails {
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        ..
                    }
                )
        }));
    }

    #[test]
    fn test_switch_int_clause_discovery() {
        let block = BasicBlock {
            id: BlockId(3),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(1)),
                targets: vec![(0, BlockId(4)), (7, BlockId(5))],
                otherwise: BlockId(6),
                span: SourceSpan::default(),
            },
        };

        let clauses = block.discovered_clauses();
        assert_eq!(clauses.len(), 3);

        assert!(clauses.iter().any(|clause| {
            matches!(clause.target, ClauseTarget::Block(BlockId(4)))
                && matches!(
                    &clause.guard,
                    GuardCondition::SwitchIntMatch { discr, value: 0 }
                        if matches!(discr, Operand::Copy(place) if *place == Place::local(1))
                )
        }));

        assert!(clauses.iter().any(|clause| {
            matches!(clause.target, ClauseTarget::Block(BlockId(5)))
                && matches!(
                    &clause.guard,
                    GuardCondition::SwitchIntMatch { discr, value: 7 }
                        if matches!(discr, Operand::Copy(place) if *place == Place::local(1))
                )
        }));

        let otherwise = clauses
            .iter()
            .find(|clause| matches!(clause.target, ClauseTarget::Block(BlockId(6))))
            .expect("otherwise clause");

        match &otherwise.guard {
            GuardCondition::SwitchIntOtherwise { discr, excluded_values } => {
                assert!(matches!(discr, Operand::Copy(place) if *place == Place::local(1)));
                assert_eq!(excluded_values.as_slice(), &[0, 7]);
            }
            other => panic!("unexpected guard: {other:?}"),
        }
    }

    #[test]
    fn test_path_map_accumulates_guards() {
        let body = VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Bool, name: Some("flag".into()) }],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(0)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(0)),
                        expected: true,
                        msg: AssertMessage::Custom("must hold".into()),
                        target: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        };

        let path_map = body.path_map();
        assert_eq!(path_map.len(), 4);

        let bb3 = path_map.iter().find(|entry| entry.block == BlockId(3)).expect("bb3");
        assert_eq!(bb3.guards.len(), 2);
        assert!(matches!(bb3.guards[0], GuardCondition::SwitchIntMatch { value: 1, .. }));
        assert!(matches!(bb3.guards[1], GuardCondition::AssertHolds { expected: true, .. }));
        assert_eq!(bb3.exits, vec![ClauseTarget::Return]);
    }

    #[test]
    fn test_path_map_tracks_otherwise_branch() {
        let body = VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::u32(), name: Some("state".into()) }],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(0)),
                        targets: vec![(0, BlockId(1)), (7, BlockId(2))],
                        otherwise: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Unreachable },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        };

        let path_map = body.path_map();
        let bb3 = path_map.iter().find(|entry| entry.block == BlockId(3)).expect("bb3");
        assert_eq!(bb3.guards.len(), 1);
        assert!(matches!(
            &bb3.guards[0],
            GuardCondition::SwitchIntOtherwise { excluded_values, .. } if excluded_values == &vec![0, 7]
        ));
        assert_eq!(bb3.exits, vec![ClauseTarget::Unreachable]);
    }

    #[test]
    fn test_content_hash_deterministic() {
        let func = VerifiableFunction {
            name: "test".to_string(),
            def_path: "test::test".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Bool, name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Bool,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let h1 = func.content_hash();
        let h2 = func.content_hash();
        assert_eq!(h1, h2, "content hash must be deterministic");
        assert_eq!(h1.len(), 64, "hash is SHA-256 (64 hex chars)");
    }

    #[test]
    fn test_content_hash_changes_with_body() {
        let func1 = VerifiableFunction {
            name: "f".to_string(),
            def_path: "m::f".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Bool, name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Bool,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let func2 = VerifiableFunction {
            name: "f".to_string(),
            def_path: "m::f".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        assert_ne!(
            func1.content_hash(),
            func2.content_hash(),
            "different bodies must have different hashes"
        );
    }

    #[test]
    fn test_content_hash_ignores_name_and_span() {
        let func1 = VerifiableFunction {
            name: "foo".to_string(),
            def_path: "m::foo".to_string(),
            span: SourceSpan {
                file: "a.rs".into(),
                line_start: 1,
                col_start: 0,
                line_end: 1,
                col_end: 10,
            },
            body: VerifiableBody {
                locals: vec![],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let func2 = VerifiableFunction {
            name: "bar".to_string(),
            def_path: "m::bar".to_string(),
            span: SourceSpan {
                file: "b.rs".into(),
                line_start: 99,
                col_start: 0,
                line_end: 99,
                col_end: 10,
            },
            body: func1.body.clone(),
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        assert_eq!(
            func1.content_hash(),
            func2.content_hash(),
            "hash depends only on body+contracts, not name/span"
        );
    }

    #[test]
    fn test_serialization_roundtrip() {
        let func = VerifiableFunction {
            name: "test".to_string(),
            def_path: "test::test".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Bool, name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Bool,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let json = serde_json::to_string(&func).expect("serialize");
        let round: VerifiableFunction = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.name, "test");
    }

    #[test]
    fn test_ty_helpers() {
        assert_eq!(Ty::u8(), Ty::Int { width: 8, signed: false });
        assert_eq!(Ty::i8(), Ty::Int { width: 8, signed: true });
        assert_eq!(Ty::u16(), Ty::Int { width: 16, signed: false });
        assert_eq!(Ty::i16(), Ty::Int { width: 16, signed: true });
        assert_eq!(Ty::u32(), Ty::Int { width: 32, signed: false });
        assert_eq!(Ty::i32(), Ty::Int { width: 32, signed: true });
        assert_eq!(Ty::u64(), Ty::Int { width: 64, signed: false });
        assert_eq!(Ty::i64(), Ty::Int { width: 64, signed: true });
        assert_eq!(Ty::u128(), Ty::Int { width: 128, signed: false });
        assert_eq!(Ty::i128(), Ty::Int { width: 128, signed: true });
        assert!(Ty::usize().is_integer());
        assert!(!Ty::usize().is_signed());
        assert_eq!(Ty::usize(), Ty::Int { width: 64, signed: false });
        assert!(Ty::isize().is_signed());
        assert_eq!(Ty::isize(), Ty::Int { width: 64, signed: true });
        assert_eq!(Ty::u32().int_width(), Some(32));
        assert_eq!(Ty::f32_ty(), Ty::Float { width: 32 });
        assert_eq!(Ty::f64_ty(), Ty::Float { width: 64 });
        assert!(Ty::f32_ty().is_float());
        assert!(Ty::f64_ty().is_float());
        assert!(!Ty::u32().is_float());
        assert!(!Ty::Bool.is_float());
        assert_eq!(Ty::f32_ty().float_width(), Some(32));
        assert_eq!(Ty::f64_ty().float_width(), Some(64));
        assert_eq!(Ty::u32().float_width(), None);
        assert_eq!(Ty::bool_ty(), Ty::Bool);
        assert_eq!(Ty::unit_ty(), Ty::Unit);
        assert_eq!(Ty::Bool.int_width(), None);
    }

    // -------------------------------------------------------------------
    // AtomicOrdering lattice tests (tRust #612)
    // -------------------------------------------------------------------

    #[test]
    fn test_ordering_is_at_least_reflexive() {
        use AtomicOrdering::*;
        for o in [Relaxed, Acquire, Release, AcqRel, SeqCst] {
            assert!(o.is_at_least(&o), "{o} should be at least itself");
        }
    }

    #[test]
    fn test_ordering_relaxed_weakest() {
        use AtomicOrdering::*;
        for o in [Relaxed, Acquire, Release, AcqRel, SeqCst] {
            assert!(o.is_at_least(&Relaxed), "{o} should be at least Relaxed");
        }
    }

    #[test]
    fn test_ordering_seqcst_strongest() {
        use AtomicOrdering::*;
        for o in [Relaxed, Acquire, Release, AcqRel, SeqCst] {
            assert!(SeqCst.is_at_least(&o), "SeqCst should be at least {o}");
        }
        // Only SeqCst is at least SeqCst.
        assert!(!AcqRel.is_at_least(&SeqCst));
        assert!(!Acquire.is_at_least(&SeqCst));
        assert!(!Release.is_at_least(&SeqCst));
        assert!(!Relaxed.is_at_least(&SeqCst));
    }

    #[test]
    fn test_ordering_acquire_release_incomparable() {
        use AtomicOrdering::*;
        assert!(!Acquire.is_at_least(&Release), "Acquire does NOT provide Release semantics");
        assert!(!Release.is_at_least(&Acquire), "Release does NOT provide Acquire semantics");
    }

    #[test]
    fn test_ordering_acqrel_subsumes_both() {
        use AtomicOrdering::*;
        assert!(AcqRel.is_at_least(&Acquire));
        assert!(AcqRel.is_at_least(&Release));
        assert!(AcqRel.is_at_least(&Relaxed));
        assert!(AcqRel.is_at_least(&AcqRel));
        assert!(!Acquire.is_at_least(&AcqRel));
        assert!(!Release.is_at_least(&AcqRel));
    }

    #[test]
    fn test_ordering_partial_cmp_equal() {
        use AtomicOrdering::*;
        for o in [Relaxed, Acquire, Release, AcqRel, SeqCst] {
            assert_eq!(o.partial_cmp(&o), Some(std::cmp::Ordering::Equal));
        }
    }

    #[test]
    fn test_ordering_partial_cmp_incomparable() {
        use AtomicOrdering::*;
        assert_eq!(Acquire.partial_cmp(&Release), None, "Acquire and Release are incomparable");
        assert_eq!(Release.partial_cmp(&Acquire), None);
    }

    #[test]
    fn test_ordering_partial_cmp_comparable() {
        use AtomicOrdering::*;
        assert_eq!(Relaxed.partial_cmp(&SeqCst), Some(std::cmp::Ordering::Less));
        assert_eq!(SeqCst.partial_cmp(&Relaxed), Some(std::cmp::Ordering::Greater));
        assert_eq!(Acquire.partial_cmp(&AcqRel), Some(std::cmp::Ordering::Less));
        assert_eq!(AcqRel.partial_cmp(&Acquire), Some(std::cmp::Ordering::Greater));
        assert_eq!(Release.partial_cmp(&AcqRel), Some(std::cmp::Ordering::Less));
        assert_eq!(AcqRel.partial_cmp(&Release), Some(std::cmp::Ordering::Greater));
        assert_eq!(Relaxed.partial_cmp(&Acquire), Some(std::cmp::Ordering::Less));
        assert_eq!(Relaxed.partial_cmp(&Release), Some(std::cmp::Ordering::Less));
    }

    #[test]
    fn test_ordering_join_lattice() {
        use AtomicOrdering::*;
        // Join is the least upper bound.
        assert_eq!(Relaxed.join(&Relaxed), Relaxed);
        assert_eq!(Relaxed.join(&Acquire), Acquire);
        assert_eq!(Relaxed.join(&Release), Release);
        assert_eq!(Acquire.join(&Release), AcqRel, "join of incomparable elements");
        assert_eq!(Release.join(&Acquire), AcqRel);
        assert_eq!(Acquire.join(&AcqRel), AcqRel);
        assert_eq!(AcqRel.join(&SeqCst), SeqCst);
        assert_eq!(SeqCst.join(&Relaxed), SeqCst);
    }

    #[test]
    fn test_ordering_meet_lattice() {
        use AtomicOrdering::*;
        // Meet is the greatest lower bound.
        assert_eq!(SeqCst.meet(&SeqCst), SeqCst);
        assert_eq!(SeqCst.meet(&AcqRel), AcqRel);
        assert_eq!(AcqRel.meet(&Acquire), Acquire);
        assert_eq!(AcqRel.meet(&Release), Release);
        assert_eq!(Acquire.meet(&Release), Relaxed, "meet of incomparable elements");
        assert_eq!(Release.meet(&Acquire), Relaxed);
        assert_eq!(Acquire.meet(&Relaxed), Relaxed);
        assert_eq!(Relaxed.meet(&Relaxed), Relaxed);
    }

    #[test]
    fn test_ordering_join_commutative() {
        use AtomicOrdering::*;
        let all = [Relaxed, Acquire, Release, AcqRel, SeqCst];
        for &a in &all {
            for &b in &all {
                assert_eq!(a.join(&b), b.join(&a), "join({a}, {b}) should be commutative");
            }
        }
    }

    #[test]
    fn test_ordering_meet_commutative() {
        use AtomicOrdering::*;
        let all = [Relaxed, Acquire, Release, AcqRel, SeqCst];
        for &a in &all {
            for &b in &all {
                assert_eq!(a.meet(&b), b.meet(&a), "meet({a}, {b}) should be commutative");
            }
        }
    }

    #[test]
    fn test_ordering_display() {
        assert_eq!(AtomicOrdering::Relaxed.to_string(), "Relaxed");
        assert_eq!(AtomicOrdering::Acquire.to_string(), "Acquire");
        assert_eq!(AtomicOrdering::Release.to_string(), "Release");
        assert_eq!(AtomicOrdering::AcqRel.to_string(), "AcqRel");
        assert_eq!(AtomicOrdering::SeqCst.to_string(), "SeqCst");
    }

    // -------------------------------------------------------------------
    // AtomicOpKind classification tests (tRust #612)
    // -------------------------------------------------------------------

    #[test]
    fn test_atomic_op_kind_classification() {
        assert!(AtomicOpKind::Load.is_load());
        assert!(!AtomicOpKind::Load.is_store());
        assert!(!AtomicOpKind::Load.is_rmw());
        assert!(!AtomicOpKind::Load.is_fence());

        assert!(AtomicOpKind::Store.is_store());
        assert!(!AtomicOpKind::Store.is_load());
        assert!(!AtomicOpKind::Store.is_rmw());

        assert!(AtomicOpKind::FetchAdd.is_rmw());
        assert!(!AtomicOpKind::FetchAdd.is_load());
        assert!(!AtomicOpKind::FetchAdd.is_store());

        assert!(AtomicOpKind::Fence.is_fence());
        assert!(AtomicOpKind::CompilerFence.is_fence());
        assert!(!AtomicOpKind::Fence.is_rmw());
    }

    #[test]
    fn test_atomic_rmw_op_from_op_kind() {
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::Exchange), Some(AtomicRmwOp::Xchg));
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::FetchAdd), Some(AtomicRmwOp::Add));
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::FetchSub), Some(AtomicRmwOp::Sub));
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::FetchAnd), Some(AtomicRmwOp::And));
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::FetchOr), Some(AtomicRmwOp::Or));
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::FetchXor), Some(AtomicRmwOp::Xor));
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::FetchNand), Some(AtomicRmwOp::Nand));
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::FetchMin), Some(AtomicRmwOp::Min));
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::FetchMax), Some(AtomicRmwOp::Max));
        // Non-RMW kinds return None.
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::Load), None);
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::Store), None);
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::Fence), None);
        assert_eq!(AtomicRmwOp::from_op_kind(AtomicOpKind::CompareExchange), None);
    }

    #[test]
    fn test_atomic_op_class_from_op_kind() {
        assert_eq!(AtomicOpClass::from_op_kind(AtomicOpKind::Load), AtomicOpClass::Load);
        assert_eq!(AtomicOpClass::from_op_kind(AtomicOpKind::Store), AtomicOpClass::Store);
        assert_eq!(AtomicOpClass::from_op_kind(AtomicOpKind::Fence), AtomicOpClass::Fence);
        assert_eq!(
            AtomicOpClass::from_op_kind(AtomicOpKind::CompareExchange),
            AtomicOpClass::CmpXchg { weak: false }
        );
        assert_eq!(
            AtomicOpClass::from_op_kind(AtomicOpKind::CompareExchangeWeak),
            AtomicOpClass::CmpXchg { weak: true }
        );
        assert_eq!(
            AtomicOpClass::from_op_kind(AtomicOpKind::FetchAdd),
            AtomicOpClass::Rmw(AtomicRmwOp::Add)
        );
    }

    #[test]
    fn test_atomic_op_class_read_write() {
        assert!(AtomicOpClass::Load.is_read());
        assert!(!AtomicOpClass::Load.is_write());
        assert!(!AtomicOpClass::Store.is_read());
        assert!(AtomicOpClass::Store.is_write());
        // RMW is both.
        let rmw = AtomicOpClass::Rmw(AtomicRmwOp::Add);
        assert!(rmw.is_read());
        assert!(rmw.is_write());
        // CmpXchg is both.
        let cas = AtomicOpClass::CmpXchg { weak: false };
        assert!(cas.is_read());
        assert!(cas.is_write());
        // Fence is neither.
        assert!(!AtomicOpClass::Fence.is_read());
        assert!(!AtomicOpClass::Fence.is_write());
    }

    #[test]
    fn test_atomic_rmw_op_display() {
        assert_eq!(AtomicRmwOp::Xchg.to_string(), "xchg");
        assert_eq!(AtomicRmwOp::Add.to_string(), "add");
        assert_eq!(AtomicRmwOp::Sub.to_string(), "sub");
        assert_eq!(AtomicRmwOp::UMin.to_string(), "umin");
        assert_eq!(AtomicRmwOp::UMax.to_string(), "umax");
    }

    #[test]
    fn test_atomic_op_class_display() {
        assert_eq!(AtomicOpClass::Load.to_string(), "load");
        assert_eq!(AtomicOpClass::Store.to_string(), "store");
        assert_eq!(AtomicOpClass::Fence.to_string(), "fence");
        assert_eq!(AtomicOpClass::CmpXchg { weak: false }.to_string(), "cmpxchg");
        assert_eq!(AtomicOpClass::CmpXchg { weak: true }.to_string(), "cmpxchg_weak");
        assert_eq!(AtomicOpClass::Rmw(AtomicRmwOp::Add).to_string(), "rmw_add");
    }

    #[test]
    fn test_atomic_rmw_op_serialization_roundtrip() {
        let ops = vec![
            AtomicRmwOp::Xchg,
            AtomicRmwOp::Add,
            AtomicRmwOp::Sub,
            AtomicRmwOp::And,
            AtomicRmwOp::Or,
            AtomicRmwOp::Xor,
            AtomicRmwOp::Nand,
            AtomicRmwOp::Min,
            AtomicRmwOp::Max,
            AtomicRmwOp::UMin,
            AtomicRmwOp::UMax,
        ];
        let json = serde_json::to_string(&ops).expect("serialize");
        let round: Vec<AtomicRmwOp> = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round, ops);
    }
}
