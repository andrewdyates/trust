// trust-vcgen/sep_engine.rs: Minimal separation logic provenance engine
//
// Combines the symbolic heap (separation_logic.rs) with provenance tracking
// (memory_provenance.rs) into a unified engine for unsafe Rust verification.
// Interprets MIR statements to update heap state and generates VCs for
// 8 unsafe patterns: raw deref read, raw deref write, alloc, dealloc,
// ptr::copy, transmute, offset, and realloc.
//
// Part of #436: Separation logic provenance engine for unsafe Rust verification
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use trust_types::{
    Formula, Operand, Place, Projection, Rvalue, Sort, SourceSpan, Statement,
    Terminator, VcKind, VerifiableFunction, VerificationCondition,
};

use crate::separation_logic::{
    PointerPermission, ProvenanceId, SepFormula, SymbolicHeap, SymbolicPointer,
};

// ────────────────────────────────────────────────────────────────────────────
// Step 1: SepEngine struct
// ────────────────────────────────────────────────────────────────────────────

/// Minimal separation logic provenance engine for unsafe Rust verification.
///
/// Combines a [`SymbolicHeap`] (heap cells and provenance tracking) with a
/// forward MIR interpreter that detects 8 unsafe patterns and generates
/// verification conditions. The engine tracks heap state across statements
/// and computes frame conditions for modular reasoning.
///
/// # Design
///
/// The engine walks MIR blocks forward, interpreting each statement and
/// terminator. When it detects an unsafe pattern (raw pointer deref, alloc,
/// dealloc, transmute, etc.), it:
///
/// 1. Snapshots the current heap state (pre-state)
/// 2. Updates the heap according to the operation's semantics
/// 3. Computes the frame (cells unchanged between pre and post)
/// 4. Generates VCs asserting the operation's safety preconditions
///
/// # References
///
/// - Reynolds (2002): Separation logic, a logic for shared mutable data
/// - O'Hearn, Pym (1999): The logic of bunched implications
#[derive(Debug, Clone)]
pub(crate) struct SepEngine {
    /// The symbolic heap tracking cells and pointers.
    heap: SymbolicHeap,
    /// Map from MIR local index to the pointer name used in the heap.
    local_to_ptr: FxHashMap<usize, String>,
    /// VCs accumulated during interpretation.
    vcs: Vec<VerificationCondition>,
    /// Function name for VC attribution.
    func_name: String,
}

impl SepEngine {
    /// Create a new engine for a given function.
    #[must_use]
    pub(crate) fn new(func_name: &str) -> Self {
        Self {
            heap: SymbolicHeap::new("sep_heap"),
            local_to_ptr: FxHashMap::default(),
            vcs: Vec::new(),
            func_name: func_name.to_string(),
        }
    }

    /// Number of accumulated VCs.
    #[must_use]
    pub(crate) fn vc_count(&self) -> usize {
        self.vcs.len()
    }

    /// Consume the engine and return accumulated VCs.
    #[must_use]
    pub(crate) fn into_vcs(self) -> Vec<VerificationCondition> {
        self.vcs
    }

    /// Get a reference to the symbolic heap.
    #[must_use]
    pub(crate) fn heap(&self) -> &SymbolicHeap {
        &self.heap
    }

    /// Look up the pointer name for a MIR local.
    #[must_use]
    pub(crate) fn ptr_name_for_local(&self, local: usize) -> Option<&str> {
        self.local_to_ptr.get(&local).map(|s| s.as_str())
    }

    // ────────────────────────────────────────────────────────────────────
    // Step 3: MIR statement interpreter for 8 unsafe patterns
    // ────────────────────────────────────────────────────────────────────

    /// Interpret a MIR statement, updating heap state and emitting VCs.
    pub(crate) fn interpret_statement(&mut self, stmt: &Statement, span: &SourceSpan) {
        if let Statement::Assign { place, rvalue, span: stmt_span } = stmt {
            let sp = if stmt_span.line_start > 0 { stmt_span } else { span };
            self.interpret_assign(place, rvalue, sp);
        }
    }

    /// Interpret a MIR terminator, updating heap state and emitting VCs.
    pub(crate) fn interpret_terminator(&mut self, term: &Terminator) {
        match term {
            // Pattern 3: Allocation via alloc::alloc, Box::new, Vec::with_capacity, etc.
            Terminator::Call { func: callee, dest, span, .. } => {
                self.interpret_call(callee, dest, span);
            }
            // Pattern 4: Deallocation via Drop
            Terminator::Drop { place, span, .. } => {
                self.interpret_drop(place, span);
            }
            _ => {}
        }
    }

    /// Interpret an assignment statement.
    fn interpret_assign(&mut self, place: &Place, rvalue: &Rvalue, span: &SourceSpan) {
        match rvalue {
            // Pattern 1: Raw pointer deref read — `_x = *ptr`
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
            | Rvalue::CopyForDeref(src)
                if has_deref(src) =>
            {
                self.interpret_raw_deref_read(src, span);
            }

            // Pattern 8: Pointer offset via BinaryOp::Add/Sub on pointer locals
            Rvalue::BinaryOp(trust_types::BinOp::Add | trust_types::BinOp::Sub, lhs_op, rhs_op) =>
            {
                // Check if LHS is a tracked pointer (pointer arithmetic)
                if let Operand::Copy(lhs_place) | Operand::Move(lhs_place) = lhs_op
                    && self.local_to_ptr.contains_key(&lhs_place.local) {
                        self.interpret_ptr_offset(place, lhs_place, rhs_op, span);
                    }
            }

            // Pattern 7: Transmute
            Rvalue::Cast(_, _) => {
                // Transmutes appear as Cast rvalues in MIR. VCs are generated
                // by the existing separation_logic::transmute_vc path (via unsafe_vc).
                // The engine here focuses on heap state tracking.
            }

            // Pattern 6: AddressOf (&raw const / &raw mut)
            Rvalue::AddressOf(mutable, src_place) => {
                self.interpret_address_of(place, src_place, *mutable, span);
            }

            // Pattern 2: Raw pointer deref write — `*ptr = val`
            // This is captured when the destination place has a Deref projection
            _ if has_deref(place) => {
                self.interpret_raw_deref_write(place, rvalue, span);
            }

            // Ref creation: track derived pointers
            Rvalue::Ref { mutable, place: src_place } => {
                self.interpret_ref(place, src_place, *mutable);
            }

            // Copy/Move: propagate pointer tracking
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) => {
                if let Some(ptr_name) = self.local_to_ptr.get(&src.local).cloned() {
                    self.local_to_ptr.insert(place.local, ptr_name);
                }
            }

            _ => {}
        }
    }

    /// Pattern 1: Raw pointer dereference read.
    ///
    /// Generates VCs for: null check, allocation validity, provenance bounds.
    fn interpret_raw_deref_read(&mut self, src: &Place, span: &SourceSpan) {
        let ptr_name = self.local_to_ptr.get(&src.local)
            .cloned()
            .unwrap_or_else(|| format!("_{}.*", src.local));

        // Generate heap-aware read VCs
        let read_vcs = self.heap.read_vc(&ptr_name, &self.func_name, span);
        if read_vcs.is_empty() {
            // Pointer not tracked in heap; fall back to deref VCs
            let vcs = crate::separation_logic::deref_vc(&self.func_name, &ptr_name, span);
            self.vcs.extend(vcs);
        } else {
            self.vcs.extend(read_vcs);
        }
    }

    /// Pattern 2: Raw pointer dereference write.
    ///
    /// Generates VCs for: all read checks + write permission + post-write consistency.
    fn interpret_raw_deref_write(
        &mut self,
        dest: &Place,
        rvalue: &Rvalue,
        span: &SourceSpan,
    ) {
        let ptr_name = self.local_to_ptr.get(&dest.local)
            .cloned()
            .unwrap_or_else(|| format!("_{}.*", dest.local));

        let value_formula = rvalue_to_formula(rvalue);

        // Generate heap-aware write VCs
        let write_vcs = self.heap.write_vc(
            &ptr_name,
            &value_formula,
            &self.func_name,
            span,
        );
        if write_vcs.is_empty() {
            // Pointer not tracked; fall back to raw_write_vc
            let vcs = crate::separation_logic::raw_write_vc(
                &self.func_name,
                &ptr_name,
                &value_formula,
                span,
            );
            self.vcs.extend(vcs);
        } else {
            self.vcs.extend(write_vcs);

            // Update heap cell if pointer is tracked
            if let Some(ptr) = self.heap.pointer(&ptr_name) {
                let addr = ptr.addr.clone();
                let prov = ptr.provenance;
                self.heap.write_cell(
                    &format!("cell_{ptr_name}"),
                    addr,
                    value_formula,
                    prov,
                );
            }
        }
    }

    /// Pattern 3: Allocation (alloc::alloc, Box::new, Vec::with_capacity, etc.).
    fn interpret_call(&mut self, callee: &str, dest: &Place, span: &SourceSpan) {
        let lower = callee.to_lowercase();

        if is_alloc_call(&lower) {
            // Fresh allocation: assign provenance and track pointer
            let prov = self.heap.allocate(&format!("alloc_{}", dest.local));
            let ptr_name = format!("alloc_{}", dest.local);
            self.local_to_ptr.insert(dest.local, ptr_name.clone());

            // VC: allocation may fail (null check on result)
            self.vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "[unsafe:sep:alloc] allocation result null check for {} in {}",
                        callee, self.func_name,
                    ),
                },
                function: self.func_name.clone(),
                location: span.clone(),
                formula: Formula::Eq(
                    Box::new(Formula::Var(format!("ptr_{ptr_name}"), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                contract_metadata: None,
            });

            // VC: allocation size must be positive
            self.vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "[unsafe:sep:alloc] allocation size check for {} ({})",
                        callee, prov,
                    ),
                },
                function: self.func_name.clone(),
                location: span.clone(),
                formula: Formula::Le(
                    Box::new(Formula::Var(prov.size_var(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                contract_metadata: None,
            });
        } else if is_dealloc_call(&lower) {
            // Deallocation via explicit dealloc call
            self.interpret_dealloc_call(dest, span, callee);
        } else if is_realloc_call(&lower) {
            // Pattern 8 variant: realloc
            self.interpret_realloc(dest, span, callee);
        } else if lower.contains("ptr::copy") || lower.contains("ptr::copy_nonoverlapping") {
            // Pattern 5: ptr::copy / ptr::copy_nonoverlapping
            self.interpret_ptr_copy(dest, span, callee);
        } else if lower.contains("mem::transmute") {
            // Pattern 7: transmute via call
            let vcs = crate::separation_logic::transmute_vc(
                &self.func_name,
                "Src",
                "Dst",
                span,
            );
            self.vcs.extend(vcs);
        }
    }

    /// Pattern 4: Deallocation via Drop terminator.
    fn interpret_drop(&mut self, place: &Place, span: &SourceSpan) {
        if let Some(ptr_name) = self.local_to_ptr.get(&place.local).cloned()
            && let Some(ptr) = self.heap.pointer(&ptr_name) {
                let prov = ptr.provenance;

                // VC: double-free check
                if self.heap.is_freed(prov) {
                    self.vcs.push(VerificationCondition {
                        kind: VcKind::Assertion {
                            message: format!(
                                "[unsafe:sep:free] double-free of `{ptr_name}` ({prov}) in {}",
                                self.func_name,
                            ),
                        },
                        function: self.func_name.clone(),
                        location: span.clone(),
                        formula: Formula::Bool(true), // definite violation
                        contract_metadata: None,
                    });
                }

                self.heap.free(prov);
            }
    }

    /// Deallocation via explicit dealloc::dealloc call.
    fn interpret_dealloc_call(&mut self, dest: &Place, span: &SourceSpan, callee: &str) {
        if let Some(ptr_name) = self.local_to_ptr.get(&dest.local).cloned()
            && let Some(ptr) = self.heap.pointer(&ptr_name) {
                let prov = ptr.provenance;
                if self.heap.is_freed(prov) {
                    self.vcs.push(VerificationCondition {
                        kind: VcKind::Assertion {
                            message: format!(
                                "[unsafe:sep:free] double-free via `{callee}` of `{ptr_name}` in {}",
                                self.func_name,
                            ),
                        },
                        function: self.func_name.clone(),
                        location: span.clone(),
                        formula: Formula::Bool(true),
                        contract_metadata: None,
                    });
                }
                self.heap.free(prov);
            }
    }

    /// Pattern 5: ptr::copy / ptr::copy_nonoverlapping.
    ///
    /// VCs: source readable, destination writable, non-overlapping if nonoverlapping variant.
    fn interpret_ptr_copy(
        &mut self,
        _dest: &Place,
        span: &SourceSpan,
        callee: &str,
    ) {
        let src_name = "copy_src";
        let dst_name = "copy_dst";

        // Source must be readable
        let read_vcs = crate::separation_logic::deref_vc(&self.func_name, src_name, span);
        self.vcs.extend(read_vcs);

        // Destination must be writable
        let value = Formula::Var("copy_value".to_string(), Sort::Int);
        let write_vcs = crate::separation_logic::raw_write_vc(
            &self.func_name,
            dst_name,
            &value,
            span,
        );
        self.vcs.extend(write_vcs);

        // Non-overlapping check for copy_nonoverlapping
        if callee.to_lowercase().contains("nonoverlapping") {
            let src_ptr = Formula::Var(format!("ptr_{src_name}"), Sort::Int);
            let dst_ptr = Formula::Var(format!("ptr_{dst_name}"), Sort::Int);
            let count = Formula::Var("copy_count".to_string(), Sort::Int);

            // Overlap: src < dst + count AND dst < src + count
            self.vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "[unsafe:sep:copy] overlap check for {} in {}",
                        callee, self.func_name,
                    ),
                },
                function: self.func_name.clone(),
                location: span.clone(),
                formula: Formula::And(vec![
                    Formula::Lt(
                        Box::new(src_ptr.clone()),
                        Box::new(Formula::Add(
                            Box::new(dst_ptr.clone()),
                            Box::new(count.clone()),
                        )),
                    ),
                    Formula::Lt(
                        Box::new(dst_ptr),
                        Box::new(Formula::Add(
                            Box::new(src_ptr),
                            Box::new(count),
                        )),
                    ),
                ]),
                contract_metadata: None,
            });
        }
    }

    /// Pattern 6: AddressOf (&raw const / &raw mut).
    fn interpret_address_of(
        &mut self,
        dest: &Place,
        src_place: &Place,
        mutable: bool,
        span: &SourceSpan,
    ) {
        let ptr_name = format!("raw_{}", dest.local);
        let permission = if mutable {
            PointerPermission::ReadWrite
        } else {
            PointerPermission::ReadOnly
        };

        // If source is tracked, derive provenance; otherwise create fresh
        let prov = if let Some(src_name) = self.local_to_ptr.get(&src_place.local) {
            self.heap.pointer(src_name)
                .map(|p| p.provenance)
                .unwrap_or(ProvenanceId::UNKNOWN)
        } else {
            ProvenanceId::UNKNOWN
        };

        let ptr = SymbolicPointer::new(&ptr_name, prov, permission);
        self.heap.track_pointer(ptr);
        self.local_to_ptr.insert(dest.local, ptr_name);

        // VC: source liveness
        let vcs = crate::separation_logic::address_of_sep_vc(
            &self.func_name,
            &format!("_{}", src_place.local),
            mutable,
            span,
        );
        self.vcs.extend(vcs);
    }

    /// Pattern 8: Pointer offset (ptr.add, ptr.offset, ptr + n).
    fn interpret_ptr_offset(
        &mut self,
        dest: &Place,
        src_place: &Place,
        offset_op: &Operand,
        span: &SourceSpan,
    ) {
        let src_name = self.local_to_ptr.get(&src_place.local)
            .cloned()
            .unwrap_or_else(|| format!("_{}", src_place.local));

        let dest_name = format!("offset_{}", dest.local);
        self.local_to_ptr.insert(dest.local, dest_name.clone());

        // Derive provenance from source
        let prov = self.heap.pointer(&src_name)
            .map(|p| p.provenance)
            .unwrap_or(ProvenanceId::UNKNOWN);

        let permission = self.heap.pointer(&src_name)
            .map(|p| p.permission)
            .unwrap_or(PointerPermission::ReadWrite);

        let offset_formula = operand_to_formula_simple(offset_op);
        let src_addr = Formula::Var(format!("ptr_{src_name}"), Sort::Int);
        let dest_addr = Formula::Add(
            Box::new(src_addr.clone()),
            Box::new(offset_formula),
        );

        let ptr = SymbolicPointer {
            addr: dest_addr,
            provenance: prov,
            name: dest_name.clone(),
            permission,
        };
        self.heap.track_pointer(ptr);

        // VC: result must remain within allocation bounds
        if prov.is_concrete() {
            let base = Formula::Var(prov.base_var(), Sort::Int);
            let size = Formula::Var(prov.size_var(), Sort::Int);
            let dest_addr_var = Formula::Var(format!("ptr_{dest_name}"), Sort::Int);

            self.vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "[unsafe:sep:offset] pointer offset out of bounds for `{src_name}` in {}",
                        self.func_name,
                    ),
                },
                function: self.func_name.clone(),
                location: span.clone(),
                formula: Formula::Or(vec![
                    // dest < base
                    Formula::Lt(
                        Box::new(dest_addr_var.clone()),
                        Box::new(base.clone()),
                    ),
                    // dest >= base + size
                    Formula::Not(Box::new(Formula::Lt(
                        Box::new(dest_addr_var),
                        Box::new(Formula::Add(Box::new(base), Box::new(size))),
                    ))),
                ]),
                contract_metadata: None,
            });
        }
    }

    /// Realloc: free old allocation, create new one.
    fn interpret_realloc(
        &mut self,
        dest: &Place,
        span: &SourceSpan,
        callee: &str,
    ) {
        // Free old allocation if tracked
        if let Some(ptr_name) = self.local_to_ptr.get(&dest.local).cloned()
            && let Some(ptr) = self.heap.pointer(&ptr_name) {
                let prov = ptr.provenance;
                self.heap.free(prov);
            }

        // Allocate new region
        let prov = self.heap.allocate(&format!("realloc_{}", dest.local));
        let ptr_name = format!("realloc_{}", dest.local);
        self.local_to_ptr.insert(dest.local, ptr_name.clone());

        // VC: realloc result null check
        self.vcs.push(VerificationCondition {
            kind: VcKind::Assertion {
                message: format!(
                    "[unsafe:sep:realloc] result null check for {} in {}",
                    callee, self.func_name,
                ),
            },
            function: self.func_name.clone(),
            location: span.clone(),
            formula: Formula::Eq(
                Box::new(Formula::Var(format!("ptr_{ptr_name}"), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
        });

        // VC: new size must be positive
        self.vcs.push(VerificationCondition {
            kind: VcKind::Assertion {
                message: format!(
                    "[unsafe:sep:realloc] new allocation size check for {} ({})",
                    callee, prov,
                ),
            },
            function: self.func_name.clone(),
            location: span.clone(),
            formula: Formula::Le(
                Box::new(Formula::Var(prov.size_var(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
        });
    }

    /// Interpret a Ref rvalue (borrow creation).
    fn interpret_ref(&mut self, dest: &Place, src_place: &Place, mutable: bool) {
        let permission = if mutable {
            PointerPermission::ReadWrite
        } else {
            PointerPermission::ReadOnly
        };

        let (prov, ptr_name) = if let Some(src_name) = self.local_to_ptr.get(&src_place.local) {
            let p = self.heap.pointer(src_name)
                .map(|ptr| ptr.provenance)
                .unwrap_or(ProvenanceId::UNKNOWN);
            (p, format!("ref_{}", dest.local))
        } else {
            (ProvenanceId::UNKNOWN, format!("ref_{}", dest.local))
        };

        let ptr = SymbolicPointer::new(&ptr_name, prov, permission);
        self.heap.track_pointer(ptr);
        self.local_to_ptr.insert(dest.local, ptr_name);
    }

    // ────────────────────────────────────────────────────────────────────
    // Step 4: Frame computation from heap diff
    // ────────────────────────────────────────────────────────────────────

    /// Compute the frame between two heap snapshots.
    ///
    /// The frame is the separating conjunction of cells that exist in
    /// `before` but are unchanged in the current heap. This enables the
    /// frame rule: `{P} C {Q}` implies `{P * R} C {Q * R}` when R is
    /// the frame.
    #[must_use]
    pub(crate) fn compute_frame(
        before: &SymbolicHeap,
        after: &SymbolicHeap,
    ) -> SepFormula {
        let before_formula = before.to_sep_formula();
        let after_formula = after.to_sep_formula();

        // If both are emp, frame is emp
        if before_formula.is_emp() && after_formula.is_emp() {
            return SepFormula::Emp;
        }

        // If before is emp, there is no frame (everything is new)
        if before_formula.is_emp() {
            return SepFormula::Emp;
        }

        // If after is emp, everything was freed; frame is emp
        if after_formula.is_emp() {
            return SepFormula::Emp;
        }

        // Conservative: the frame is the before state minus modified cells.
        // In a more precise implementation, we would track which cells changed.
        // For now, return the before state as a conservative over-approximation
        // of the frame (the caller verifies disjointness separately).
        before_formula
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Step 2: SepFormula::PointsToMulti extension
// ────────────────────────────────────────────────────────────────────────────

/// Create a multi-cell PointsTo formula for a contiguous allocation.
///
/// `points_to_multi(base, values)` produces:
///   `base |-> values[0] * (base+1) |-> values[1] * ... * (base+n-1) |-> values[n-1]`
///
/// This is the natural extension for modeling arrays, slices, and
/// multi-byte allocations in separation logic.
#[must_use]
pub(crate) fn points_to_multi(base: &Formula, values: &[Formula]) -> SepFormula {
    if values.is_empty() {
        return SepFormula::Emp;
    }

    let cells: Vec<SepFormula> = values
        .iter()
        .enumerate()
        .map(|(i, val)| {
            let addr = if i == 0 {
                base.clone()
            } else {
                Formula::Add(
                    Box::new(base.clone()),
                    Box::new(Formula::Int(i as i128)),
                )
            };
            SepFormula::points_to(addr, val.clone())
        })
        .collect();

    SepFormula::star_many(cells)
}

// ────────────────────────────────────────────────────────────────────────────
// Step 5: Integration — check_sep_unsafe for generate_vcs
// ────────────────────────────────────────────────────────────────────────────

/// Generate separation-logic-based VCs for unsafe operations in a function.
///
/// Walks MIR forward through all blocks, interpreting statements and
/// terminators with the [`SepEngine`]. Returns VCs for detected unsafe
/// patterns: raw deref read/write, alloc, dealloc, ptr::copy, transmute,
/// address_of, and pointer offset.
///
/// This function is called from `generate_vcs` in lib.rs.
#[must_use]
pub(crate) fn check_sep_unsafe(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    // Quick check: skip functions with no unsafe-looking patterns
    if !has_unsafe_patterns(func) {
        return Vec::new();
    }

    let mut engine = SepEngine::new(&func.name);

    // Initialize pointer tracking for ref-typed arguments
    for local in &func.body.locals {
        if local.index > 0 && local.index <= func.body.arg_count
            && let trust_types::Ty::Ref { mutable, .. } = &local.ty {
                let ptr_name = format!("arg_{}", local.index);
                let prov = engine.heap.allocate(&ptr_name);
                let permission = if *mutable {
                    PointerPermission::ReadWrite
                } else {
                    PointerPermission::ReadOnly
                };
                let ptr = SymbolicPointer::new(&ptr_name, prov, permission);
                engine.heap.track_pointer(ptr);
                engine.local_to_ptr.insert(local.index, ptr_name);
            }
    }

    // Forward walk through blocks
    let default_span = SourceSpan::default();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let span = match stmt {
                Statement::Assign { span, .. } => span,
                _ => &default_span,
            };
            engine.interpret_statement(stmt, span);
        }
        engine.interpret_terminator(&block.terminator);
    }

    engine.into_vcs()
}

// ────────────────────────────────────────────────────────────────────────────
// Helpers
// ────────────────────────────────────────────────────────────────────────────

/// Check if a place has a Deref projection.
fn has_deref(place: &Place) -> bool {
    place.projections.iter().any(|p| matches!(p, Projection::Deref))
}

/// Check if a function contains patterns that warrant sep-logic analysis.
fn has_unsafe_patterns(func: &VerifiableFunction) -> bool {
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                // Deref on source or destination
                if has_deref(place) {
                    return true;
                }
                match rvalue {
                    Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                    | Rvalue::CopyForDeref(p) if has_deref(p) => return true,
                    Rvalue::AddressOf(_, _) => return true,
                    _ => {}
                }
            }
        }
        // Check for unsafe calls
        if let Terminator::Call { func: callee, .. } = &block.terminator {
            let lower = callee.to_lowercase();
            if is_alloc_call(&lower)
                || is_dealloc_call(&lower)
                || is_realloc_call(&lower)
                || lower.contains("ptr::copy")
                || lower.contains("mem::transmute")
            {
                return true;
            }
        }
    }
    false
}

/// Check if a callee is an allocation function.
fn is_alloc_call(lower: &str) -> bool {
    lower.contains("alloc::alloc")
        || lower.contains("box::new")
        || lower.contains("vec::with_capacity")
        || lower.contains("vec::new")
        || lower.contains("alloc::alloc_zeroed")
}

/// Check if a callee is a deallocation function.
fn is_dealloc_call(lower: &str) -> bool {
    lower.contains("alloc::dealloc") || lower.contains("drop_in_place")
}

/// Check if a callee is a reallocation function.
fn is_realloc_call(lower: &str) -> bool {
    lower.contains("alloc::realloc")
}

/// Convert an rvalue to a formula (simplified).
fn rvalue_to_formula(rvalue: &Rvalue) -> Formula {
    match rvalue {
        Rvalue::Use(op) => operand_to_formula_simple(op),
        _ => Formula::Var("rval".to_string(), Sort::Int),
    }
}

/// Simplified operand-to-formula for the engine (no function context needed).
fn operand_to_formula_simple(op: &Operand) -> Formula {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            Formula::Var(format!("_{}", place.local), Sort::Int)
        }
        Operand::Constant(cv) => match cv {
            trust_types::ConstValue::Bool(b) => Formula::Bool(*b),
            trust_types::ConstValue::Int(n) => Formula::Int(*n),
            trust_types::ConstValue::Uint(n, _) => match i128::try_from(*n) {
                Ok(n) => Formula::Int(n),
                Err(_) => Formula::UInt(*n),
            },
            trust_types::ConstValue::Float(f) => {
                Formula::Var(format!("float_{f}"), Sort::BitVec(64))
            }
            trust_types::ConstValue::Unit => Formula::Int(0),
            _ => Formula::Var("__unknown_const".to_string(), Sort::Int),
        },
        _ => Formula::Var("__unknown_operand".to_string(), Sort::Int),
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{
        BasicBlock, BlockId, LocalDecl, Operand, Place, Projection, Rvalue,
        SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody,
        VerifiableFunction, ProofLevel,
    };

    fn empty_span() -> SourceSpan {
        SourceSpan::default()
    }

    fn make_func(
        name: &str,
        locals: Vec<LocalDecl>,
        arg_count: usize,
        blocks: Vec<BasicBlock>,
    ) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: empty_span(),
            body: VerifiableBody {
                return_ty: Ty::Unit,
                locals,
                arg_count,
                blocks,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    // ── SepEngine basic tests ─────────────────────────────────────────

    #[test]
    fn test_sep_engine_new() {
        let engine = SepEngine::new("test_fn");
        assert_eq!(engine.vc_count(), 0);
        assert_eq!(engine.func_name, "test_fn");
    }

    #[test]
    fn test_sep_engine_into_vcs_empty() {
        let engine = SepEngine::new("test_fn");
        let vcs = engine.into_vcs();
        assert!(vcs.is_empty());
    }

    // ── Pattern 1: Raw pointer deref read ─────────────────────────────

    #[test]
    fn test_raw_deref_read_generates_vcs() {
        let func = make_func(
            "deref_read",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("val".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("ptr".into()) },
            ],
            0,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 2,
                        projections: vec![Projection::Deref],
                    })),
                    span: empty_span(),
                }],
                terminator: Terminator::Return,
            }],
        );

        let vcs = check_sep_unsafe(&func);
        // Should produce deref VCs (null, alloc, align)
        assert!(vcs.len() >= 3, "raw deref read should produce at least 3 VCs, got {}", vcs.len());
        assert!(vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("null check")
        )));
    }

    // ── Pattern 2: Raw pointer deref write ────────────────────────────

    #[test]
    fn test_raw_deref_write_generates_vcs() {
        let func = make_func(
            "deref_write",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("ptr".into()) },
            ],
            0,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place {
                        local: 1,
                        projections: vec![Projection::Deref],
                    },
                    rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Uint(42, 32))),
                    span: empty_span(),
                }],
                terminator: Terminator::Return,
            }],
        );

        let vcs = check_sep_unsafe(&func);
        // Should produce deref VCs + write permission + post-write consistency
        assert!(vcs.len() >= 5, "raw deref write should produce at least 5 VCs, got {}", vcs.len());
        assert!(vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("write permission")
        )));
    }

    // ── Pattern 3: Allocation ─────────────────────────────────────────

    #[test]
    fn test_alloc_generates_vcs() {
        let func = make_func(
            "alloc_test",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("ptr".into()) },
            ],
            0,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    func: "std::alloc::alloc".to_string(),
                    args: vec![],
                    dest: Place::local(1),
                    target: Some(BlockId(1)),
                    span: empty_span(),
                    atomic: None,
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
        );

        let vcs = check_sep_unsafe(&func);
        assert!(vcs.len() >= 2, "alloc should produce at least 2 VCs (null + size), got {}", vcs.len());
        assert!(vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("null check")
        )));
        assert!(vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("size check")
        )));
    }

    // ── Pattern 4: Deallocation (Drop) ────────────────────────────────

    #[test]
    fn test_double_free_generates_vc() {
        let func = make_func(
            "double_free",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("ptr".into()) },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "std::alloc::alloc".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Drop {
                        place: Place::local(1),
                        target: BlockId(2),
                        span: empty_span(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Drop {
                        place: Place::local(1),
                        target: BlockId(3),
                        span: empty_span(),
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![],
                    terminator: Terminator::Return,
                },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        assert!(vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("double-free")
        )), "double drop should produce a double-free VC");
    }

    // ── Pattern 5: ptr::copy_nonoverlapping ───────────────────────────

    #[test]
    fn test_ptr_copy_nonoverlapping_generates_overlap_vc() {
        let func = make_func(
            "copy_test",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("dst".into()) },
            ],
            0,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    func: "std::ptr::copy_nonoverlapping".to_string(),
                    args: vec![],
                    dest: Place::local(1),
                    target: Some(BlockId(1)),
                    span: empty_span(),
                    atomic: None,
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
        );

        let vcs = check_sep_unsafe(&func);
        assert!(vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("overlap")
        )), "copy_nonoverlapping should produce an overlap check VC");
    }

    // ── Pattern 6: AddressOf ──────────────────────────────────────────

    #[test]
    fn test_address_of_generates_vc() {
        let func = make_func(
            "addr_of_test",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("ptr".into()) },
            ],
            0,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::AddressOf(true, Place::local(1)),
                    span: empty_span(),
                }],
                terminator: Terminator::Return,
            }],
        );

        let vcs = check_sep_unsafe(&func);
        assert!(vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("&raw mut")
        )), "AddressOf should produce a source liveness VC");
    }

    // ── Pattern 7: Transmute ──────────────────────────────────────────

    #[test]
    fn test_transmute_call_generates_vcs() {
        let func = make_func(
            "transmute_test",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("val".into()) },
            ],
            0,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    func: "std::mem::transmute".to_string(),
                    args: vec![],
                    dest: Place::local(1),
                    target: Some(BlockId(1)),
                    span: empty_span(),
                    atomic: None,
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
        );

        let vcs = check_sep_unsafe(&func);
        assert_eq!(vcs.len(), 3, "transmute should produce 3 VCs (layout, validity, align)");
        assert!(vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("layout")
        )));
    }

    // ── points_to_multi tests ─────────────────────────────────────────

    #[test]
    fn test_points_to_multi_empty() {
        let base = Formula::Var("base".to_string(), Sort::Int);
        let result = points_to_multi(&base, &[]);
        assert!(result.is_emp());
    }

    #[test]
    fn test_points_to_multi_single() {
        let base = Formula::Var("base".to_string(), Sort::Int);
        let result = points_to_multi(&base, &[Formula::Int(42)]);
        assert_eq!(result.cell_count(), 1);
    }

    #[test]
    fn test_points_to_multi_multiple() {
        let base = Formula::Var("base".to_string(), Sort::Int);
        let values = vec![Formula::Int(1), Formula::Int(2), Formula::Int(3)];
        let result = points_to_multi(&base, &values);
        assert_eq!(result.cell_count(), 3);
    }

    // ── Frame computation tests ───────────────────────────────────────

    #[test]
    fn test_compute_frame_both_empty() {
        let before = SymbolicHeap::new("h1");
        let after = SymbolicHeap::new("h2");
        let frame = SepEngine::compute_frame(&before, &after);
        assert!(frame.is_emp());
    }

    #[test]
    fn test_compute_frame_before_empty() {
        let before = SymbolicHeap::new("h1");
        let mut after = SymbolicHeap::new("h2");
        let prov = after.allocate("p");
        after.write_cell("cell", Formula::Int(0), Formula::Int(42), prov);

        let frame = SepEngine::compute_frame(&before, &after);
        assert!(frame.is_emp(), "no cells before means no frame");
    }

    #[test]
    fn test_compute_frame_with_cells() {
        let mut before = SymbolicHeap::new("h1");
        let prov = before.allocate("p");
        before.write_cell("cell_a", Formula::Int(0), Formula::Int(1), prov);

        let mut after = SymbolicHeap::new("h2");
        let prov2 = after.allocate("q");
        after.write_cell("cell_b", Formula::Int(1), Formula::Int(2), prov2);

        let frame = SepEngine::compute_frame(&before, &after);
        // Conservative: frame is the before state
        assert_eq!(frame.cell_count(), 1);
    }

    // ── Integration: safe function produces no VCs ────────────────────

    #[test]
    fn test_safe_function_no_sep_vcs() {
        let func = make_func(
            "safe_add",
            vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            ],
            2,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        trust_types::BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: empty_span(),
                }],
                terminator: Terminator::Return,
            }],
        );

        let vcs = check_sep_unsafe(&func);
        assert!(vcs.is_empty(), "safe function should produce no sep VCs");
    }

    // ── All sep engine VCs are L0Safety ───────────────────────────────

    #[test]
    fn test_all_sep_engine_vcs_are_l0_safety() {
        let func = make_func(
            "mixed_unsafe",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("ptr".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("val".into()) },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Deref],
                        })),
                        span: empty_span(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        for vc in &vcs {
            assert_eq!(
                vc.kind.proof_level(),
                ProofLevel::L0Safety,
                "all sep engine VCs should be L0Safety"
            );
        }
    }

    // ── Ref argument tracking ─────────────────────────────────────────

    #[test]
    fn test_ref_arg_tracked_and_readable() {
        // fn f(x: &u32) -> u32 { *x }
        let func = make_func(
            "read_ref",
            vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                    name: Some("x".into()),
                },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("val".into()) },
            ],
            1,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Deref],
                    })),
                    span: empty_span(),
                }],
                terminator: Terminator::Return,
            }],
        );

        let vcs = check_sep_unsafe(&func);
        // Ref args are tracked; read through them should produce heap-aware VCs
        // (provenance bounds check, not use-after-free)
        assert!(!vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("use-after-free")
        )), "valid ref arg read should not produce use-after-free VC");
    }

    // ── Use-after-free detection ──────────────────────────────────────

    #[test]
    fn test_use_after_free_detected() {
        // alloc, free, then read through the pointer
        let func = make_func(
            "use_after_free",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("ptr".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("val".into()) },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "std::alloc::alloc".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Drop {
                        place: Place::local(1),
                        target: BlockId(2),
                        span: empty_span(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Deref],
                        })),
                        span: empty_span(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        assert!(vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("use-after-free")
        )), "reading freed pointer should produce use-after-free VC");
    }

    // ── Realloc ───────────────────────────────────────────────────────

    #[test]
    fn test_realloc_generates_vcs() {
        let func = make_func(
            "realloc_test",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("ptr".into()) },
            ],
            0,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    func: "std::alloc::realloc".to_string(),
                    args: vec![],
                    dest: Place::local(1),
                    target: Some(BlockId(1)),
                    span: empty_span(),
                    atomic: None,
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
        );

        let vcs = check_sep_unsafe(&func);
        assert!(vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("realloc")
        )), "realloc should produce VCs");
    }
}
