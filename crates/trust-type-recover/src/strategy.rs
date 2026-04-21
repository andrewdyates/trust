// trust-type-recover: type recovery strategy trait and implementations
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::error::TypeRecoveryError;
use crate::evidence::{EvidenceSource, SignaturePosition, TypeEvidence};
use crate::types::{RecoveredType, StructField};
use trust_types::Ty;

/// Input context for type recovery strategies.
///
/// Each strategy extracts what it needs from this context.
#[derive(Debug, Clone, Default)]
pub struct RecoveryContext {
    /// DWARF debug info entries: (die_offset, tag, name, byte_size, type_encoding).
    /// `type_encoding`: 0x05 = signed int, 0x07 = unsigned int, 0x04 = float,
    /// 0x02 = boolean, 0x08 = unsigned char.
    pub dwarf_entries: Vec<DwarfEntry>,

    /// Memory access observations: (instruction_addr, access_offset, access_size).
    pub access_observations: Vec<AccessObservation>,

    /// Value range observations from VSA: (address, min_value, max_value).
    pub value_ranges: Vec<ValueRangeObservation>,

    /// Known function call sites: (call_addr, callee_name, arg_count).
    pub call_sites: Vec<CallSiteObservation>,

    /// Struct-like base+offset memory access observations.
    /// Each entry records an access via base_register + constant_offset.
    pub struct_access_observations: Vec<StructAccessObservation>,

    /// Indexed (array-like) memory access observations.
    /// Each entry records an access via base + index * stride.
    pub indexed_access_observations: Vec<IndexedAccessObservation>,

    /// Pointer dereference observations.
    /// Each entry records a load-then-dereference pattern.
    pub dereference_observations: Vec<DereferenceObservation>,

    /// Return register usage observations at call sites.
    /// Each entry records how the return register is used after a function call.
    pub return_register_observations: Vec<crate::return_type::ReturnTypeObservation>,

    /// Return register state observations at function exits.
    /// Each entry records what the callee leaves in the return register.
    pub callee_return_observations: Vec<crate::return_type::CalleeReturnObservation>,
}

/// A DWARF debug information entry relevant to type recovery.
#[derive(Debug, Clone)]
pub struct DwarfEntry {
    /// Offset within `.debug_info`.
    pub die_offset: u64,
    /// DWARF tag (e.g., `DW_TAG_base_type`, `DW_TAG_pointer_type`).
    pub tag: DwarfTag,
    /// Name attribute, if present.
    pub name: Option<String>,
    /// Byte size attribute, if present.
    pub byte_size: Option<u64>,
    /// Type encoding for base types (DW_ATE_*).
    pub encoding: Option<u8>,
    /// For pointer/array types, the referenced type's DIE offset.
    pub type_ref: Option<u64>,
    /// For struct types, member entries.
    pub members: Vec<DwarfMember>,
}

/// DWARF tag categories relevant to type recovery.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum DwarfTag {
    /// `DW_TAG_base_type` — primitive types.
    BaseType,
    /// `DW_TAG_pointer_type` — pointer to another type.
    PointerType,
    /// `DW_TAG_structure_type` — struct or class.
    StructureType,
    /// `DW_TAG_array_type` — array with element type and bounds.
    ArrayType,
    /// `DW_TAG_subroutine_type` — function signature.
    SubroutineType,
    /// Any other tag we don't specifically handle.
    Other,
}

/// A struct member from DWARF debug info.
#[derive(Debug, Clone)]
pub struct DwarfMember {
    /// Member name.
    pub name: Option<String>,
    /// Byte offset within the struct.
    pub offset: u64,
    /// DIE offset of the member's type.
    pub type_ref: u64,
}

/// An observed memory access for pattern analysis.
#[derive(Debug, Clone)]
pub struct AccessObservation {
    /// Address of the instruction performing the access.
    pub instruction_addr: u64,
    /// Byte offset from a base address being accessed.
    pub access_offset: u64,
    /// Size of the access in bytes.
    pub access_size: u64,
}

/// A value range observation from VSA.
#[derive(Debug, Clone)]
pub struct ValueRangeObservation {
    /// Address where the value was observed.
    pub address: u64,
    /// Minimum value in the range.
    pub min: i128,
    /// Maximum value in the range.
    pub max: i128,
}

/// A call site observation for signature matching.
#[derive(Debug, Clone)]
pub struct CallSiteObservation {
    /// Address of the call instruction.
    pub call_addr: u64,
    /// Name of the called function.
    pub callee_name: String,
    /// Number of arguments observed.
    pub arg_count: usize,
}

/// An observed base+offset memory access (struct field access pattern).
///
/// This captures instructions like `LDR x0, [x1, #16]` where `x1` holds a
/// base pointer and `#16` is a constant field offset.
#[derive(Debug, Clone)]
pub struct StructAccessObservation {
    /// Address of the instruction performing the access.
    pub instruction_addr: u64,
    /// Identifier for the base register/variable (e.g., register number).
    pub base_id: u64,
    /// Constant byte offset from the base.
    pub field_offset: u64,
    /// Size of the access in bytes.
    pub access_size: u64,
}

/// An observed indexed memory access (array access pattern).
///
/// This captures instructions like `LDR x0, [x1, x2, LSL #2]` where `x1`
/// is the base, `x2` is a variable index, and the stride is 4 bytes.
#[derive(Debug, Clone)]
pub struct IndexedAccessObservation {
    /// Address of the instruction performing the access.
    pub instruction_addr: u64,
    /// Identifier for the base register/variable.
    pub base_id: u64,
    /// Stride (element size) in bytes, inferred from shift amount or scale.
    pub stride: u64,
    /// Size of each element access in bytes.
    pub element_size: u64,
    /// Number of distinct index values observed (0 if unknown).
    pub observed_count: u64,
}

/// An observed pointer dereference pattern.
///
/// This captures a load-then-use pattern: first a pointer value is loaded
/// from memory, then that value is used as an address for a subsequent
/// memory access. Indicates pointer indirection.
#[derive(Debug, Clone)]
pub struct DereferenceObservation {
    /// Address of the instruction that loads the pointer.
    pub load_addr: u64,
    /// Address of the instruction that dereferences the loaded pointer.
    pub deref_addr: u64,
    /// Size of the pointer load (typically 8 on 64-bit).
    pub pointer_size: u64,
    /// Size of the dereferenced access (reveals pointee size).
    pub pointee_access_size: u64,
    /// Whether the dereference is a store (write) vs load (read).
    pub is_store: bool,
}

/// Trait for type recovery strategies.
///
/// Each strategy examines different evidence sources (DWARF, access patterns,
/// value ranges) and produces [`TypeEvidence`] with confidence scores.
pub trait TypeRecoveryStrategy {
    /// Human-readable name of this strategy.
    fn name(&self) -> &str;

    /// Attempt to recover type information from the given context.
    ///
    /// Returns a list of evidence items (possibly empty if this strategy
    /// finds nothing applicable). Errors only on malformed input.
    fn recover(&self, ctx: &RecoveryContext) -> Result<Vec<TypeEvidence>, TypeRecoveryError>;
}

// ---------------------------------------------------------------------------
// Strategy: DWARF debug info
// ---------------------------------------------------------------------------

/// Recovers types from DWARF debug information entries.
///
/// This is the highest-confidence strategy when debug info is available.
/// Maps `DW_TAG_base_type`, `DW_TAG_pointer_type`, `DW_TAG_structure_type`,
/// and `DW_TAG_array_type` to `RecoveredType` variants.
#[derive(Debug, Default)]
pub struct DwarfStrategy;

impl TypeRecoveryStrategy for DwarfStrategy {
    fn name(&self) -> &str {
        "dwarf"
    }

    fn recover(&self, ctx: &RecoveryContext) -> Result<Vec<TypeEvidence>, TypeRecoveryError> {
        let mut evidence = Vec::new();

        for entry in &ctx.dwarf_entries {
            if let Some(recovered) = recover_from_dwarf_entry(entry, &ctx.dwarf_entries)? {
                evidence.push(TypeEvidence::new(
                    recovered,
                    0.95, // DWARF is high-confidence when present
                    EvidenceSource::Dwarf {
                        die_offset: entry.die_offset,
                    },
                ));
            }
        }

        Ok(evidence)
    }
}

/// Recover a type from a single DWARF entry, resolving type references.
fn recover_from_dwarf_entry(
    entry: &DwarfEntry,
    all_entries: &[DwarfEntry],
) -> Result<Option<RecoveredType>, TypeRecoveryError> {
    match entry.tag {
        DwarfTag::BaseType => {
            let Some(size) = entry.byte_size else {
                return Err(TypeRecoveryError::DwarfParse(
                    "base type missing byte_size".to_string(),
                ));
            };
            let encoding = entry.encoding.unwrap_or(0);
            let ty = match encoding {
                0x02 => RecoveredType::Primitive(Ty::Bool),         // DW_ATE_boolean
                0x05 => RecoveredType::Primitive(Ty::Int {          // DW_ATE_signed
                    width: (size * 8) as u32,
                    signed: true,
                }),
                0x07 | 0x08 => RecoveredType::Primitive(Ty::Int {   // DW_ATE_unsigned / unsigned_char
                    width: (size * 8) as u32,
                    signed: false,
                }),
                0x04 => RecoveredType::Primitive(Ty::Float {        // DW_ATE_float
                    width: (size * 8) as u32,
                }),
                _ => RecoveredType::Opaque { size },
            };
            Ok(Some(ty))
        }
        DwarfTag::PointerType => {
            let pointee = if let Some(type_ref) = entry.type_ref {
                let referred = all_entries.iter().find(|e| e.die_offset == type_ref);
                if let Some(referred_entry) = referred {
                    recover_from_dwarf_entry(referred_entry, all_entries)?
                        .unwrap_or(RecoveredType::Opaque { size: 0 })
                } else {
                    RecoveredType::Opaque { size: 0 }
                }
            } else {
                // void pointer
                RecoveredType::Opaque { size: 0 }
            };
            Ok(Some(RecoveredType::Pointer {
                mutable: true, // DWARF doesn't distinguish const at pointer level easily
                pointee: Box::new(pointee),
            }))
        }
        DwarfTag::StructureType => {
            let name = entry
                .name
                .clone()
                .unwrap_or_else(|| format!("anon_struct_{:#x}", entry.die_offset));
            let size = entry.byte_size.unwrap_or(0);

            let fields = entry
                .members
                .iter()
                .enumerate()
                .map(|(i, member)| {
                    let field_name = member
                        .name
                        .clone()
                        .unwrap_or_else(|| format!("field_{i}"));
                    let field_ty = all_entries
                        .iter()
                        .find(|e| e.die_offset == member.type_ref)
                        .and_then(|e| recover_from_dwarf_entry(e, all_entries).ok().flatten())
                        .unwrap_or(RecoveredType::Opaque { size: 0 });
                    StructField {
                        name: field_name,
                        offset: member.offset,
                        ty: field_ty,
                    }
                })
                .collect();

            Ok(Some(RecoveredType::Struct {
                name,
                fields,
                size,
            }))
        }
        DwarfTag::ArrayType => {
            let element = if let Some(type_ref) = entry.type_ref {
                all_entries
                    .iter()
                    .find(|e| e.die_offset == type_ref)
                    .and_then(|e| recover_from_dwarf_entry(e, all_entries).ok().flatten())
                    .unwrap_or(RecoveredType::Opaque { size: 0 })
            } else {
                RecoveredType::Opaque { size: 0 }
            };
            // Array length: infer from byte_size / element size
            let length = entry
                .byte_size
                .and_then(|total| element.size_bytes().map(|elem| total / elem.max(1)))
                .unwrap_or(0);
            Ok(Some(RecoveredType::Array {
                element: Box::new(element),
                length,
            }))
        }
        DwarfTag::SubroutineType | DwarfTag::Other => Ok(None),
    }
}

// ---------------------------------------------------------------------------
// Strategy: Access pattern analysis
// ---------------------------------------------------------------------------

/// Infers struct layouts and array types from memory access patterns.
///
/// Groups accesses by base address and looks for:
/// - Regular stride patterns (arrays)
/// - Irregular but consistent offsets (struct fields)
#[derive(Debug, Default)]
pub struct AccessPatternStrategy;

impl TypeRecoveryStrategy for AccessPatternStrategy {
    fn name(&self) -> &str {
        "access_pattern"
    }

    fn recover(&self, ctx: &RecoveryContext) -> Result<Vec<TypeEvidence>, TypeRecoveryError> {
        let mut evidence = Vec::new();

        if ctx.access_observations.is_empty() {
            return Ok(evidence);
        }

        // Detect array patterns: look for regular stride in access offsets
        if let Some(array_evidence) = detect_array_pattern(&ctx.access_observations) {
            evidence.push(array_evidence);
        }

        // Detect struct patterns: irregular offsets with varying sizes
        if let Some(struct_evidence) = detect_struct_pattern(&ctx.access_observations) {
            evidence.push(struct_evidence);
        }

        Ok(evidence)
    }
}

/// Detect an array pattern from regularly-strided accesses.
fn detect_array_pattern(observations: &[AccessObservation]) -> Option<TypeEvidence> {
    if observations.len() < 2 {
        return None;
    }

    let mut sorted: Vec<_> = observations.iter().collect();
    sorted.sort_by_key(|o| o.access_offset);

    // Check if all accesses have the same size (element size)
    let first_size = sorted[0].access_size;
    let uniform_size = sorted.iter().all(|o| o.access_size == first_size);

    if !uniform_size || first_size == 0 {
        return None;
    }

    // Check for regular stride
    let strides: Vec<u64> = sorted
        .windows(2)
        .map(|w| w[1].access_offset.saturating_sub(w[0].access_offset))
        .collect();

    let first_stride = *strides.first()?;
    if first_stride == 0 {
        return None;
    }

    let is_regular = strides.iter().all(|&s| s == first_stride);
    if !is_regular {
        return None;
    }

    let element_ty = size_to_primitive(first_size);
    let length = sorted.len() as u64;

    Some(TypeEvidence::new(
        RecoveredType::Array {
            element: Box::new(element_ty),
            length,
        },
        0.6, // Moderate confidence — pattern could be coincidental
        EvidenceSource::AccessPattern {
            instruction_addr: sorted[0].instruction_addr,
            access_offset: sorted[0].access_offset,
            access_size: first_size,
        },
    ))
}

/// Detect a struct pattern from irregular accesses with varying sizes.
fn detect_struct_pattern(observations: &[AccessObservation]) -> Option<TypeEvidence> {
    if observations.len() < 2 {
        return None;
    }

    let mut sorted: Vec<_> = observations.iter().collect();
    sorted.sort_by_key(|o| o.access_offset);

    // Struct pattern: varying access sizes at different offsets
    let sizes_vary = sorted.windows(2).any(|w| w[0].access_size != w[1].access_size);
    if !sizes_vary {
        return None;
    }

    // Deduplicate by offset (keep largest access size per offset)
    let mut fields: Vec<StructField> = Vec::new();
    for obs in &sorted {
        if !fields.iter().any(|f| f.offset == obs.access_offset) {
            fields.push(StructField {
                name: format!("field_{}", fields.len()),
                offset: obs.access_offset,
                ty: size_to_primitive(obs.access_size),
            });
        }
    }

    if fields.len() < 2 {
        return None;
    }

    // Estimate total size from last field offset + size
    let last = fields.last()?;
    let total_size = last.offset + last.ty.size_bytes().unwrap_or(0);

    Some(TypeEvidence::new(
        RecoveredType::Struct {
            name: format!("recovered_struct_{:#x}", sorted[0].access_offset),
            fields,
            size: total_size,
        },
        0.5, // Lower confidence — field names are synthesized
        EvidenceSource::AccessPattern {
            instruction_addr: sorted[0].instruction_addr,
            access_offset: sorted[0].access_offset,
            access_size: sorted[0].access_size,
        },
    ))
}

// ---------------------------------------------------------------------------
// Strategy: Value range analysis
// ---------------------------------------------------------------------------

/// Infers types from value-set analysis (VSA) results.
///
/// Maps value ranges to the smallest integer type that can represent
/// the observed range. Also detects boolean patterns (values in {0, 1}).
#[derive(Debug, Default)]
pub struct ValueRangeStrategy;

impl TypeRecoveryStrategy for ValueRangeStrategy {
    fn name(&self) -> &str {
        "value_range"
    }

    fn recover(&self, ctx: &RecoveryContext) -> Result<Vec<TypeEvidence>, TypeRecoveryError> {
        ctx.value_ranges
            .iter()
            .map(|vr| {
                if vr.min > vr.max {
                    return Err(TypeRecoveryError::InconsistentValueRange(format!(
                        "min ({}) > max ({})",
                        vr.min, vr.max
                    )));
                }

                let recovered = infer_type_from_range(vr.min, vr.max);
                Ok(TypeEvidence::new(
                    recovered,
                    0.4, // Low confidence — range alone is weak evidence
                    EvidenceSource::ValueRange {
                        min: vr.min,
                        max: vr.max,
                    },
                ))
            })
            .collect()
    }
}

/// Infer the most specific type from a value range.
fn infer_type_from_range(min: i128, max: i128) -> RecoveredType {
    // Boolean: only 0 and 1
    if min >= 0 && max <= 1 {
        return RecoveredType::Primitive(Ty::Bool);
    }

    // Unsigned ranges
    if min >= 0 {
        let width = if max <= i128::from(u8::MAX) {
            8
        } else if max <= i128::from(u16::MAX) {
            16
        } else if max <= i128::from(u32::MAX) {
            32
        } else {
            64
        };
        return RecoveredType::Primitive(Ty::Int {
            width,
            signed: false,
        });
    }

    // Signed ranges
    let width = if min >= i128::from(i8::MIN) && max <= i128::from(i8::MAX) {
        8
    } else if min >= i128::from(i16::MIN) && max <= i128::from(i16::MAX) {
        16
    } else if min >= i128::from(i32::MIN) && max <= i128::from(i32::MAX) {
        32
    } else {
        64
    };
    RecoveredType::Primitive(Ty::Int {
        width,
        signed: true,
    })
}

/// Map an access size in bytes to a primitive recovered type.
fn size_to_primitive(size: u64) -> RecoveredType {
    match size {
        1 => RecoveredType::Primitive(Ty::Int {
            width: 8,
            signed: false,
        }),
        2 => RecoveredType::Primitive(Ty::Int {
            width: 16,
            signed: false,
        }),
        4 => RecoveredType::Primitive(Ty::Int {
            width: 32,
            signed: false,
        }),
        8 => RecoveredType::Primitive(Ty::Int {
            width: 64,
            signed: false,
        }),
        other => RecoveredType::Opaque { size: other },
    }
}

// ---------------------------------------------------------------------------
// Strategy: Signature matching
// ---------------------------------------------------------------------------

/// Infers types by matching function call sites against a catalog of known
/// function signatures (C standard library, POSIX, etc.).
///
/// When a call site references a known function name, this strategy emits
/// evidence for each parameter type and the return type with moderate
/// confidence (0.75). If the observed argument count mismatches the known
/// signature, confidence is reduced.
#[derive(Debug, Default)]
pub struct SignatureMatchStrategy;

impl TypeRecoveryStrategy for SignatureMatchStrategy {
    fn name(&self) -> &str {
        "signature_match"
    }

    fn recover(&self, ctx: &RecoveryContext) -> Result<Vec<TypeEvidence>, TypeRecoveryError> {
        let mut evidence = Vec::new();

        for site in &ctx.call_sites {
            if let Some(sig) = lookup_known_signature(&site.callee_name) {
                // Confidence: full if arg count matches, reduced otherwise.
                let base_confidence = if site.arg_count == sig.params.len() {
                    0.75
                } else {
                    0.45
                };

                // Emit evidence for the return type.
                evidence.push(TypeEvidence::new(
                    sig.return_ty.clone(),
                    base_confidence,
                    EvidenceSource::SignatureMatch {
                        function_name: site.callee_name.clone(),
                        position: SignaturePosition::ReturnValue,
                    },
                ));

                // Emit evidence for each parameter type.
                for (i, param_ty) in sig.params.iter().enumerate() {
                    evidence.push(TypeEvidence::new(
                        param_ty.clone(),
                        base_confidence,
                        EvidenceSource::SignatureMatch {
                            function_name: site.callee_name.clone(),
                            position: SignaturePosition::Parameter(i),
                        },
                    ));
                }
            }
        }

        Ok(evidence)
    }
}

/// A known function signature from the catalog.
struct KnownSignature {
    /// Parameter types in order.
    params: Vec<RecoveredType>,
    /// Return type.
    return_ty: RecoveredType,
}

/// Void pointer: `*mut u8` (opaque).
fn void_ptr() -> RecoveredType {
    RecoveredType::Pointer {
        mutable: true,
        pointee: Box::new(RecoveredType::Opaque { size: 0 }),
    }
}

/// Const void pointer: `*const u8` (opaque).
fn const_void_ptr() -> RecoveredType {
    RecoveredType::Pointer {
        mutable: false,
        pointee: Box::new(RecoveredType::Opaque { size: 0 }),
    }
}

/// Const char pointer: `*const i8`.
fn const_char_ptr() -> RecoveredType {
    RecoveredType::Pointer {
        mutable: false,
        pointee: Box::new(RecoveredType::Primitive(Ty::Int {
            width: 8,
            signed: true,
        })),
    }
}

/// `size_t` — unsigned 64-bit integer.
fn size_t() -> RecoveredType {
    RecoveredType::Primitive(Ty::Int {
        width: 64,
        signed: false,
    })
}

/// `int` — signed 32-bit integer.
fn c_int() -> RecoveredType {
    RecoveredType::Primitive(Ty::Int {
        width: 32,
        signed: true,
    })
}

/// `ssize_t` — signed 64-bit integer.
fn ssize_t() -> RecoveredType {
    RecoveredType::Primitive(Ty::Int {
        width: 64,
        signed: true,
    })
}

/// Look up a function name in the known-signature catalog.
///
/// Matches against C standard library, POSIX, and common runtime functions.
/// Names are matched exactly (no demangling — callers should demangle first).
fn lookup_known_signature(name: &str) -> Option<KnownSignature> {
    let sig = match name {
        // -- Memory allocation (stdlib.h) --
        // void *malloc(size_t size)
        "malloc" => KnownSignature {
            params: vec![size_t()],
            return_ty: void_ptr(),
        },
        // void free(void *ptr)
        "free" => KnownSignature {
            params: vec![void_ptr()],
            return_ty: RecoveredType::Primitive(Ty::Unit),
        },
        // void *realloc(void *ptr, size_t size)
        "realloc" => KnownSignature {
            params: vec![void_ptr(), size_t()],
            return_ty: void_ptr(),
        },
        // void *calloc(size_t nmemb, size_t size)
        "calloc" => KnownSignature {
            params: vec![size_t(), size_t()],
            return_ty: void_ptr(),
        },

        // -- Memory operations (string.h) --
        // void *memcpy(void *dest, const void *src, size_t n)
        "memcpy" => KnownSignature {
            params: vec![void_ptr(), const_void_ptr(), size_t()],
            return_ty: void_ptr(),
        },
        // void *memset(void *s, int c, size_t n)
        "memset" => KnownSignature {
            params: vec![void_ptr(), c_int(), size_t()],
            return_ty: void_ptr(),
        },
        // void *memmove(void *dest, const void *src, size_t n)
        "memmove" => KnownSignature {
            params: vec![void_ptr(), const_void_ptr(), size_t()],
            return_ty: void_ptr(),
        },
        // int memcmp(const void *s1, const void *s2, size_t n)
        "memcmp" => KnownSignature {
            params: vec![const_void_ptr(), const_void_ptr(), size_t()],
            return_ty: c_int(),
        },

        // -- String operations (string.h) --
        // size_t strlen(const char *s)
        "strlen" => KnownSignature {
            params: vec![const_char_ptr()],
            return_ty: size_t(),
        },
        // int strcmp(const char *s1, const char *s2)
        "strcmp" | "strncmp" => KnownSignature {
            params: vec![const_char_ptr(), const_char_ptr()],
            return_ty: c_int(),
        },
        // char *strcpy(char *dest, const char *src)
        "strcpy" | "strncpy" => KnownSignature {
            params: vec![void_ptr(), const_char_ptr()],
            return_ty: void_ptr(),
        },
        // char *strcat(char *dest, const char *src)
        "strcat" => KnownSignature {
            params: vec![void_ptr(), const_char_ptr()],
            return_ty: void_ptr(),
        },

        // -- I/O (stdio.h) --
        // int printf(const char *format, ...)
        "printf" => KnownSignature {
            params: vec![const_char_ptr()],
            return_ty: c_int(),
        },
        // int puts(const char *s)
        "puts" => KnownSignature {
            params: vec![const_char_ptr()],
            return_ty: c_int(),
        },
        // int fprintf(FILE *stream, const char *format, ...)
        "fprintf" => KnownSignature {
            params: vec![void_ptr(), const_char_ptr()],
            return_ty: c_int(),
        },
        // int snprintf(char *str, size_t size, const char *format, ...)
        "snprintf" => KnownSignature {
            params: vec![void_ptr(), size_t(), const_char_ptr()],
            return_ty: c_int(),
        },

        // -- Process (stdlib.h / unistd.h) --
        // void exit(int status) — technically noreturn, approximate as Unit.
        "exit" | "_exit" => KnownSignature {
            params: vec![c_int()],
            return_ty: RecoveredType::Primitive(Ty::Unit),
        },
        // void abort(void)
        "abort" => KnownSignature {
            params: vec![],
            return_ty: RecoveredType::Primitive(Ty::Unit),
        },

        // -- File I/O (POSIX) --
        // int open(const char *pathname, int flags, ...)
        "open" => KnownSignature {
            params: vec![const_char_ptr(), c_int()],
            return_ty: c_int(),
        },
        // int close(int fd)
        "close" => KnownSignature {
            params: vec![c_int()],
            return_ty: c_int(),
        },
        // ssize_t read(int fd, void *buf, size_t count)
        "read" => KnownSignature {
            params: vec![c_int(), void_ptr(), size_t()],
            return_ty: ssize_t(),
        },
        // ssize_t write(int fd, const void *buf, size_t count)
        "write" => KnownSignature {
            params: vec![c_int(), const_void_ptr(), size_t()],
            return_ty: ssize_t(),
        },

        _ => return None,
    };
    Some(sig)
}

// ---------------------------------------------------------------------------
// Strategy: Struct recovery from base+offset patterns
// ---------------------------------------------------------------------------

/// Recovers struct types by analyzing base+offset memory access patterns.
///
/// Groups accesses sharing the same `base_id` and interprets distinct
/// constant offsets as struct fields. Each unique (offset, size) pair
/// becomes a `StructField` with a synthesized name.
#[derive(Debug, Default)]
pub struct StructRecoveryStrategy;

impl TypeRecoveryStrategy for StructRecoveryStrategy {
    fn name(&self) -> &str {
        "struct_recovery"
    }

    fn recover(&self, ctx: &RecoveryContext) -> Result<Vec<TypeEvidence>, TypeRecoveryError> {
        let mut evidence = Vec::new();

        if ctx.struct_access_observations.is_empty() {
            return Ok(evidence);
        }

        // Group observations by base_id
        let mut groups: std::collections::BTreeMap<u64, Vec<&StructAccessObservation>> =
            std::collections::BTreeMap::new();
        for obs in &ctx.struct_access_observations {
            groups.entry(obs.base_id).or_default().push(obs);
        }

        for (base_id, accesses) in &groups {
            // Deduplicate by field_offset, keeping the first observation per offset
            let mut seen_offsets: std::collections::BTreeMap<u64, &StructAccessObservation> =
                std::collections::BTreeMap::new();
            for obs in accesses {
                seen_offsets.entry(obs.field_offset).or_insert(obs);
            }

            // Need at least 2 distinct offsets to identify a struct
            if seen_offsets.len() < 2 {
                continue;
            }

            let mut fields: Vec<StructField> = Vec::new();
            for (i, (&offset, &obs)) in seen_offsets.iter().enumerate() {
                fields.push(StructField {
                    name: format!("field_{i}"),
                    offset,
                    ty: size_to_primitive(obs.access_size),
                });
            }

            // Estimate total size from last field
            let last = fields.last().expect("checked >= 2 fields");
            let total_size = last.offset + last.ty.size_bytes().unwrap_or(0);

            let first_addr = accesses[0].instruction_addr;

            evidence.push(TypeEvidence::new(
                RecoveredType::Struct {
                    name: format!("struct_base_{base_id:#x}"),
                    fields,
                    size: total_size,
                },
                0.65, // Higher than generic access pattern (we have explicit base+offset info)
                EvidenceSource::StructAccess {
                    base_id: *base_id,
                    instruction_addr: first_addr,
                },
            ));
        }

        Ok(evidence)
    }
}

// ---------------------------------------------------------------------------
// Strategy: Array recovery from indexed access patterns
// ---------------------------------------------------------------------------

/// Recovers array types by analyzing indexed memory access patterns.
///
/// Detects patterns like `base + index * stride` which indicate array
/// element access. The stride reveals element size, and the number of
/// observed distinct indices provides an array length lower bound.
#[derive(Debug, Default)]
pub struct ArrayRecoveryStrategy;

impl TypeRecoveryStrategy for ArrayRecoveryStrategy {
    fn name(&self) -> &str {
        "array_recovery"
    }

    fn recover(&self, ctx: &RecoveryContext) -> Result<Vec<TypeEvidence>, TypeRecoveryError> {
        let mut evidence = Vec::new();

        if ctx.indexed_access_observations.is_empty() {
            return Ok(evidence);
        }

        // Group by (base_id, stride) — same base and stride = same array
        let mut groups: std::collections::BTreeMap<(u64, u64), Vec<&IndexedAccessObservation>> =
            std::collections::BTreeMap::new();
        for obs in &ctx.indexed_access_observations {
            if obs.stride == 0 {
                continue; // Invalid stride
            }
            groups.entry((obs.base_id, obs.stride)).or_default().push(obs);
        }

        for (&(base_id, stride), accesses) in &groups {
            let element_size = accesses[0].element_size;

            // Array length: max observed_count across all observations, minimum 1
            let length = accesses
                .iter()
                .map(|a| a.observed_count)
                .max()
                .unwrap_or(1)
                .max(1);

            let element_ty = size_to_primitive(element_size);
            let first_addr = accesses[0].instruction_addr;

            evidence.push(TypeEvidence::new(
                RecoveredType::Array {
                    element: Box::new(element_ty),
                    length,
                },
                0.7, // Good confidence — explicit index+stride is strong evidence
                EvidenceSource::IndexedAccess {
                    base_id,
                    stride,
                    instruction_addr: first_addr,
                },
            ));
        }

        Ok(evidence)
    }
}

// ---------------------------------------------------------------------------
// Strategy: Pointer recovery from dereference patterns
// ---------------------------------------------------------------------------

/// Recovers pointer types by analyzing load-then-dereference patterns.
///
/// When code loads a value from memory (the pointer) and then uses that
/// value as an address for a subsequent access, this indicates pointer
/// indirection. The pointee size reveals what the pointer points to.
#[derive(Debug, Default)]
pub struct PointerRecoveryStrategy;

impl TypeRecoveryStrategy for PointerRecoveryStrategy {
    fn name(&self) -> &str {
        "pointer_recovery"
    }

    fn recover(&self, ctx: &RecoveryContext) -> Result<Vec<TypeEvidence>, TypeRecoveryError> {
        let mut evidence = Vec::new();

        for obs in &ctx.dereference_observations {
            let pointee_ty = size_to_primitive(obs.pointee_access_size);

            evidence.push(TypeEvidence::new(
                RecoveredType::Pointer {
                    mutable: obs.is_store,
                    pointee: Box::new(pointee_ty),
                },
                0.7, // Good confidence — dereference pattern is strong evidence
                EvidenceSource::Dereference {
                    load_addr: obs.load_addr,
                    deref_addr: obs.deref_addr,
                },
            ));
        }

        Ok(evidence)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dwarf_strategy_base_type_i32() {
        let ctx = RecoveryContext {
            dwarf_entries: vec![DwarfEntry {
                die_offset: 0x100,
                tag: DwarfTag::BaseType,
                name: Some("int".to_string()),
                byte_size: Some(4),
                encoding: Some(0x05), // DW_ATE_signed
                type_ref: None,
                members: vec![],
            }],
            ..Default::default()
        };

        let strategy = DwarfStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        assert_eq!(
            evidence[0].recovered_type,
            RecoveredType::Primitive(Ty::Int {
                width: 32,
                signed: true
            })
        );
        assert!(evidence[0].confidence > 0.9);
    }

    #[test]
    fn test_dwarf_strategy_pointer_type() {
        let ctx = RecoveryContext {
            dwarf_entries: vec![
                DwarfEntry {
                    die_offset: 0x100,
                    tag: DwarfTag::BaseType,
                    name: Some("int".to_string()),
                    byte_size: Some(4),
                    encoding: Some(0x05),
                    type_ref: None,
                    members: vec![],
                },
                DwarfEntry {
                    die_offset: 0x200,
                    tag: DwarfTag::PointerType,
                    name: None,
                    byte_size: Some(8),
                    encoding: None,
                    type_ref: Some(0x100),
                    members: vec![],
                },
            ],
            ..Default::default()
        };

        let strategy = DwarfStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 2);
        // Second entry should be pointer to i32
        assert_eq!(
            evidence[1].recovered_type,
            RecoveredType::Pointer {
                mutable: true,
                pointee: Box::new(RecoveredType::Primitive(Ty::Int {
                    width: 32,
                    signed: true
                })),
            }
        );
    }

    #[test]
    fn test_dwarf_strategy_struct_type() {
        let ctx = RecoveryContext {
            dwarf_entries: vec![
                DwarfEntry {
                    die_offset: 0x10,
                    tag: DwarfTag::BaseType,
                    name: Some("int".to_string()),
                    byte_size: Some(4),
                    encoding: Some(0x05),
                    type_ref: None,
                    members: vec![],
                },
                DwarfEntry {
                    die_offset: 0x20,
                    tag: DwarfTag::BaseType,
                    name: Some("float".to_string()),
                    byte_size: Some(4),
                    encoding: Some(0x04),
                    type_ref: None,
                    members: vec![],
                },
                DwarfEntry {
                    die_offset: 0x30,
                    tag: DwarfTag::StructureType,
                    name: Some("Point".to_string()),
                    byte_size: Some(8),
                    encoding: None,
                    type_ref: None,
                    members: vec![
                        DwarfMember {
                            name: Some("x".to_string()),
                            offset: 0,
                            type_ref: 0x10,
                        },
                        DwarfMember {
                            name: Some("y".to_string()),
                            offset: 4,
                            type_ref: 0x20,
                        },
                    ],
                },
            ],
            ..Default::default()
        };

        let strategy = DwarfStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        // 3 entries: int, float, struct
        assert_eq!(evidence.len(), 3);
        let struct_ev = &evidence[2];
        match &struct_ev.recovered_type {
            RecoveredType::Struct { name, fields, size } => {
                assert_eq!(name, "Point");
                assert_eq!(*size, 8);
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].name, "x");
                assert_eq!(fields[1].name, "y");
            }
            other => panic!("expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn test_access_pattern_array_detection() {
        let ctx = RecoveryContext {
            access_observations: vec![
                AccessObservation {
                    instruction_addr: 0x1000,
                    access_offset: 0,
                    access_size: 4,
                },
                AccessObservation {
                    instruction_addr: 0x1004,
                    access_offset: 4,
                    access_size: 4,
                },
                AccessObservation {
                    instruction_addr: 0x1008,
                    access_offset: 8,
                    access_size: 4,
                },
                AccessObservation {
                    instruction_addr: 0x100c,
                    access_offset: 12,
                    access_size: 4,
                },
            ],
            ..Default::default()
        };

        let strategy = AccessPatternStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert!(!evidence.is_empty());
        let arr_ev = evidence
            .iter()
            .find(|e| matches!(e.recovered_type, RecoveredType::Array { .. }))
            .expect("should find array evidence");
        match &arr_ev.recovered_type {
            RecoveredType::Array { element, length } => {
                assert_eq!(*length, 4);
                assert_eq!(element.size_bytes(), Some(4));
            }
            other => panic!("expected Array, got {other:?}"),
        }
    }

    #[test]
    fn test_access_pattern_struct_detection() {
        let ctx = RecoveryContext {
            access_observations: vec![
                AccessObservation {
                    instruction_addr: 0x2000,
                    access_offset: 0,
                    access_size: 4,
                },
                AccessObservation {
                    instruction_addr: 0x2004,
                    access_offset: 4,
                    access_size: 8,
                },
                AccessObservation {
                    instruction_addr: 0x200c,
                    access_offset: 12,
                    access_size: 1,
                },
            ],
            ..Default::default()
        };

        let strategy = AccessPatternStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        let struct_ev = evidence
            .iter()
            .find(|e| matches!(e.recovered_type, RecoveredType::Struct { .. }))
            .expect("should find struct evidence");
        match &struct_ev.recovered_type {
            RecoveredType::Struct { fields, size, .. } => {
                assert_eq!(fields.len(), 3);
                assert_eq!(*size, 13); // 12 + 1
            }
            other => panic!("expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn test_value_range_bool() {
        let ctx = RecoveryContext {
            value_ranges: vec![ValueRangeObservation {
                address: 0x3000,
                min: 0,
                max: 1,
            }],
            ..Default::default()
        };

        let strategy = ValueRangeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        assert_eq!(
            evidence[0].recovered_type,
            RecoveredType::Primitive(Ty::Bool)
        );
    }

    #[test]
    fn test_value_range_unsigned_u8() {
        let ctx = RecoveryContext {
            value_ranges: vec![ValueRangeObservation {
                address: 0x3000,
                min: 0,
                max: 200,
            }],
            ..Default::default()
        };

        let strategy = ValueRangeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        assert_eq!(
            evidence[0].recovered_type,
            RecoveredType::Primitive(Ty::Int {
                width: 8,
                signed: false
            })
        );
    }

    #[test]
    fn test_value_range_signed_i32() {
        let ctx = RecoveryContext {
            value_ranges: vec![ValueRangeObservation {
                address: 0x3000,
                min: -1000,
                max: 50000,
            }],
            ..Default::default()
        };

        let strategy = ValueRangeStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(
            evidence[0].recovered_type,
            RecoveredType::Primitive(Ty::Int {
                width: 32,
                signed: true
            })
        );
    }

    #[test]
    fn test_value_range_inconsistent_error() {
        let ctx = RecoveryContext {
            value_ranges: vec![ValueRangeObservation {
                address: 0x3000,
                min: 100,
                max: 50, // min > max
            }],
            ..Default::default()
        };

        let strategy = ValueRangeStrategy;
        let result = strategy.recover(&ctx);
        assert!(matches!(
            result,
            Err(TypeRecoveryError::InconsistentValueRange(_))
        ));
    }

    #[test]
    fn test_infer_type_from_range_u16() {
        let ty = infer_type_from_range(0, 50000);
        assert_eq!(
            ty,
            RecoveredType::Primitive(Ty::Int {
                width: 16,
                signed: false
            })
        );
    }

    #[test]
    fn test_infer_type_from_range_i8() {
        let ty = infer_type_from_range(-50, 50);
        assert_eq!(
            ty,
            RecoveredType::Primitive(Ty::Int {
                width: 8,
                signed: true
            })
        );
    }

    // -----------------------------------------------------------------------
    // StructRecoveryStrategy tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_struct_recovery_basic() {
        let ctx = RecoveryContext {
            struct_access_observations: vec![
                StructAccessObservation {
                    instruction_addr: 0x4000,
                    base_id: 1,
                    field_offset: 0,
                    access_size: 4,
                },
                StructAccessObservation {
                    instruction_addr: 0x4004,
                    base_id: 1,
                    field_offset: 4,
                    access_size: 8,
                },
                StructAccessObservation {
                    instruction_addr: 0x400c,
                    base_id: 1,
                    field_offset: 12,
                    access_size: 1,
                },
            ],
            ..Default::default()
        };

        let strategy = StructRecoveryStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);

        match &evidence[0].recovered_type {
            RecoveredType::Struct { name, fields, size } => {
                assert!(name.contains("struct_base_0x1"));
                assert_eq!(fields.len(), 3);
                assert_eq!(fields[0].offset, 0);
                assert_eq!(fields[0].ty.size_bytes(), Some(4));
                assert_eq!(fields[1].offset, 4);
                assert_eq!(fields[1].ty.size_bytes(), Some(8));
                assert_eq!(fields[2].offset, 12);
                assert_eq!(fields[2].ty.size_bytes(), Some(1));
                assert_eq!(*size, 13); // 12 + 1
            }
            other => panic!("expected Struct, got {other:?}"),
        }
        assert!(evidence[0].confidence >= 0.6);
    }

    #[test]
    fn test_struct_recovery_multiple_bases() {
        let ctx = RecoveryContext {
            struct_access_observations: vec![
                // Base 1: two fields
                StructAccessObservation {
                    instruction_addr: 0x5000,
                    base_id: 1,
                    field_offset: 0,
                    access_size: 8,
                },
                StructAccessObservation {
                    instruction_addr: 0x5008,
                    base_id: 1,
                    field_offset: 8,
                    access_size: 8,
                },
                // Base 2: two fields
                StructAccessObservation {
                    instruction_addr: 0x5010,
                    base_id: 2,
                    field_offset: 0,
                    access_size: 4,
                },
                StructAccessObservation {
                    instruction_addr: 0x5014,
                    base_id: 2,
                    field_offset: 4,
                    access_size: 4,
                },
            ],
            ..Default::default()
        };

        let strategy = StructRecoveryStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 2); // One struct per base_id
    }

    #[test]
    fn test_struct_recovery_single_field_skipped() {
        // Only one unique offset -> not enough to identify a struct
        let ctx = RecoveryContext {
            struct_access_observations: vec![StructAccessObservation {
                instruction_addr: 0x6000,
                base_id: 1,
                field_offset: 0,
                access_size: 4,
            }],
            ..Default::default()
        };

        let strategy = StructRecoveryStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert!(evidence.is_empty());
    }

    #[test]
    fn test_struct_recovery_deduplicates_offsets() {
        // Two observations at the same offset -> should yield one field
        let ctx = RecoveryContext {
            struct_access_observations: vec![
                StructAccessObservation {
                    instruction_addr: 0x7000,
                    base_id: 1,
                    field_offset: 0,
                    access_size: 4,
                },
                StructAccessObservation {
                    instruction_addr: 0x7004,
                    base_id: 1,
                    field_offset: 0, // duplicate offset
                    access_size: 4,
                },
                StructAccessObservation {
                    instruction_addr: 0x7008,
                    base_id: 1,
                    field_offset: 8,
                    access_size: 4,
                },
            ],
            ..Default::default()
        };

        let strategy = StructRecoveryStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        match &evidence[0].recovered_type {
            RecoveredType::Struct { fields, .. } => {
                assert_eq!(fields.len(), 2); // Deduplicated
            }
            other => panic!("expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn test_struct_recovery_empty_input() {
        let ctx = RecoveryContext::default();
        let strategy = StructRecoveryStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert!(evidence.is_empty());
    }

    // -----------------------------------------------------------------------
    // ArrayRecoveryStrategy tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_array_recovery_basic() {
        let ctx = RecoveryContext {
            indexed_access_observations: vec![IndexedAccessObservation {
                instruction_addr: 0x8000,
                base_id: 1,
                stride: 4,
                element_size: 4,
                observed_count: 10,
            }],
            ..Default::default()
        };

        let strategy = ArrayRecoveryStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);

        match &evidence[0].recovered_type {
            RecoveredType::Array { element, length } => {
                assert_eq!(*length, 10);
                assert_eq!(element.size_bytes(), Some(4));
            }
            other => panic!("expected Array, got {other:?}"),
        }
        assert!(evidence[0].confidence >= 0.7);
    }

    #[test]
    fn test_array_recovery_groups_by_base_and_stride() {
        let ctx = RecoveryContext {
            indexed_access_observations: vec![
                // Same base, same stride -> one array
                IndexedAccessObservation {
                    instruction_addr: 0x9000,
                    base_id: 1,
                    stride: 8,
                    element_size: 8,
                    observed_count: 5,
                },
                IndexedAccessObservation {
                    instruction_addr: 0x9008,
                    base_id: 1,
                    stride: 8,
                    element_size: 8,
                    observed_count: 10, // max is used
                },
                // Different stride -> separate array
                IndexedAccessObservation {
                    instruction_addr: 0x9010,
                    base_id: 1,
                    stride: 4,
                    element_size: 4,
                    observed_count: 3,
                },
            ],
            ..Default::default()
        };

        let strategy = ArrayRecoveryStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 2);

        // Find the stride=8 array — should have max observed_count=10
        let arr8 = evidence
            .iter()
            .find(|e| match &e.recovered_type {
                RecoveredType::Array { element, .. } => element.size_bytes() == Some(8),
                _ => false,
            })
            .expect("should find stride-8 array");
        match &arr8.recovered_type {
            RecoveredType::Array { length, .. } => assert_eq!(*length, 10),
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_array_recovery_zero_stride_skipped() {
        let ctx = RecoveryContext {
            indexed_access_observations: vec![IndexedAccessObservation {
                instruction_addr: 0xa000,
                base_id: 1,
                stride: 0, // invalid
                element_size: 4,
                observed_count: 5,
            }],
            ..Default::default()
        };

        let strategy = ArrayRecoveryStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert!(evidence.is_empty());
    }

    #[test]
    fn test_array_recovery_minimum_length_one() {
        let ctx = RecoveryContext {
            indexed_access_observations: vec![IndexedAccessObservation {
                instruction_addr: 0xb000,
                base_id: 1,
                stride: 4,
                element_size: 4,
                observed_count: 0, // unknown count -> defaults to 1
            }],
            ..Default::default()
        };

        let strategy = ArrayRecoveryStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        match &evidence[0].recovered_type {
            RecoveredType::Array { length, .. } => assert_eq!(*length, 1),
            other => panic!("expected Array, got {other:?}"),
        }
    }

    #[test]
    fn test_array_recovery_empty_input() {
        let ctx = RecoveryContext::default();
        let strategy = ArrayRecoveryStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert!(evidence.is_empty());
    }

    // -----------------------------------------------------------------------
    // PointerRecoveryStrategy tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_pointer_recovery_read_pointer() {
        let ctx = RecoveryContext {
            dereference_observations: vec![DereferenceObservation {
                load_addr: 0xc000,
                deref_addr: 0xc004,
                pointer_size: 8,
                pointee_access_size: 4,
                is_store: false,
            }],
            ..Default::default()
        };

        let strategy = PointerRecoveryStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);

        match &evidence[0].recovered_type {
            RecoveredType::Pointer { mutable, pointee } => {
                assert!(!mutable); // read-only dereference
                assert_eq!(pointee.size_bytes(), Some(4));
            }
            other => panic!("expected Pointer, got {other:?}"),
        }
        assert!(evidence[0].confidence >= 0.7);
    }

    #[test]
    fn test_pointer_recovery_write_pointer() {
        let ctx = RecoveryContext {
            dereference_observations: vec![DereferenceObservation {
                load_addr: 0xd000,
                deref_addr: 0xd004,
                pointer_size: 8,
                pointee_access_size: 8,
                is_store: true,
            }],
            ..Default::default()
        };

        let strategy = PointerRecoveryStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);

        match &evidence[0].recovered_type {
            RecoveredType::Pointer { mutable, pointee } => {
                assert!(mutable); // write dereference
                assert_eq!(pointee.size_bytes(), Some(8));
            }
            other => panic!("expected Pointer, got {other:?}"),
        }
    }

    #[test]
    fn test_pointer_recovery_multiple() {
        let ctx = RecoveryContext {
            dereference_observations: vec![
                DereferenceObservation {
                    load_addr: 0xe000,
                    deref_addr: 0xe004,
                    pointer_size: 8,
                    pointee_access_size: 1,
                    is_store: false,
                },
                DereferenceObservation {
                    load_addr: 0xe010,
                    deref_addr: 0xe014,
                    pointer_size: 8,
                    pointee_access_size: 4,
                    is_store: true,
                },
            ],
            ..Default::default()
        };

        let strategy = PointerRecoveryStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 2);
    }

    #[test]
    fn test_pointer_recovery_empty_input() {
        let ctx = RecoveryContext::default();
        let strategy = PointerRecoveryStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert!(evidence.is_empty());
    }

    #[test]
    fn test_pointer_recovery_byte_pointee() {
        let ctx = RecoveryContext {
            dereference_observations: vec![DereferenceObservation {
                load_addr: 0xf000,
                deref_addr: 0xf004,
                pointer_size: 8,
                pointee_access_size: 1,
                is_store: false,
            }],
            ..Default::default()
        };

        let strategy = PointerRecoveryStrategy;
        let evidence = strategy.recover(&ctx).expect("should recover");
        assert_eq!(evidence.len(), 1);
        match &evidence[0].recovered_type {
            RecoveredType::Pointer { pointee, .. } => {
                // size 1 -> u8
                assert_eq!(
                    **pointee,
                    RecoveredType::Primitive(Ty::Int {
                        width: 8,
                        signed: false
                    })
                );
            }
            other => panic!("expected Pointer, got {other:?}"),
        }
    }
}
