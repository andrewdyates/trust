// trust-type-recover: core type representations
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::Ty;

/// A type recovered from binary analysis, with structural information
/// beyond what `trust_types::Ty` captures (e.g., field names from DWARF).
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum RecoveredType {
    /// Primitive integer or float, directly maps to a `Ty`.
    Primitive(Ty),

    /// Pointer to another recovered type (includes raw vs ref, mutability).
    Pointer {
        /// Whether this is a mutable pointer.
        mutable: bool,
        /// The pointed-to type.
        pointee: Box<RecoveredType>,
    },

    /// Struct with named fields at known offsets.
    Struct {
        /// Struct name (from DWARF or synthesized).
        name: String,
        /// Fields: (name, offset in bytes, recovered type).
        fields: Vec<StructField>,
        /// Total size in bytes.
        size: u64,
    },

    /// Fixed-size array.
    Array {
        /// Element type.
        element: Box<RecoveredType>,
        /// Number of elements.
        length: u64,
    },

    /// Function signature recovered from call-site analysis.
    FunctionSig {
        /// Parameter types.
        params: Vec<RecoveredType>,
        /// Return type.
        return_ty: Box<RecoveredType>,
    },

    /// Type is unknown; only the size is known.
    Opaque {
        /// Size in bytes.
        size: u64,
    },
}

/// A field within a recovered struct type.
#[derive(Debug, Clone, PartialEq)]
pub struct StructField {
    /// Field name (from DWARF debug info, or synthesized like `field_0`).
    pub name: String,
    /// Byte offset from the start of the struct.
    pub offset: u64,
    /// Recovered type of the field.
    pub ty: RecoveredType,
}

impl RecoveredType {
    /// Convert this recovered type to the closest `trust_types::Ty`.
    ///
    /// Loses metadata like field offsets and struct names that `Ty` doesn't track
    /// (it uses string names rather than byte-level layout info).
    #[must_use]
    pub fn to_ty(&self) -> Ty {
        match self {
            Self::Primitive(ty) => ty.clone(),
            Self::Pointer { mutable, pointee } => Ty::RawPtr {
                mutable: *mutable,
                pointee: Box::new(pointee.to_ty()),
            },
            Self::Struct { name, fields, .. } => Ty::Adt {
                name: name.clone(),
                fields: fields.iter().map(|f| (f.name.clone(), f.ty.to_ty())).collect(),
            },
            Self::Array { element, length } => Ty::Array {
                elem: Box::new(element.to_ty()),
                len: *length,
            },
            Self::FunctionSig { return_ty, .. } => {
                // Ty doesn't have a function type; approximate as the return type.
                return_ty.to_ty()
            }
            Self::Opaque { size } => {
                // Best effort: treat as a byte array.
                Ty::Array {
                    elem: Box::new(Ty::Int {
                        width: 8,
                        signed: false,
                    }),
                    len: *size,
                }
            }
        }
    }

    /// Returns the size in bytes if statically known.
    #[must_use]
    pub fn size_bytes(&self) -> Option<u64> {
        match self {
            Self::Primitive(ty) => match ty {
                Ty::Bool => Some(1),
                Ty::Int { width, .. } => Some(u64::from(*width) / 8),
                Ty::Float { width } => Some(u64::from(*width) / 8),
                Ty::Unit => Some(0),
                _ => None,
            },
            Self::Pointer { .. } => Some(8), // Assume 64-bit pointers
            Self::Struct { size, .. } => Some(*size),
            Self::Array { element, length } => {
                element.size_bytes().map(|elem_sz| elem_sz * length)
            }
            Self::Opaque { size } => Some(*size),
            Self::FunctionSig { .. } => Some(8), // Function pointer size
        }
    }
}
