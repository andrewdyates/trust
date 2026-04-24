// trust-machine-sem: Machine state representation
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort};

/// Symbolic machine state: registers, flags, memory, and program counter.
///
/// All components are represented as SMT-level `Formula` values, enabling
/// symbolic reasoning about instruction effects.
#[derive(Debug, Clone)]
pub struct MachineState {
    /// General-purpose registers X0-X30, each a 64-bit bitvector.
    pub gpr: [Formula; 31],
    /// SIMD/FP registers V0-V31, each a 128-bit bitvector.
    /// Scalar FP operations (S/D) use the low 32/64 bits; upper bits are zeroed.
    pub fpr: [Formula; 32],
    /// Stack pointer (SP), 64-bit bitvector.
    pub sp: Formula,
    /// Program counter (PC), 64-bit bitvector.
    pub pc: Formula,
    /// NZCV condition flags (individual booleans).
    pub flags: Flags,
    /// Memory as an SMT array: `(Array BitVec64 BitVec8)`.
    pub memory: Formula,
}

/// The four AArch64 condition flags.
#[derive(Debug, Clone)]
pub struct Flags {
    /// Negative flag.
    pub n: Formula,
    /// Zero flag.
    pub z: Formula,
    /// Carry flag.
    pub c: Formula,
    /// Overflow flag.
    pub v: Formula,
}

impl Flags {
    /// Create symbolic flag variables with a given prefix (e.g. "pre" or "post").
    #[must_use]
    pub fn symbolic(prefix: &str) -> Self {
        Self {
            n: Formula::Var(format!("{prefix}_N"), Sort::Bool),
            z: Formula::Var(format!("{prefix}_Z"), Sort::Bool),
            c: Formula::Var(format!("{prefix}_C"), Sort::Bool),
            v: Formula::Var(format!("{prefix}_V"), Sort::Bool),
        }
    }
}

impl MachineState {
    /// Create a fully symbolic initial state with named variables.
    ///
    /// Registers are `X0`..`X30`, FP registers are `V0`..`V31`,
    /// SP is `SP`, PC is `PC`, flags are `N/Z/C/V`, memory is `MEM`.
    #[must_use]
    pub fn symbolic() -> Self {
        let bv64 = Sort::BitVec(64);
        let bv128 = Sort::BitVec(128);
        let gpr = core::array::from_fn(|i| Formula::Var(format!("X{i}"), bv64.clone()));
        let fpr = core::array::from_fn(|i| Formula::Var(format!("V{i}"), bv128.clone()));
        Self {
            gpr,
            fpr,
            sp: Formula::Var("SP".into(), bv64.clone()),
            pc: Formula::Var("PC".into(), bv64),
            flags: Flags::symbolic(""),
            memory: Formula::Var(
                "MEM".into(),
                Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
            ),
        }
    }

    /// Read a GPR by index (0-30). Returns the zero constant for index 31 at
    /// the given width.
    #[must_use]
    pub fn read_gpr(&self, index: u8, width: u32) -> Formula {
        if index >= 31 {
            // Zero register
            return Formula::BitVec { value: 0, width };
        }
        let full = self.gpr[index as usize].clone();
        if width == 64 {
            full
        } else {
            // Truncate to lower `width` bits.
            Formula::BvExtract { inner: Box::new(full), high: width - 1, low: 0 }
        }
    }

    /// Read the stack pointer at the given width.
    #[must_use]
    pub fn read_sp(&self, width: u32) -> Formula {
        if width == 64 {
            self.sp.clone()
        } else {
            Formula::BvExtract { inner: Box::new(self.sp.clone()), high: width - 1, low: 0 }
        }
    }

    /// Read a SIMD/FP register by index (0-31) at the given width (32/64/128).
    ///
    /// The full register is 128 bits (Q). Scalar accesses (S=32, D=64) extract
    /// the low bits.
    #[must_use]
    pub fn read_fpr(&self, index: u8, width: u32) -> Formula {
        let full = self.fpr[index as usize].clone();
        if width >= 128 {
            full
        } else {
            Formula::BvExtract { inner: Box::new(full), high: width - 1, low: 0 }
        }
    }
}
