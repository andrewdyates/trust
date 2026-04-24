// trust-lift: public binary-to-tMIR API
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#[cfg(any(feature = "macho", feature = "elf"))]
use crate::{FunctionBoundary, Lifter};
use crate::{LiftError, LiftedFunction};

/// Which functions to lift from a binary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinaryFunctionSelection {
    /// Lift the parsed binary entry point.
    Entry,
    /// Lift every detected function symbol.
    All,
    /// Lift functions containing these virtual addresses.
    Addresses(Vec<u64>),
    /// Lift functions with these exact normalized symbol names.
    Names(Vec<String>),
}

impl Default for BinaryFunctionSelection {
    fn default() -> Self {
        Self::Entry
    }
}

/// Options for [`lift_binary_to_tmir`].
///
/// The default is conservative proof mode: lift the binary entry point and
/// return an error on the first selected function that cannot be lifted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryLiftOptions {
    /// Function selection policy.
    pub functions: BinaryFunctionSelection,
    /// When true, fail the whole request on the first per-function lift error.
    pub strict: bool,
}

impl Default for BinaryLiftOptions {
    fn default() -> Self {
        Self { functions: BinaryFunctionSelection::Entry, strict: true }
    }
}

impl BinaryLiftOptions {
    /// Select all detected function symbols.
    #[must_use]
    pub fn all_functions() -> Self {
        Self { functions: BinaryFunctionSelection::All, ..Self::default() }
    }

    /// Select functions by virtual address.
    pub fn functions_by_address<I>(addresses: I) -> Self
    where
        I: IntoIterator<Item = u64>,
    {
        Self {
            functions: BinaryFunctionSelection::Addresses(addresses.into_iter().collect()),
            ..Self::default()
        }
    }

    /// Select functions by normalized symbol name.
    pub fn functions_by_name<I, S>(names: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self {
            functions: BinaryFunctionSelection::Names(names.into_iter().map(Into::into).collect()),
            ..Self::default()
        }
    }

    /// Allow partial results and collect per-function failures.
    #[must_use]
    pub fn best_effort(mut self) -> Self {
        self.strict = false;
        self
    }
}

/// Per-function failure recorded when [`BinaryLiftOptions::strict`] is false.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiftedFunctionFailure {
    /// Normalized symbol name, when available.
    pub name: Option<String>,
    /// Requested virtual address.
    pub entry_point: u64,
    /// Display form of the lift error.
    pub error: String,
}

/// Lifted tMIR functions plus binary metadata.
#[derive(Debug, Clone)]
pub struct LiftedBinary {
    /// Detected binary format.
    pub format: &'static str,
    /// Detected target architecture.
    pub architecture: &'static str,
    /// Parsed binary entry point, when present.
    pub entry_point: Option<u64>,
    /// Successfully lifted functions.
    pub functions: Vec<LiftedFunction>,
    /// Best-effort per-function failures.
    pub failures: Vec<LiftedFunctionFailure>,
}

/// Lift a binary image directly into tMIR functions.
///
/// Uses `trust_binary_parse::parse_binary` for format/architecture metadata
/// when the `elf` or `macho` feature is enabled. ELF and Mach-O dispatch
/// through the existing [`Lifter::from_elf`] and [`Lifter::from_macho`]
/// constructors. PE/COFF is detected and rejected with a clear unsupported
/// error until PE lifting is implemented.
///
/// # Errors
///
/// Returns [`LiftError`] if binary parser support is unavailable, parsing
/// fails, the format is unsupported, selection finds no function, or lifting a
/// selected function fails in strict proof mode.
#[cfg(not(any(feature = "macho", feature = "elf")))]
pub fn lift_binary_to_tmir(
    _bytes: &[u8],
    _options: BinaryLiftOptions,
) -> Result<LiftedBinary, LiftError> {
    Err(LiftError::BinaryParserUnavailable)
}

/// Lift a binary image directly into tMIR functions.
///
/// See the non-feature-gated item documentation for details.
#[cfg(any(feature = "macho", feature = "elf"))]
pub fn lift_binary_to_tmir(
    bytes: &[u8],
    options: BinaryLiftOptions,
) -> Result<LiftedBinary, LiftError> {
    use trust_binary_parse::{BinaryFormat, detect_format, parse_binary};

    if matches!(detect_format(bytes), Some(BinaryFormat::Pe)) {
        return Err(pe_unsupported());
    }

    let info = parse_binary(bytes)?;
    match info.format {
        BinaryFormat::Elf => lift_elf(bytes, &info, options),
        BinaryFormat::MachO | BinaryFormat::FatMachO => lift_macho(bytes, &info, options),
        BinaryFormat::Pe => Err(pe_unsupported()),
        _ => Err(LiftError::UnsupportedBinaryFormat {
            format: "unknown",
            reason: "binary format is not implemented by trust-lift",
        }),
    }
}

#[cfg(feature = "elf")]
fn lift_elf(
    bytes: &[u8],
    info: &trust_binary_parse::BinaryInfo,
    options: BinaryLiftOptions,
) -> Result<LiftedBinary, LiftError> {
    let elf = trust_binary_parse::Elf64::parse(bytes)?;
    let lifter = Lifter::from_elf(&elf)?;
    lift_with_lifter(bytes, &lifter, info, options)
}

#[cfg(all(not(feature = "elf"), feature = "macho"))]
fn lift_elf(
    _bytes: &[u8],
    info: &trust_binary_parse::BinaryInfo,
    _options: BinaryLiftOptions,
) -> Result<LiftedBinary, LiftError> {
    Err(LiftError::UnsupportedBinaryFormat {
        format: info.format.name(),
        reason: "trust-lift was built without the `elf` feature",
    })
}

#[cfg(feature = "macho")]
fn lift_macho(
    bytes: &[u8],
    info: &trust_binary_parse::BinaryInfo,
    options: BinaryLiftOptions,
) -> Result<LiftedBinary, LiftError> {
    let macho = trust_binary_parse::MachO::parse_prefer_aarch64(bytes)?;
    let lifter = Lifter::from_macho(&macho)?;
    lift_with_lifter(macho.data(), &lifter, info, options)
}

#[cfg(all(not(feature = "macho"), feature = "elf"))]
fn lift_macho(
    _bytes: &[u8],
    info: &trust_binary_parse::BinaryInfo,
    _options: BinaryLiftOptions,
) -> Result<LiftedBinary, LiftError> {
    Err(LiftError::UnsupportedBinaryFormat {
        format: info.format.name(),
        reason: "trust-lift was built without the `macho` feature",
    })
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn lift_with_lifter(
    bytes: &[u8],
    lifter: &Lifter,
    info: &trust_binary_parse::BinaryInfo,
    options: BinaryLiftOptions,
) -> Result<LiftedBinary, LiftError> {
    let targets = select_targets(lifter, info, &options.functions)?;
    let mut functions = Vec::new();
    let mut failures = Vec::new();

    for target in targets {
        match lifter.lift_function(bytes, target.entry_point) {
            Ok(function) => functions.push(function),
            Err(error) if options.strict => return Err(error),
            Err(error) => failures.push(LiftedFunctionFailure {
                name: target.name,
                entry_point: target.entry_point,
                error: error.to_string(),
            }),
        }
    }

    Ok(LiftedBinary {
        format: info.format.name(),
        architecture: info.architecture.name(),
        entry_point: info.entry_point,
        functions,
        failures,
    })
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn select_targets(
    lifter: &Lifter,
    info: &trust_binary_parse::BinaryInfo,
    selection: &BinaryFunctionSelection,
) -> Result<Vec<FunctionTarget>, LiftError> {
    let mut targets = Vec::new();

    match selection {
        BinaryFunctionSelection::Entry => {
            let entry = info.entry_point.ok_or(LiftError::NoBinaryEntryPoint)?;
            let target = boundary_for_address(lifter.functions(), entry)
                .map(target_from_boundary)
                .unwrap_or_else(|| FunctionTarget { name: None, entry_point: entry });
            push_unique(&mut targets, target);
        }
        BinaryFunctionSelection::All => {
            for boundary in lifter.functions() {
                push_unique(&mut targets, target_from_boundary(boundary));
            }
        }
        BinaryFunctionSelection::Addresses(addresses) => {
            for address in addresses {
                let target = boundary_for_address(lifter.functions(), *address)
                    .map(target_from_boundary)
                    .unwrap_or_else(|| FunctionTarget { name: None, entry_point: *address });
                push_unique(&mut targets, target);
            }
        }
        BinaryFunctionSelection::Names(names) => {
            for name in names {
                let boundary = lifter
                    .functions()
                    .iter()
                    .find(|boundary| boundary.name == *name)
                    .ok_or_else(|| LiftError::NoFunctionNamed(name.clone()))?;
                push_unique(&mut targets, target_from_boundary(boundary));
            }
        }
    }

    if targets.is_empty() {
        return Err(LiftError::NoFunctionsSelected);
    }

    Ok(targets)
}

#[cfg(any(feature = "macho", feature = "elf"))]
#[derive(Debug, Clone)]
struct FunctionTarget {
    name: Option<String>,
    entry_point: u64,
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn target_from_boundary(boundary: &FunctionBoundary) -> FunctionTarget {
    FunctionTarget { name: Some(boundary.name.clone()), entry_point: boundary.start }
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn boundary_for_address(
    boundaries: &[FunctionBoundary],
    address: u64,
) -> Option<&FunctionBoundary> {
    boundaries.iter().find(|boundary| {
        let end = boundary.start.saturating_add(boundary.size);
        address >= boundary.start && address < end
    })
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn push_unique(targets: &mut Vec<FunctionTarget>, target: FunctionTarget) {
    if !targets.iter().any(|existing| existing.entry_point == target.entry_point) {
        targets.push(target);
    }
}

#[cfg(any(feature = "macho", feature = "elf"))]
fn pe_unsupported() -> LiftError {
    LiftError::UnsupportedBinaryFormat {
        format: "PE/COFF",
        reason: "PE lifting is not implemented yet",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_options_are_entry_strict() {
        let options = BinaryLiftOptions::default();
        assert_eq!(options.functions, BinaryFunctionSelection::Entry);
        assert!(options.strict);
    }

    #[test]
    fn options_builders_set_selection() {
        assert_eq!(BinaryLiftOptions::all_functions().functions, BinaryFunctionSelection::All);
        assert_eq!(
            BinaryLiftOptions::functions_by_address([0x1000]).functions,
            BinaryFunctionSelection::Addresses(vec![0x1000])
        );
        assert_eq!(
            BinaryLiftOptions::functions_by_name(["main"]).functions,
            BinaryFunctionSelection::Names(vec!["main".to_string()])
        );
        assert!(!BinaryLiftOptions::all_functions().best_effort().strict);
    }

    #[cfg(not(any(feature = "macho", feature = "elf")))]
    #[test]
    fn no_parser_feature_returns_clear_error() {
        let error = lift_binary_to_tmir(&[], BinaryLiftOptions::default()).unwrap_err();
        assert!(matches!(error, LiftError::BinaryParserUnavailable));
    }

    #[cfg(any(feature = "macho", feature = "elf"))]
    #[test]
    fn pe_returns_clear_unsupported_error() {
        let error =
            lift_binary_to_tmir(&[b'M', b'Z', 0, 0], BinaryLiftOptions::default()).unwrap_err();
        assert!(matches!(
            error,
            LiftError::UnsupportedBinaryFormat {
                format: "PE/COFF",
                reason: "PE lifting is not implemented yet"
            }
        ));
    }
}
