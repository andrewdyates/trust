// trust-proof-cert/proof_bundle.rs: ProofBundle format with assumptions,
// environment capture, and assurance tiers.
//
// A ProofBundle packages all verification artifacts for a crate or function
// into a single, integrity-verified structure. It extends (not replaces) the
// existing ProofCertificate/CertificateChain infrastructure.
//
// Part of #830: Phase 1 of the Universal Proof Certificate Format.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{CertError, CertificateChain, ProofCertificate};

// ---------------------------------------------------------------------------
// Assurance Tiers
// ---------------------------------------------------------------------------

/// Classification of proof strength, from strongest to weakest.
///
/// Each tier represents a different level of confidence in the verification.
/// Tiers are ordered: Tier1 > Tier2 > Tier3 > Tier4.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AssuranceTier {
    /// Full formal proof verified by an independent proof kernel (lean5).
    /// The solver's proof was independently type-checked.
    Tier1Formal,
    /// SMT solver proved the property UNSAT (no counterexample exists).
    /// Sound but not independently verified.
    Tier2SmtVerified,
    /// Bounded model checking: property holds up to a finite depth.
    /// Sound within bounds, not a complete proof.
    Tier3BoundedVerified,
    /// Type-checked only: Rust's type system guarantees.
    /// No solver involvement — relies on compiler guarantees.
    Tier4TypeChecked,
}

impl AssuranceTier {
    /// Human-readable name for the tier.
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            Self::Tier1Formal => "Formal Proof (lean5-certified)",
            Self::Tier2SmtVerified => "SMT Verified (solver-proved)",
            Self::Tier3BoundedVerified => "Bounded Verification",
            Self::Tier4TypeChecked => "Type-Checked Only",
        }
    }

    /// Derive the assurance tier from a ProofCertificate.
    #[must_use]
    pub fn from_certificate(cert: &ProofCertificate) -> Self {
        use crate::CertificationStatus;
        #[allow(unreachable_patterns)] // CertificationStatus is #[non_exhaustive]
        match cert.status {
            CertificationStatus::Certified => Self::Tier1Formal,
            CertificationStatus::Trusted => {
                if cert.solver.strength.is_sound() {
                    Self::Tier2SmtVerified
                } else if cert.solver.strength.is_bounded() {
                    Self::Tier3BoundedVerified
                } else {
                    Self::Tier4TypeChecked
                }
            }
            // non_exhaustive future variants default to weakest tier
            _ => Self::Tier4TypeChecked,
        }
    }
}

impl fmt::Display for AssuranceTier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

// ---------------------------------------------------------------------------
// AssumptionSet
// ---------------------------------------------------------------------------

/// Captures all assumptions under which a proof bundle was generated.
///
/// A proof is only valid when its assumptions hold. This struct makes those
/// assumptions explicit and machine-readable.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct AssumptionSet {
    /// Trust levels assumed for external dependencies (e.g., "std::vec::Vec: Trusted").
    pub trust_levels: Vec<TrustAssumption>,
    /// Axioms assumed by the solver (e.g., integer overflow semantics).
    pub axioms: Vec<String>,
    /// Code paths that were NOT verified (e.g., unsafe blocks, FFI calls).
    pub unverified_paths: Vec<String>,
    /// Panic strategy assumed during verification (abort vs unwind).
    pub panic_strategy: PanicStrategy,
    /// Codegen options that affect verification soundness.
    pub codegen_options: Vec<CodegenOption>,
    /// Solver versions used (solver_name -> version string).
    pub solver_versions: Vec<SolverVersion>,
}

/// A trust assumption about an external dependency or function.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustAssumption {
    /// Path of the trusted item (e.g., "std::vec::Vec::push").
    pub path: String,
    /// What level of trust is assumed.
    pub level: TrustAssumptionLevel,
    /// Why this assumption is made.
    pub reason: String,
}

/// Level of trust assumed for an external item.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TrustAssumptionLevel {
    /// Fully verified by tRust (has its own ProofBundle).
    Verified,
    /// Assumed correct based on Rust's type system guarantees.
    TypeSafe,
    /// Assumed correct without verification (e.g., FFI, unsafe).
    Trusted,
    /// Known to be unverified; proof is conditional on this item's correctness.
    Conditional,
}

/// Panic strategy affects verification semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
#[non_exhaustive]
pub enum PanicStrategy {
    /// panic = "abort" — unwinding is not modeled.
    #[default]
    Abort,
    /// panic = "unwind" — unwinding paths must be verified.
    Unwind,
}

impl fmt::Display for PanicStrategy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Abort => write!(f, "abort"),
            Self::Unwind => write!(f, "unwind"),
        }
    }
}

/// A codegen option that may affect soundness.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CodegenOption {
    /// Option name (e.g., "opt-level", "overflow-checks").
    pub name: String,
    /// Option value.
    pub value: String,
}

/// Version of a solver used in verification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolverVersion {
    /// Solver name (e.g., "z4", "sunder", "lean5").
    pub name: String,
    /// Version string.
    pub version: String,
}

// ---------------------------------------------------------------------------
// EnvironmentFingerprint
// ---------------------------------------------------------------------------

/// Captures the build/verification environment at proof time.
///
/// Two proofs generated in different environments may not be equivalent even
/// if the source is identical, because codegen, optimization, and platform
/// differences can affect semantics.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct EnvironmentFingerprint {
    /// tRust compiler version.
    pub trust_version: String,
    /// Rust toolchain version (e.g., "nightly-2026-04-15").
    pub rust_toolchain: String,
    /// Target triple (e.g., "aarch64-apple-darwin").
    pub target_triple: String,
    /// Platform description (e.g., "Darwin 25.4.0").
    pub platform: String,
    /// Solver timeout in milliseconds (0 = no timeout).
    pub solver_timeout_ms: u64,
    /// Whether path remapping was applied (affects debug info, not semantics).
    pub path_remap: bool,
    /// Deterministic seed for reproducible verification.
    pub deterministic_seed: Option<u64>,
    /// Linker identifier (affects binary layout).
    pub linker_id: String,
    /// Optimization level.
    pub opt_level: String,
}

// ---------------------------------------------------------------------------
// ProvenArtifact
// ---------------------------------------------------------------------------

/// A content-addressed artifact with optional inline bytes.
///
/// Artifacts are identified by their SHA-256 hash. The actual bytes may be
/// stored inline (for small artifacts) or referenced externally.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProvenArtifact {
    /// SHA-256 hash of the artifact content.
    pub artifact_hash: [u8; 32],
    /// Human-readable description of the artifact.
    pub description: String,
    /// MIME type or format identifier (e.g., "application/x-elf", "text/x-rust").
    pub format: String,
    /// Inline artifact bytes (None if stored externally).
    #[serde(default, skip_serializing_if = "Option::is_none", with = "optional_bytes_as_base64")]
    pub inline_bytes: Option<Vec<u8>>,
    /// Size of the artifact in bytes.
    pub size_bytes: u64,
}

impl ProvenArtifact {
    /// Create a new artifact from raw bytes.
    #[must_use]
    pub fn from_bytes(bytes: &[u8], description: &str, format: &str) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(bytes);
        let hash: [u8; 32] = hasher.finalize().into();
        Self {
            artifact_hash: hash,
            description: description.to_string(),
            format: format.to_string(),
            inline_bytes: Some(bytes.to_vec()),
            size_bytes: bytes.len() as u64,
        }
    }

    /// Create an artifact reference without inline bytes.
    #[must_use]
    pub fn reference_only(hash: [u8; 32], size: u64, description: &str, format: &str) -> Self {
        Self {
            artifact_hash: hash,
            description: description.to_string(),
            format: format.to_string(),
            inline_bytes: None,
            size_bytes: size,
        }
    }

    /// Verify that inline bytes match the artifact hash.
    pub fn verify_integrity(&self) -> Result<bool, CertError> {
        match &self.inline_bytes {
            Some(bytes) => {
                let mut hasher = Sha256::new();
                hasher.update(bytes);
                let computed: [u8; 32] = hasher.finalize().into();
                Ok(computed == self.artifact_hash)
            }
            None => Ok(true), // external artifacts can't be verified inline
        }
    }
}

// ---------------------------------------------------------------------------
// DependencyRef
// ---------------------------------------------------------------------------

/// Reference to another proof bundle (cross-crate composition).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DependencyRef {
    /// Crate name of the dependency.
    pub crate_name: String,
    /// Crate version.
    pub crate_version: String,
    /// SHA-256 hash of the dependency's proof bundle.
    pub bundle_hash: [u8; 32],
    /// Assurance tier of the dependency's proof.
    pub tier: AssuranceTier,
    /// Functions from the dependency that this bundle relies on.
    pub relied_functions: Vec<String>,
}

// ---------------------------------------------------------------------------
// Certificate wrappers
// ---------------------------------------------------------------------------

/// Wraps an existing ProofCertificate for MIR-level verification.
///
/// This provides backward compatibility with the existing certificate format
/// while fitting into the new ProofBundle structure.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionCertificate {
    /// The existing MIR-level proof certificate.
    pub mir_cert: ProofCertificate,
    /// The certificate chain for this function.
    pub chain: CertificateChain,
    /// Assurance tier derived from the certificate.
    pub tier: AssuranceTier,
    /// Function def_path.
    pub function_path: String,
}

impl FunctionCertificate {
    /// Create from an existing ProofCertificate and chain.
    #[must_use]
    pub fn from_existing(cert: ProofCertificate, chain: CertificateChain) -> Self {
        let tier = AssuranceTier::from_certificate(&cert);
        let function_path = cert.function.clone();
        Self { mir_cert: cert, chain, tier, function_path }
    }
}

/// Certificate for translation validation (MIR -> LLVM IR).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransvalCertificate {
    /// Hash of the MIR input.
    pub mir_hash: [u8; 32],
    /// Hash of the LLVM IR output.
    pub llvm_hash: [u8; 32],
    /// Solver that verified the translation.
    pub solver: String,
    /// Time spent verifying in milliseconds.
    pub time_ms: u64,
    /// Timestamp of verification.
    pub timestamp: String,
}

/// Certificate for codegen verification (LLVM IR -> machine code).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CodegenCertificate {
    /// Hash of the LLVM IR input.
    pub llvm_hash: [u8; 32],
    /// Hash of the machine code output.
    pub machine_hash: [u8; 32],
    /// Verification method used.
    pub method: String,
    /// Time spent verifying in milliseconds.
    pub time_ms: u64,
    /// Timestamp of verification.
    pub timestamp: String,
}

/// Self-certification level for the tRust compiler itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SelfCertLevel {
    /// The compiler's verification pass is verified by an external tool.
    ExternallyVerified,
    /// The compiler verified itself (bootstrapped trust).
    SelfVerified,
    /// No self-certification performed.
    None,
}

/// Self-certification certificate for the compiler.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SelfCertificate {
    /// Self-certification level.
    pub level: SelfCertLevel,
    /// Hash of the compiler binary that performed verification.
    pub compiler_hash: [u8; 32],
    /// Description of the self-certification process.
    pub description: String,
    /// Timestamp.
    pub timestamp: String,
}

// ---------------------------------------------------------------------------
// CoverageReport
// ---------------------------------------------------------------------------

/// Tracks what was and was not verified within a crate.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct CoverageReport {
    /// Total number of functions in the crate.
    pub total_functions: usize,
    /// Number of functions with proofs.
    pub verified_functions: usize,
    /// Functions that were verified, by def_path.
    pub verified: Vec<String>,
    /// Functions that were NOT verified, with reasons.
    pub unverified: Vec<UnverifiedItem>,
    /// Total number of VCs generated.
    pub total_vcs: usize,
    /// Number of VCs proved.
    pub proved_vcs: usize,
}

impl CoverageReport {
    /// Coverage percentage (0.0 to 100.0).
    #[must_use]
    pub fn coverage_percent(&self) -> f64 {
        if self.total_functions == 0 {
            0.0
        } else {
            (self.verified_functions as f64 / self.total_functions as f64) * 100.0
        }
    }

    /// VC proof coverage percentage (0.0 to 100.0).
    #[must_use]
    pub fn vc_coverage_percent(&self) -> f64 {
        if self.total_vcs == 0 {
            0.0
        } else {
            (self.proved_vcs as f64 / self.total_vcs as f64) * 100.0
        }
    }
}

/// A function that was not verified, with a reason.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnverifiedItem {
    /// Function def_path.
    pub path: String,
    /// Why the function was not verified.
    pub reason: UnverifiedReason,
}

/// Reason a function was not verified.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum UnverifiedReason {
    /// Contains unsafe code.
    UnsafeCode,
    /// Contains FFI calls.
    FfiCall,
    /// Solver timed out.
    Timeout,
    /// Solver returned unknown.
    Unknown,
    /// No specification provided.
    NoSpec,
    /// Excluded by configuration.
    Excluded,
    /// Other reason with description.
    Other(String),
}

// ---------------------------------------------------------------------------
// ProofBundle
// ---------------------------------------------------------------------------

/// Current proof bundle format version.
pub const PROOF_BUNDLE_VERSION: u32 = 1;

/// A complete proof bundle packaging all verification artifacts.
///
/// This is the top-level structure for tRust's Universal Proof Certificate Format.
/// It contains function certificates, environment fingerprint, assumptions,
/// coverage data, and integrity metadata.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofBundle {
    /// Format version.
    pub version: u32,
    /// Crate name.
    pub crate_name: String,
    /// Crate version.
    pub crate_version: String,
    /// When this bundle was created (ISO 8601).
    pub created_at: String,
    /// Overall assurance tier (minimum across all certificates).
    pub assurance_tier: AssuranceTier,
    /// Function-level certificates.
    pub function_certs: Vec<FunctionCertificate>,
    /// Translation validation certificates (MIR -> LLVM).
    pub transval_certs: Vec<TransvalCertificate>,
    /// Codegen certificates (LLVM -> machine code).
    pub codegen_certs: Vec<CodegenCertificate>,
    /// Self-certification of the compiler, if available.
    pub self_cert: Option<SelfCertificate>,
    /// Assumptions under which verification was performed.
    pub assumptions: AssumptionSet,
    /// Environment fingerprint at verification time.
    pub environment: EnvironmentFingerprint,
    /// Dependencies with their proof status.
    pub dependencies: Vec<DependencyRef>,
    /// Coverage report.
    pub coverage: CoverageReport,
    /// Proven artifacts (e.g., the compiled binary).
    pub artifacts: Vec<ProvenArtifact>,
    /// SHA-256 hash of the canonical bundle content (integrity check).
    pub bundle_hash: [u8; 32],
}

impl ProofBundle {
    /// Create a new proof bundle builder.
    #[must_use = "builder must be consumed via .build() to produce a ProofBundle"]
    pub fn builder(crate_name: &str, crate_version: &str) -> ProofBundleBuilder {
        ProofBundleBuilder {
            crate_name: crate_name.to_string(),
            crate_version: crate_version.to_string(),
            function_certs: Vec::new(),
            transval_certs: Vec::new(),
            codegen_certs: Vec::new(),
            self_cert: None,
            assumptions: AssumptionSet::default(),
            environment: EnvironmentFingerprint::default(),
            dependencies: Vec::new(),
            coverage: CoverageReport::default(),
            artifacts: Vec::new(),
            timestamp: current_timestamp(),
        }
    }

    /// Create a bundle from existing ProofCertificates (backward compatibility).
    ///
    /// Wraps each `(ProofCertificate, CertificateChain)` pair in a
    /// `FunctionCertificate` and computes the overall assurance tier.
    #[must_use]
    pub fn from_existing_certs(
        crate_name: &str,
        crate_version: &str,
        certs: Vec<(ProofCertificate, CertificateChain)>,
    ) -> Self {
        let function_certs: Vec<FunctionCertificate> = certs
            .into_iter()
            .map(|(cert, chain)| FunctionCertificate::from_existing(cert, chain))
            .collect();

        let assurance_tier = compute_min_tier(&function_certs);
        let verified: Vec<String> =
            function_certs.iter().map(|fc| fc.function_path.clone()).collect();

        let coverage = CoverageReport {
            total_functions: function_certs.len(),
            verified_functions: function_certs.len(),
            verified,
            unverified: Vec::new(),
            total_vcs: function_certs.len(),
            proved_vcs: function_certs.len(),
        };

        let timestamp = current_timestamp();

        let mut bundle = Self {
            version: PROOF_BUNDLE_VERSION,
            crate_name: crate_name.to_string(),
            crate_version: crate_version.to_string(),
            created_at: timestamp,
            assurance_tier,
            function_certs,
            transval_certs: Vec::new(),
            codegen_certs: Vec::new(),
            self_cert: None,
            assumptions: AssumptionSet::default(),
            environment: EnvironmentFingerprint::default(),
            dependencies: Vec::new(),
            coverage,
            artifacts: Vec::new(),
            bundle_hash: [0u8; 32], // computed below
        };

        // Safe to use expect here: only fails on serialization of the bundle's own fields,
        // which are all known-good constructed above.
        bundle.bundle_hash =
            bundle.compute_hash().expect("invariant: bundle fields are serializable");
        bundle
    }

    /// Verify bundle integrity by recomputing the hash.
    pub fn verify_integrity(&self) -> Result<bool, CertError> {
        let computed = self.compute_hash()?;
        Ok(computed == self.bundle_hash)
    }

    /// Verify all artifacts within the bundle.
    pub fn verify_artifacts(&self) -> Result<Vec<bool>, CertError> {
        self.artifacts.iter().map(|a| a.verify_integrity()).collect()
    }

    /// Compute the SHA-256 hash of the canonical bundle content.
    ///
    /// The hash covers everything except the `bundle_hash` field itself.
    fn compute_hash(&self) -> Result<[u8; 32], CertError> {
        let mut hasher = Sha256::new();

        // Version and identity
        hasher.update(self.version.to_le_bytes());
        hasher.update(self.crate_name.as_bytes());
        hasher.update(b"|");
        hasher.update(self.crate_version.as_bytes());
        hasher.update(b"|");
        hasher.update(self.created_at.as_bytes());
        hasher.update(b"|");
        hasher.update(format!("{:?}", self.assurance_tier).as_bytes());
        hasher.update(b"|");

        // Function certificates (serialized)
        let fc_json = serde_json::to_string(&self.function_certs)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        hasher.update(fc_json.as_bytes());
        hasher.update(b"|");

        // Transval certificates
        let tv_json = serde_json::to_string(&self.transval_certs)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        hasher.update(tv_json.as_bytes());
        hasher.update(b"|");

        // Codegen certificates
        let cg_json = serde_json::to_string(&self.codegen_certs)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        hasher.update(cg_json.as_bytes());
        hasher.update(b"|");

        // Self cert
        let sc_json = serde_json::to_string(&self.self_cert)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        hasher.update(sc_json.as_bytes());
        hasher.update(b"|");

        // Assumptions
        let as_json = serde_json::to_string(&self.assumptions)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        hasher.update(as_json.as_bytes());
        hasher.update(b"|");

        // Environment
        let env_json = serde_json::to_string(&self.environment)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        hasher.update(env_json.as_bytes());
        hasher.update(b"|");

        // Dependencies
        let dep_json = serde_json::to_string(&self.dependencies)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        hasher.update(dep_json.as_bytes());
        hasher.update(b"|");

        // Coverage
        let cov_json = serde_json::to_string(&self.coverage)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        hasher.update(cov_json.as_bytes());
        hasher.update(b"|");

        // Artifacts (hashes only, not inline bytes)
        for artifact in &self.artifacts {
            hasher.update(artifact.artifact_hash);
            hasher.update(artifact.size_bytes.to_le_bytes());
        }

        Ok(hasher.finalize().into())
    }

    /// Serialize to JSON.
    pub fn to_json(&self) -> Result<String, CertError> {
        serde_json::to_string_pretty(self)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })
    }

    /// Deserialize from JSON.
    pub fn from_json(json: &str) -> Result<Self, CertError> {
        serde_json::from_str(json)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })
    }
}

impl fmt::Display for ProofBundle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "ProofBundle: {} v{}", self.crate_name, self.crate_version)?;
        writeln!(f, "  Created: {}", self.created_at)?;
        writeln!(f, "  Assurance: {}", self.assurance_tier)?;
        writeln!(
            f,
            "  Functions: {}/{} verified ({:.1}%)",
            self.coverage.verified_functions,
            self.coverage.total_functions,
            self.coverage.coverage_percent()
        )?;
        writeln!(
            f,
            "  VCs: {}/{} proved ({:.1}%)",
            self.coverage.proved_vcs,
            self.coverage.total_vcs,
            self.coverage.vc_coverage_percent()
        )?;
        writeln!(f, "  Dependencies: {}", self.dependencies.len())?;
        writeln!(f, "  Artifacts: {}", self.artifacts.len())?;

        if !self.assumptions.axioms.is_empty() {
            writeln!(f, "  Axioms: {}", self.assumptions.axioms.len())?;
        }
        if !self.assumptions.unverified_paths.is_empty() {
            writeln!(f, "  Unverified paths: {}", self.assumptions.unverified_paths.len())?;
        }

        writeln!(f, "  Environment:")?;
        if !self.environment.trust_version.is_empty() {
            writeln!(f, "    tRust: {}", self.environment.trust_version)?;
        }
        if !self.environment.rust_toolchain.is_empty() {
            writeln!(f, "    Toolchain: {}", self.environment.rust_toolchain)?;
        }
        if !self.environment.target_triple.is_empty() {
            writeln!(f, "    Target: {}", self.environment.target_triple)?;
        }

        let hash_hex: String = self.bundle_hash.iter().map(|b| format!("{b:02x}")).collect();
        writeln!(f, "  Hash: {}", &hash_hex[..16])?;
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Builder
// ---------------------------------------------------------------------------

/// Builder for constructing a ProofBundle incrementally.
#[must_use]
pub struct ProofBundleBuilder {
    crate_name: String,
    crate_version: String,
    function_certs: Vec<FunctionCertificate>,
    transval_certs: Vec<TransvalCertificate>,
    codegen_certs: Vec<CodegenCertificate>,
    self_cert: Option<SelfCertificate>,
    assumptions: AssumptionSet,
    environment: EnvironmentFingerprint,
    dependencies: Vec<DependencyRef>,
    coverage: CoverageReport,
    artifacts: Vec<ProvenArtifact>,
    timestamp: String,
}

impl ProofBundleBuilder {
    /// Add a function certificate.
    pub fn add_function_cert(&mut self, cert: FunctionCertificate) -> &mut Self {
        self.function_certs.push(cert);
        self
    }

    /// Add an existing ProofCertificate with its chain.
    pub fn add_existing_cert(
        &mut self,
        cert: ProofCertificate,
        chain: CertificateChain,
    ) -> &mut Self {
        self.function_certs.push(FunctionCertificate::from_existing(cert, chain));
        self
    }

    /// Add a translation validation certificate.
    pub fn add_transval_cert(&mut self, cert: TransvalCertificate) -> &mut Self {
        self.transval_certs.push(cert);
        self
    }

    /// Add a codegen certificate.
    pub fn add_codegen_cert(&mut self, cert: CodegenCertificate) -> &mut Self {
        self.codegen_certs.push(cert);
        self
    }

    /// Set the self-certification certificate.
    pub fn set_self_cert(&mut self, cert: SelfCertificate) -> &mut Self {
        self.self_cert = Some(cert);
        self
    }

    /// Set the assumptions.
    pub fn set_assumptions(&mut self, assumptions: AssumptionSet) -> &mut Self {
        self.assumptions = assumptions;
        self
    }

    /// Set the environment fingerprint.
    pub fn set_environment(&mut self, env: EnvironmentFingerprint) -> &mut Self {
        self.environment = env;
        self
    }

    /// Add a dependency reference.
    pub fn add_dependency(&mut self, dep: DependencyRef) -> &mut Self {
        self.dependencies.push(dep);
        self
    }

    /// Set the coverage report.
    pub fn set_coverage(&mut self, coverage: CoverageReport) -> &mut Self {
        self.coverage = coverage;
        self
    }

    /// Add a proven artifact.
    pub fn add_artifact(&mut self, artifact: ProvenArtifact) -> &mut Self {
        self.artifacts.push(artifact);
        self
    }

    /// Set the timestamp.
    pub fn set_timestamp(&mut self, timestamp: &str) -> &mut Self {
        self.timestamp = timestamp.to_string();
        self
    }

    /// Build the ProofBundle, computing the integrity hash.
    pub fn build(self) -> Result<ProofBundle, CertError> {
        let assurance_tier = compute_min_tier(&self.function_certs);

        let mut bundle = ProofBundle {
            version: PROOF_BUNDLE_VERSION,
            crate_name: self.crate_name,
            crate_version: self.crate_version,
            created_at: self.timestamp,
            assurance_tier,
            function_certs: self.function_certs,
            transval_certs: self.transval_certs,
            codegen_certs: self.codegen_certs,
            self_cert: self.self_cert,
            assumptions: self.assumptions,
            environment: self.environment,
            dependencies: self.dependencies,
            coverage: self.coverage,
            artifacts: self.artifacts,
            bundle_hash: [0u8; 32],
        };

        bundle.bundle_hash = bundle.compute_hash()?;
        Ok(bundle)
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Compute the minimum assurance tier across all function certificates.
/// Returns Tier4 if there are no certificates.
fn compute_min_tier(certs: &[FunctionCertificate]) -> AssuranceTier {
    certs
        .iter()
        .map(|fc| fc.tier)
        // AssuranceTier derives Ord with Tier1 < Tier4 (alphabetical),
        // but conceptually Tier4 is the weakest. Since we defined the enum
        // in strongest-first order and Ord follows variant order, max() gives
        // the weakest tier.
        .max()
        .unwrap_or(AssuranceTier::Tier4TypeChecked)
}

/// Get the current UTC timestamp.
fn current_timestamp() -> String {
    let dur =
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap_or_default();
    format!("{}Z", dur.as_secs())
}

// ---------------------------------------------------------------------------
// Serde helper for Option<Vec<u8>> as base64
// ---------------------------------------------------------------------------

mod optional_bytes_as_base64 {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub(crate) fn serialize<S>(data: &Option<Vec<u8>>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match data {
            Some(bytes) => {
                // Encode bytes as hex string for JSON compatibility without
                // adding a base64 dependency.
                let hex: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
                hex.serialize(serializer)
            }
            None => serializer.serialize_none(),
        }
    }

    pub(crate) fn deserialize<'de, D>(deserializer: D) -> Result<Option<Vec<u8>>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let opt: Option<String> = Option::deserialize(deserializer)?;
        match opt {
            Some(hex) => {
                let bytes: Result<Vec<u8>, _> = (0..hex.len())
                    .step_by(2)
                    .map(|i| {
                        u8::from_str_radix(&hex[i..i + 2], 16).map_err(serde::de::Error::custom)
                    })
                    .collect();
                Ok(Some(bytes?))
            }
            None => Ok(None),
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::ProofStrength;

    use super::*;
    use crate::{
        CertificateChain, ChainStep, ChainStepType, FunctionHash, ProofCertificate, SolverInfo,
        VcSnapshot,
    };

    fn make_cert(function: &str, certified: bool) -> ProofCertificate {
        let vc_snapshot = VcSnapshot {
            kind: "Assertion".to_string(),
            formula_json: format!("{function}-vc"),
            location: None,
        };
        let solver = SolverInfo {
            name: "z4".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        };
        let mut cert = ProofCertificate::new_trusted(
            function.to_string(),
            FunctionHash::from_bytes(format!("{function}-body").as_bytes()),
            vc_snapshot,
            solver,
            vec![1, 2, 3],
            "2026-04-15T00:00:00Z".to_string(),
        );
        if certified {
            cert.status = crate::CertificationStatus::Certified;
        }
        cert
    }

    fn make_chain() -> CertificateChain {
        let mut chain = CertificateChain::new();
        chain.push(ChainStep {
            step_type: ChainStepType::VcGeneration,
            tool: "trust-vcgen".to_string(),
            tool_version: "0.1.0".to_string(),
            input_hash: "mir".to_string(),
            output_hash: "vc".to_string(),
            time_ms: 1,
            timestamp: "2026-04-15T00:00:00Z".to_string(),
        });
        chain.push(ChainStep {
            step_type: ChainStepType::SolverProof,
            tool: "z4".to_string(),
            tool_version: "1.0.0".to_string(),
            input_hash: "vc".to_string(),
            output_hash: "proof".to_string(),
            time_ms: 10,
            timestamp: "2026-04-15T00:00:01Z".to_string(),
        });
        chain
    }

    fn make_environment() -> EnvironmentFingerprint {
        EnvironmentFingerprint {
            trust_version: "0.1.0".to_string(),
            rust_toolchain: "nightly-2026-04-15".to_string(),
            target_triple: "aarch64-apple-darwin".to_string(),
            platform: "Darwin 25.4.0".to_string(),
            solver_timeout_ms: 30000,
            path_remap: false,
            deterministic_seed: Some(42),
            linker_id: "ld-prime".to_string(),
            opt_level: "2".to_string(),
        }
    }

    fn make_assumptions() -> AssumptionSet {
        AssumptionSet {
            trust_levels: vec![TrustAssumption {
                path: "std::vec::Vec::push".to_string(),
                level: TrustAssumptionLevel::TypeSafe,
                reason: "stdlib type safety".to_string(),
            }],
            axioms: vec!["integer overflow wraps".to_string()],
            unverified_paths: vec!["crate::ffi::extern_call".to_string()],
            panic_strategy: PanicStrategy::Abort,
            codegen_options: vec![CodegenOption {
                name: "overflow-checks".to_string(),
                value: "true".to_string(),
            }],
            solver_versions: vec![SolverVersion {
                name: "z4".to_string(),
                version: "1.0.0".to_string(),
            }],
        }
    }

    // -----------------------------------------------------------------------
    // AssuranceTier
    // -----------------------------------------------------------------------

    #[test]
    fn test_assurance_tier_ordering() {
        assert!(AssuranceTier::Tier1Formal < AssuranceTier::Tier2SmtVerified);
        assert!(AssuranceTier::Tier2SmtVerified < AssuranceTier::Tier3BoundedVerified);
        assert!(AssuranceTier::Tier3BoundedVerified < AssuranceTier::Tier4TypeChecked);
    }

    #[test]
    fn test_assurance_tier_from_certified_cert() {
        let cert = make_cert("crate::foo", true);
        assert_eq!(AssuranceTier::from_certificate(&cert), AssuranceTier::Tier1Formal);
    }

    #[test]
    fn test_assurance_tier_from_smt_cert() {
        let cert = make_cert("crate::foo", false);
        assert_eq!(AssuranceTier::from_certificate(&cert), AssuranceTier::Tier2SmtVerified);
    }

    #[test]
    fn test_assurance_tier_from_bounded_cert() {
        let vc_snapshot = VcSnapshot {
            kind: "Assertion".to_string(),
            formula_json: "vc-data".to_string(),
            location: None,
        };
        let solver = SolverInfo {
            name: "zani".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 100,
            strength: ProofStrength::bounded(10),
            evidence: None,
        };
        let cert = ProofCertificate::new_trusted(
            "crate::bounded".to_string(),
            FunctionHash::from_bytes(b"bounded-body"),
            vc_snapshot,
            solver,
            vec![],
            "2026-04-15T00:00:00Z".to_string(),
        );
        assert_eq!(AssuranceTier::from_certificate(&cert), AssuranceTier::Tier3BoundedVerified);
    }

    #[test]
    fn test_assurance_tier_display() {
        assert_eq!(format!("{}", AssuranceTier::Tier1Formal), "Formal Proof (lean5-certified)");
        assert_eq!(format!("{}", AssuranceTier::Tier2SmtVerified), "SMT Verified (solver-proved)");
    }

    // -----------------------------------------------------------------------
    // ProvenArtifact
    // -----------------------------------------------------------------------

    #[test]
    fn test_artifact_from_bytes_and_verify() {
        let data = b"fn main() { println!(\"hello\"); }";
        let artifact = ProvenArtifact::from_bytes(data, "main.rs source", "text/x-rust");

        assert_eq!(artifact.size_bytes, data.len() as u64);
        assert!(artifact.inline_bytes.is_some());
        assert!(artifact.verify_integrity().expect("should verify"));
    }

    #[test]
    fn test_artifact_reference_only() {
        let hash = [0xABu8; 32];
        let artifact = ProvenArtifact::reference_only(hash, 1024, "binary", "application/x-elf");

        assert!(artifact.inline_bytes.is_none());
        assert_eq!(artifact.size_bytes, 1024);
        // External artifacts always pass integrity check
        assert!(artifact.verify_integrity().expect("should verify"));
    }

    #[test]
    fn test_artifact_tampered_fails_integrity() {
        let data = b"original content";
        let mut artifact = ProvenArtifact::from_bytes(data, "test", "text/plain");

        // Tamper with the inline bytes
        if let Some(ref mut bytes) = artifact.inline_bytes {
            bytes[0] = 0xFF;
        }

        assert!(!artifact.verify_integrity().expect("should compute"));
    }

    // -----------------------------------------------------------------------
    // ProofBundle construction and integrity
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_bundle_from_existing_certs() {
        let certs = vec![
            (make_cert("crate::foo", false), make_chain()),
            (make_cert("crate::bar", true), make_chain()),
        ];

        let bundle = ProofBundle::from_existing_certs("test-crate", "0.1.0", certs);

        assert_eq!(bundle.crate_name, "test-crate");
        assert_eq!(bundle.crate_version, "0.1.0");
        assert_eq!(bundle.function_certs.len(), 2);
        assert_eq!(bundle.version, PROOF_BUNDLE_VERSION);
        // Min tier: Tier2 (foo is SMT, bar is Formal, weakest = SMT)
        assert_eq!(bundle.assurance_tier, AssuranceTier::Tier2SmtVerified);
    }

    #[test]
    fn test_proof_bundle_integrity_valid() {
        let certs = vec![(make_cert("crate::foo", false), make_chain())];
        let bundle = ProofBundle::from_existing_certs("test", "0.1.0", certs);

        assert!(bundle.verify_integrity().expect("should verify"));
    }

    #[test]
    fn test_proof_bundle_integrity_tampered() {
        let certs = vec![(make_cert("crate::foo", false), make_chain())];
        let mut bundle = ProofBundle::from_existing_certs("test", "0.1.0", certs);

        // Tamper with the crate name
        bundle.crate_name = "evil-crate".to_string();

        assert!(!bundle.verify_integrity().expect("should compute"));
    }

    // -----------------------------------------------------------------------
    // JSON roundtrip
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_bundle_json_roundtrip() {
        let certs = vec![
            (make_cert("crate::foo", false), make_chain()),
            (make_cert("crate::bar", true), make_chain()),
        ];
        let bundle = ProofBundle::from_existing_certs("test-crate", "0.1.0", certs);

        let json = bundle.to_json().expect("should serialize");
        let restored = ProofBundle::from_json(&json).expect("should deserialize");

        assert_eq!(restored.crate_name, bundle.crate_name);
        assert_eq!(restored.function_certs.len(), bundle.function_certs.len());
        assert_eq!(restored.bundle_hash, bundle.bundle_hash);
        assert!(restored.verify_integrity().expect("should verify"));
    }

    #[test]
    fn test_proof_bundle_full_roundtrip_with_all_fields() {
        let mut builder = ProofBundle::builder("full-crate", "1.2.3");
        builder
            .add_existing_cert(make_cert("crate::alpha", true), make_chain())
            .add_existing_cert(make_cert("crate::beta", false), make_chain())
            .set_assumptions(make_assumptions())
            .set_environment(make_environment())
            .add_dependency(DependencyRef {
                crate_name: "dep-crate".to_string(),
                crate_version: "0.5.0".to_string(),
                bundle_hash: [0x42; 32],
                tier: AssuranceTier::Tier2SmtVerified,
                relied_functions: vec!["dep::util::helper".to_string()],
            })
            .set_coverage(CoverageReport {
                total_functions: 10,
                verified_functions: 8,
                verified: vec!["crate::alpha".to_string(), "crate::beta".to_string()],
                unverified: vec![UnverifiedItem {
                    path: "crate::ffi_bridge".to_string(),
                    reason: UnverifiedReason::FfiCall,
                }],
                total_vcs: 20,
                proved_vcs: 18,
            })
            .add_artifact(ProvenArtifact::from_bytes(
                b"test binary",
                "test artifact",
                "application/octet-stream",
            ))
            .set_timestamp("2026-04-15T12:00:00Z");

        let bundle = builder.build().expect("should build");

        let json = bundle.to_json().expect("should serialize");
        let restored = ProofBundle::from_json(&json).expect("should deserialize");

        // Verify all fields survive roundtrip
        assert_eq!(restored.crate_name, "full-crate");
        assert_eq!(restored.crate_version, "1.2.3");
        assert_eq!(restored.created_at, "2026-04-15T12:00:00Z");
        assert_eq!(restored.function_certs.len(), 2);
        assert_eq!(restored.dependencies.len(), 1);
        assert_eq!(restored.dependencies[0].crate_name, "dep-crate");
        assert_eq!(restored.assumptions.axioms, vec!["integer overflow wraps"]);
        assert_eq!(restored.assumptions.panic_strategy, PanicStrategy::Abort);
        assert_eq!(restored.environment.trust_version, "0.1.0");
        assert_eq!(restored.environment.solver_timeout_ms, 30000);
        assert_eq!(restored.environment.deterministic_seed, Some(42));
        assert_eq!(restored.coverage.total_functions, 10);
        assert_eq!(restored.coverage.verified_functions, 8);
        assert_eq!(restored.artifacts.len(), 1);
        assert!(restored.verify_integrity().expect("should verify"));
        assert_eq!(restored.bundle_hash, bundle.bundle_hash);
    }

    // -----------------------------------------------------------------------
    // Builder tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_builder_empty() {
        let mut builder = ProofBundle::builder("empty", "0.0.0");
        builder.set_timestamp("2026-04-15T00:00:00Z");
        let bundle = builder.build().expect("should build");

        assert_eq!(bundle.function_certs.len(), 0);
        assert_eq!(bundle.assurance_tier, AssuranceTier::Tier4TypeChecked);
        assert!(bundle.verify_integrity().expect("should verify"));
    }

    #[test]
    fn test_builder_incremental() {
        let mut builder = ProofBundle::builder("inc", "0.1.0");
        builder.add_existing_cert(make_cert("crate::a", false), make_chain());
        builder.add_existing_cert(make_cert("crate::b", false), make_chain());
        builder.set_timestamp("2026-04-15T00:00:00Z");

        let bundle = builder.build().expect("should build");

        assert_eq!(bundle.function_certs.len(), 2);
        assert_eq!(bundle.assurance_tier, AssuranceTier::Tier2SmtVerified);
    }

    // -----------------------------------------------------------------------
    // CoverageReport
    // -----------------------------------------------------------------------

    #[test]
    fn test_coverage_percent_full() {
        let cov = CoverageReport {
            total_functions: 10,
            verified_functions: 10,
            verified: Vec::new(),
            unverified: Vec::new(),
            total_vcs: 20,
            proved_vcs: 20,
        };
        assert!((cov.coverage_percent() - 100.0).abs() < f64::EPSILON);
        assert!((cov.vc_coverage_percent() - 100.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_coverage_percent_partial() {
        let cov = CoverageReport {
            total_functions: 4,
            verified_functions: 3,
            verified: Vec::new(),
            unverified: Vec::new(),
            total_vcs: 10,
            proved_vcs: 7,
        };
        assert!((cov.coverage_percent() - 75.0).abs() < f64::EPSILON);
        assert!((cov.vc_coverage_percent() - 70.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_coverage_percent_empty() {
        let cov = CoverageReport::default();
        assert!((cov.coverage_percent() - 0.0).abs() < f64::EPSILON);
        assert!((cov.vc_coverage_percent() - 0.0).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // Display
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_bundle_display() {
        let certs = vec![(make_cert("crate::foo", false), make_chain())];
        let bundle = ProofBundle::from_existing_certs("display-test", "0.1.0", certs);

        let output = format!("{bundle}");
        assert!(output.contains("display-test"));
        assert!(output.contains("v0.1.0"));
        assert!(output.contains("SMT Verified"));
        assert!(output.contains("1/1 verified"));
    }

    // -----------------------------------------------------------------------
    // FunctionCertificate backward compat
    // -----------------------------------------------------------------------

    #[test]
    fn test_function_cert_from_existing() {
        let cert = make_cert("crate::compat", false);
        let chain = make_chain();

        let fc = FunctionCertificate::from_existing(cert.clone(), chain.clone());

        assert_eq!(fc.function_path, "crate::compat");
        assert_eq!(fc.tier, AssuranceTier::Tier2SmtVerified);
        assert_eq!(fc.mir_cert, cert);
        assert_eq!(fc.chain, chain);
    }

    // -----------------------------------------------------------------------
    // AssumptionSet serde
    // -----------------------------------------------------------------------

    #[test]
    fn test_assumption_set_json_roundtrip() {
        let assumptions = make_assumptions();
        let json = serde_json::to_string_pretty(&assumptions).expect("should serialize");
        let restored: AssumptionSet = serde_json::from_str(&json).expect("should deserialize");

        assert_eq!(restored, assumptions);
    }

    // -----------------------------------------------------------------------
    // EnvironmentFingerprint serde
    // -----------------------------------------------------------------------

    #[test]
    fn test_environment_json_roundtrip() {
        let env = make_environment();
        let json = serde_json::to_string_pretty(&env).expect("should serialize");
        let restored: EnvironmentFingerprint =
            serde_json::from_str(&json).expect("should deserialize");

        assert_eq!(restored, env);
    }

    // -----------------------------------------------------------------------
    // Artifact serde
    // -----------------------------------------------------------------------

    #[test]
    fn test_artifact_json_roundtrip_with_bytes() {
        let artifact = ProvenArtifact::from_bytes(b"hello world", "test", "text/plain");
        let json = serde_json::to_string_pretty(&artifact).expect("should serialize");
        let restored: ProvenArtifact = serde_json::from_str(&json).expect("should deserialize");

        assert_eq!(restored.artifact_hash, artifact.artifact_hash);
        assert_eq!(restored.inline_bytes, artifact.inline_bytes);
        assert!(restored.verify_integrity().expect("should verify"));
    }

    #[test]
    fn test_artifact_json_roundtrip_without_bytes() {
        let artifact =
            ProvenArtifact::reference_only([0xAB; 32], 512, "binary", "application/x-elf");
        let json = serde_json::to_string_pretty(&artifact).expect("should serialize");
        let restored: ProvenArtifact = serde_json::from_str(&json).expect("should deserialize");

        assert_eq!(restored.artifact_hash, artifact.artifact_hash);
        assert!(restored.inline_bytes.is_none());
    }

    // -----------------------------------------------------------------------
    // Verify all artifacts
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_artifacts_all_valid() {
        let mut builder = ProofBundle::builder("art-test", "0.1.0");
        builder
            .add_artifact(ProvenArtifact::from_bytes(b"a", "a", "text/plain"))
            .add_artifact(ProvenArtifact::from_bytes(b"b", "b", "text/plain"))
            .set_timestamp("2026-04-15T00:00:00Z");

        let bundle = builder.build().expect("should build");
        let results = bundle.verify_artifacts().expect("should verify");

        assert_eq!(results.len(), 2);
        assert!(results.iter().all(|&v| v));
    }

    // -----------------------------------------------------------------------
    // Min tier computation
    // -----------------------------------------------------------------------

    #[test]
    fn test_min_tier_mixed() {
        let certs = vec![
            FunctionCertificate::from_existing(make_cert("a", true), make_chain()), // Tier1
            FunctionCertificate::from_existing(make_cert("b", false), make_chain()), // Tier2
        ];
        // Weakest is Tier2
        assert_eq!(compute_min_tier(&certs), AssuranceTier::Tier2SmtVerified);
    }

    #[test]
    fn test_min_tier_all_formal() {
        let certs = vec![
            FunctionCertificate::from_existing(make_cert("a", true), make_chain()),
            FunctionCertificate::from_existing(make_cert("b", true), make_chain()),
        ];
        assert_eq!(compute_min_tier(&certs), AssuranceTier::Tier1Formal);
    }

    #[test]
    fn test_min_tier_empty() {
        let certs: Vec<FunctionCertificate> = Vec::new();
        assert_eq!(compute_min_tier(&certs), AssuranceTier::Tier4TypeChecked);
    }
}
