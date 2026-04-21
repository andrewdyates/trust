// trust-driver/codegen.rs: Verified codegen backend abstraction (LLVM2 integration)
//
// Defines the CodegenBackend trait for verified compilation backends.
// The primary implementation is Llvm2Backend which wraps the external LLVM2
// tool (andrewdyates/LLVM2) for verified code generation.
//
// VISION.md M5: "LLVM2 integration begins."
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};
use trust_proof_cert::{CertificateChain, ChainStep, ChainStepType, ProofCertificate};
use trust_types::{VerifiableFunction, VerificationResult};

// tRust #815: LLVM2 integration for verified codegen.
use trust_llvm2_bridge::BridgeError;

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors from codegen backend operations.
#[derive(Debug, thiserror::Error)]
pub(crate) enum CodegenError {
    #[error("LLVM2 backend unavailable: {reason}")]
    BackendUnavailable { reason: String },

    #[error("MIR lowering failed for `{function}`: {reason}")]
    LoweringFailed { function: String, reason: String },

    #[error("AArch64 pipeline error for `{function}`: {reason}")]
    AArch64PipelineFailed { function: String, reason: String },

    #[error("object emission failed: {reason}")]
    EmissionFailed { reason: String },

    #[error("lowering verification failed for `{function}`: {reason}")]
    VerificationFailed { function: String, reason: String },

    // tRust #815: Bridge errors from trust-llvm2-bridge.
    #[error("LLVM2 bridge error: {0}")]
    BridgeFailed(#[from] BridgeError),
}

// ---------------------------------------------------------------------------
// Core trait
// ---------------------------------------------------------------------------

/// A codegen backend that can lower MIR to machine code and optionally
/// verify the correctness of each lowering transformation.
///
/// Implementations include:
/// - `Llvm2Backend`: verified codegen via the LLVM2 tool
/// - Standard LLVM: fallback (not modeled here; handled by rustc itself)
pub(crate) trait CodegenBackend {
    /// Human-readable name of this backend (e.g. "llvm2", "cranelift").
    fn name(&self) -> &str;

    /// Whether this backend is available and ready to use.
    fn is_available(&self) -> bool;

    /// Lower a single MIR function to the backend's IR.
    ///
    /// `function_name` is the fully-qualified function path.
    /// `mir_body` is an opaque MIR representation (will be refined in
    /// future milestones to use the actual rustc MIR types).
    fn lower_mir(
        &self,
        function_name: &str,
        mir_body: &MirBody,
    ) -> Result<LoweredFunction, CodegenError>;

    /// Emit an object file from previously lowered functions.
    fn emit_object(
        &self,
        lowered: &[LoweredFunction],
        output_path: &Path,
    ) -> Result<CodegenArtifact, CodegenError>;

    /// Verify that the lowering from MIR to backend IR is semantics-preserving.
    ///
    /// Returns a verification result proving (or disproving) that the lowered
    /// code faithfully implements the MIR semantics.
    fn verify_lowering(
        &self,
        function_name: &str,
        mir_body: &MirBody,
        lowered: &LoweredFunction,
    ) -> Result<VerificationResult, CodegenError>;
}

// ---------------------------------------------------------------------------
// Data types
// ---------------------------------------------------------------------------

/// Opaque MIR function body.
///
/// This is a placeholder that will be replaced with the actual rustc MIR
/// representation once native compiler integration is complete.
#[derive(Debug, Clone)]
pub(crate) struct MirBody {
    /// Fully-qualified function name.
    pub function_name: String,
    /// Number of basic blocks (for reporting).
    pub basic_block_count: usize,
    /// Serialized MIR bytes (opaque for now).
    pub data: Vec<u8>,
}

/// Result of lowering a single MIR function to backend IR.
#[derive(Debug, Clone)]
pub(crate) struct LoweredFunction {
    /// The function that was lowered.
    pub function_name: String,
    /// Backend-specific IR (opaque bytes).
    pub ir_data: Vec<u8>,
    /// Number of instructions in the lowered IR.
    pub instruction_count: usize,
}

/// Artifact produced by object emission.
#[derive(Debug, Clone)]
pub(crate) struct CodegenArtifact {
    /// Path to the emitted object file.
    pub object_path: PathBuf,
    /// Total size in bytes.
    pub size_bytes: u64,
    /// Number of functions included.
    pub function_count: usize,
}

/// Result of compiling a VerifiableFunction through the LLVM2 pipeline.
#[derive(Debug, Clone)]
pub(crate) struct CompiledFunction {
    /// Function name.
    pub function_name: String,
    /// Raw machine code or object file bytes.
    pub machine_code: Vec<u8>,
    /// Target architecture (e.g. "x86_64", "aarch64").
    pub target: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TargetArch {
    AArch64,
    X86_64,
}

impl TargetArch {
    /// Auto-detect from compile-time target.
    #[must_use]
    pub(crate) fn host() -> Self {
        if cfg!(target_arch = "aarch64") { Self::AArch64 } else { Self::X86_64 }
    }

    #[must_use]
    fn as_str(self) -> &'static str {
        match self {
            Self::AArch64 => "aarch64",
            Self::X86_64 => "x86_64",
        }
    }
}

/// Combines a codegen artifact with its verification results.
///
/// This is the output of a fully verified compilation: the binary plus
/// proof certificates for each lowering transformation.
#[derive(Debug, Clone)]
pub(crate) struct VerifiedCodegen {
    /// The compiled artifact.
    pub artifact: CodegenArtifact,
    /// Per-function verification results for the lowering step.
    pub lowering_proofs: Vec<LoweringProof>,
    /// Whether all lowering transformations were proved correct.
    pub fully_verified: bool,
}

/// Proof that a single function's lowering is correct.
#[derive(Debug, Clone)]
pub(crate) struct LoweringProof {
    /// Function that was verified.
    pub function_name: String,
    /// Verification result from the backend.
    pub result: VerificationResult,
    /// Optional proof certificate bytes.
    pub certificate: Option<Vec<u8>>,
}

// ---------------------------------------------------------------------------
// tRust #824: Proven binary — chains MIR verification through codegen
// ---------------------------------------------------------------------------

/// A compiled binary with chained proof certificates from MIR verification
/// through codegen to the final machine code.
///
/// This is the key type for self-hosting (#824): it proves that the machine
/// code bytes faithfully implement the verified MIR, by chaining:
/// 1. MIR verification proof (from trust-proof-cert / trust-router)
/// 2. Codegen lowering proof (translation validation from LLVM2)
/// 3. A combined certificate hash binding both proofs to the binary
#[derive(Debug, Clone)]
pub(crate) struct ProvenBinary {
    /// Function name.
    pub function_name: String,
    /// Raw machine code bytes.
    pub machine_code: Vec<u8>,
    /// Target architecture (e.g. "x86_64", "aarch64").
    pub target: String,
    /// MIR verification proof certificate (from the verification pipeline).
    pub mir_proof: Option<ProofCertificate>,
    /// Codegen lowering proof (translation validation from LLVM2).
    pub lowering_proof: LoweringProof,
    /// Certificate chain linking MIR verification through codegen to binary.
    pub chain: CertificateChain,
    /// SHA-256 hash binding all certificates to the machine code bytes.
    /// Computed over: machine_code || mir_proof_hash || lowering_cert_hash.
    pub combined_hash: [u8; 32],
}

impl ProvenBinary {
    /// Build a `ProvenBinary` by chaining a compiled function with its
    /// MIR verification proof certificate and codegen lowering proof.
    ///
    /// The `mir_proof` is the proof certificate from the MIR verification
    /// pipeline (may be `None` if verification was skipped or failed).
    /// The `lowering_proof` comes from LLVM2 translation validation.
    #[must_use]
    pub(crate) fn new(
        compiled: CompiledFunction,
        mir_proof: Option<ProofCertificate>,
        lowering_proof: LoweringProof,
    ) -> Self {
        // Build the certificate chain from available proofs.
        let mut chain = CertificateChain::new();

        // If we have a MIR proof, include its chain steps.
        if let Some(ref cert) = mir_proof {
            for step in &cert.chain.steps {
                chain.push(step.clone());
            }
        }

        // Add the codegen lowering step.
        let lowering_input_hash = Self::hash_lowering_input(&compiled.function_name, &mir_proof);
        let lowering_output_hash = Self::hash_bytes(&compiled.machine_code);
        chain.push(ChainStep {
            step_type: ChainStepType::CodegenLowering,
            tool: "llvm2".to_string(),
            tool_version: "0.1.0".to_string(),
            input_hash: lowering_input_hash,
            output_hash: lowering_output_hash,
            time_ms: 0, // not timed at this level
            timestamp: String::new(),
        });

        // Compute the combined hash binding everything together.
        let combined_hash = Self::compute_combined_hash(
            &compiled.machine_code,
            &mir_proof,
            &lowering_proof.certificate,
        );

        ProvenBinary {
            function_name: compiled.function_name,
            machine_code: compiled.machine_code,
            target: compiled.target,
            mir_proof,
            lowering_proof,
            chain,
            combined_hash,
        }
    }

    /// Whether both the MIR verification and codegen lowering are proved.
    #[must_use]
    pub(crate) fn is_fully_proved(&self) -> bool {
        let mir_proved = self.mir_proof.is_some();
        let lowering_proved = self.lowering_proof.result.is_proved();
        mir_proved && lowering_proved
    }

    /// Verify the chain integrity (hash linkage between steps).
    pub(crate) fn verify_chain(&self) -> Result<(), trust_proof_cert::CertError> {
        if self.chain.is_empty() {
            return Ok(()); // No chain to verify (no MIR proof, no lowering)
        }
        self.chain.verify_integrity()
    }

    /// Recompute the combined hash and check it matches the stored value.
    #[must_use]
    pub(crate) fn verify_combined_hash(&self) -> bool {
        let recomputed = Self::compute_combined_hash(
            &self.machine_code,
            &self.mir_proof,
            &self.lowering_proof.certificate,
        );
        recomputed == self.combined_hash
    }

    /// SHA-256 of arbitrary bytes, returned as hex string for chain hashes.
    fn hash_bytes(data: &[u8]) -> String {
        let hash = Sha256::digest(data);
        format!("{hash:x}")
    }

    /// Hash the lowering input: function name + MIR proof certificate ID (if present).
    fn hash_lowering_input(function_name: &str, mir_proof: &Option<ProofCertificate>) -> String {
        let mut hasher = Sha256::new();
        hasher.update(function_name.as_bytes());
        if let Some(ref cert) = mir_proof {
            hasher.update(b":");
            hasher.update(cert.id.0.as_bytes());
        }
        let hash = hasher.finalize();
        format!("{hash:x}")
    }

    /// Compute the combined hash binding machine code, MIR proof, and lowering cert.
    fn compute_combined_hash(
        machine_code: &[u8],
        mir_proof: &Option<ProofCertificate>,
        lowering_cert: &Option<Vec<u8>>,
    ) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(machine_code);
        if let Some(ref cert) = mir_proof {
            hasher.update(cert.id.0.as_bytes());
            hasher.update(cert.vc_hash);
        }
        if let Some(ref cert_bytes) = lowering_cert {
            hasher.update(cert_bytes);
        }
        hasher.finalize().into()
    }
}

// ---------------------------------------------------------------------------
// LLVM2 backend (stub)
// ---------------------------------------------------------------------------

/// Verified codegen backend wrapping the LLVM2 tool.
///
/// LLVM2 (`andrewdyates/LLVM2`) takes tMIR and produces machine
/// code with z4-proved correctness of each transformation. This struct
/// provides the integration point.
///
/// The `compile_verified` method provides the real end-to-end path:
/// VerifiableFunction → trust-llvm2-bridge → LIR → target pipeline.
#[derive(Debug, Clone)]
pub(crate) struct Llvm2Backend {
    /// Path to the LLVM2 tool binary (if using CLI mode).
    #[allow(dead_code)] // Reserved for future CLI invocation mode (LLVM2 crate integration).
    tool_path: Option<PathBuf>,
    /// Whether the backend has been verified as available.
    available: bool,
    /// Target architecture for verified code generation.
    target: TargetArch,
}

impl Llvm2Backend {
    /// Create a new LLVM2 backend.
    ///
    /// If `tool_path` is provided, the backend will attempt to use the
    /// LLVM2 CLI tool at that path. Otherwise, it uses the library API
    /// (when the llvm2 crate dependency is available).
    ///
    /// When `target` is `None`, the backend uses the compile-time host target.
    #[must_use]
    pub(crate) fn new(tool_path: Option<PathBuf>, target: Option<TargetArch>) -> Self {
        Self {
            tool_path,
            // tRust #815: LLVM2 crate is now wired as a dependency.
            available: true,
            target: target.unwrap_or_else(TargetArch::host),
        }
    }

    /// Create a stub backend for testing.
    ///
    /// The stub reports as available and returns placeholder results.
    #[must_use]
    pub(crate) fn stub() -> Self {
        Self { tool_path: None, available: true, target: TargetArch::host() }
    }
}

impl Default for Llvm2Backend {
    fn default() -> Self {
        Self::new(None, None)
    }
}

impl Llvm2Backend {
    /// Compile via the x86-64 pipeline.
    fn compile_verified_x86_64(
        &self,
        func: &VerifiableFunction,
        lir_func: &llvm2_lower::Function,
    ) -> Result<CompiledFunction, CodegenError> {
        let pipeline = llvm2_codegen::x86_64::pipeline::X86Pipeline::default_config();
        let machine_code = pipeline.compile_tmir_function(lir_func).map_err(|e| {
            CodegenError::LoweringFailed { function: func.name.clone(), reason: e.to_string() }
        })?;

        Ok(CompiledFunction {
            function_name: func.name.clone(),
            machine_code,
            target: TargetArch::X86_64.as_str().to_string(),
        })
    }

    /// Compile via AArch64 pipeline (Mach-O output).
    fn compile_verified_aarch64(
        &self,
        func: &VerifiableFunction,
        lir_func: &llvm2_lower::Function,
    ) -> Result<CompiledFunction, CodegenError> {
        let pipeline = llvm2_codegen::Pipeline::default_o2();
        let machine_code = pipeline.compile_function(lir_func).map_err(|e| {
            CodegenError::AArch64PipelineFailed {
                function: func.name.clone(),
                reason: e.to_string(),
            }
        })?;

        Ok(CompiledFunction {
            function_name: func.name.clone(),
            machine_code,
            target: TargetArch::AArch64.as_str().to_string(),
        })
    }

    /// Compile a VerifiableFunction through the full LLVM2 pipeline.
    ///
    /// Pipeline: VerifiableFunction → trust-llvm2-bridge → LIR → target pipeline.
    pub(crate) fn compile_verified(
        &self,
        func: &VerifiableFunction,
    ) -> Result<CompiledFunction, CodegenError> {
        if !self.available {
            return Err(CodegenError::BackendUnavailable {
                reason: "LLVM2 backend not available".to_string(),
            });
        }

        // Phase 1: Bridge trust-types → LLVM2 LIR
        let lir_func = trust_llvm2_bridge::lower_to_lir(func)?;

        match self.target {
            TargetArch::AArch64 => self.compile_verified_aarch64(func, &lir_func),
            TargetArch::X86_64 => self.compile_verified_x86_64(func, &lir_func),
        }
    }

    /// Compile a VerifiableFunction and wrap the result in a Mach-O object.
    pub(crate) fn compile_to_macho(
        &self,
        func: &VerifiableFunction,
    ) -> Result<CompiledFunction, CodegenError> {
        if !self.available {
            return Err(CodegenError::BackendUnavailable {
                reason: "LLVM2 backend not available".to_string(),
            });
        }

        if self.target != TargetArch::AArch64 {
            return Err(CodegenError::EmissionFailed {
                reason: format!(
                    "Mach-O emission is only supported for aarch64 targets (current target: {})",
                    self.target.as_str()
                ),
            });
        }

        let lir_func = trust_llvm2_bridge::lower_to_lir(func)?;
        let pipeline = llvm2_codegen::Pipeline::new(llvm2_codegen::PipelineConfig::default());
        let machine_code = pipeline.compile_function(&lir_func).map_err(|e| {
            CodegenError::AArch64PipelineFailed {
                function: func.name.clone(),
                reason: e.to_string(),
            }
        })?;

        Ok(CompiledFunction {
            function_name: func.name.clone(),
            machine_code,
            target: TargetArch::AArch64.as_str().to_string(),
        })
    }

    /// Compile a VerifiableFunction and wrap the result in an ELF object.
    pub(crate) fn compile_to_elf(
        &self,
        func: &VerifiableFunction,
    ) -> Result<CompiledFunction, CodegenError> {
        if !self.available {
            return Err(CodegenError::BackendUnavailable {
                reason: "LLVM2 backend not available".to_string(),
            });
        }

        if self.target != TargetArch::X86_64 {
            return Err(CodegenError::EmissionFailed {
                reason: format!(
                    "ELF emission is only supported for x86_64 targets (current target: {})",
                    self.target.as_str()
                ),
            });
        }

        let lir_func = trust_llvm2_bridge::lower_to_lir(func)?;

        let pipeline = llvm2_codegen::x86_64::pipeline::X86Pipeline::new(
            llvm2_codegen::x86_64::pipeline::X86PipelineConfig { emit_elf: true, emit_frame: true },
        );
        let machine_code = pipeline.compile_tmir_function(&lir_func).map_err(|e| {
            CodegenError::LoweringFailed { function: func.name.clone(), reason: e.to_string() }
        })?;

        Ok(CompiledFunction {
            function_name: func.name.clone(),
            machine_code,
            target: TargetArch::X86_64.as_str().to_string(),
        })
    }

    // tRust #824: Produce a proven binary by compiling and chaining certificates.
    /// Compile a VerifiableFunction and produce a `ProvenBinary` that chains
    /// the MIR verification proof certificate through codegen to the binary.
    ///
    /// `mir_proof` is the proof certificate from the MIR verification pipeline
    /// (from trust-proof-cert). If `None`, the binary is compiled but only the
    /// codegen lowering proof is included.
    pub(crate) fn produce_proven_binary(
        &self,
        func: &VerifiableFunction,
        mir_proof: Option<ProofCertificate>,
    ) -> Result<ProvenBinary, CodegenError> {
        let compiled = self.compile_verified(func)?;

        // Translation validation: currently produces a placeholder lowering proof.
        // Full translation validation proofs will come from LLVM2#264.
        let lowering_proof = LoweringProof {
            function_name: compiled.function_name.clone(),
            result: VerificationResult::Unknown {
                solver: "llvm2".to_string(),
                time_ms: 0,
                reason: "LLVM2 translation validation not yet wired (LLVM2#264)".to_string(),
            },
            certificate: None,
        };

        Ok(ProvenBinary::new(compiled, mir_proof, lowering_proof))
    }
}

impl CodegenBackend for Llvm2Backend {
    fn name(&self) -> &str {
        "llvm2"
    }

    fn is_available(&self) -> bool {
        self.available
    }

    fn lower_mir(
        &self,
        function_name: &str,
        mir_body: &MirBody,
    ) -> Result<LoweredFunction, CodegenError> {
        if !self.available {
            return Err(CodegenError::BackendUnavailable {
                reason: "LLVM2 crate not yet wired as dependency".to_string(),
            });
        }

        // Opaque MirBody path: placeholder.
        // Use compile_verified() for the real VerifiableFunction → machine code path.
        Ok(LoweredFunction {
            function_name: function_name.to_string(),
            ir_data: mir_body.data.clone(),
            instruction_count: mir_body.basic_block_count * 3, // rough estimate
        })
    }

    fn emit_object(
        &self,
        lowered: &[LoweredFunction],
        output_path: &Path,
    ) -> Result<CodegenArtifact, CodegenError> {
        if !self.available {
            return Err(CodegenError::BackendUnavailable {
                reason: "LLVM2 crate not yet wired as dependency".to_string(),
            });
        }

        // Opaque MirBody path: placeholder.
        // Use compile_to_elf() for the real path.
        let total_size: u64 = lowered.iter().map(|f| f.ir_data.len() as u64).sum();

        Ok(CodegenArtifact {
            object_path: output_path.to_path_buf(),
            size_bytes: total_size,
            function_count: lowered.len(),
        })
    }

    fn verify_lowering(
        &self,
        _function_name: &str,
        _mir_body: &MirBody,
        _lowered: &LoweredFunction,
    ) -> Result<VerificationResult, CodegenError> {
        if !self.available {
            return Err(CodegenError::BackendUnavailable {
                reason: "LLVM2 crate not yet wired as dependency".to_string(),
            });
        }

        // Lowering verification via opaque MirBody is not supported.
        // Use compile_verified() which goes through the typed bridge.
        Ok(VerificationResult::Unknown {
            solver: "llvm2".to_string(),
            time_ms: 0,
            reason: "LLVM2 verification not yet implemented".to_string(),
        })
    }
}

// ---------------------------------------------------------------------------
// Orchestration: compile + verify pipeline
// ---------------------------------------------------------------------------

/// Run verified codegen for a set of MIR functions through a backend.
///
/// For each function:
/// 1. Lower MIR to backend IR
/// 2. Verify the lowering is semantics-preserving
/// 3. Emit the object file
///
/// Returns a `VerifiedCodegen` combining the artifact and proofs.
pub(crate) fn run_verified_codegen(
    backend: &dyn CodegenBackend,
    functions: &[MirBody],
    output_path: &Path,
) -> Result<VerifiedCodegen, CodegenError> {
    if !backend.is_available() {
        return Err(CodegenError::BackendUnavailable {
            reason: format!("backend '{}' is not available", backend.name()),
        });
    }

    let mut lowered_fns = Vec::with_capacity(functions.len());
    let mut proofs = Vec::with_capacity(functions.len());

    for mir in functions {
        // Step 1: Lower
        let lowered = backend.lower_mir(&mir.function_name, mir)?;

        // Step 2: Verify lowering
        let result = backend.verify_lowering(&mir.function_name, mir, &lowered)?;
        let certificate = if result.is_proved() {
            // Extract proof certificate if available
            if let VerificationResult::Proved { proof_certificate, .. } = &result {
                proof_certificate.clone()
            } else {
                None
            }
        } else {
            None
        };

        proofs.push(LoweringProof {
            function_name: mir.function_name.clone(),
            result,
            certificate,
        });

        lowered_fns.push(lowered);
    }

    // Step 3: Emit object
    let artifact = backend.emit_object(&lowered_fns, output_path)?;

    let fully_verified = proofs.iter().all(|p| p.result.is_proved());

    Ok(VerifiedCodegen { artifact, lowering_proofs: proofs, fully_verified })
}

/// Compile a set of VerifiableFunctions through the real LLVM2 pipeline.
///
/// This is the primary verified compilation entry point:
/// VerifiableFunction → trust-llvm2-bridge → LIR → target pipeline
///
/// Unlike `run_verified_codegen` (which uses the opaque MirBody trait path),
/// this function goes through the real type-aware bridge.
pub(crate) fn run_verified_compilation(
    backend: &Llvm2Backend,
    functions: &[VerifiableFunction],
) -> Result<Vec<CompiledFunction>, CodegenError> {
    if !backend.is_available() {
        return Err(CodegenError::BackendUnavailable {
            reason: "LLVM2 backend not available".to_string(),
        });
    }

    let mut results = Vec::with_capacity(functions.len());
    for func in functions {
        let compiled = backend.compile_verified(func)?;
        results.push(compiled);
    }
    Ok(results)
}
// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_mir(name: &str) -> MirBody {
        MirBody {
            function_name: name.to_string(),
            basic_block_count: 4,
            data: vec![0xDE, 0xAD, 0xBE, 0xEF],
        }
    }

    // -- CodegenBackend trait tests via Llvm2Backend::stub() --

    #[test]
    fn test_llvm2_stub_name() {
        let backend = Llvm2Backend::stub();
        assert_eq!(backend.name(), "llvm2");
    }

    #[test]
    fn test_llvm2_stub_is_available() {
        let stub = Llvm2Backend::stub();
        assert!(stub.is_available());

        // LLVM2 is now wired as a dependency, so default() is available.
        let default = Llvm2Backend::default();
        assert!(default.is_available());
        assert_eq!(default.target, TargetArch::host());
    }

    #[test]
    fn test_llvm2_stub_lower_mir() {
        let backend = Llvm2Backend::stub();
        let mir = sample_mir("test::foo");

        let lowered = backend.lower_mir("test::foo", &mir).expect("stub should succeed");
        assert_eq!(lowered.function_name, "test::foo");
        assert_eq!(lowered.ir_data, mir.data);
        assert_eq!(lowered.instruction_count, 12); // 4 blocks * 3
    }

    #[test]
    fn test_llvm2_stub_emit_object() {
        let backend = Llvm2Backend::stub();
        let mir = sample_mir("test::bar");
        let lowered = backend.lower_mir("test::bar", &mir).expect("lower should succeed");

        let artifact =
            backend.emit_object(&[lowered], Path::new("/tmp/test.o")).expect("emit should succeed");
        assert_eq!(artifact.object_path, PathBuf::from("/tmp/test.o"));
        assert_eq!(artifact.function_count, 1);
        assert_eq!(artifact.size_bytes, 4); // 4 bytes of mir data
    }

    #[test]
    fn test_llvm2_stub_verify_lowering() {
        let backend = Llvm2Backend::stub();
        let mir = sample_mir("test::baz");
        let lowered = backend.lower_mir("test::baz", &mir).expect("lower should succeed");

        let result =
            backend.verify_lowering("test::baz", &mir, &lowered).expect("verify should succeed");

        // Stub returns Unknown
        assert!(matches!(result, VerificationResult::Unknown { .. }));
    }

    #[test]
    fn test_llvm2_unavailable_returns_error() {
        // Manually construct an unavailable backend for testing.
        let backend =
            Llvm2Backend { tool_path: None, available: false, target: TargetArch::host() };
        let mir = sample_mir("test::unavail");

        let err = backend.lower_mir("test::unavail", &mir).unwrap_err();
        assert!(matches!(err, CodegenError::BackendUnavailable { .. }));

        let err = backend.emit_object(&[], Path::new("/tmp/test.o")).unwrap_err();
        assert!(matches!(err, CodegenError::BackendUnavailable { .. }));
    }

    // -- VerifiedCodegen pipeline tests --

    #[test]
    fn test_run_verified_codegen_single_function() {
        let backend = Llvm2Backend::stub();
        let functions = vec![sample_mir("test::single")];

        let result = run_verified_codegen(&backend, &functions, Path::new("/tmp/out.o"))
            .expect("pipeline should succeed");

        assert_eq!(result.artifact.function_count, 1);
        assert_eq!(result.lowering_proofs.len(), 1);
        assert_eq!(result.lowering_proofs[0].function_name, "test::single");
        // Stub returns Unknown, so not fully verified
        assert!(!result.fully_verified);
    }

    #[test]
    fn test_run_verified_codegen_multiple_functions() {
        let backend = Llvm2Backend::stub();
        let functions =
            vec![sample_mir("test::alpha"), sample_mir("test::beta"), sample_mir("test::gamma")];

        let result = run_verified_codegen(&backend, &functions, Path::new("/tmp/multi.o"))
            .expect("pipeline should succeed");

        assert_eq!(result.artifact.function_count, 3);
        assert_eq!(result.lowering_proofs.len(), 3);
        assert_eq!(result.artifact.size_bytes, 12); // 3 * 4 bytes
    }

    #[test]
    fn test_run_verified_codegen_unavailable_backend() {
        let backend =
            Llvm2Backend { tool_path: None, available: false, target: TargetArch::host() };
        let functions = vec![sample_mir("test::fail")];

        let err = run_verified_codegen(&backend, &functions, Path::new("/tmp/fail.o")).unwrap_err();
        assert!(matches!(err, CodegenError::BackendUnavailable { .. }));
    }

    #[test]
    fn test_run_verified_codegen_empty_functions() {
        let backend = Llvm2Backend::stub();

        let result = run_verified_codegen(&backend, &[], Path::new("/tmp/empty.o"))
            .expect("empty should succeed");

        assert_eq!(result.artifact.function_count, 0);
        assert!(result.lowering_proofs.is_empty());
        assert!(result.fully_verified); // vacuously true
    }

    // -- Data type tests --

    #[test]
    fn test_mir_body_construction() {
        let mir = MirBody {
            function_name: "my_crate::my_fn".to_string(),
            basic_block_count: 10,
            data: vec![1, 2, 3],
        };
        assert_eq!(mir.function_name, "my_crate::my_fn");
        assert_eq!(mir.basic_block_count, 10);
        assert_eq!(mir.data.len(), 3);
    }

    #[test]
    fn test_codegen_error_display() {
        let err = CodegenError::BackendUnavailable { reason: "not installed".to_string() };
        assert_eq!(err.to_string(), "LLVM2 backend unavailable: not installed");

        let err = CodegenError::LoweringFailed {
            function: "foo".to_string(),
            reason: "bad MIR".to_string(),
        };
        assert_eq!(err.to_string(), "MIR lowering failed for `foo`: bad MIR");

        let err = CodegenError::AArch64PipelineFailed {
            function: "bar".to_string(),
            reason: "bad Mach-O".to_string(),
        };
        assert_eq!(err.to_string(), "AArch64 pipeline error for `bar`: bad Mach-O");
    }

    #[test]
    fn test_verified_codegen_fully_verified_false_with_unknown() {
        // Manually construct a VerifiedCodegen with an Unknown result
        let vc = VerifiedCodegen {
            artifact: CodegenArtifact {
                object_path: PathBuf::from("/tmp/test.o"),
                size_bytes: 100,
                function_count: 1,
            },
            lowering_proofs: vec![LoweringProof {
                function_name: "test::fn".to_string(),
                result: VerificationResult::Unknown {
                    solver: "test".to_string(),
                    time_ms: 0,
                    reason: "stub".to_string(),
                },
                certificate: None,
            }],
            fully_verified: false,
        };
        assert!(!vc.fully_verified);
        assert!(vc.lowering_proofs[0].certificate.is_none());
    }

    // -- End-to-end LLVM2 compilation tests --

    /// Build an `add(a: i32, b: i32) -> i32` VerifiableFunction for testing.
    fn make_add_verifiable() -> VerifiableFunction {
        use trust_types::{
            BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
            Terminator, Ty, VerifiableBody,
        };

        VerifiableFunction {
            name: "add".to_string(),
            def_path: "test::add".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn is_macho_magic(bytes: &[u8]) -> bool {
        bytes.len() >= 4
            && (bytes[..4] == [0xCF, 0xFA, 0xED, 0xFE] || bytes[..4] == [0xFE, 0xED, 0xFA, 0xCF])
    }

    #[test]
    fn test_target_arch_auto_detect() {
        assert_eq!(TargetArch::host(), TargetArch::AArch64);
    }

    #[test]
    fn test_e2e_compile_verified_x86_64() {
        // End-to-end: VerifiableFunction -> bridge -> LIR -> x86-64 -> machine code
        let backend = Llvm2Backend::new(None, Some(TargetArch::X86_64));
        let func = make_add_verifiable();

        let result = backend.compile_verified(&func).expect("e2e compilation should succeed");
        assert_eq!(result.function_name, "add");
        assert_eq!(result.target, "x86_64");
        assert!(!result.machine_code.is_empty(), "should produce machine code bytes");
        assert!(
            result.machine_code.len() < 1024,
            "machine code too large: {} bytes",
            result.machine_code.len()
        );
    }

    #[test]
    fn test_e2e_compile_verified_aarch64() {
        let backend = Llvm2Backend::new(None, Some(TargetArch::AArch64));
        let func = make_add_verifiable();

        let result = backend.compile_verified(&func).expect("aarch64 compilation should succeed");
        assert_eq!(result.function_name, "add");
        assert_eq!(result.target, "aarch64");
        assert!(!result.machine_code.is_empty(), "should produce Mach-O bytes");
        assert!(is_macho_magic(&result.machine_code), "output should be Mach-O");
    }

    #[test]
    fn test_e2e_compile_to_elf_add() {
        // End-to-end: VerifiableFunction -> bridge -> LIR -> x86-64 -> ELF
        let backend = Llvm2Backend::new(None, Some(TargetArch::X86_64));
        let func = make_add_verifiable();

        let result = backend.compile_to_elf(&func).expect("ELF compilation should succeed");
        assert_eq!(result.function_name, "add");
        assert_eq!(result.target, "x86_64");
        assert!(!result.machine_code.is_empty());
        // ELF magic number: 0x7f 'E' 'L' 'F'
        assert_eq!(&result.machine_code[..4], b"\x7fELF", "output should be a valid ELF file");
    }

    #[test]
    fn test_e2e_compile_to_macho() {
        let backend = Llvm2Backend::new(None, Some(TargetArch::AArch64));
        let func = make_add_verifiable();

        let result = backend.compile_to_macho(&func).expect("Mach-O compilation should succeed");
        assert_eq!(result.function_name, "add");
        assert_eq!(result.target, "aarch64");
        assert!(is_macho_magic(&result.machine_code), "output should be Mach-O");
    }

    #[test]
    fn test_compile_verified_dispatches_by_target() {
        let func = make_add_verifiable();

        let aarch64 = Llvm2Backend::new(None, Some(TargetArch::AArch64))
            .compile_verified(&func)
            .expect("aarch64 compilation should succeed");
        let x86_64 = Llvm2Backend::new(None, Some(TargetArch::X86_64))
            .compile_verified(&func)
            .expect("x86_64 compilation should succeed");

        assert_eq!(aarch64.target, "aarch64");
        assert_eq!(x86_64.target, "x86_64");
        assert!(is_macho_magic(&aarch64.machine_code));
        assert!(!x86_64.machine_code.is_empty());
    }

    #[test]
    fn test_e2e_run_verified_compilation() {
        let backend = Llvm2Backend::default();
        let funcs = vec![make_add_verifiable()];

        let results = run_verified_compilation(&backend, &funcs)
            .expect("verified compilation should succeed");
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].function_name, "add");
        assert!(!results[0].machine_code.is_empty());
        assert_eq!(results[0].target, TargetArch::host().as_str());
    }

    // -- tRust #822: E2E binary round-trip tests (compile → lift → verify structure) --

    /// E2E round-trip: compile `add(a, b) -> i32` to ELF, then lift the ELF
    /// back to tMIR via trust-lift, and verify the lifted tMIR has the expected
    /// structure (basic blocks, locals, return block).
    ///
    /// This wires together: trust-llvm2-bridge -> LLVM2 x86-64 pipeline -> ELF
    /// emission -> trust-binary-parse ELF parsing -> trust-lift CFG recovery ->
    /// SSA construction -> semantic lift -> tMIR body.
    #[test]
    fn test_e2e_binary_round_trip_compile_lift() {
        // Step 1: Compile add(a, b) -> i32 to x86-64 ELF.
        let backend = Llvm2Backend::new(None, Some(TargetArch::X86_64));
        let func = make_add_verifiable();

        let compiled = backend
            .compile_to_elf(&func)
            .expect("ELF compilation should succeed");
        let elf_bytes = &compiled.machine_code;

        // Verify ELF magic.
        assert!(elf_bytes.len() >= 4, "ELF too small: {} bytes", elf_bytes.len());
        assert_eq!(&elf_bytes[..4], b"\x7fELF", "should be valid ELF");

        // Step 2: Parse the ELF with trust-binary-parse to extract text section info.
        let elf = trust_binary_parse::Elf64::parse(elf_bytes)
            .expect("should parse generated ELF");

        // Verify it's an x86-64 ELF (e_machine = 0x3E).
        assert_eq!(elf.header.e_machine, 0x3E, "should be x86-64 ELF");

        // Extract text section (or first executable segment) for lifter setup.
        // The LLVM2-emitted ELF may not have a symbol table, so we construct
        // the function boundary manually from compilation metadata.
        let (text_base, text_size, text_file_offset) = if let Some(text) = elf.text_section() {
            (text.sh_addr, text.sh_size, text.sh_offset as usize)
        } else {
            let exec_segs = elf.executable_segments();
            let seg = exec_segs.first().expect("ELF should have an executable segment");
            (seg.p_vaddr, seg.p_filesz, seg.p_offset as usize)
        };

        // Step 3: Construct the lifter with known function boundary.
        // We know the compiled function spans the entire text section.
        let boundary = trust_lift::FunctionBoundary {
            name: compiled.function_name.clone(),
            start: text_base,
            size: text_size,
        };

        let lifter = trust_lift::Lifter::new_with_arch(
            vec![boundary],
            text_base,
            text_size,
            text_file_offset,
            trust_lift::LiftArch::X86_64,
        );

        // Lift the function back to tMIR.
        let lifted = lifter
            .lift_function(elf_bytes, text_base)
            .expect("should lift function from ELF");

        // Step 4: Verify the lifted tMIR has expected structure.

        // Name should match the compiled function.
        assert_eq!(lifted.name, "add", "lifted function name should match");

        // Entry point should match text base.
        assert_eq!(lifted.entry_point, text_base);

        // CFG should have at least one basic block.
        assert!(
            !lifted.cfg.blocks.is_empty(),
            "lifted CFG should have at least one basic block"
        );

        // tMIR body should have x86-64 layout (24 locals: 16 GPR + 8 flags).
        assert_eq!(
            lifted.tmir_body.locals.len(),
            24,
            "x86-64 tMIR should have 24 locals (16 GPR + 8 flags)"
        );

        // tMIR body should have at least one basic block.
        assert!(
            !lifted.tmir_body.blocks.is_empty(),
            "lifted tMIR body should have at least one basic block"
        );

        // SSA form should be constructed.
        assert!(lifted.ssa.is_some(), "SSA form should be constructed");

        // Proof annotations should link tMIR statements to binary offsets.
        assert!(
            !lifted.annotations.is_empty(),
            "should have proof annotations linking to binary offsets"
        );

        // Verify the tMIR body has a return terminator in at least one block.
        let has_return = lifted.tmir_body.blocks.iter().any(|block| {
            matches!(block.terminator, trust_types::Terminator::Return)
        });
        assert!(has_return, "lifted tMIR should have at least one return block");

        // Verify the round-trip preserved semantic structure:
        // The original function had 2 arguments and the lifted tMIR should
        // detect argument register usage consistent with a 2-arg function.
        assert!(
            lifted.tmir_body.arg_count >= 1,
            "lifted function should detect at least 1 argument register (got {})",
            lifted.tmir_body.arg_count,
        );
    }

    // -- tRust #824: ProvenBinary tests --

    fn sample_compiled_function() -> CompiledFunction {
        CompiledFunction {
            function_name: "test::add".to_string(),
            machine_code: vec![0x55, 0x48, 0x89, 0xE5], // x86 prologue stub
            target: "x86_64".to_string(),
        }
    }

    fn sample_lowering_proof_proved() -> LoweringProof {
        use trust_types::ProofStrength;
        LoweringProof {
            function_name: "test::add".to_string(),
            result: VerificationResult::Proved {
                solver: "llvm2".to_string(),
                time_ms: 10,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(vec![0xCA, 0xFE]),
                solver_warnings: None,
            },
            certificate: Some(vec![0xCA, 0xFE]),
        }
    }

    fn sample_lowering_proof_unknown() -> LoweringProof {
        LoweringProof {
            function_name: "test::add".to_string(),
            result: VerificationResult::Unknown {
                solver: "llvm2".to_string(),
                time_ms: 0,
                reason: "not yet wired".to_string(),
            },
            certificate: None,
        }
    }

    fn sample_mir_proof_certificate() -> ProofCertificate {
        use trust_proof_cert::{
            CertificateChain, ChainStep, ChainStepType, FunctionHash, SolverInfo, VcSnapshot,
        };
        use trust_types::ProofStrength;

        let vc_snapshot = VcSnapshot {
            kind: "Assertion".to_string(),
            formula_json: "true".to_string(),
            location: None,
        };
        let solver = SolverInfo {
            name: "z4".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 42,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        };

        let mut chain = CertificateChain::new();
        chain.push(ChainStep {
            step_type: ChainStepType::VcGeneration,
            tool: "trust-vcgen".to_string(),
            tool_version: "0.1.0".to_string(),
            input_hash: "mir-hash".to_string(),
            output_hash: "vc-hash".to_string(),
            time_ms: 5,
            timestamp: "2026-04-15T00:00:00Z".to_string(),
        });
        chain.push(ChainStep {
            step_type: ChainStepType::SolverProof,
            tool: "z4".to_string(),
            tool_version: "1.0.0".to_string(),
            input_hash: "vc-hash".to_string(),
            output_hash: "proof-hash".to_string(),
            time_ms: 42,
            timestamp: "2026-04-15T00:00:01Z".to_string(),
        });

        ProofCertificate::new_trusted(
            "test::add".to_string(),
            FunctionHash::from_bytes(b"test::add-body"),
            vc_snapshot,
            solver,
            vec![1, 2, 3],
            "2026-04-15T00:00:00Z".to_string(),
        )
        .with_chain(chain)
    }

    #[test]
    fn test_proven_binary_without_mir_proof() {
        let compiled = sample_compiled_function();
        let lowering = sample_lowering_proof_unknown();

        let proven = ProvenBinary::new(compiled, None, lowering);

        assert_eq!(proven.function_name, "test::add");
        assert_eq!(proven.machine_code, vec![0x55, 0x48, 0x89, 0xE5]);
        assert_eq!(proven.target, "x86_64");
        assert!(proven.mir_proof.is_none());
        assert!(!proven.is_fully_proved()); // No MIR proof
        assert!(proven.verify_combined_hash()); // Hash should match
        // Chain has just the codegen lowering step.
        assert_eq!(proven.chain.len(), 1);
        assert_eq!(proven.chain.steps[0].step_type, ChainStepType::CodegenLowering);
    }

    #[test]
    fn test_proven_binary_with_mir_proof_and_lowering() {
        let compiled = sample_compiled_function();
        let mir_proof = sample_mir_proof_certificate();
        let lowering = sample_lowering_proof_proved();

        let proven = ProvenBinary::new(compiled, Some(mir_proof), lowering);

        assert!(proven.mir_proof.is_some());
        assert!(proven.lowering_proof.result.is_proved());
        assert!(proven.is_fully_proved());
        assert!(proven.verify_combined_hash());
        // Chain: VcGeneration + SolverProof + CodegenLowering = 3 steps.
        assert_eq!(proven.chain.len(), 3);
        assert_eq!(proven.chain.steps[0].step_type, ChainStepType::VcGeneration);
        assert_eq!(proven.chain.steps[1].step_type, ChainStepType::SolverProof);
        assert_eq!(proven.chain.steps[2].step_type, ChainStepType::CodegenLowering);
    }

    #[test]
    fn test_proven_binary_not_fully_proved_without_lowering() {
        let compiled = sample_compiled_function();
        let mir_proof = sample_mir_proof_certificate();
        let lowering = sample_lowering_proof_unknown(); // Unknown = not proved

        let proven = ProvenBinary::new(compiled, Some(mir_proof), lowering);

        // Has MIR proof but lowering is Unknown -> not fully proved.
        assert!(!proven.is_fully_proved());
    }

    #[test]
    fn test_proven_binary_combined_hash_deterministic() {
        let compiled1 = sample_compiled_function();
        let compiled2 = sample_compiled_function();
        let lowering1 = sample_lowering_proof_proved();
        let lowering2 = sample_lowering_proof_proved();

        let proven1 = ProvenBinary::new(compiled1, None, lowering1);
        let proven2 = ProvenBinary::new(compiled2, None, lowering2);

        assert_eq!(proven1.combined_hash, proven2.combined_hash);
    }

    #[test]
    fn test_proven_binary_combined_hash_changes_with_machine_code() {
        let compiled1 = sample_compiled_function();
        let mut compiled2 = sample_compiled_function();
        compiled2.machine_code = vec![0xFF, 0xFF]; // different code

        let lowering1 = sample_lowering_proof_proved();
        let lowering2 = sample_lowering_proof_proved();

        let proven1 = ProvenBinary::new(compiled1, None, lowering1);
        let proven2 = ProvenBinary::new(compiled2, None, lowering2);

        assert_ne!(proven1.combined_hash, proven2.combined_hash);
    }

    #[test]
    fn test_proven_binary_verify_combined_hash_detects_tampering() {
        let compiled = sample_compiled_function();
        let lowering = sample_lowering_proof_proved();

        let mut proven = ProvenBinary::new(compiled, None, lowering);
        assert!(proven.verify_combined_hash());

        // Tamper with machine code — hash should no longer match.
        proven.machine_code = vec![0x00, 0x00];
        assert!(!proven.verify_combined_hash());
    }

    #[test]
    fn test_e2e_produce_proven_binary() {
        let backend = Llvm2Backend::default();
        let func = make_add_verifiable();

        let proven = backend
            .produce_proven_binary(&func, None)
            .expect("produce_proven_binary should succeed");

        assert_eq!(proven.function_name, "add");
        assert!(!proven.machine_code.is_empty());
        assert!(proven.verify_combined_hash());
        // Without MIR proof and with placeholder lowering -> not fully proved.
        assert!(!proven.is_fully_proved());
        // Chain has just the codegen lowering step.
        assert_eq!(proven.chain.len(), 1);
    }

    #[test]
    fn test_e2e_produce_proven_binary_with_mir_cert() {
        let backend = Llvm2Backend::default();
        let func = make_add_verifiable();
        let mir_proof = sample_mir_proof_certificate();

        let proven = backend
            .produce_proven_binary(&func, Some(mir_proof))
            .expect("produce_proven_binary with mir_proof should succeed");

        assert!(proven.mir_proof.is_some());
        assert!(proven.verify_combined_hash());
        // Chain: VcGeneration + SolverProof + CodegenLowering = 3 steps.
        assert_eq!(proven.chain.len(), 3);
    }

    // -- tRust #821: Complex e2e tests (branch, multi-block, loop, batch) --

    /// Build `max(a: i32, b: i32) -> i32` with branch (Icmp + Brif).
    ///
    /// MIR layout:
    ///   bb0: _3 = Gt(_1, _2); SwitchInt(_3, [(1, bb1)], otherwise=bb2)
    ///   bb1: _0 = Use(_1); Return
    ///   bb2: _0 = Use(_2); Return
    fn make_max_verifiable() -> VerifiableFunction {
        use trust_types::{
            BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue,
            SourceSpan, Statement, Terminator, Ty, VerifiableBody,
        };

        VerifiableFunction {
            name: "max".to_string(),
            def_path: "test::max".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },        // return
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: None },          // cmp result
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Gt,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(3)),
                            targets: vec![(1, BlockId(1))],
                            otherwise: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build `abs_diff(a: i32, b: i32) -> i32` with if-else merge (4 blocks).
    ///
    /// MIR layout:
    ///   bb0: _3 = Gt(_1, _2); SwitchInt(_3, [(1, bb1)], otherwise=bb2)
    ///   bb1: _0 = Sub(_1, _2); Goto(bb3)
    ///   bb2: _0 = Sub(_2, _1); Goto(bb3)
    ///   bb3: Return
    fn make_abs_diff_verifiable() -> VerifiableFunction {
        use trust_types::{
            BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue,
            SourceSpan, Statement, Terminator, Ty, VerifiableBody,
        };

        VerifiableFunction {
            name: "abs_diff".to_string(),
            def_path: "test::abs_diff".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Gt,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(3)),
                            targets: vec![(1, BlockId(1))],
                            otherwise: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Sub,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Sub,
                                Operand::Copy(Place::local(2)),
                                Operand::Copy(Place::local(1)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build `countdown(n: i32) -> i32` with a loop (Jump back-edge).
    ///
    /// MIR layout (computes sum = n + (n-1) + ... + 1):
    ///   bb0: _3 = Use(_1); _4 = Iconst(0); Goto(bb1)         // init counter=n, acc=0
    ///   bb1: _5 = Gt(_3, Iconst(0)); SwitchInt(_5, [(1, bb2)], otherwise=bb3)
    ///   bb2: _4 = Add(_4, _3); _3 = Sub(_3, Iconst(1)); Goto(bb1)  // back-edge
    ///   bb3: _0 = Use(_4); Return
    fn make_countdown_verifiable() -> VerifiableFunction {
        use trust_types::{
            BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue,
            SourceSpan, Statement, Terminator, Ty, VerifiableBody,
        };

        VerifiableFunction {
            name: "countdown".to_string(),
            def_path: "test::countdown".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },          // return
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("n".into()) },  // arg
                    LocalDecl { index: 2, ty: Ty::i32(), name: None },          // unused padding
                    LocalDecl { index: 3, ty: Ty::i32(), name: None },          // counter
                    LocalDecl { index: 4, ty: Ty::i32(), name: None },          // accumulator
                    LocalDecl { index: 5, ty: Ty::Bool, name: None },           // cmp result
                ],
                blocks: vec![
                    // bb0: init counter = n, acc = 0; goto bb1
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(3),
                                rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(4),
                                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    // bb1: if counter > 0 then bb2 else bb3
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Gt,
                                Operand::Copy(Place::local(3)),
                                Operand::Constant(ConstValue::Int(0)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(5)),
                            targets: vec![(1, BlockId(2))],
                            otherwise: BlockId(3),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb2: acc += counter; counter -= 1; goto bb1 (back-edge)
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(4),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Add,
                                    Operand::Copy(Place::local(4)),
                                    Operand::Copy(Place::local(3)),
                                ),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(3),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Sub,
                                    Operand::Copy(Place::local(3)),
                                    Operand::Constant(ConstValue::Int(1)),
                                ),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    // bb3: return acc
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(4))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_e2e_branch_max_x86_64() {
        // E2E: max(a, b) using Icmp + Brif + two return blocks
        let backend = Llvm2Backend::new(None, Some(TargetArch::X86_64));
        let func = make_max_verifiable();

        let result = backend.compile_verified(&func).expect("max should compile");
        assert_eq!(result.function_name, "max");
        assert_eq!(result.target, "x86_64");
        assert!(!result.machine_code.is_empty(), "should produce machine code");
        assert!(
            result.machine_code.len() < 4096,
            "machine code suspiciously large: {} bytes",
            result.machine_code.len()
        );
    }

    #[test]
    fn test_e2e_branch_max_aarch64() {
        let backend = Llvm2Backend::new(None, Some(TargetArch::AArch64));
        let func = make_max_verifiable();

        let result = backend.compile_verified(&func).expect("max aarch64 should compile");
        assert_eq!(result.function_name, "max");
        assert_eq!(result.target, "aarch64");
        assert!(!result.machine_code.is_empty());
        assert!(is_macho_magic(&result.machine_code), "output should be Mach-O");
    }

    #[test]
    fn test_e2e_if_else_merge_x86_64() {
        // E2E: abs_diff with if-else diamond + merge block (4 blocks)
        let backend = Llvm2Backend::new(None, Some(TargetArch::X86_64));
        let func = make_abs_diff_verifiable();

        let result = backend.compile_verified(&func).expect("abs_diff should compile");
        assert_eq!(result.function_name, "abs_diff");
        assert_eq!(result.target, "x86_64");
        assert!(!result.machine_code.is_empty(), "should produce machine code");
    }

    #[test]
    fn test_e2e_if_else_merge_aarch64() {
        let backend = Llvm2Backend::new(None, Some(TargetArch::AArch64));
        let func = make_abs_diff_verifiable();

        let result = backend.compile_verified(&func).expect("abs_diff aarch64 should compile");
        assert_eq!(result.function_name, "abs_diff");
        assert_eq!(result.target, "aarch64");
        assert!(!result.machine_code.is_empty());
        assert!(is_macho_magic(&result.machine_code), "output should be Mach-O");
    }

    #[test]
    fn test_e2e_loop_countdown_x86_64() {
        // E2E: countdown loop with Jump back-edge
        let backend = Llvm2Backend::new(None, Some(TargetArch::X86_64));
        let func = make_countdown_verifiable();

        let result = backend.compile_verified(&func).expect("countdown should compile");
        assert_eq!(result.function_name, "countdown");
        assert_eq!(result.target, "x86_64");
        assert!(!result.machine_code.is_empty(), "should produce machine code");
    }

    #[test]
    fn test_e2e_loop_countdown_aarch64() {
        let backend = Llvm2Backend::new(None, Some(TargetArch::AArch64));
        let func = make_countdown_verifiable();

        let result = backend.compile_verified(&func).expect("countdown aarch64 should compile");
        assert_eq!(result.function_name, "countdown");
        assert_eq!(result.target, "aarch64");
        assert!(!result.machine_code.is_empty());
        assert!(is_macho_magic(&result.machine_code), "output should be Mach-O");
    }

    #[test]
    fn test_e2e_batch_compile_complex_functions() {
        // E2E: compile all three complex functions together via run_verified_compilation
        let backend = Llvm2Backend::default();
        let funcs = vec![
            make_max_verifiable(),
            make_abs_diff_verifiable(),
            make_countdown_verifiable(),
        ];

        let results = run_verified_compilation(&backend, &funcs)
            .expect("batch compilation should succeed");
        assert_eq!(results.len(), 3);
        assert_eq!(results[0].function_name, "max");
        assert_eq!(results[1].function_name, "abs_diff");
        assert_eq!(results[2].function_name, "countdown");
        for result in &results {
            assert!(!result.machine_code.is_empty(), "{} produced empty code", result.function_name);
            assert_eq!(result.target, TargetArch::host().as_str());
        }
    }

    #[test]
    fn test_e2e_branch_max_to_elf() {
        let backend = Llvm2Backend::new(None, Some(TargetArch::X86_64));
        let func = make_max_verifiable();

        let result = backend.compile_to_elf(&func).expect("max ELF should compile");
        assert_eq!(&result.machine_code[..4], b"\x7fELF", "output should be valid ELF");
    }

    #[test]
    fn test_e2e_if_else_merge_to_elf() {
        let backend = Llvm2Backend::new(None, Some(TargetArch::X86_64));
        let func = make_abs_diff_verifiable();

        let result = backend.compile_to_elf(&func).expect("abs_diff ELF should compile");
        assert_eq!(&result.machine_code[..4], b"\x7fELF", "output should be valid ELF");
    }

    #[test]
    fn test_e2e_loop_countdown_to_elf() {
        let backend = Llvm2Backend::new(None, Some(TargetArch::X86_64));
        let func = make_countdown_verifiable();

        let result = backend.compile_to_elf(&func).expect("countdown ELF should compile");
        assert_eq!(&result.machine_code[..4], b"\x7fELF", "output should be valid ELF");
    }

}
