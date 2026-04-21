// trust-decompile output types
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Naming style for decompiled variables.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum NamingStyle {
    /// Use MIR-style names (_0, _1, _2, ...), preserving original names where available.
    #[default]
    MirPreserved,
    /// Infer names from type and usage (e.g., `count` for a loop counter, `ptr` for pointers).
    TypeBased,
}

/// How much commentary to include in decompiled output.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum CommentLevel {
    /// No comments — bare Rust source only.
    None,
    /// Minimal comments: basic block labels and goto annotations.
    #[default]
    Minimal,
    /// Verbose comments: include MIR origin info, confidence annotations, pattern hints.
    Verbose,
}

/// A decompiled function with source code and metadata.
#[derive(Debug, Clone)]
pub struct DecompiledFunction {
    /// The function name.
    pub name: String,
    /// Parameter names and types as `(name, type_str)` pairs.
    pub params: Vec<(String, String)>,
    /// The decompiled Rust source code (full function body).
    pub source: String,
    /// Confidence score (0.0 = raw MIR dump, 1.0 = fully idiomatic Rust).
    /// Stage 1 raw emission starts at ~0.3; pattern recovery lifts it.
    pub confidence: f64,
}

/// A decompiled module — a collection of decompiled functions with imports.
#[derive(Debug, Clone)]
pub struct DecompiledModule {
    /// Module name (derived from the source crate or binary name).
    pub name: String,
    /// Import/use statements needed by the decompiled functions.
    pub imports: Vec<String>,
    /// Decompiled functions in this module.
    pub functions: Vec<DecompiledFunction>,
}

impl DecompiledModule {
    /// Create a new empty module with the given name.
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            imports: Vec::new(),
            functions: Vec::new(),
        }
    }

    /// Render the full module as a Rust source string.
    #[must_use]
    pub fn to_source(&self) -> String {
        let mut lines = Vec::new();

        // Module-level comment
        lines.push(format!("// Decompiled module: {}", self.name));
        lines.push(String::new());

        // Imports
        for import in &self.imports {
            lines.push(format!("use {import};"));
        }
        if !self.imports.is_empty() {
            lines.push(String::new());
        }

        // Functions
        for (i, func) in self.functions.iter().enumerate() {
            lines.push(func.source.clone());
            if i + 1 < self.functions.len() {
                lines.push(String::new());
            }
        }

        lines.join("\n")
    }
}

/// Options controlling which decompilation stages to apply.
#[derive(Debug, Clone)]
pub struct DecompileOptions {
    /// Apply Stage 1: raw MIR-to-Rust emission.
    /// Always true in practice; provided for testing partial stages.
    pub raw_emission: bool,
    /// Apply Stage 2: pattern recovery (Box, for loops, Option).
    pub pattern_recovery: bool,
    /// Naming style for local variables.
    pub naming_style: NamingStyle,
    /// Level of commentary in the output.
    pub comment_level: CommentLevel,
}

impl Default for DecompileOptions {
    fn default() -> Self {
        Self {
            raw_emission: true,
            pattern_recovery: true,
            naming_style: NamingStyle::default(),
            comment_level: CommentLevel::default(),
        }
    }
}

impl DecompileOptions {
    /// Raw emission only, no pattern recovery.
    #[must_use]
    pub fn raw_only() -> Self {
        Self {
            raw_emission: true,
            pattern_recovery: false,
            naming_style: NamingStyle::MirPreserved,
            comment_level: CommentLevel::Minimal,
        }
    }
}
