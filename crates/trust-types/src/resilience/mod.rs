// trust-types/resilience: External dependency failure modeling and resilience analysis
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod types;
mod analysis;
mod helpers;
mod external_patterns;

#[cfg(test)]
mod tests;

pub use types::*;
pub use analysis::ResilienceAnalysis;
pub use external_patterns::{extract_failure_model, match_external_call, EXTERNAL_CALL_PATTERNS};
