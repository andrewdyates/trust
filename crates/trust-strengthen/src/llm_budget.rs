// trust-strengthen/llm_budget.rs: Token budget management for AI Model API prompts
//
// Estimates token counts, allocates budgets across prompt sections, and
// truncates lowest-priority content when the prompt exceeds the budget.
// Phase 5 of the AI Model API integration (#613).
//
// Design: `designs/2026-04-13-AI Model-api-integration-design.md` -- Phase 5
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;
use std::fmt::Write;

/// Token budget configuration for AI Model API requests.
///
/// Controls the maximum prompt size, response allocation, and safety margin
/// to prevent exceeding the model's context window. Lives in `InferenceConfig`
/// only (not duplicated in `ClaudeConfig`).
#[derive(Debug, Clone)]
pub struct TokenBudget {
    /// Maximum tokens allowed in the prompt (default: 24000).
    ///
    /// Conservative for Sonnet's 200K context: leaves room for system prompt,
    /// response, and overhead.
    pub max_prompt_tokens: usize,
    /// Maximum tokens allocated for the response (default: 2048).
    pub max_response_tokens: usize,
    /// Safety margin multiplier (default: 1.3).
    ///
    /// Accounts for BPE under-counting on code with heavy punctuation.
    /// Applied to character-based estimates before comparing to budget.
    pub safety_margin: f64,
    /// Token overhead for tool_use schema JSON (default: 200).
    ///
    /// Subtracted from the prompt budget when tool_use is enabled.
    pub tool_use_overhead: usize,
}

impl Default for TokenBudget {
    fn default() -> Self {
        Self {
            max_prompt_tokens: 24_000,
            max_response_tokens: 2048,
            safety_margin: 1.3,
            tool_use_overhead: 200,
        }
    }
}

impl TokenBudget {
    /// Returns the effective prompt token budget, accounting for tool_use overhead.
    #[must_use]
    pub fn effective_prompt_budget(&self, tool_use_enabled: bool) -> usize {
        if tool_use_enabled {
            self.max_prompt_tokens.saturating_sub(self.tool_use_overhead)
        } else {
            self.max_prompt_tokens
        }
    }
}

/// Estimate the token count for a text string.
///
/// Uses the conservative heuristic: `character_count / 3 * safety_margin`.
/// Code with heavy punctuation (Rust, MIR) tends to have more tokens per
/// character than English prose, so the 1.3x safety margin compensates.
#[must_use]
pub fn estimate_tokens(text: &str, safety_margin: f64) -> usize {
    let char_count = text.len();
    let raw_estimate = (char_count as f64) / 3.0;
    (raw_estimate * safety_margin).ceil() as usize
}

/// Content section priority for truncation (highest priority = last to be cut).
///
/// When the prompt exceeds the token budget, sections are removed starting
/// from the lowest priority. This ordering ensures the most essential context
/// is preserved.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ContentPriority {
    /// Reconstructed source from MIR decompilation (lowest priority).
    ReconstructedSource = 0,
    /// MIR text dump.
    MirText = 1,
    /// Existing specification annotations on the function.
    ExistingSpecs = 2,
    /// Original source code of the function.
    OriginalSource = 3,
    /// Verification failure descriptions.
    FailureDescriptions = 4,
    /// Function signature (highest priority -- never truncated).
    Signature = 5,
}

impl fmt::Display for ContentPriority {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ReconstructedSource => write!(f, "reconstructed_source"),
            Self::MirText => write!(f, "mir_text"),
            Self::ExistingSpecs => write!(f, "existing_specs"),
            Self::OriginalSource => write!(f, "original_source"),
            Self::FailureDescriptions => write!(f, "failure_descriptions"),
            Self::Signature => write!(f, "signature"),
        }
    }
}

/// A named section of prompt content with its priority and estimated tokens.
#[derive(Debug, Clone)]
pub struct PromptSection {
    /// Which content priority this section has.
    pub priority: ContentPriority,
    /// The text content of this section.
    pub content: String,
    /// Estimated token count (computed via `estimate_tokens`).
    pub estimated_tokens: usize,
}

impl PromptSection {
    /// Create a new prompt section, estimating tokens with the given safety margin.
    #[must_use]
    pub fn new(priority: ContentPriority, content: String, safety_margin: f64) -> Self {
        let estimated_tokens = estimate_tokens(&content, safety_margin);
        Self {
            priority,
            content,
            estimated_tokens,
        }
    }
}

/// Record of which truncations were applied to fit within the token budget.
#[derive(Debug, Clone, Default)]
pub struct TruncationRecord {
    /// Sections that were completely removed, in order of removal.
    pub sections_removed: Vec<ContentPriority>,
    /// Whether source truncation was applied (partial removal via line limit).
    pub source_truncated: bool,
    /// Original estimated total tokens before truncation.
    pub original_tokens: usize,
    /// Final estimated total tokens after truncation.
    pub final_tokens: usize,
    /// Whether any truncation was needed.
    pub was_truncated: bool,
}

/// Cost tracking for a single LLM inference request.
#[derive(Debug, Clone, Default)]
pub struct RequestCost {
    /// Estimated prompt tokens sent.
    pub prompt_tokens: usize,
    /// Response tokens received (0 if not yet known).
    pub response_tokens: usize,
    /// Total estimated tokens (prompt + response).
    pub total_tokens: usize,
}

/// Accumulated cost tracking across a verification run.
#[derive(Debug, Clone, Default)]
pub struct RunCostTracker {
    /// Total requests made.
    pub total_requests: usize,
    /// Total estimated prompt tokens across all requests.
    pub total_prompt_tokens: usize,
    /// Total response tokens across all requests.
    pub total_response_tokens: usize,
    /// Per-request cost breakdown.
    pub requests: Vec<RequestCost>,
}

impl RunCostTracker {
    /// Record a completed request.
    pub fn record(&mut self, prompt_tokens: usize, response_tokens: usize) {
        let cost = RequestCost {
            prompt_tokens,
            response_tokens,
            total_tokens: prompt_tokens + response_tokens,
        };
        self.total_requests += 1;
        self.total_prompt_tokens += prompt_tokens;
        self.total_response_tokens += response_tokens;
        self.requests.push(cost);
    }

    /// Total tokens consumed across all requests.
    #[must_use]
    pub fn total_tokens(&self) -> usize {
        self.total_prompt_tokens + self.total_response_tokens
    }
}

/// Truncate a list of prompt sections to fit within the given token budget.
///
/// Removes sections starting from the lowest priority until the total
/// estimated tokens fits within `budget_tokens`. Returns the surviving
/// sections (in original order) and a record of what was removed.
///
/// The `Signature` priority is never removed -- if the signature alone
/// exceeds the budget, truncation still preserves it and reports the overflow.
#[must_use]
pub fn truncate_to_budget(
    sections: &[PromptSection],
    budget_tokens: usize,
) -> (Vec<PromptSection>, TruncationRecord) {
    let original_tokens: usize = sections.iter().map(|s| s.estimated_tokens).sum();

    if original_tokens <= budget_tokens {
        return (
            sections.to_vec(),
            TruncationRecord {
                original_tokens,
                final_tokens: original_tokens,
                was_truncated: false,
                ..Default::default()
            },
        );
    }

    // Sort by priority ascending (lowest priority first) for removal order.
    let mut indexed: Vec<(usize, &PromptSection)> = sections.iter().enumerate().collect();
    indexed.sort_by_key(|(_, s)| s.priority);

    let mut removed: Vec<ContentPriority> = Vec::new();
    let mut removed_indices: Vec<usize> = Vec::new();
    let mut current_tokens = original_tokens;

    for (idx, section) in &indexed {
        if current_tokens <= budget_tokens {
            break;
        }
        // Never remove Signature
        if section.priority == ContentPriority::Signature {
            continue;
        }
        current_tokens = current_tokens.saturating_sub(section.estimated_tokens);
        removed.push(section.priority);
        removed_indices.push(*idx);
    }

    let surviving: Vec<PromptSection> = sections
        .iter()
        .enumerate()
        .filter(|(i, _)| !removed_indices.contains(i))
        .map(|(_, s)| s.clone())
        .collect();

    let final_tokens: usize = surviving.iter().map(|s| s.estimated_tokens).sum();

    (
        surviving,
        TruncationRecord {
            sections_removed: removed,
            source_truncated: false,
            original_tokens,
            final_tokens,
            was_truncated: true,
        },
    )
}

/// Truncate source text to a maximum number of lines.
///
/// Keeps the first and last portions of the source, inserting an elision
/// marker in the middle. Returns `None` if the source is already within
/// the line limit.
#[must_use]
pub fn truncate_source_lines(source: &str, max_lines: usize) -> Option<String> {
    let lines: Vec<&str> = source.lines().collect();
    if lines.len() <= max_lines {
        return None;
    }

    // Keep first half and last half of the allowed lines
    let keep_start = max_lines / 2;
    let keep_end = max_lines - keep_start;
    let omitted = lines.len() - max_lines;

    let mut result = String::new();
    for line in &lines[..keep_start] {
        result.push_str(line);
        result.push('\n');
    }
    let _ = writeln!(result, "    // ... ({omitted} lines omitted) ...");
    for (i, line) in lines[lines.len() - keep_end..].iter().enumerate() {
        result.push_str(line);
        if i < keep_end - 1 {
            result.push('\n');
        }
    }

    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- estimate_tokens tests --

    #[test]
    fn test_estimate_tokens_empty() {
        assert_eq!(estimate_tokens("", 1.0), 0);
        assert_eq!(estimate_tokens("", 1.3), 0);
    }

    #[test]
    fn test_estimate_tokens_short_text() {
        // "hello" = 5 chars, 5/3 * 1.0 = 1.67 -> ceil = 2
        assert_eq!(estimate_tokens("hello", 1.0), 2);
    }

    #[test]
    fn test_estimate_tokens_with_safety_margin() {
        // "hello world" = 11 chars, 11/3 * 1.3 = 4.77 -> ceil = 5
        assert_eq!(estimate_tokens("hello world", 1.3), 5);
    }

    #[test]
    fn test_estimate_tokens_code_snippet() {
        let code = "fn get_midpoint(a: u64, b: u64) -> u64 {\n    (a + b) / 2\n}";
        let tokens = estimate_tokens(code, 1.3);
        // 59 chars / 3 * 1.3 = 25.57 -> ceil = 26
        assert_eq!(tokens, 26);
    }

    #[test]
    fn test_estimate_tokens_large_mir() {
        let mir = "bb0: {\n".repeat(100);
        let tokens_no_margin = estimate_tokens(&mir, 1.0);
        let tokens_with_margin = estimate_tokens(&mir, 1.3);
        assert!(tokens_with_margin > tokens_no_margin);
        // With safety margin, should be ~30% more
        let ratio = tokens_with_margin as f64 / tokens_no_margin as f64;
        assert!((1.2..=1.4).contains(&ratio), "ratio was {ratio}");
    }

    #[test]
    fn test_estimate_tokens_safety_margin_default() {
        let budget = TokenBudget::default();
        let text = "a".repeat(300); // 300 chars -> 100 tokens * 1.3 = 130
        let tokens = estimate_tokens(&text, budget.safety_margin);
        assert_eq!(tokens, 130);
    }

    // -- TokenBudget tests --

    #[test]
    fn test_token_budget_defaults() {
        let budget = TokenBudget::default();
        assert_eq!(budget.max_prompt_tokens, 24_000);
        assert_eq!(budget.max_response_tokens, 2048);
        assert!((budget.safety_margin - 1.3).abs() < f64::EPSILON);
        assert_eq!(budget.tool_use_overhead, 200);
    }

    #[test]
    fn test_effective_budget_without_tool_use() {
        let budget = TokenBudget::default();
        assert_eq!(budget.effective_prompt_budget(false), 24_000);
    }

    #[test]
    fn test_effective_budget_with_tool_use() {
        let budget = TokenBudget::default();
        assert_eq!(budget.effective_prompt_budget(true), 23_800);
    }

    #[test]
    fn test_effective_budget_custom() {
        let budget = TokenBudget {
            max_prompt_tokens: 10_000,
            tool_use_overhead: 500,
            ..Default::default()
        };
        assert_eq!(budget.effective_prompt_budget(true), 9_500);
        assert_eq!(budget.effective_prompt_budget(false), 10_000);
    }

    // -- ContentPriority ordering tests --

    #[test]
    fn test_content_priority_ordering() {
        assert!(ContentPriority::ReconstructedSource < ContentPriority::MirText);
        assert!(ContentPriority::MirText < ContentPriority::ExistingSpecs);
        assert!(ContentPriority::ExistingSpecs < ContentPriority::OriginalSource);
        assert!(ContentPriority::OriginalSource < ContentPriority::FailureDescriptions);
        assert!(ContentPriority::FailureDescriptions < ContentPriority::Signature);
    }

    #[test]
    fn test_content_priority_display() {
        assert_eq!(ContentPriority::ReconstructedSource.to_string(), "reconstructed_source");
        assert_eq!(ContentPriority::MirText.to_string(), "mir_text");
        assert_eq!(ContentPriority::ExistingSpecs.to_string(), "existing_specs");
        assert_eq!(ContentPriority::OriginalSource.to_string(), "original_source");
        assert_eq!(ContentPriority::FailureDescriptions.to_string(), "failure_descriptions");
        assert_eq!(ContentPriority::Signature.to_string(), "signature");
    }

    // -- PromptSection tests --

    #[test]
    fn test_prompt_section_new() {
        let section = PromptSection::new(
            ContentPriority::OriginalSource,
            "fn foo() {}".into(),
            1.3,
        );
        assert_eq!(section.priority, ContentPriority::OriginalSource);
        assert_eq!(section.content, "fn foo() {}");
        assert!(section.estimated_tokens > 0);
    }

    // -- truncate_to_budget tests --

    #[test]
    fn test_truncate_within_budget_no_change() {
        let sections = vec![
            PromptSection::new(ContentPriority::Signature, "fn foo()".into(), 1.0),
            PromptSection::new(ContentPriority::OriginalSource, "let x = 1;".into(), 1.0),
        ];
        let total: usize = sections.iter().map(|s| s.estimated_tokens).sum();

        let (result, record) = truncate_to_budget(&sections, total + 100);
        assert_eq!(result.len(), 2);
        assert!(!record.was_truncated);
        assert!(record.sections_removed.is_empty());
    }

    #[test]
    fn test_truncate_removes_lowest_priority_first() {
        let sections = vec![
            PromptSection::new(ContentPriority::Signature, "sig".into(), 1.0),
            PromptSection::new(ContentPriority::OriginalSource, "a".repeat(300), 1.0),
            PromptSection::new(ContentPriority::MirText, "b".repeat(300), 1.0),
            PromptSection::new(
                ContentPriority::ReconstructedSource,
                "c".repeat(300),
                1.0,
            ),
        ];

        // Budget that fits signature + one section but not all
        let sig_tokens = sections[0].estimated_tokens;
        let one_section = sections[1].estimated_tokens;
        let budget = sig_tokens + one_section + 5;

        let (result, record) = truncate_to_budget(&sections, budget);
        assert!(record.was_truncated);

        // ReconstructedSource (lowest priority) should be removed first, then MirText
        assert!(record.sections_removed.contains(&ContentPriority::ReconstructedSource));
        // Signature should always survive
        assert!(result.iter().any(|s| s.priority == ContentPriority::Signature));
    }

    #[test]
    fn test_truncate_preserves_signature_always() {
        let sections = vec![
            PromptSection::new(ContentPriority::Signature, "a".repeat(600), 1.0),
            PromptSection::new(ContentPriority::OriginalSource, "b".repeat(600), 1.0),
        ];

        // Budget smaller than signature alone
        let (result, record) = truncate_to_budget(&sections, 10);
        assert!(record.was_truncated);
        // Signature is never removed
        assert!(result.iter().any(|s| s.priority == ContentPriority::Signature));
        assert!(record.sections_removed.contains(&ContentPriority::OriginalSource));
        assert!(!record.sections_removed.contains(&ContentPriority::Signature));
    }

    #[test]
    fn test_truncate_removes_multiple_sections() {
        let sections = vec![
            PromptSection::new(ContentPriority::Signature, "fn f()".into(), 1.0),
            PromptSection::new(
                ContentPriority::FailureDescriptions,
                "overflow".into(),
                1.0,
            ),
            PromptSection::new(ContentPriority::OriginalSource, "a".repeat(300), 1.0),
            PromptSection::new(ContentPriority::ExistingSpecs, "b".repeat(300), 1.0),
            PromptSection::new(ContentPriority::MirText, "c".repeat(300), 1.0),
            PromptSection::new(
                ContentPriority::ReconstructedSource,
                "d".repeat(300),
                1.0,
            ),
        ];

        // Very tight budget: only signature + failures fit
        let sig = sections[0].estimated_tokens;
        let fail = sections[1].estimated_tokens;
        let budget = sig + fail + 2;

        let (result, record) = truncate_to_budget(&sections, budget);
        assert!(record.was_truncated);
        assert_eq!(result.len(), 2);
        assert!(result.iter().any(|s| s.priority == ContentPriority::Signature));
        assert!(result.iter().any(|s| s.priority == ContentPriority::FailureDescriptions));

        // All lower-priority sections should be removed
        assert!(record.sections_removed.contains(&ContentPriority::ReconstructedSource));
        assert!(record.sections_removed.contains(&ContentPriority::MirText));
        assert!(record.sections_removed.contains(&ContentPriority::ExistingSpecs));
        assert!(record.sections_removed.contains(&ContentPriority::OriginalSource));
    }

    #[test]
    fn test_truncate_record_tokens() {
        let sections = vec![
            PromptSection::new(ContentPriority::Signature, "fn f()".into(), 1.0),
            PromptSection::new(ContentPriority::MirText, "a".repeat(900), 1.0),
        ];
        let total: usize = sections.iter().map(|s| s.estimated_tokens).sum();

        let (_, record) = truncate_to_budget(&sections, 10);
        assert!(record.was_truncated);
        assert_eq!(record.original_tokens, total);
        assert!(record.final_tokens < total);
    }

    #[test]
    fn test_truncate_empty_sections() {
        let (result, record) = truncate_to_budget(&[], 1000);
        assert!(result.is_empty());
        assert!(!record.was_truncated);
        assert_eq!(record.original_tokens, 0);
    }

    // -- truncate_source_lines tests --

    #[test]
    fn test_truncate_source_within_limit() {
        let source = "line1\nline2\nline3";
        assert!(truncate_source_lines(source, 5).is_none());
        assert!(truncate_source_lines(source, 3).is_none());
    }

    #[test]
    fn test_truncate_source_exceeds_limit() {
        let lines: Vec<String> = (0..20).map(|i| format!("line {i}")).collect();
        let source = lines.join("\n");
        let truncated = truncate_source_lines(&source, 10).expect("should truncate");
        assert!(truncated.contains("omitted"));
        assert!(truncated.contains("line 0")); // first line preserved
        assert!(truncated.contains("line 19")); // last line preserved
    }

    #[test]
    fn test_truncate_source_preserves_head_and_tail() {
        let lines: Vec<String> = (0..100).map(|i| format!("    let x{i} = {i};")).collect();
        let source = lines.join("\n");
        let truncated = truncate_source_lines(&source, 20).expect("should truncate");

        // Should contain first ~10 lines and last ~10 lines
        assert!(truncated.contains("let x0 = 0;"));
        assert!(truncated.contains("let x99 = 99;"));
        assert!(truncated.contains("80 lines omitted"));
    }

    // -- RunCostTracker tests --

    #[test]
    fn test_cost_tracker_empty() {
        let tracker = RunCostTracker::default();
        assert_eq!(tracker.total_requests, 0);
        assert_eq!(tracker.total_tokens(), 0);
    }

    #[test]
    fn test_cost_tracker_single_request() {
        let mut tracker = RunCostTracker::default();
        tracker.record(1000, 200);
        assert_eq!(tracker.total_requests, 1);
        assert_eq!(tracker.total_prompt_tokens, 1000);
        assert_eq!(tracker.total_response_tokens, 200);
        assert_eq!(tracker.total_tokens(), 1200);
        assert_eq!(tracker.requests.len(), 1);
        assert_eq!(tracker.requests[0].total_tokens, 1200);
    }

    #[test]
    fn test_cost_tracker_multiple_requests() {
        let mut tracker = RunCostTracker::default();
        tracker.record(1000, 200);
        tracker.record(800, 150);
        tracker.record(1200, 300);
        assert_eq!(tracker.total_requests, 3);
        assert_eq!(tracker.total_prompt_tokens, 3000);
        assert_eq!(tracker.total_response_tokens, 650);
        assert_eq!(tracker.total_tokens(), 3650);
    }

    // -- Integration-style test: large MIR triggers truncation --

    #[test]
    fn test_large_mir_triggers_truncation() {
        // Simulate a large MIR dump that would exceed a small budget
        let large_mir = "bb0: {\n    _1 = Add(_2, _3);\n}\n".repeat(500);
        let budget = TokenBudget {
            max_prompt_tokens: 500,
            safety_margin: 1.3,
            ..Default::default()
        };

        let sections = vec![
            PromptSection::new(
                ContentPriority::Signature,
                "fn get_midpoint(a: u64, b: u64) -> u64".into(),
                budget.safety_margin,
            ),
            PromptSection::new(
                ContentPriority::FailureDescriptions,
                "Arithmetic overflow (Add) in get_midpoint (solver: z4)".into(),
                budget.safety_margin,
            ),
            PromptSection::new(
                ContentPriority::OriginalSource,
                "fn get_midpoint(a: u64, b: u64) -> u64 {\n    (a + b) / 2\n}".into(),
                budget.safety_margin,
            ),
            PromptSection::new(
                ContentPriority::MirText,
                large_mir,
                budget.safety_margin,
            ),
            PromptSection::new(
                ContentPriority::ReconstructedSource,
                "fn get_midpoint(a: u64, b: u64) -> u64 {\n    let _3 = a + b;\n    _3 / 2\n}"
                    .into(),
                budget.safety_margin,
            ),
        ];

        let effective_budget = budget.effective_prompt_budget(false);
        let (surviving, record) = truncate_to_budget(&sections, effective_budget);

        assert!(record.was_truncated);
        assert!(!record.sections_removed.is_empty());

        // Signature should always survive
        assert!(
            surviving.iter().any(|s| s.priority == ContentPriority::Signature),
            "signature must survive truncation"
        );

        // ReconstructedSource (lowest priority) should be removed before MirText
        if record.sections_removed.len() >= 2 {
            assert_eq!(
                record.sections_removed[0],
                ContentPriority::ReconstructedSource,
                "reconstructed source should be removed first"
            );
        }

        // Final tokens should be within budget (or close, given Signature protection)
        let final_total: usize = surviving.iter().map(|s| s.estimated_tokens).sum();
        assert_eq!(final_total, record.final_tokens);
    }
}
