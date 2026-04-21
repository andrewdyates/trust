// trust-strengthen/llm_token_budget.rs: Token budget management for AI Model API prompts.
//
// Estimates token counts and truncates prompt sections by priority to stay within
// the model's context window. Uses a chars/4 approximation for token estimation.
//
// Part of Phase 5 (#613): Token budget management for AI Model API prompts.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Priority level for prompt sections. Higher-priority sections are kept first
/// when the prompt must be truncated to fit the token budget.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Priority {
    /// Lowest priority: example code or few-shot demonstrations.
    Examples = 0,
    /// Context from callers or surrounding code.
    CallerContext = 1,
    /// The function body being analyzed — core to the task.
    FunctionBody = 2,
    /// System-level instructions — highest priority, always kept.
    SystemPrompt = 3,
}

/// Token budget configuration for a model.
#[derive(Debug, Clone)]
pub struct TokenBudget {
    /// Total context window size in tokens (e.g. 200_000 for AI Model Sonnet).
    pub model_context_size: usize,
    /// Tokens reserved for the model's response.
    pub reserved_for_response: usize,
    /// Maximum tokens available for the prompt (computed from the above two).
    pub max_prompt_tokens: usize,
}

impl TokenBudget {
    /// Create a new token budget.
    ///
    /// `max_prompt_tokens` is computed as `model_context_size - reserved_for_response`.
    /// If `reserved_for_response >= model_context_size`, `max_prompt_tokens` is 0.
    pub fn new(model_context_size: usize, reserved_for_response: usize) -> Self {
        let max_prompt_tokens = model_context_size.saturating_sub(reserved_for_response);
        Self {
            model_context_size,
            reserved_for_response,
            max_prompt_tokens,
        }
    }
}

impl Default for TokenBudget {
    fn default() -> Self {
        // AI Model Sonnet default: 200k context, 1024 reserved for response.
        Self::new(200_000, 1024)
    }
}

/// Estimate the token count for a text string.
///
/// Uses the chars/4 approximation, which is a reasonable estimate for English
/// text and code with the AI Model tokenizer. This avoids depending on a full
/// tokenizer library while being accurate enough for budget management.
pub fn estimate_tokens(text: &str) -> usize {
    // chars/4, minimum 1 token for non-empty text.
    let char_count = text.chars().count();
    if char_count == 0 {
        return 0;
    }
    char_count.div_ceil(4) // ceiling division
}

/// Truncate prompt sections to fit within the token budget.
///
/// Sections are provided as `(Priority, String)` pairs. Higher-priority sections
/// are kept first. Within the same priority level, earlier sections take precedence.
///
/// If all sections fit within the budget, they are concatenated in input order
/// with double-newline separators. If they don't fit, lowest-priority sections
/// are dropped first. If a single section exceeds the remaining budget, it is
/// truncated at a character boundary that fits.
///
/// Returns the concatenated prompt string that fits within the budget.
pub fn truncate_to_budget(sections: Vec<(Priority, String)>, budget: &TokenBudget) -> String {
    if sections.is_empty() {
        return String::new();
    }

    let max_tokens = budget.max_prompt_tokens;

    // Sort sections by priority (descending) while preserving original index
    // for stable ordering within the same priority.
    let mut indexed: Vec<(usize, Priority, String)> = sections
        .into_iter()
        .enumerate()
        .map(|(i, (p, s))| (i, p, s))
        .collect();
    indexed.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));

    // Greedily add sections in priority order until budget is exhausted.
    let mut kept: Vec<(usize, String)> = Vec::new();
    let mut used_tokens: usize = 0;

    for (orig_idx, _priority, text) in indexed {
        let section_tokens = estimate_tokens(&text);
        // Account for separator tokens (double newline ~ 1 token).
        let separator_cost = if kept.is_empty() { 0 } else { 1 };

        if used_tokens + separator_cost + section_tokens <= max_tokens {
            // Entire section fits.
            used_tokens += separator_cost + section_tokens;
            kept.push((orig_idx, text));
        } else {
            // Try to fit a truncated version.
            let remaining = max_tokens.saturating_sub(used_tokens + separator_cost);
            if remaining > 0 {
                let max_chars = remaining * 4; // inverse of chars/4
                let truncated: String = text.chars().take(max_chars).collect();
                if !truncated.is_empty() {
                    // No need to update used_tokens — we break immediately after.
                    let _ = separator_cost;
                    kept.push((orig_idx, truncated));
                }
            }
            break; // Budget exhausted.
        }
    }

    // Restore original order for output.
    kept.sort_by_key(|(idx, _)| *idx);

    kept.into_iter()
        .map(|(_, text)| text)
        .collect::<Vec<_>>()
        .join("\n\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- estimate_tokens tests --

    #[test]
    fn test_estimate_tokens_empty() {
        assert_eq!(estimate_tokens(""), 0);
    }

    #[test]
    fn test_estimate_tokens_short() {
        // "hi" = 2 chars => (2+3)/4 = 1 token
        assert_eq!(estimate_tokens("hi"), 1);
    }

    #[test]
    fn test_estimate_tokens_four_chars() {
        // "abcd" = 4 chars => (4+3)/4 = 1 token
        assert_eq!(estimate_tokens("abcd"), 1);
    }

    #[test]
    fn test_estimate_tokens_five_chars() {
        // "abcde" = 5 chars => (5+3)/4 = 2 tokens
        assert_eq!(estimate_tokens("abcde"), 2);
    }

    #[test]
    fn test_estimate_tokens_longer_text() {
        // 100 chars => (100+3)/4 = 25 tokens
        let text = "a".repeat(100);
        assert_eq!(estimate_tokens(&text), 25);
    }

    #[test]
    fn test_estimate_tokens_unicode() {
        // Unicode chars count as chars, not bytes.
        // 4 unicode chars => (4+3)/4 = 1 token
        assert_eq!(estimate_tokens("\u{00e9}\u{00e9}\u{00e9}\u{00e9}"), 1);
    }

    // -- TokenBudget tests --

    #[test]
    fn test_token_budget_new() {
        let budget = TokenBudget::new(100_000, 2048);
        assert_eq!(budget.model_context_size, 100_000);
        assert_eq!(budget.reserved_for_response, 2048);
        assert_eq!(budget.max_prompt_tokens, 97_952);
    }

    #[test]
    fn test_token_budget_default() {
        let budget = TokenBudget::default();
        assert_eq!(budget.model_context_size, 200_000);
        assert_eq!(budget.reserved_for_response, 1024);
        assert_eq!(budget.max_prompt_tokens, 198_976);
    }

    #[test]
    fn test_token_budget_overflow_protection() {
        // reserved >= context => max_prompt_tokens = 0
        let budget = TokenBudget::new(1000, 2000);
        assert_eq!(budget.max_prompt_tokens, 0);
    }

    // -- Priority ordering tests --

    #[test]
    fn test_priority_ordering() {
        assert!(Priority::SystemPrompt > Priority::FunctionBody);
        assert!(Priority::FunctionBody > Priority::CallerContext);
        assert!(Priority::CallerContext > Priority::Examples);
    }

    // -- truncate_to_budget tests --

    #[test]
    fn test_truncate_empty_sections() {
        let budget = TokenBudget::default();
        assert_eq!(truncate_to_budget(vec![], &budget), "");
    }

    #[test]
    fn test_truncate_all_fit() {
        let budget = TokenBudget::new(1000, 0);
        let sections = vec![
            (Priority::SystemPrompt, "System instructions.".to_string()),
            (Priority::FunctionBody, "fn foo() {}".to_string()),
        ];
        let result = truncate_to_budget(sections, &budget);
        // Both should be present in original order.
        assert!(result.contains("System instructions."));
        assert!(result.contains("fn foo() {}"));
        // Original order preserved.
        assert!(result.find("System").unwrap() < result.find("fn foo").unwrap());
    }

    #[test]
    fn test_truncate_drops_low_priority_first() {
        // Budget fits ~10 tokens = ~40 chars.
        let budget = TokenBudget::new(12, 0);
        let sections = vec![
            (Priority::Examples, "This is a long example section that exceeds budget".to_string()),
            (Priority::SystemPrompt, "Keep this.".to_string()),
        ];
        let result = truncate_to_budget(sections, &budget);
        // SystemPrompt should be kept, Examples should be dropped or truncated.
        assert!(result.contains("Keep this."));
    }

    #[test]
    fn test_truncate_preserves_original_order() {
        let budget = TokenBudget::new(10000, 0);
        let sections = vec![
            (Priority::CallerContext, "AAA".to_string()),
            (Priority::SystemPrompt, "BBB".to_string()),
            (Priority::FunctionBody, "CCC".to_string()),
        ];
        let result = truncate_to_budget(sections, &budget);
        // Output should be in original order: AAA, BBB, CCC
        let pos_a = result.find("AAA").unwrap();
        let pos_b = result.find("BBB").unwrap();
        let pos_c = result.find("CCC").unwrap();
        assert!(pos_a < pos_b);
        assert!(pos_b < pos_c);
    }

    #[test]
    fn test_truncate_section_gets_truncated() {
        // Budget for ~5 tokens = ~20 chars total.
        let budget = TokenBudget::new(5, 0);
        let sections = vec![
            (Priority::SystemPrompt, "a".repeat(100)),
        ];
        let result = truncate_to_budget(sections, &budget);
        // Result should be truncated, not the full 100 chars.
        assert!(result.len() <= 20);
        assert!(!result.is_empty());
    }

    #[test]
    fn test_truncate_zero_budget() {
        let budget = TokenBudget::new(0, 0);
        let sections = vec![
            (Priority::SystemPrompt, "anything".to_string()),
        ];
        let result = truncate_to_budget(sections, &budget);
        assert!(result.is_empty());
    }

    #[test]
    fn test_truncate_budget_equals_reserved() {
        // All budget reserved for response => 0 for prompt.
        let budget = TokenBudget::new(1000, 1000);
        let sections = vec![
            (Priority::SystemPrompt, "hello".to_string()),
        ];
        let result = truncate_to_budget(sections, &budget);
        assert!(result.is_empty());
    }

    #[test]
    fn test_truncate_multiple_same_priority() {
        // When priorities are the same, earlier sections kept first.
        let budget = TokenBudget::new(5, 0); // ~20 chars
        let sections = vec![
            (Priority::FunctionBody, "first".to_string()),
            (Priority::FunctionBody, "second".to_string()),
        ];
        let result = truncate_to_budget(sections, &budget);
        assert!(result.contains("first"));
    }

    #[test]
    fn test_truncate_real_world_scenario() {
        // Simulate a real prompt with system prompt + function body + examples.
        let budget = TokenBudget::new(200_000, 1024);
        let system = "You are a formal verification expert.".to_string();
        let body = "fn get_midpoint(a: u64, b: u64) -> u64 { (a + b) / 2 }".to_string();
        let examples = "Example: #[requires(\"a <= u64::MAX - b\")]".to_string();
        let caller = "Called from fn main() with arbitrary u64 values.".to_string();

        let sections = vec![
            (Priority::SystemPrompt, system.clone()),
            (Priority::FunctionBody, body.clone()),
            (Priority::Examples, examples.clone()),
            (Priority::CallerContext, caller.clone()),
        ];
        let result = truncate_to_budget(sections, &budget);
        // Everything should fit in 200k context.
        assert!(result.contains(&system));
        assert!(result.contains(&body));
        assert!(result.contains(&examples));
        assert!(result.contains(&caller));
    }
}
