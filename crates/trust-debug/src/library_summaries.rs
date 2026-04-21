// trust-debug/library_summaries.rs: Pre-computed libc specifications
//
// Models common libc entry points with summary-level semantics inspired by
// angr SimProcedures. These summaries let binary analyses reason about common
// calls without inlining their implementations.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use serde::{Deserialize, Serialize};

/// Pre-computed summary for a common library function.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct LibrarySummary {
    /// Function name as it appears in the binary.
    pub name: String,
    /// Abstract return classification used by the analyzer.
    pub return_type: ReturnSpec,
    /// Preconditions that must hold before the call.
    pub preconditions: Vec<Precondition>,
    /// Postconditions captured by the summary model.
    pub postconditions: Vec<Postcondition>,
    /// How taint flows through the function.
    pub taint_propagation: TaintPropagation,
    /// Observable side effects of the call.
    pub side_effects: Vec<SideEffect>,
    /// Coarse function family for reporting and lookup.
    pub category: FunctionCategory,
}

/// Abstract return specification for summarized functions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum ReturnSpec {
    Void,
    Pointer,
    Integer,
    Boolean,
    SizeT,
}

/// Preconditions that need to hold before a call.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum Precondition {
    NonNull { arg_index: usize },
    ValidBuffer { ptr_arg: usize, size_arg: usize },
    NonOverlapping { ptr1_arg: usize, size1_arg: usize, ptr2_arg: usize, size2_arg: usize },
    Positive { arg_index: usize },
    ValidFd { arg_index: usize },
}

/// Postconditions established by a summarized call.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum Postcondition {
    ReturnNonNull,
    ReturnInRange { min: i64, max: i64 },
    BufferWritten { ptr_arg: usize, size_arg: usize },
    NullTerminated { ptr_arg: usize },
    ReturnAllocated { size_arg: usize },
    Freed { ptr_arg: usize },
}

/// Taint propagation summary for a function.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct TaintPropagation {
    pub propagation_rules: Vec<TaintRule>,
}

/// Individual taint rule from a source to a sink.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct TaintRule {
    pub source: TaintSource,
    pub sink: TaintSink,
}

/// Places taint can originate from.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum TaintSource {
    Arg(usize),
    Return,
    Global(String),
}

/// Places taint can flow to.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum TaintSink {
    Arg(usize),
    Return,
    Memory { ptr_arg: usize },
}

/// Observable side effects used by the binary analyzer.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum SideEffect {
    AllocatesMemory,
    FreesMemory { ptr_arg: usize },
    WritesMemory { ptr_arg: usize },
    ReadsFile,
    WritesFile,
    NetworkIO,
    ModifiesGlobal(String),
}

/// Coarse function family.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum FunctionCategory {
    Memory,
    String,
    IO,
    Math,
    Process,
    Network,
    Sync,
}

/// Database of known library summaries keyed by function name.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct LibrarySummaryDb {
    summaries: FxHashMap<String, LibrarySummary>,
}

impl LibrarySummaryDb {
    /// Build a pre-populated summary database for common libc entry points.
    #[must_use]
    pub(crate) fn new() -> Self {
        let summaries =
            libc_summaries().into_iter().map(|summary| (summary.name.clone(), summary)).collect();
        Self { summaries }
    }

    /// Look up a summary by symbol name.
    #[must_use]
    pub(crate) fn lookup(&self, name: &str) -> Option<&LibrarySummary> {
        self.summaries.get(name)
    }

    /// Group summarized functions by category.
    #[must_use]
    pub(crate) fn categories(&self) -> FxHashMap<FunctionCategory, Vec<String>> {
        let mut categories = FxHashMap::default();

        for summary in self.summaries.values() {
            categories.entry(summary.category).or_insert_with(Vec::new).push(summary.name.clone());
        }

        for names in categories.values_mut() {
            names.sort();
        }

        categories
    }
}

impl Default for LibrarySummaryDb {
    fn default() -> Self {
        Self::new()
    }
}

fn libc_summaries() -> Vec<LibrarySummary> {
    vec![
        summary(
            "malloc",
            ReturnSpec::Pointer,
            vec![Precondition::Positive { arg_index: 0 }],
            vec![Postcondition::ReturnNonNull, Postcondition::ReturnAllocated { size_arg: 0 }],
            taint(vec![]),
            vec![SideEffect::AllocatesMemory],
            FunctionCategory::Memory,
        ),
        summary(
            "calloc",
            ReturnSpec::Pointer,
            vec![Precondition::Positive { arg_index: 0 }, Precondition::Positive { arg_index: 1 }],
            vec![Postcondition::ReturnNonNull, Postcondition::ReturnAllocated { size_arg: 1 }],
            taint(vec![]),
            vec![SideEffect::AllocatesMemory],
            FunctionCategory::Memory,
        ),
        summary(
            "realloc",
            ReturnSpec::Pointer,
            vec![Precondition::Positive { arg_index: 1 }],
            vec![Postcondition::ReturnNonNull, Postcondition::ReturnAllocated { size_arg: 1 }],
            taint(vec![arg_to_return(0)]),
            vec![SideEffect::AllocatesMemory, SideEffect::FreesMemory { ptr_arg: 0 }],
            FunctionCategory::Memory,
        ),
        summary(
            "free",
            ReturnSpec::Void,
            vec![Precondition::NonNull { arg_index: 0 }],
            vec![Postcondition::Freed { ptr_arg: 0 }],
            taint(vec![]),
            vec![SideEffect::FreesMemory { ptr_arg: 0 }],
            FunctionCategory::Memory,
        ),
        summary(
            "memcpy",
            ReturnSpec::Pointer,
            vec![
                Precondition::NonNull { arg_index: 0 },
                Precondition::NonNull { arg_index: 1 },
                Precondition::ValidBuffer { ptr_arg: 0, size_arg: 2 },
                Precondition::ValidBuffer { ptr_arg: 1, size_arg: 2 },
                Precondition::NonOverlapping {
                    ptr1_arg: 0,
                    size1_arg: 2,
                    ptr2_arg: 1,
                    size2_arg: 2,
                },
            ],
            vec![
                Postcondition::ReturnNonNull,
                Postcondition::BufferWritten { ptr_arg: 0, size_arg: 2 },
            ],
            taint(vec![arg_to_return(0), arg_to_memory(1, 0)]),
            vec![SideEffect::WritesMemory { ptr_arg: 0 }],
            FunctionCategory::Memory,
        ),
        summary(
            "memmove",
            ReturnSpec::Pointer,
            vec![
                Precondition::NonNull { arg_index: 0 },
                Precondition::NonNull { arg_index: 1 },
                Precondition::ValidBuffer { ptr_arg: 0, size_arg: 2 },
                Precondition::ValidBuffer { ptr_arg: 1, size_arg: 2 },
            ],
            vec![
                Postcondition::ReturnNonNull,
                Postcondition::BufferWritten { ptr_arg: 0, size_arg: 2 },
            ],
            taint(vec![arg_to_return(0), arg_to_memory(1, 0)]),
            vec![SideEffect::WritesMemory { ptr_arg: 0 }],
            FunctionCategory::Memory,
        ),
        summary(
            "memset",
            ReturnSpec::Pointer,
            vec![
                Precondition::NonNull { arg_index: 0 },
                Precondition::ValidBuffer { ptr_arg: 0, size_arg: 2 },
            ],
            vec![
                Postcondition::ReturnNonNull,
                Postcondition::BufferWritten { ptr_arg: 0, size_arg: 2 },
            ],
            taint(vec![arg_to_return(0), arg_to_memory(1, 0)]),
            vec![SideEffect::WritesMemory { ptr_arg: 0 }],
            FunctionCategory::Memory,
        ),
        summary(
            "memcmp",
            ReturnSpec::Integer,
            vec![
                Precondition::NonNull { arg_index: 0 },
                Precondition::NonNull { arg_index: 1 },
                Precondition::ValidBuffer { ptr_arg: 0, size_arg: 2 },
                Precondition::ValidBuffer { ptr_arg: 1, size_arg: 2 },
            ],
            vec![Postcondition::ReturnInRange { min: -255, max: 255 }],
            taint(vec![arg_to_return(0), arg_to_return(1)]),
            vec![],
            FunctionCategory::Memory,
        ),
        summary(
            "strlen",
            ReturnSpec::SizeT,
            vec![Precondition::NonNull { arg_index: 0 }],
            vec![Postcondition::ReturnInRange { min: 0, max: i64::MAX }],
            taint(vec![arg_to_return(0)]),
            vec![],
            FunctionCategory::String,
        ),
        summary(
            "strcpy",
            ReturnSpec::Pointer,
            vec![Precondition::NonNull { arg_index: 0 }, Precondition::NonNull { arg_index: 1 }],
            vec![Postcondition::ReturnNonNull, Postcondition::NullTerminated { ptr_arg: 0 }],
            taint(vec![arg_to_return(0), arg_to_memory(1, 0)]),
            vec![SideEffect::WritesMemory { ptr_arg: 0 }],
            FunctionCategory::String,
        ),
        summary(
            "strncpy",
            ReturnSpec::Pointer,
            vec![
                Precondition::NonNull { arg_index: 0 },
                Precondition::NonNull { arg_index: 1 },
                Precondition::ValidBuffer { ptr_arg: 0, size_arg: 2 },
                Precondition::ValidBuffer { ptr_arg: 1, size_arg: 2 },
            ],
            vec![
                Postcondition::ReturnNonNull,
                Postcondition::BufferWritten { ptr_arg: 0, size_arg: 2 },
            ],
            taint(vec![arg_to_return(0), arg_to_memory(1, 0)]),
            vec![SideEffect::WritesMemory { ptr_arg: 0 }],
            FunctionCategory::String,
        ),
        summary(
            "strcat",
            ReturnSpec::Pointer,
            vec![Precondition::NonNull { arg_index: 0 }, Precondition::NonNull { arg_index: 1 }],
            vec![Postcondition::ReturnNonNull, Postcondition::NullTerminated { ptr_arg: 0 }],
            taint(vec![arg_to_return(0), arg_to_memory(1, 0)]),
            vec![SideEffect::WritesMemory { ptr_arg: 0 }],
            FunctionCategory::String,
        ),
        summary(
            "strncat",
            ReturnSpec::Pointer,
            vec![
                Precondition::NonNull { arg_index: 0 },
                Precondition::NonNull { arg_index: 1 },
                Precondition::Positive { arg_index: 2 },
                Precondition::ValidBuffer { ptr_arg: 1, size_arg: 2 },
            ],
            vec![
                Postcondition::ReturnNonNull,
                Postcondition::NullTerminated { ptr_arg: 0 },
                Postcondition::BufferWritten { ptr_arg: 0, size_arg: 2 },
            ],
            taint(vec![arg_to_return(0), arg_to_memory(1, 0)]),
            vec![SideEffect::WritesMemory { ptr_arg: 0 }],
            FunctionCategory::String,
        ),
        summary(
            "strcmp",
            ReturnSpec::Integer,
            vec![Precondition::NonNull { arg_index: 0 }, Precondition::NonNull { arg_index: 1 }],
            vec![Postcondition::ReturnInRange { min: -255, max: 255 }],
            taint(vec![arg_to_return(0), arg_to_return(1)]),
            vec![],
            FunctionCategory::String,
        ),
        summary(
            "strncmp",
            ReturnSpec::Integer,
            vec![
                Precondition::NonNull { arg_index: 0 },
                Precondition::NonNull { arg_index: 1 },
                Precondition::Positive { arg_index: 2 },
                Precondition::ValidBuffer { ptr_arg: 0, size_arg: 2 },
                Precondition::ValidBuffer { ptr_arg: 1, size_arg: 2 },
            ],
            vec![Postcondition::ReturnInRange { min: -255, max: 255 }],
            taint(vec![arg_to_return(0), arg_to_return(1)]),
            vec![],
            FunctionCategory::String,
        ),
        summary(
            "printf",
            ReturnSpec::Integer,
            vec![Precondition::NonNull { arg_index: 0 }],
            vec![Postcondition::ReturnInRange { min: -1, max: i64::MAX }],
            taint(vec![arg_to_return(0)]),
            vec![SideEffect::WritesFile],
            FunctionCategory::IO,
        ),
        summary(
            "sprintf",
            ReturnSpec::Integer,
            vec![Precondition::NonNull { arg_index: 0 }, Precondition::NonNull { arg_index: 1 }],
            vec![
                Postcondition::NullTerminated { ptr_arg: 0 },
                Postcondition::ReturnInRange { min: -1, max: i64::MAX },
            ],
            taint(vec![arg_to_memory(1, 0), arg_to_return(1)]),
            vec![SideEffect::WritesMemory { ptr_arg: 0 }],
            FunctionCategory::IO,
        ),
        summary(
            "snprintf",
            ReturnSpec::Integer,
            vec![
                Precondition::NonNull { arg_index: 0 },
                Precondition::NonNull { arg_index: 2 },
                Precondition::Positive { arg_index: 1 },
                Precondition::ValidBuffer { ptr_arg: 0, size_arg: 1 },
            ],
            vec![
                Postcondition::BufferWritten { ptr_arg: 0, size_arg: 1 },
                Postcondition::NullTerminated { ptr_arg: 0 },
                Postcondition::ReturnInRange { min: -1, max: i64::MAX },
            ],
            taint(vec![arg_to_memory(2, 0), arg_to_return(2)]),
            vec![SideEffect::WritesMemory { ptr_arg: 0 }],
            FunctionCategory::IO,
        ),
        summary(
            "fprintf",
            ReturnSpec::Integer,
            vec![Precondition::NonNull { arg_index: 0 }, Precondition::NonNull { arg_index: 1 }],
            vec![Postcondition::ReturnInRange { min: -1, max: i64::MAX }],
            taint(vec![arg_to_arg(1, 0), arg_to_return(1)]),
            vec![SideEffect::WritesFile],
            FunctionCategory::IO,
        ),
        summary(
            "fopen",
            ReturnSpec::Pointer,
            vec![Precondition::NonNull { arg_index: 0 }, Precondition::NonNull { arg_index: 1 }],
            vec![Postcondition::ReturnNonNull],
            taint(vec![arg_to_return(0)]),
            vec![errno_side_effect()],
            FunctionCategory::IO,
        ),
        summary(
            "fclose",
            ReturnSpec::Integer,
            vec![Precondition::NonNull { arg_index: 0 }],
            vec![Postcondition::ReturnInRange { min: -1, max: 0 }],
            taint(vec![arg_to_return(0)]),
            vec![SideEffect::WritesFile, errno_side_effect()],
            FunctionCategory::IO,
        ),
        summary(
            "fread",
            ReturnSpec::SizeT,
            vec![
                Precondition::NonNull { arg_index: 0 },
                Precondition::NonNull { arg_index: 3 },
                Precondition::Positive { arg_index: 1 },
                Precondition::Positive { arg_index: 2 },
                Precondition::ValidBuffer { ptr_arg: 0, size_arg: 1 },
            ],
            vec![
                Postcondition::BufferWritten { ptr_arg: 0, size_arg: 1 },
                Postcondition::ReturnInRange { min: 0, max: i64::MAX },
            ],
            taint(vec![global_to_memory("file_contents", 0), arg_to_return(3)]),
            vec![SideEffect::ReadsFile, SideEffect::WritesMemory { ptr_arg: 0 }],
            FunctionCategory::IO,
        ),
        summary(
            "fwrite",
            ReturnSpec::SizeT,
            vec![
                Precondition::NonNull { arg_index: 0 },
                Precondition::NonNull { arg_index: 3 },
                Precondition::Positive { arg_index: 1 },
                Precondition::Positive { arg_index: 2 },
                Precondition::ValidBuffer { ptr_arg: 0, size_arg: 1 },
            ],
            vec![Postcondition::ReturnInRange { min: 0, max: i64::MAX }],
            taint(vec![arg_to_arg(0, 3), arg_to_return(2)]),
            vec![SideEffect::WritesFile],
            FunctionCategory::IO,
        ),
        summary(
            "read",
            ReturnSpec::Integer,
            vec![
                Precondition::ValidFd { arg_index: 0 },
                Precondition::NonNull { arg_index: 1 },
                Precondition::Positive { arg_index: 2 },
                Precondition::ValidBuffer { ptr_arg: 1, size_arg: 2 },
            ],
            vec![
                Postcondition::BufferWritten { ptr_arg: 1, size_arg: 2 },
                Postcondition::ReturnInRange { min: -1, max: i64::MAX },
            ],
            taint(vec![global_to_memory("fd_contents", 1), arg_to_return(0)]),
            vec![
                SideEffect::ReadsFile,
                SideEffect::WritesMemory { ptr_arg: 1 },
                errno_side_effect(),
            ],
            FunctionCategory::IO,
        ),
        summary(
            "write",
            ReturnSpec::Integer,
            vec![
                Precondition::ValidFd { arg_index: 0 },
                Precondition::NonNull { arg_index: 1 },
                Precondition::Positive { arg_index: 2 },
                Precondition::ValidBuffer { ptr_arg: 1, size_arg: 2 },
            ],
            vec![Postcondition::ReturnInRange { min: -1, max: i64::MAX }],
            taint(vec![arg_to_arg(1, 0), arg_to_return(2)]),
            vec![SideEffect::WritesFile, errno_side_effect()],
            FunctionCategory::IO,
        ),
        summary(
            "open",
            ReturnSpec::Integer,
            vec![Precondition::NonNull { arg_index: 0 }],
            vec![Postcondition::ReturnInRange { min: -1, max: i64::MAX }],
            taint(vec![arg_to_return(0)]),
            vec![errno_side_effect()],
            FunctionCategory::IO,
        ),
        summary(
            "close",
            ReturnSpec::Integer,
            vec![Precondition::ValidFd { arg_index: 0 }],
            vec![Postcondition::ReturnInRange { min: -1, max: 0 }],
            taint(vec![arg_to_return(0)]),
            vec![errno_side_effect()],
            FunctionCategory::IO,
        ),
        summary(
            "socket",
            ReturnSpec::Integer,
            vec![],
            vec![Postcondition::ReturnInRange { min: -1, max: i64::MAX }],
            taint(vec![arg_to_return(0), arg_to_return(1)]),
            vec![SideEffect::NetworkIO, errno_side_effect()],
            FunctionCategory::Network,
        ),
        summary(
            "connect",
            ReturnSpec::Integer,
            vec![
                Precondition::ValidFd { arg_index: 0 },
                Precondition::NonNull { arg_index: 1 },
                Precondition::Positive { arg_index: 2 },
            ],
            vec![Postcondition::ReturnInRange { min: -1, max: 0 }],
            taint(vec![arg_to_arg(1, 0), arg_to_return(1)]),
            vec![SideEffect::NetworkIO, errno_side_effect()],
            FunctionCategory::Network,
        ),
        summary(
            "send",
            ReturnSpec::Integer,
            vec![
                Precondition::ValidFd { arg_index: 0 },
                Precondition::NonNull { arg_index: 1 },
                Precondition::Positive { arg_index: 2 },
                Precondition::ValidBuffer { ptr_arg: 1, size_arg: 2 },
            ],
            vec![Postcondition::ReturnInRange { min: -1, max: i64::MAX }],
            taint(vec![arg_to_arg(1, 0), arg_to_return(2)]),
            vec![SideEffect::NetworkIO, errno_side_effect()],
            FunctionCategory::Network,
        ),
        summary(
            "recv",
            ReturnSpec::Integer,
            vec![
                Precondition::ValidFd { arg_index: 0 },
                Precondition::NonNull { arg_index: 1 },
                Precondition::Positive { arg_index: 2 },
                Precondition::ValidBuffer { ptr_arg: 1, size_arg: 2 },
            ],
            vec![
                Postcondition::BufferWritten { ptr_arg: 1, size_arg: 2 },
                Postcondition::ReturnInRange { min: -1, max: i64::MAX },
            ],
            taint(vec![global_to_memory("network_input", 1), arg_to_return(0)]),
            vec![
                SideEffect::NetworkIO,
                SideEffect::WritesMemory { ptr_arg: 1 },
                errno_side_effect(),
            ],
            FunctionCategory::Network,
        ),
    ]
}

fn summary(
    name: &str,
    return_type: ReturnSpec,
    preconditions: Vec<Precondition>,
    postconditions: Vec<Postcondition>,
    taint_propagation: TaintPropagation,
    side_effects: Vec<SideEffect>,
    category: FunctionCategory,
) -> LibrarySummary {
    LibrarySummary {
        name: name.to_string(),
        return_type,
        preconditions,
        postconditions,
        taint_propagation,
        side_effects,
        category,
    }
}

fn taint(propagation_rules: Vec<TaintRule>) -> TaintPropagation {
    TaintPropagation { propagation_rules }
}

fn arg_to_return(arg_index: usize) -> TaintRule {
    TaintRule { source: TaintSource::Arg(arg_index), sink: TaintSink::Return }
}

fn arg_to_arg(source_arg: usize, sink_arg: usize) -> TaintRule {
    TaintRule { source: TaintSource::Arg(source_arg), sink: TaintSink::Arg(sink_arg) }
}

fn arg_to_memory(source_arg: usize, ptr_arg: usize) -> TaintRule {
    TaintRule { source: TaintSource::Arg(source_arg), sink: TaintSink::Memory { ptr_arg } }
}

fn global_to_memory(name: &str, ptr_arg: usize) -> TaintRule {
    TaintRule { source: TaintSource::Global(name.to_string()), sink: TaintSink::Memory { ptr_arg } }
}

fn errno_side_effect() -> SideEffect {
    SideEffect::ModifiesGlobal("errno".to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lookup_malloc() {
        let db = LibrarySummaryDb::new();
        let malloc = db.lookup("malloc").expect("malloc summary should exist");

        assert_eq!(malloc.return_type, ReturnSpec::Pointer);
        assert_eq!(malloc.category, FunctionCategory::Memory);
        assert!(malloc.preconditions.contains(&Precondition::Positive { arg_index: 0 }));
        assert!(malloc.postconditions.contains(&Postcondition::ReturnAllocated { size_arg: 0 }));
        assert!(malloc.side_effects.contains(&SideEffect::AllocatesMemory));
    }

    #[test]
    fn test_lookup_free() {
        let db = LibrarySummaryDb::new();
        let free = db.lookup("free").expect("free summary should exist");

        assert_eq!(free.return_type, ReturnSpec::Void);
        assert!(free.preconditions.contains(&Precondition::NonNull { arg_index: 0 }));
        assert!(free.postconditions.contains(&Postcondition::Freed { ptr_arg: 0 }));
        assert!(free.side_effects.contains(&SideEffect::FreesMemory { ptr_arg: 0 }));
    }

    #[test]
    fn test_lookup_memcpy() {
        let db = LibrarySummaryDb::new();
        let memcpy = db.lookup("memcpy").expect("memcpy summary should exist");

        assert_eq!(memcpy.category, FunctionCategory::Memory);
        assert!(memcpy.preconditions.contains(&Precondition::NonOverlapping {
            ptr1_arg: 0,
            size1_arg: 2,
            ptr2_arg: 1,
            size2_arg: 2,
        }));
        assert!(
            memcpy
                .postconditions
                .contains(&Postcondition::BufferWritten { ptr_arg: 0, size_arg: 2 })
        );
    }

    #[test]
    fn test_all_summaries_have_category() {
        let db = LibrarySummaryDb::new();
        let categories = db.categories();

        assert!(db.summaries.len() >= 31);

        let categorized_count: usize = categories.values().map(Vec::len).sum();
        assert_eq!(categorized_count, db.summaries.len());

        for (name, summary) in &db.summaries {
            let names = categories.get(&summary.category).expect("category should be present");
            assert!(names.contains(name));
        }
    }

    #[test]
    fn test_taint_propagation_memcpy() {
        let db = LibrarySummaryDb::new();
        let memcpy = db.lookup("memcpy").expect("memcpy summary should exist");
        let expected_rule =
            TaintRule { source: TaintSource::Arg(1), sink: TaintSink::Memory { ptr_arg: 0 } };

        assert!(memcpy.taint_propagation.propagation_rules.contains(&expected_rule));
    }

    #[test]
    fn test_missing_function_returns_none() {
        let db = LibrarySummaryDb::new();
        assert!(db.lookup("definitely_not_libc").is_none());
    }
}
