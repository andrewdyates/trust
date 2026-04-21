// trust-symex/heap.rs: Symbolic heap modeling (#251)
//
// Models heap allocations symbolically for detecting memory safety
// violations: use-after-free, double-free, heap buffer overflow.
// Builds on the memory.rs object-based model with allocation tracking.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use crate::state::SymbolicValue;

// ---------------------------------------------------------------------------
// Allocation state machine
// ---------------------------------------------------------------------------

/// State of a heap allocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum AllocState {
    /// Memory is allocated and valid for access.
    Allocated,
    /// Memory has been freed; accessing it is use-after-free.
    Freed,
}

impl std::fmt::Display for AllocState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Allocated => write!(f, "allocated"),
            Self::Freed => write!(f, "freed"),
        }
    }
}

/// A heap region with symbolic size and bounds.
#[derive(Debug, Clone)]
pub(crate) struct HeapRegion {
    /// Unique allocation ID.
    pub id: u64,
    /// Symbolic or concrete size in bytes.
    pub size: SymbolicValue,
    /// Current state.
    pub state: AllocState,
    /// Contents: offset -> symbolic value.
    pub contents: FxHashMap<u64, SymbolicValue>,
    /// Source location hint for diagnostics.
    pub alloc_site: String,
}

impl HeapRegion {
    /// Create a new allocated region.
    pub(crate) fn new(id: u64, size: SymbolicValue, alloc_site: impl Into<String>) -> Self {
        Self {
            id,
            size,
            state: AllocState::Allocated,
            contents: FxHashMap::default(),
            alloc_site: alloc_site.into(),
        }
    }

    /// Mark this region as freed.
    pub(crate) fn free(&mut self) {
        self.state = AllocState::Freed;
    }

    /// Check if this region is still allocated.
    #[must_use]
    pub(crate) fn is_allocated(&self) -> bool {
        self.state == AllocState::Allocated
    }
}

// ---------------------------------------------------------------------------
// Heap error types
// ---------------------------------------------------------------------------

/// A heap safety violation detected during symbolic execution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum HeapViolation {
    /// Access to freed memory.
    UseAfterFree {
        alloc_id: u64,
        alloc_site: String,
        access_offset: u64,
    },
    /// Freeing already-freed memory.
    DoubleFree {
        alloc_id: u64,
        alloc_site: String,
    },
    /// Access beyond allocation bounds.
    HeapOverflow {
        alloc_id: u64,
        alloc_site: String,
        access_offset: u64,
        alloc_size: u64,
    },
    /// Freeing a pointer that was never allocated.
    InvalidFree {
        alloc_id: u64,
    },
    /// Memory leak: allocated but never freed on all paths.
    MemoryLeak {
        alloc_id: u64,
        alloc_site: String,
    },
}

impl std::fmt::Display for HeapViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UseAfterFree { alloc_id, alloc_site, access_offset } => {
                write!(f, "use-after-free: alloc #{alloc_id} (at {alloc_site}), offset {access_offset}")
            }
            Self::DoubleFree { alloc_id, alloc_site } => {
                write!(f, "double-free: alloc #{alloc_id} (at {alloc_site})")
            }
            Self::HeapOverflow { alloc_id, alloc_site, access_offset, alloc_size } => {
                write!(
                    f,
                    "heap overflow: alloc #{alloc_id} (at {alloc_site}), access at offset {access_offset}, size {alloc_size}"
                )
            }
            Self::InvalidFree { alloc_id } => {
                write!(f, "invalid free: alloc #{alloc_id} not found")
            }
            Self::MemoryLeak { alloc_id, alloc_site } => {
                write!(f, "memory leak: alloc #{alloc_id} (at {alloc_site}) never freed")
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Symbolic heap
// ---------------------------------------------------------------------------

/// Symbolic heap model tracking allocations and detecting violations.
pub(crate) struct SymbolicHeap {
    /// All heap regions, keyed by allocation ID.
    regions: FxHashMap<u64, HeapRegion>,
    /// Next allocation ID to assign.
    next_id: u64,
    /// Detected violations.
    violations: Vec<HeapViolation>,
}

impl SymbolicHeap {
    /// Create a new empty heap.
    pub(crate) fn new() -> Self {
        Self {
            regions: FxHashMap::default(),
            next_id: 1,
            violations: Vec::new(),
        }
    }

    /// Allocate a new heap region.
    ///
    /// Returns the allocation ID for subsequent read/write/free.
    pub(crate) fn alloc(&mut self, size: SymbolicValue, site: impl Into<String>) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        let region = HeapRegion::new(id, size, site);
        self.regions.insert(id, region);
        id
    }

    /// Free a heap region by allocation ID.
    ///
    /// Records DoubleFree if already freed, InvalidFree if unknown.
    pub(crate) fn free(&mut self, alloc_id: u64) {
        match self.regions.get_mut(&alloc_id) {
            Some(region) if region.state == AllocState::Freed => {
                self.violations.push(HeapViolation::DoubleFree {
                    alloc_id,
                    alloc_site: region.alloc_site.clone(),
                });
            }
            Some(region) => {
                region.free();
            }
            None => {
                self.violations.push(HeapViolation::InvalidFree { alloc_id });
            }
        }
    }

    /// Read from a heap region at the given offset.
    ///
    /// Returns the symbolic value, or records a violation.
    pub(crate) fn read(&mut self, alloc_id: u64, offset: u64) -> Option<SymbolicValue> {
        match self.regions.get(&alloc_id) {
            Some(region) if region.state == AllocState::Freed => {
                self.violations.push(HeapViolation::UseAfterFree {
                    alloc_id,
                    alloc_site: region.alloc_site.clone(),
                    access_offset: offset,
                });
                None
            }
            Some(region) => {
                // Check bounds if size is concrete.
                if let SymbolicValue::Concrete(size) = &region.size
                    && offset >= *size as u64 {
                        self.violations.push(HeapViolation::HeapOverflow {
                            alloc_id,
                            alloc_site: region.alloc_site.clone(),
                            access_offset: offset,
                            alloc_size: *size as u64,
                        });
                        return None;
                    }
                region.contents.get(&offset).cloned()
            }
            None => {
                self.violations.push(HeapViolation::InvalidFree { alloc_id });
                None
            }
        }
    }

    /// Write to a heap region at the given offset.
    ///
    /// Records violations for use-after-free or overflow.
    pub(crate) fn write(&mut self, alloc_id: u64, offset: u64, value: SymbolicValue) -> bool {
        match self.regions.get_mut(&alloc_id) {
            Some(region) if region.state == AllocState::Freed => {
                self.violations.push(HeapViolation::UseAfterFree {
                    alloc_id,
                    alloc_site: region.alloc_site.clone(),
                    access_offset: offset,
                });
                false
            }
            Some(region) => {
                // Check bounds if size is concrete.
                if let SymbolicValue::Concrete(size) = &region.size
                    && offset >= *size as u64 {
                        self.violations.push(HeapViolation::HeapOverflow {
                            alloc_id,
                            alloc_site: region.alloc_site.clone(),
                            access_offset: offset,
                            alloc_size: *size as u64,
                        });
                        return false;
                    }
                region.contents.insert(offset, value);
                true
            }
            None => {
                self.violations.push(HeapViolation::InvalidFree { alloc_id });
                false
            }
        }
    }

    /// Check for memory leaks: allocated regions that were never freed.
    pub(crate) fn check_leaks(&mut self) {
        let leaks: Vec<_> = self.regions.values()
            .filter(|r| r.state == AllocState::Allocated)
            .map(|r| HeapViolation::MemoryLeak {
                alloc_id: r.id,
                alloc_site: r.alloc_site.clone(),
            })
            .collect();
        self.violations.extend(leaks);
    }

    /// Take a snapshot of the current heap state for path merging.
    #[must_use]
    pub(crate) fn snapshot(&self) -> HeapSnapshot {
        HeapSnapshot {
            regions: self.regions.clone(),
            next_id: self.next_id,
        }
    }

    /// Restore heap state from a snapshot.
    pub(crate) fn restore(&mut self, snapshot: &HeapSnapshot) {
        self.regions = snapshot.regions.clone();
        self.next_id = snapshot.next_id;
    }

    /// Get all detected violations.
    #[must_use]
    pub(crate) fn violations(&self) -> &[HeapViolation] {
        &self.violations
    }

    /// Get the number of active allocations.
    #[must_use]
    pub(crate) fn active_allocations(&self) -> usize {
        self.regions.values().filter(|r| r.is_allocated()).count()
    }

    /// Get the total number of allocations ever made.
    #[must_use]
    pub(crate) fn total_allocations(&self) -> u64 {
        self.next_id - 1
    }

    /// Clear all violations.
    pub(crate) fn clear_violations(&mut self) {
        self.violations.clear();
    }
}

impl Default for SymbolicHeap {
    fn default() -> Self {
        Self::new()
    }
}

/// Snapshot of heap state for path exploration.
#[derive(Debug, Clone)]
pub(crate) struct HeapSnapshot {
    /// Heap regions at snapshot time.
    pub regions: FxHashMap<u64, HeapRegion>,
    /// Next allocation ID.
    pub next_id: u64,
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alloc_and_free() {
        let mut heap = SymbolicHeap::new();
        let id = heap.alloc(SymbolicValue::Concrete(64), "test_alloc");
        assert_eq!(heap.active_allocations(), 1);
        heap.free(id);
        assert_eq!(heap.active_allocations(), 0);
        assert!(heap.violations().is_empty());
    }

    #[test]
    fn test_double_free() {
        let mut heap = SymbolicHeap::new();
        let id = heap.alloc(SymbolicValue::Concrete(64), "test_alloc");
        heap.free(id);
        heap.free(id); // double free!
        assert_eq!(heap.violations().len(), 1);
        assert!(matches!(heap.violations()[0], HeapViolation::DoubleFree { .. }));
    }

    #[test]
    fn test_use_after_free_read() {
        let mut heap = SymbolicHeap::new();
        let id = heap.alloc(SymbolicValue::Concrete(64), "test_alloc");
        heap.write(id, 0, SymbolicValue::Concrete(42));
        heap.free(id);
        let result = heap.read(id, 0);
        assert!(result.is_none());
        assert_eq!(heap.violations().len(), 1);
        assert!(matches!(heap.violations()[0], HeapViolation::UseAfterFree { .. }));
    }

    #[test]
    fn test_use_after_free_write() {
        let mut heap = SymbolicHeap::new();
        let id = heap.alloc(SymbolicValue::Concrete(64), "test_alloc");
        heap.free(id);
        let ok = heap.write(id, 0, SymbolicValue::Concrete(42));
        assert!(!ok);
        assert!(matches!(heap.violations()[0], HeapViolation::UseAfterFree { .. }));
    }

    #[test]
    fn test_heap_overflow_read() {
        let mut heap = SymbolicHeap::new();
        let id = heap.alloc(SymbolicValue::Concrete(8), "test_alloc");
        let result = heap.read(id, 10); // offset 10 > size 8
        assert!(result.is_none());
        assert!(matches!(heap.violations()[0], HeapViolation::HeapOverflow { .. }));
    }

    #[test]
    fn test_heap_overflow_write() {
        let mut heap = SymbolicHeap::new();
        let id = heap.alloc(SymbolicValue::Concrete(8), "test_alloc");
        let ok = heap.write(id, 10, SymbolicValue::Concrete(0));
        assert!(!ok);
        assert!(matches!(heap.violations()[0], HeapViolation::HeapOverflow { .. }));
    }

    #[test]
    fn test_invalid_free() {
        let mut heap = SymbolicHeap::new();
        heap.free(999); // never allocated
        assert!(matches!(heap.violations()[0], HeapViolation::InvalidFree { alloc_id: 999 }));
    }

    #[test]
    fn test_memory_leak_detection() {
        let mut heap = SymbolicHeap::new();
        heap.alloc(SymbolicValue::Concrete(64), "leak1");
        heap.alloc(SymbolicValue::Concrete(32), "leak2");
        heap.check_leaks();
        assert_eq!(heap.violations().len(), 2);
        assert!(heap.violations().iter().all(|v| matches!(v, HeapViolation::MemoryLeak { .. })));
    }

    #[test]
    fn test_no_leak_when_freed() {
        let mut heap = SymbolicHeap::new();
        let id1 = heap.alloc(SymbolicValue::Concrete(64), "a");
        let id2 = heap.alloc(SymbolicValue::Concrete(32), "b");
        heap.free(id1);
        heap.free(id2);
        heap.check_leaks();
        assert!(heap.violations().is_empty());
    }

    #[test]
    fn test_read_write_roundtrip() {
        let mut heap = SymbolicHeap::new();
        let id = heap.alloc(SymbolicValue::Concrete(64), "test");
        heap.write(id, 0, SymbolicValue::Concrete(42));
        heap.write(id, 8, SymbolicValue::Concrete(99));
        assert_eq!(heap.read(id, 0), Some(SymbolicValue::Concrete(42)));
        assert_eq!(heap.read(id, 8), Some(SymbolicValue::Concrete(99)));
        assert_eq!(heap.read(id, 16), None); // unwritten but in bounds (64 bytes)
        assert!(heap.violations().is_empty());
    }

    #[test]
    fn test_snapshot_restore() {
        let mut heap = SymbolicHeap::new();
        let id = heap.alloc(SymbolicValue::Concrete(64), "test");
        heap.write(id, 0, SymbolicValue::Concrete(42));
        let snap = heap.snapshot();

        // Modify after snapshot.
        heap.write(id, 0, SymbolicValue::Concrete(99));
        heap.free(id);

        // Restore — should see original state.
        heap.restore(&snap);
        assert_eq!(heap.active_allocations(), 1);
        assert_eq!(heap.read(id, 0), Some(SymbolicValue::Concrete(42)));
    }

    #[test]
    fn test_total_allocations() {
        let mut heap = SymbolicHeap::new();
        heap.alloc(SymbolicValue::Concrete(8), "a");
        heap.alloc(SymbolicValue::Concrete(8), "b");
        heap.alloc(SymbolicValue::Concrete(8), "c");
        assert_eq!(heap.total_allocations(), 3);
    }

    #[test]
    fn test_alloc_state_display() {
        assert_eq!(AllocState::Allocated.to_string(), "allocated");
        assert_eq!(AllocState::Freed.to_string(), "freed");
    }

    #[test]
    fn test_violation_display() {
        let v = HeapViolation::UseAfterFree {
            alloc_id: 1,
            alloc_site: "main.rs:10".into(),
            access_offset: 0,
        };
        assert!(v.to_string().contains("use-after-free"));

        let v = HeapViolation::DoubleFree {
            alloc_id: 2,
            alloc_site: "lib.rs:20".into(),
        };
        assert!(v.to_string().contains("double-free"));
    }

    #[test]
    fn test_clear_violations() {
        let mut heap = SymbolicHeap::new();
        heap.free(999);
        assert!(!heap.violations().is_empty());
        heap.clear_violations();
        assert!(heap.violations().is_empty());
    }
}
