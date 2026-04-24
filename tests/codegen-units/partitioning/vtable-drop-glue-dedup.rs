// tRust: Regression test for rust-lang#88438: excessive drop glue duplication in vtables.
// Verifies that drop glue for types used in trait objects gets GloballyShared
// instantiation mode, producing a single copy rather than duplicating per-CGU.

//@ compile-flags: -O -Ccodegen-units=4

#![crate_type = "rlib"]

trait TraitA {
    fn method_a(&self);
}

trait TraitB {
    fn method_b(&self);
}

// Type with explicit Drop impl used in multiple trait objects.
//~ MONO_ITEM fn std::ptr::drop_in_place::<DropType> - shim(Some(DropType)) @@ vtable_drop_glue_dedup-fallback.cgu[External]
struct DropType {
    _data: String,
}

impl Drop for DropType {
    //~ MONO_ITEM fn <DropType as std::ops::Drop>::drop @@ vtable_drop_glue_dedup-fallback.cgu[External]
    fn drop(&mut self) {}
}

impl TraitA for DropType {
    //~ MONO_ITEM fn <DropType as TraitA>::method_a @@ vtable_drop_glue_dedup-fallback.cgu[External]
    fn method_a(&self) {}
}

impl TraitB for DropType {
    //~ MONO_ITEM fn <DropType as TraitB>::method_b @@ vtable_drop_glue_dedup-fallback.cgu[External]
    fn method_b(&self) {}
}

// Type WITHOUT explicit Drop but with droppable fields, used in multiple trait objects.
// tRust: this is the key case -- previously this got LocalCopy and was duplicated.
//~ MONO_ITEM fn std::ptr::drop_in_place::<NoDrop> - shim(Some(NoDrop)) @@ vtable_drop_glue_dedup-fallback.cgu[External]
struct NoDrop {
    _data: String,
}

impl TraitA for NoDrop {
    //~ MONO_ITEM fn <NoDrop as TraitA>::method_a @@ vtable_drop_glue_dedup-fallback.cgu[External]
    fn method_a(&self) {}
}

impl TraitB for NoDrop {
    //~ MONO_ITEM fn <NoDrop as TraitB>::method_b @@ vtable_drop_glue_dedup-fallback.cgu[External]
    fn method_b(&self) {}
}

// Functions in different modules that create trait objects, causing vtable generation.
pub mod user1 {
    use super::*;

    //~ MONO_ITEM fn user1::use_as_trait_a @@ vtable_drop_glue_dedup-user1[External]
    pub fn use_as_trait_a(x: Box<DropType>) -> Box<dyn TraitA> {
        x
    }

    //~ MONO_ITEM fn user1::use_nodrop_a @@ vtable_drop_glue_dedup-user1[External]
    pub fn use_nodrop_a(x: Box<NoDrop>) -> Box<dyn TraitA> {
        x
    }
}

pub mod user2 {
    use super::*;

    //~ MONO_ITEM fn user2::use_as_trait_b @@ vtable_drop_glue_dedup-user2[External]
    pub fn use_as_trait_b(x: Box<DropType>) -> Box<dyn TraitB> {
        x
    }

    //~ MONO_ITEM fn user2::use_nodrop_b @@ vtable_drop_glue_dedup-user2[External]
    pub fn use_nodrop_b(x: Box<NoDrop>) -> Box<dyn TraitB> {
        x
    }
}
