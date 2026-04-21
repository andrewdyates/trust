// trust-vcgen/binary_analysis/mod.rs: Binary analysis pipeline
//
// Refactors binary pattern detection/type recovery into a module directory and
// adds binary lifting, CFG reconstruction, P-code translation, and CFGFast
// function recovery utilities.
//
// Part of #148: Binary analysis pipeline
// Part of #101: Binary Lifting
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod lowering;

pub mod cfg_fast;
pub mod cfg_reconstruct;
pub mod lifter;
pub mod pcode;
pub mod type_recovery;
pub mod patterns;

#[allow(unused_imports)]
pub use cfg_fast::*;
#[allow(unused_imports)]
pub use cfg_reconstruct::*;
#[allow(unused_imports)]
pub use lifter::*;
#[allow(unused_imports)]
pub use pcode::*;
pub use patterns::*;
