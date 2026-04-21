// trust-driver/phases: Production implementations of verification loop phase traits.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub mod backprop;
pub mod strengthen;
pub mod verify;

pub use backprop::ProductionBackpropPhase;
pub use strengthen::ProductionStrengthenPhase;
pub use verify::ProductionVerifyPhase;
