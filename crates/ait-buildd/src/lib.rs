// ait-buildd: Memory-aware build daemon. See Cargo.toml for details.
// Part of #895 (Phase 3: Build daemon), epic #894.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// tRust #970: missing_docs disabled until crate stabilizes.
// #![warn(missing_docs)]

//! Build daemon library.
//!
//! ait-buildd is a long-lived build daemon that accepts cargo build requests
//! over a Unix-domain socket and coalesces redundant work across concurrent
//! agents. This crate currently exposes:
//!
//! - [`scheduler`]: memory-pressure reader, per-build job-cap math, and
//!   SIGSTOP/SIGCONT backpressure.
//! - [`protocol`] / [`server`] / [`priority`]: wire protocol and server
//!   skeleton that echoes Build requests and answers HealthCheck/Shutdown.
//!
//! Wiring the scheduler into the server's request-handling loop, request
//! deduplication, and cargo-wrapper auto-start are deferred to subsequent
//! milestones of #895. See
//! `designs/2026-04-17-multi-agent-build-coordination.md` §Component 5.

pub mod priority;
pub mod protocol;
pub mod scheduler;
pub mod server;

pub use priority::{Priority, priority_for_request};
pub use protocol::{
    Profile, ProtocolError, Request, Response, decode_request, decode_response, encode,
};
pub use server::{BuildDaemon, ServerError, default_socket_path};
