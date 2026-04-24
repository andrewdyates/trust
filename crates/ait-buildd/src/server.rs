// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
// Part of #895 (Phase 3: Build daemon). Milestone 1: Unix-socket server.
//
// BuildDaemon owns a Unix-domain-socket listener and serves a single request
// per connection:
//   HealthCheck -> Health { status: "ok", version: <cargo pkg version> }
//   Build { .. } -> Ok { message: "echo: received build request for <name>" }
//   Shutdown    -> ShutdownAck, then the listener stops and the socket file
//                  is removed.
//
// This milestone is deliberately an echo server; real cargo dispatch,
// request deduplication, memory-aware scheduling, and per-build job caps
// come in subsequent milestones of #895.

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;

use thiserror::Error;

use crate::protocol::{ProtocolError, Request, Response, decode_request, encode};

/// Errors that can arise when running the daemon.
#[derive(Debug, Error)]
pub enum ServerError {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    #[error("protocol error: {0}")]
    Protocol(#[from] ProtocolError),
    #[error("could not resolve $HOME for default socket path")]
    HomeDirNotFound,
}

/// Default on-disk location of the daemon socket, under `$HOME/.ait_cas/`.
///
/// The caller is expected to ensure `$HOME` is set; in the rare case it is
/// not, this returns an error so the binary can surface a clear message
/// instead of panicking on `PathBuf::join`.
pub fn default_socket_path() -> Result<PathBuf, ServerError> {
    let home = dirs::home_dir().ok_or(ServerError::HomeDirNotFound)?;
    Ok(home.join(".ait_cas").join("buildd.sock"))
}

/// A single-process build daemon serving JSON-lines over a Unix socket.
pub struct BuildDaemon {
    socket_path: PathBuf,
    shutdown: Arc<AtomicBool>,
}

impl BuildDaemon {
    /// Construct a daemon bound to `socket_path` (not yet listening).
    #[must_use]
    pub fn new(socket_path: PathBuf) -> Self {
        Self { socket_path, shutdown: Arc::new(AtomicBool::new(false)) }
    }

    /// Path the daemon will bind on [`Self::run`].
    #[must_use]
    pub fn socket_path(&self) -> &Path {
        &self.socket_path
    }

    /// Bind the socket and serve until a [`Request::Shutdown`] is received or
    /// an unrecoverable I/O error occurs. On return, the socket file has
    /// been removed.
    pub fn run(&self) -> Result<(), ServerError> {
        if let Some(parent) = self.socket_path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        // Remove any stale socket left by a previous daemon. It is safe to
        // ignore NotFound; any other error indicates something is wrong with
        // the path and we want to surface it.
        match std::fs::remove_file(&self.socket_path) {
            Ok(()) => {}
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => return Err(e.into()),
        }

        let listener = UnixListener::bind(&self.socket_path)?;
        // Non-blocking accept with a short poll lets us honour the shutdown
        // flag without needing a separate wake-up channel.
        listener.set_nonblocking(true)?;

        let mut handles: Vec<thread::JoinHandle<()>> = Vec::new();
        while !self.shutdown.load(Ordering::SeqCst) {
            match listener.accept() {
                Ok((stream, _addr)) => {
                    let shutdown = Arc::clone(&self.shutdown);
                    handles.push(thread::spawn(move || {
                        if let Err(e) = handle_connection(stream, &shutdown) {
                            // Connection-level errors are not fatal to the
                            // daemon; log to stderr and move on.
                            eprintln!("ait-buildd: connection error: {e}");
                        }
                    }));
                }
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                    thread::sleep(std::time::Duration::from_millis(25));
                }
                Err(e) => {
                    let _ = std::fs::remove_file(&self.socket_path);
                    return Err(e.into());
                }
            }
        }

        for h in handles {
            let _ = h.join();
        }
        let _ = std::fs::remove_file(&self.socket_path);
        Ok(())
    }
}

/// Handle a single client connection: read one request line, write one
/// response line, close. `shutdown` is flipped when a [`Request::Shutdown`]
/// arrives so the accept loop can exit.
fn handle_connection(stream: UnixStream, shutdown: &AtomicBool) -> Result<(), ServerError> {
    // Writes on the accept-side stream need a clone because BufReader takes
    // ownership; they share the same underlying socket FD.
    let write_stream = stream.try_clone()?;
    let mut reader = BufReader::new(stream);
    let mut writer = write_stream;

    let mut line = String::new();
    let n = reader.read_line(&mut line)?;
    if n == 0 {
        // Client closed before sending a request; nothing to do.
        return Ok(());
    }

    let response = match decode_request(&line) {
        Ok(req) => dispatch(&req, shutdown),
        Err(e) => Response::Error { message: format!("decode error: {e}") },
    };

    let encoded = encode(&response).map_err(ProtocolError::from)?;
    writer.write_all(encoded.as_bytes())?;
    writer.flush()?;
    Ok(())
}

/// Pure request→response dispatch, isolated for testability. Side effect:
/// sets the shutdown flag for [`Request::Shutdown`].
fn dispatch(req: &Request, shutdown: &AtomicBool) -> Response {
    match req {
        Request::HealthCheck => Response::Health {
            status: "ok".to_string(),
            version: env!("CARGO_PKG_VERSION").to_string(),
        },
        Request::Build { crate_name, .. } => {
            Response::Ok { message: format!("echo: received build request for {crate_name}") }
        }
        Request::Shutdown => {
            shutdown.store(true, Ordering::SeqCst);
            Response::ShutdownAck
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::protocol::Profile;

    #[test]
    fn test_dispatch_health_check_returns_ok_status() {
        let flag = AtomicBool::new(false);
        let resp = dispatch(&Request::HealthCheck, &flag);
        match resp {
            Response::Health { status, version } => {
                assert_eq!(status, "ok");
                assert_eq!(version, env!("CARGO_PKG_VERSION"));
            }
            other => panic!("expected Health, got {other:?}"),
        }
        assert!(!flag.load(Ordering::SeqCst));
    }

    #[test]
    fn test_dispatch_build_echoes_crate_name() {
        let flag = AtomicBool::new(false);
        let resp = dispatch(
            &Request::Build {
                crate_name: "trust-types".to_string(),
                profile: Profile::Dev,
                features: vec![],
            },
            &flag,
        );
        match resp {
            Response::Ok { message } => {
                assert!(message.contains("trust-types"), "message={message}");
            }
            other => panic!("expected Ok, got {other:?}"),
        }
        assert!(!flag.load(Ordering::SeqCst));
    }

    #[test]
    fn test_dispatch_shutdown_sets_flag_and_acks() {
        let flag = AtomicBool::new(false);
        let resp = dispatch(&Request::Shutdown, &flag);
        assert!(matches!(resp, Response::ShutdownAck));
        assert!(flag.load(Ordering::SeqCst));
    }

    #[test]
    fn test_default_socket_path_ends_with_buildd_sock() {
        let path = default_socket_path().expect("home dir resolved");
        assert!(path.ends_with("buildd.sock"), "path={path:?}");
        assert!(
            path.parent().map(|p| p.ends_with(".ait_cas")).unwrap_or(false),
            "parent should be .ait_cas: {path:?}"
        );
    }
}
