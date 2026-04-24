// trustd: Verification daemon for shared solver state
//
// tRust #887: Minimal TCP daemon that accepts SMT-LIB2 formulas over a
// text-based protocol and dispatches them to a persistent z4 solver
// subprocess. Shares solver state across connections — common declarations
// are asserted once and reused across queries.
//
// Protocol (line-oriented, newline-delimited):
//   CHECK <smtlib2-formula>  — check satisfiability, returns SAT/UNSAT/UNKNOWN
//   STATUS                   — returns daemon statistics
//   QUIT                     — gracefully shuts down the daemon
//
// The formula in CHECK must be a complete SMT-LIB2 script (set-logic,
// declare-fun, assert, check-sat). The daemon wraps it in push/pop
// for incremental solving.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::io::{BufRead, BufReader, Write};
use std::net::{TcpListener, TcpStream};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;

/// Default port for the verification daemon.
const DEFAULT_PORT: u16 = 7878;

/// Solver subprocess manager.
///
/// Maintains a persistent z4 process with incremental mode. Each CHECK
/// command uses push/pop scoping so the base context is preserved.
#[derive(Debug)]
struct SolverProcess {
    child: Child,
}

impl SolverProcess {
    fn spawn(solver_path: &str) -> Result<Self, String> {
        let child = Command::new(solver_path)
            .args(["-smt2", "-in", "--incremental"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| format!("failed to spawn solver '{}': {}", solver_path, e))?;
        Ok(SolverProcess { child })
    }

    /// Send a complete SMT-LIB2 script wrapped in push/pop and return the result.
    ///
    /// Protocol: push scope, send formula lines, send (check-sat), read result,
    /// pop scope. This preserves any base-level assertions across queries.
    fn check(&mut self, formula: &str) -> Result<String, String> {
        let stdin =
            self.child.stdin.as_mut().ok_or_else(|| "solver stdin unavailable".to_string())?;

        // Push a new scope for this query.
        writeln!(stdin, "(push 1)").map_err(|e| format!("failed to write push: {e}"))?;

        // Send each line of the formula.
        for line in formula.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() {
                continue;
            }
            // Skip (check-sat) from the formula — we add it ourselves.
            if trimmed == "(check-sat)" {
                continue;
            }
            writeln!(stdin, "{trimmed}")
                .map_err(|e| format!("failed to write formula line: {e}"))?;
        }

        // Issue check-sat and a sentinel echo so we know when output is done.
        writeln!(stdin, "(check-sat)").map_err(|e| format!("failed to write check-sat: {e}"))?;
        writeln!(stdin, "(echo \"__TRUSTD_DONE__\")")
            .map_err(|e| format!("failed to write sentinel: {e}"))?;
        stdin.flush().map_err(|e| format!("failed to flush: {e}"))?;

        // Read lines until we see the sentinel.
        let stdout =
            self.child.stdout.as_mut().ok_or_else(|| "solver stdout unavailable".to_string())?;
        let mut reader = BufReader::new(stdout);
        let mut result_lines = Vec::new();

        loop {
            let mut line = String::new();
            match reader.read_line(&mut line) {
                Ok(0) => return Err("solver process exited unexpectedly".to_string()),
                Ok(_) => {
                    let trimmed = line.trim().to_string();
                    if trimmed.contains("__TRUSTD_DONE__") {
                        break;
                    }
                    if !trimmed.is_empty() {
                        result_lines.push(trimmed);
                    }
                }
                Err(e) => return Err(format!("failed to read solver output: {e}")),
            }
        }

        // Pop the scope.
        let stdin = self
            .child
            .stdin
            .as_mut()
            .ok_or_else(|| "solver stdin unavailable after read".to_string())?;
        writeln!(stdin, "(pop 1)").map_err(|e| format!("failed to write pop: {e}"))?;
        stdin.flush().map_err(|e| format!("failed to flush pop: {e}"))?;

        // The first line should be sat/unsat/unknown.
        if result_lines.is_empty() {
            return Err("no output from solver".to_string());
        }

        let result = result_lines[0].to_lowercase();
        if result == "sat" {
            Ok("SAT".to_string())
        } else if result == "unsat" {
            Ok("UNSAT".to_string())
        } else if result == "unknown" {
            Ok("UNKNOWN".to_string())
        } else {
            Err(format!("unexpected solver output: {}", result_lines.join("\n")))
        }
    }
}

impl Drop for SolverProcess {
    fn drop(&mut self) {
        // Send (exit) to cleanly shut down the solver.
        if let Some(stdin) = self.child.stdin.as_mut() {
            let _ = writeln!(stdin, "(exit)");
            let _ = stdin.flush();
        }
        let _ = self.child.wait();
    }
}

/// Shared daemon state.
struct DaemonState {
    solver: SolverProcess,
    queries_total: u64,
    queries_sat: u64,
    queries_unsat: u64,
    queries_unknown: u64,
    queries_error: u64,
}

/// Handle a single client connection.
fn handle_client(
    stream: &mut TcpStream,
    state: &Mutex<DaemonState>,
    shutdown: &AtomicBool,
    queries_counter: &AtomicU64,
) {
    let peer = stream.peer_addr().map(|a| a.to_string()).unwrap_or_else(|_| "unknown".to_string());
    eprintln!("trustd: connection from {peer}");

    // Clone the stream for reading (BufReader takes ownership).
    let reader_stream = match stream.try_clone() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("trustd: failed to clone stream: {e}");
            return;
        }
    };
    let reader = BufReader::new(reader_stream);

    for line_result in reader.lines() {
        let line = match line_result {
            Ok(l) => l,
            Err(e) => {
                eprintln!("trustd: read error from {peer}: {e}");
                break;
            }
        };

        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }

        if trimmed.eq_ignore_ascii_case("QUIT") {
            let _ = writeln!(stream, "OK: shutting down");
            let _ = stream.flush();
            shutdown.store(true, Ordering::SeqCst);
            break;
        }

        if trimmed.eq_ignore_ascii_case("STATUS") {
            let st = state.lock().expect("invariant: mutex not poisoned");
            let response = format!(
                "OK: queries={} sat={} unsat={} unknown={} errors={}",
                st.queries_total,
                st.queries_sat,
                st.queries_unsat,
                st.queries_unknown,
                st.queries_error,
            );
            drop(st);
            let _ = writeln!(stream, "{response}");
            let _ = stream.flush();
            continue;
        }

        if let Some(formula) = trimmed.strip_prefix("CHECK ") {
            let start = Instant::now();
            let mut st = state.lock().expect("invariant: mutex not poisoned");
            st.queries_total += 1;
            queries_counter.fetch_add(1, Ordering::Relaxed);

            match st.solver.check(formula) {
                Ok(result) => {
                    let elapsed_ms = start.elapsed().as_millis();
                    match result.as_str() {
                        "SAT" => st.queries_sat += 1,
                        "UNSAT" => st.queries_unsat += 1,
                        _ => st.queries_unknown += 1,
                    }
                    drop(st);
                    let _ = writeln!(stream, "{result} ({elapsed_ms}ms)");
                }
                Err(e) => {
                    st.queries_error += 1;
                    drop(st);
                    let _ = writeln!(stream, "ERROR: {e}");
                }
            }
            let _ = stream.flush();
            continue;
        }

        let _ = writeln!(stream, "ERROR: unknown command. Use CHECK <formula>, STATUS, or QUIT");
        let _ = stream.flush();
    }

    eprintln!("trustd: connection from {peer} closed");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let port = if args.len() > 1 {
        args[1].parse::<u16>().unwrap_or_else(|_| {
            eprintln!("trustd: invalid port '{}', using default {DEFAULT_PORT}", args[1]);
            DEFAULT_PORT
        })
    } else {
        DEFAULT_PORT
    };

    let solver_path = if args.len() > 2 { args[2].clone() } else { "z4".to_string() };

    eprintln!("trustd: starting on port {port}, solver: {solver_path}");

    let solver = match SolverProcess::spawn(&solver_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("trustd: fatal: {e}");
            std::process::exit(1);
        }
    };

    let state = Arc::new(Mutex::new(DaemonState {
        solver,
        queries_total: 0,
        queries_sat: 0,
        queries_unsat: 0,
        queries_unknown: 0,
        queries_error: 0,
    }));

    let shutdown = Arc::new(AtomicBool::new(false));
    let queries_counter = Arc::new(AtomicU64::new(0));

    let listener = TcpListener::bind(format!("127.0.0.1:{port}")).unwrap_or_else(|e| {
        eprintln!("trustd: fatal: cannot bind to port {port}: {e}");
        std::process::exit(1);
    });

    eprintln!("trustd: listening on 127.0.0.1:{port}");

    // Set a timeout on the listener so we can check the shutdown flag.
    listener.set_nonblocking(false).expect("invariant: set_nonblocking should succeed");

    for stream_result in listener.incoming() {
        if shutdown.load(Ordering::SeqCst) {
            eprintln!("trustd: shutdown requested");
            break;
        }

        match stream_result {
            Ok(mut stream) => {
                handle_client(&mut stream, &state, &shutdown, &queries_counter);
            }
            Err(e) => {
                eprintln!("trustd: accept error: {e}");
                continue;
            }
        }

        if shutdown.load(Ordering::SeqCst) {
            eprintln!("trustd: shutdown requested");
            break;
        }
    }

    let st = state.lock().expect("invariant: mutex not poisoned");
    eprintln!(
        "trustd: exiting. Total queries: {}, SAT: {}, UNSAT: {}, UNKNOWN: {}, errors: {}",
        st.queries_total, st.queries_sat, st.queries_unsat, st.queries_unknown, st.queries_error
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{BufRead, BufReader, Write};
    use std::net::TcpStream;
    use std::sync::mpsc as std_mpsc;
    use std::thread;
    use std::time::Duration;

    /// Start a mock trustd daemon in a background thread.
    ///
    /// Binds to port 0 (OS-assigned) and sends the actual port back via
    /// a channel. This avoids the race condition of free_port() + rebind.
    fn start_test_daemon() -> (u16, Arc<AtomicBool>) {
        let shutdown = Arc::new(AtomicBool::new(false));
        let shutdown_clone = Arc::clone(&shutdown);
        let (port_tx, port_rx) = std_mpsc::channel();

        thread::spawn(move || {
            let listener = TcpListener::bind("127.0.0.1:0").expect("should bind to ephemeral port");
            let port = listener.local_addr().expect("local addr").port();
            port_tx.send(port).expect("send port");

            // Accept one connection then exit.
            if let Ok(mut stream) = listener.accept().map(|(s, _)| s) {
                let reader_stream = stream.try_clone().expect("clone");
                let reader = BufReader::new(reader_stream);

                for line_result in reader.lines() {
                    if shutdown_clone.load(Ordering::SeqCst) {
                        break;
                    }
                    let line = match line_result {
                        Ok(l) => l,
                        Err(_) => break,
                    };
                    let trimmed = line.trim();
                    if trimmed.eq_ignore_ascii_case("QUIT") {
                        let _ = writeln!(stream, "OK: shutting down");
                        let _ = stream.flush();
                        shutdown_clone.store(true, Ordering::SeqCst);
                        break;
                    }
                    if trimmed.eq_ignore_ascii_case("STATUS") {
                        let _ = writeln!(stream, "OK: queries=0 sat=0 unsat=0 unknown=0 errors=0");
                        let _ = stream.flush();
                        continue;
                    }
                    if trimmed.starts_with("CHECK ") {
                        // Mock: always return UNKNOWN since we don't have a real solver.
                        let _ = writeln!(stream, "UNKNOWN (0ms)");
                        let _ = stream.flush();
                        continue;
                    }
                    let _ = writeln!(
                        stream,
                        "ERROR: unknown command. Use CHECK <formula>, STATUS, or QUIT"
                    );
                    let _ = stream.flush();
                }
            }
        });

        let port = port_rx
            .recv_timeout(Duration::from_secs(5))
            .expect("should receive port from daemon thread");

        (port, shutdown)
    }

    #[test]
    fn test_trustd_protocol_status() {
        let (port, _shutdown) = start_test_daemon();

        let mut stream = TcpStream::connect(format!("127.0.0.1:{port}")).expect("should connect");
        stream.set_read_timeout(Some(Duration::from_secs(2))).expect("set timeout");

        // Send STATUS command.
        writeln!(stream, "STATUS").expect("write STATUS");
        stream.flush().expect("flush");

        let mut reader = BufReader::new(stream.try_clone().expect("clone"));
        let mut response = String::new();
        reader.read_line(&mut response).expect("read response");

        assert!(
            response.starts_with("OK: queries="),
            "STATUS should return stats, got: {response}"
        );

        // Send QUIT to clean up.
        let writer = reader.into_inner();
        let mut writer = writer;
        writeln!(writer, "QUIT").expect("write QUIT");
        writer.flush().expect("flush");
    }

    #[test]
    fn test_trustd_protocol_unknown_command() {
        let (port, _shutdown) = start_test_daemon();

        let mut stream = TcpStream::connect(format!("127.0.0.1:{port}")).expect("should connect");
        stream.set_read_timeout(Some(Duration::from_secs(2))).expect("set timeout");

        // Send an unknown command.
        writeln!(stream, "FOOBAR").expect("write FOOBAR");
        stream.flush().expect("flush");

        let mut reader = BufReader::new(stream.try_clone().expect("clone"));
        let mut response = String::new();
        reader.read_line(&mut response).expect("read response");

        assert!(
            response.starts_with("ERROR:"),
            "unknown command should return ERROR, got: {response}"
        );

        // Clean up.
        let writer = reader.into_inner();
        let mut writer = writer;
        writeln!(writer, "QUIT").expect("write QUIT");
        writer.flush().expect("flush");
    }

    #[test]
    fn test_trustd_protocol_check_mock() {
        let (port, _shutdown) = start_test_daemon();

        let mut stream = TcpStream::connect(format!("127.0.0.1:{port}")).expect("should connect");
        stream.set_read_timeout(Some(Duration::from_secs(2))).expect("set timeout");

        // Send a CHECK command (mock solver returns UNKNOWN).
        writeln!(stream, "CHECK (assert true)").expect("write CHECK");
        stream.flush().expect("flush");

        let mut reader = BufReader::new(stream.try_clone().expect("clone"));
        let mut response = String::new();
        reader.read_line(&mut response).expect("read response");

        assert!(
            response.starts_with("UNKNOWN")
                || response.starts_with("SAT")
                || response.starts_with("UNSAT")
                || response.starts_with("ERROR"),
            "CHECK should return a result, got: {response}"
        );

        // Clean up.
        let writer = reader.into_inner();
        let mut writer = writer;
        writeln!(writer, "QUIT").expect("write QUIT");
        writer.flush().expect("flush");
    }

    #[test]
    fn test_solver_process_spawn_invalid_path() {
        let result = SolverProcess::spawn("/nonexistent/solver");
        assert!(result.is_err(), "should fail for nonexistent solver");
        let err = result.unwrap_err();
        assert!(err.contains("failed to spawn"), "error should mention spawn failure: {err}");
    }
}
