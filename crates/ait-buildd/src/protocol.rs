// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
// Part of #895 (Phase 3: Build daemon). Milestone 1: JSON-lines protocol.
//
// Wire protocol for ait-buildd: one JSON object per line, terminated by `\n`.
// Requests and responses are internally-tagged enums so the wire format is
// flat and human-readable:
//
//     {"type":"HealthCheck"}
//     {"type":"Build","crate_name":"trust-types","profile":"Dev","features":[]}
//     {"type":"Shutdown"}
//     {"type":"Health","status":"ok","version":"0.1.0"}
//     {"type":"Ok","message":"..."}
//     {"type":"Error","message":"..."}
//     {"type":"ShutdownAck"}

use serde::{Deserialize, Serialize};
use thiserror::Error;

/// A build profile understood by the daemon. Mirrors the cargo profile names.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Profile {
    Dev,
    Release,
    Test,
}

/// Request message from client to daemon.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum Request {
    /// Request a build of a single crate. `crate_name` avoids the `crate`
    /// keyword. Features are additive; empty vec means default features.
    Build { crate_name: String, profile: Profile, features: Vec<String> },
    /// Liveness probe. Daemon replies with [`Response::Health`].
    HealthCheck,
    /// Request the daemon to exit cleanly. Daemon replies with
    /// [`Response::ShutdownAck`] before closing the listener and removing the
    /// socket file.
    Shutdown,
}

/// Response message from daemon to client.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum Response {
    /// Acknowledgement for a non-health, non-shutdown request. For this
    /// milestone every Build request receives an `Ok` echo; later milestones
    /// will replace this with structured build outcomes.
    Ok { message: String },
    /// Reply to [`Request::HealthCheck`].
    Health { status: String, version: String },
    /// Reply to [`Request::Shutdown`].
    ShutdownAck,
    /// Any protocol-level error the daemon wants to surface to the client
    /// before closing the connection.
    Error { message: String },
}

/// Errors that can arise when decoding a protocol message.
#[derive(Debug, Error)]
pub enum ProtocolError {
    #[error("protocol message was not valid JSON: {0}")]
    InvalidJson(#[from] serde_json::Error),
    #[error("protocol message was empty")]
    EmptyLine,
}

/// Encode a message as a single JSON line terminated by `\n`.
///
/// The caller is responsible for writing the resulting string atomically to
/// the socket; partial writes would violate the line-delimited framing.
pub fn encode<T: Serialize>(msg: &T) -> Result<String, serde_json::Error> {
    let mut s = serde_json::to_string(msg)?;
    s.push('\n');
    Ok(s)
}

/// Decode a single request line. Rejects empty/whitespace-only lines.
pub fn decode_request(line: &str) -> Result<Request, ProtocolError> {
    let trimmed = line.trim();
    if trimmed.is_empty() {
        return Err(ProtocolError::EmptyLine);
    }
    Ok(serde_json::from_str(trimmed)?)
}

/// Decode a single response line. Rejects empty/whitespace-only lines.
pub fn decode_response(line: &str) -> Result<Response, ProtocolError> {
    let trimmed = line.trim();
    if trimmed.is_empty() {
        return Err(ProtocolError::EmptyLine);
    }
    Ok(serde_json::from_str(trimmed)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn roundtrip_request(req: Request) {
        let line = encode(&req).expect("encode request");
        assert!(line.ends_with('\n'), "encoded line must end with newline");
        let decoded = decode_request(&line).expect("decode request");
        assert_eq!(req, decoded);
    }

    fn roundtrip_response(resp: Response) {
        let line = encode(&resp).expect("encode response");
        assert!(line.ends_with('\n'), "encoded line must end with newline");
        let decoded = decode_response(&line).expect("decode response");
        assert_eq!(resp, decoded);
    }

    #[test]
    fn test_request_roundtrip_build_dev() {
        roundtrip_request(Request::Build {
            crate_name: "trust-types".to_string(),
            profile: Profile::Dev,
            features: vec![],
        });
    }

    #[test]
    fn test_request_roundtrip_build_release_with_features() {
        roundtrip_request(Request::Build {
            crate_name: "trust-router".to_string(),
            profile: Profile::Release,
            features: vec!["pipeline-v2".to_string(), "z4-direct".to_string()],
        });
    }

    #[test]
    fn test_request_roundtrip_build_test_profile() {
        roundtrip_request(Request::Build {
            crate_name: "trust-vcgen".to_string(),
            profile: Profile::Test,
            features: vec![],
        });
    }

    #[test]
    fn test_request_roundtrip_health_check() {
        roundtrip_request(Request::HealthCheck);
    }

    #[test]
    fn test_request_roundtrip_shutdown() {
        roundtrip_request(Request::Shutdown);
    }

    #[test]
    fn test_response_roundtrip_ok() {
        roundtrip_response(Response::Ok {
            message: "echo: received build request for trust-types".to_string(),
        });
    }

    #[test]
    fn test_response_roundtrip_health() {
        roundtrip_response(Response::Health {
            status: "ok".to_string(),
            version: "0.1.0".to_string(),
        });
    }

    #[test]
    fn test_response_roundtrip_shutdown_ack() {
        roundtrip_response(Response::ShutdownAck);
    }

    #[test]
    fn test_response_roundtrip_error() {
        roundtrip_response(Response::Error { message: "bad request".to_string() });
    }

    #[test]
    fn test_decode_request_rejects_empty_line() {
        match decode_request("") {
            Err(ProtocolError::EmptyLine) => {}
            other => panic!("expected EmptyLine, got {other:?}"),
        }
    }

    #[test]
    fn test_decode_request_rejects_whitespace_only() {
        match decode_request("   \t  ") {
            Err(ProtocolError::EmptyLine) => {}
            other => panic!("expected EmptyLine, got {other:?}"),
        }
    }

    #[test]
    fn test_decode_response_rejects_empty_line() {
        match decode_response("") {
            Err(ProtocolError::EmptyLine) => {}
            other => panic!("expected EmptyLine, got {other:?}"),
        }
    }

    #[test]
    fn test_decode_request_rejects_invalid_json() {
        match decode_request("{not json}") {
            Err(ProtocolError::InvalidJson(_)) => {}
            other => panic!("expected InvalidJson, got {other:?}"),
        }
    }

    #[test]
    fn test_wire_format_uses_internally_tagged_type() {
        let line = encode(&Request::HealthCheck).unwrap();
        assert!(line.contains(r#""type":"HealthCheck""#), "wire: {line}");
    }
}
