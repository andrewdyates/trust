// trust-lsp/transport.rs: LSP base protocol transport (stdin/stdout)
//
// Implements the LSP base protocol: Content-Length header framing over
// stdin/stdout with JSON-RPC 2.0 message bodies.
//
// Wire format:
//   Content-Length: <byte count>\r\n
//   \r\n
//   <JSON body>
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::io::{self, BufRead, Write};

use crate::protocol::Request;

/// Error type for transport operations.
#[derive(Debug, thiserror::Error)]
pub enum TransportError {
    #[error("I/O error: {0}")]
    Io(#[from] io::Error),
    #[error("Invalid header: {0}")]
    InvalidHeader(String),
    #[error("Missing Content-Length header")]
    MissingContentLength,
    #[error("JSON parse error: {0}")]
    JsonParse(#[from] serde_json::Error),
    #[error("Connection closed")]
    ConnectionClosed,
}

/// Read one LSP message from a buffered reader.
///
/// Parses the `Content-Length` header, reads the body, and deserializes
/// the JSON-RPC request/notification.
pub(crate) fn read_message(reader: &mut impl BufRead) -> Result<Request, TransportError> {
    // Read headers until empty line.
    let mut content_length: Option<usize> = None;
    loop {
        let mut header_line = String::new();
        let bytes_read = reader.read_line(&mut header_line)?;
        if bytes_read == 0 {
            return Err(TransportError::ConnectionClosed);
        }

        let trimmed = header_line.trim();
        if trimmed.is_empty() {
            break;
        }

        if let Some(value) = trimmed.strip_prefix("Content-Length:") {
            let len: usize = value
                .trim()
                .parse()
                .map_err(|_| TransportError::InvalidHeader(header_line.clone()))?;
            content_length = Some(len);
        }
        // Ignore other headers (e.g., Content-Type).
    }

    let length = content_length.ok_or(TransportError::MissingContentLength)?;

    // Read exactly `length` bytes.
    let mut body = vec![0u8; length];
    reader.read_exact(&mut body)?;

    let request: Request = serde_json::from_slice(&body)?;
    Ok(request)
}

/// Write an LSP message to a writer.
///
/// Serializes the value as JSON, prepends the `Content-Length` header,
/// and flushes.
pub(crate) fn write_message(writer: &mut impl Write, value: &impl serde::Serialize) -> Result<(), TransportError> {
    let body = serde_json::to_string(value)?;
    let header = format!("Content-Length: {}\r\n\r\n", body.len());
    writer.write_all(header.as_bytes())?;
    writer.write_all(body.as_bytes())?;
    writer.flush()?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    fn make_lsp_message(json: &str) -> Vec<u8> {
        let body = json.as_bytes();
        let header = format!("Content-Length: {}\r\n\r\n", body.len());
        let mut msg = header.into_bytes();
        msg.extend_from_slice(body);
        msg
    }

    #[test]
    fn test_read_message_initialize() {
        let json = r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"rootUri":"file:///project"}}"#;
        let data = make_lsp_message(json);
        let mut reader = io::BufReader::new(Cursor::new(data));

        let req = read_message(&mut reader).expect("should parse message");
        assert_eq!(req.method, "initialize");
        assert!(req.id.is_some());
    }

    #[test]
    fn test_read_message_notification() {
        let json = r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#;
        let data = make_lsp_message(json);
        let mut reader = io::BufReader::new(Cursor::new(data));

        let req = read_message(&mut reader).expect("should parse notification");
        assert_eq!(req.method, "initialized");
        assert!(req.id.is_none());
    }

    #[test]
    fn test_read_message_multiple() {
        let json1 = r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#;
        let json2 = r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#;
        let mut data = make_lsp_message(json1);
        data.extend_from_slice(&make_lsp_message(json2));

        let mut reader = io::BufReader::new(Cursor::new(data));

        let req1 = read_message(&mut reader).expect("first message");
        assert_eq!(req1.method, "initialize");

        let req2 = read_message(&mut reader).expect("second message");
        assert_eq!(req2.method, "initialized");
    }

    #[test]
    fn test_read_message_connection_closed() {
        let mut reader = io::BufReader::new(Cursor::new(Vec::new()));
        let result = read_message(&mut reader);
        assert!(matches!(result, Err(TransportError::ConnectionClosed)));
    }

    #[test]
    fn test_read_message_missing_content_length() {
        let data = b"Some-Header: value\r\n\r\n{}";
        let mut reader = io::BufReader::new(Cursor::new(data.to_vec()));
        let result = read_message(&mut reader);
        assert!(matches!(result, Err(TransportError::MissingContentLength)));
    }

    #[test]
    fn test_read_message_invalid_content_length() {
        let data = b"Content-Length: abc\r\n\r\n{}";
        let mut reader = io::BufReader::new(Cursor::new(data.to_vec()));
        let result = read_message(&mut reader);
        assert!(matches!(result, Err(TransportError::InvalidHeader(_))));
    }

    #[test]
    fn test_write_message_format() {
        use crate::protocol::Response;

        let resp = Response::success(
            Some(crate::protocol::RequestId::Integer(1)),
            serde_json::json!({"capabilities": {}}),
        );
        let mut buf = Vec::new();
        write_message(&mut buf, &resp).expect("write should succeed");

        let output = String::from_utf8(buf).expect("valid utf8");
        assert!(output.starts_with("Content-Length: "));
        assert!(output.contains("\r\n\r\n"));

        // Parse body after header
        let body_start = output.find("\r\n\r\n").unwrap() + 4;
        let body = &output[body_start..];
        let parsed: serde_json::Value = serde_json::from_str(body).expect("valid JSON body");
        assert_eq!(parsed["jsonrpc"], "2.0");
        assert_eq!(parsed["id"], 1);
    }

    #[test]
    fn test_write_read_roundtrip() {
        use crate::protocol::Notification;

        let notif = Notification::new(
            "textDocument/publishDiagnostics",
            serde_json::json!({"uri": "file:///test.rs", "diagnostics": []}),
        );

        let mut buf = Vec::new();
        write_message(&mut buf, &notif).expect("write");

        // Read back as a Request (notification has no id)
        let mut reader = io::BufReader::new(Cursor::new(buf));
        let req = read_message(&mut reader).expect("read");
        assert_eq!(req.method, "textDocument/publishDiagnostics");
        assert!(req.id.is_none());
    }
}
