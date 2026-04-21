// trust-proof-cert cert_serialize
//
// Compact serialization/deserialization of proof certificates for storage and transmission.
// Supports Binary (bincode), Json (serde_json), and Compact (minified JSON) formats
// with optional compression and size limits.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use thiserror::Error;

/// Wire format for serialized proof certificates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CertFormat {
    /// Bincode binary encoding.
    Binary,
    /// Pretty-printed JSON.
    Json,
    /// Minified JSON (no whitespace).
    Compact,
}

/// Configuration for certificate serialization.
#[derive(Debug, Clone)]
pub struct SerializeConfig {
    /// Output format.
    pub format: CertFormat,
    /// Whether to apply run-length compression after encoding.
    pub compress: bool,
    /// Whether to include metadata wrapper in output.
    pub include_metadata: bool,
    /// Optional maximum output size in bytes.
    pub max_size_bytes: Option<usize>,
}

impl Default for SerializeConfig {
    fn default() -> Self {
        Self {
            format: CertFormat::Json,
            compress: false,
            include_metadata: true,
            max_size_bytes: None,
        }
    }
}

/// A serialized proof certificate with metadata about the encoding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SerializedCert {
    /// The raw serialized bytes.
    pub data: Vec<u8>,
    /// The format used.
    pub format: CertFormat,
    /// Size of the data before compression (if compressed), else same as `data.len()`.
    pub original_size: usize,
    /// Whether the data is compressed.
    pub compressed: bool,
}

/// Errors arising during certificate serialization/deserialization.
#[derive(Debug, Error)]
pub enum SerializeError {
    /// The format or encoding is invalid.
    #[error("format error: {0}")]
    FormatError(String),

    /// Serialized output exceeds the configured size limit.
    #[error("size limit exceeded: {actual} bytes > {limit} byte limit")]
    SizeLimitExceeded {
        /// Actual size in bytes.
        actual: usize,
        /// Configured limit in bytes.
        limit: usize,
    },

    /// The input data is invalid for the requested operation.
    #[error("invalid data: {0}")]
    InvalidData(String),

    /// Deserialization failed.
    #[error("deserialization failed: {0}")]
    DeserializeFailed(String),
}

// ---------------------------------------------------------------------------
// Magic / version constants for the Binary format
// ---------------------------------------------------------------------------

/// Magic bytes identifying a cert_serialize binary blob.
const CERT_MAGIC: &[u8; 4] = b"tRCS";

/// Current binary format version.
const CERT_FORMAT_VERSION: u8 = 1;

/// Flag byte: no compression.
const FLAG_UNCOMPRESSED: u8 = 0x00;

/// Flag byte: RLE-compressed payload.
const FLAG_COMPRESSED: u8 = 0x01;

// ---------------------------------------------------------------------------
// CertWriter
// ---------------------------------------------------------------------------

/// Writes (serializes) certificate data according to a [`SerializeConfig`].
#[derive(Debug)]
pub struct CertWriter {
    config: SerializeConfig,
}

impl CertWriter {
    /// Create a new writer with the given configuration.
    pub fn new(config: SerializeConfig) -> Self {
        Self { config }
    }

    /// Serialize certificate data (as a string) into a [`SerializedCert`].
    pub fn serialize(&self, cert_data: &str) -> Result<SerializedCert, SerializeError> {
        if cert_data.is_empty() {
            return Err(SerializeError::InvalidData(
                "certificate data is empty".to_string(),
            ));
        }

        let raw_bytes = match self.config.format {
            CertFormat::Binary => {
                let payload = cert_data.as_bytes();
                let mut buf = Vec::with_capacity(CERT_MAGIC.len() + 2 + payload.len());
                buf.extend_from_slice(CERT_MAGIC);
                buf.push(CERT_FORMAT_VERSION);
                buf.push(if self.config.compress {
                    FLAG_COMPRESSED
                } else {
                    FLAG_UNCOMPRESSED
                });
                buf.extend_from_slice(payload);
                buf
            }
            CertFormat::Json => {
                if self.config.include_metadata {
                    let wrapper = format!(
                        "{{\n  \"format\": \"trust-cert\",\n  \"version\": 1,\n  \"data\": {cert_data}\n}}"
                    );
                    wrapper.into_bytes()
                } else {
                    cert_data.as_bytes().to_vec()
                }
            }
            CertFormat::Compact => {
                if self.config.include_metadata {
                    let wrapper = format!(
                        "{{\"format\":\"trust-cert\",\"version\":1,\"data\":{cert_data}}}"
                    );
                    wrapper.into_bytes()
                } else {
                    // Strip whitespace for compact representation.
                    let compacted: String = compact_json(cert_data);
                    compacted.into_bytes()
                }
            }
        };

        let original_size = raw_bytes.len();

        let final_bytes = if self.config.compress {
            self.compress_cert(&raw_bytes)
        } else {
            raw_bytes
        };

        // Check size limit.
        if let Some(limit) = self.config.max_size_bytes
            && final_bytes.len() > limit {
                return Err(SerializeError::SizeLimitExceeded {
                    actual: final_bytes.len(),
                    limit,
                });
            }

        Ok(SerializedCert {
            data: final_bytes,
            format: self.config.format,
            original_size,
            compressed: self.config.compress,
        })
    }

    /// Apply simple run-length encoding compression to `data`.
    ///
    /// Format: for each run of identical bytes, emit `[byte, count_high, count_low]`
    /// where count is a big-endian u16. Maximum run length per chunk is 65535.
    pub fn compress_cert(&self, data: &[u8]) -> Vec<u8> {
        rle_compress(data)
    }

    /// Estimate the serialized size of `cert_data` under the current config
    /// (without actually performing compression or allocation).
    pub fn cert_size_estimate(&self, cert_data: &str) -> usize {
        let base = cert_data.len();
        let overhead = match self.config.format {
            CertFormat::Binary => CERT_MAGIC.len() + 2, // magic + version + flags
            CertFormat::Json => {
                if self.config.include_metadata {
                    // Rough overhead of the JSON wrapper.
                    60
                } else {
                    0
                }
            }
            CertFormat::Compact => {
                if self.config.include_metadata {
                    50
                } else {
                    0
                }
            }
        };
        base + overhead
    }
}

// ---------------------------------------------------------------------------
// CertReader
// ---------------------------------------------------------------------------

/// Reads (deserializes) certificate data from a [`SerializedCert`].
#[derive(Debug)]
pub struct CertReader {
    _priv: (),
}

impl CertReader {
    /// Create a new reader.
    pub fn new() -> Self {
        Self { _priv: () }
    }

    /// Deserialize a [`SerializedCert`] back to a certificate data string.
    pub fn deserialize(&self, serialized: &SerializedCert) -> Result<String, SerializeError> {
        let raw = if serialized.compressed {
            rle_decompress(&serialized.data)?
        } else {
            serialized.data.clone()
        };

        if !self.validate_on_deserialize(&raw) {
            return Err(SerializeError::DeserializeFailed(
                "validation failed: data appears corrupt".to_string(),
            ));
        }

        match serialized.format {
            CertFormat::Binary => {
                let header_len = CERT_MAGIC.len() + 2; // magic + version + flags
                if raw.len() < header_len {
                    return Err(SerializeError::DeserializeFailed(format!(
                        "binary too short: expected >= {header_len} bytes, got {}",
                        raw.len()
                    )));
                }
                if &raw[..CERT_MAGIC.len()] != CERT_MAGIC {
                    return Err(SerializeError::DeserializeFailed(
                        "invalid magic bytes".to_string(),
                    ));
                }
                let version = raw[CERT_MAGIC.len()];
                if version != CERT_FORMAT_VERSION {
                    return Err(SerializeError::DeserializeFailed(format!(
                        "unsupported version: {version}"
                    )));
                }
                let payload = &raw[header_len..];
                String::from_utf8(payload.to_vec()).map_err(|e| {
                    SerializeError::DeserializeFailed(format!("invalid UTF-8 payload: {e}"))
                })
            }
            CertFormat::Json | CertFormat::Compact => {
                String::from_utf8(raw).map_err(|e| {
                    SerializeError::DeserializeFailed(format!("invalid UTF-8: {e}"))
                })
            }
        }
    }

    /// Validate raw bytes before deserialization. Returns `true` if the data
    /// passes basic integrity checks.
    pub fn validate_on_deserialize(&self, data: &[u8]) -> bool {
        // Must be non-empty.
        if data.is_empty() {
            return false;
        }
        // If it starts with the binary magic, check minimum header length.
        if data.len() >= CERT_MAGIC.len() && &data[..CERT_MAGIC.len()] == CERT_MAGIC {
            return data.len() >= CERT_MAGIC.len() + 2;
        }
        true
    }

    /// Attempt to detect the format of raw serialized bytes.
    pub fn detect_format(&self, data: &[u8]) -> Option<CertFormat> {
        if data.is_empty() {
            return None;
        }
        // Binary: starts with magic bytes.
        if data.len() >= CERT_MAGIC.len() && &data[..CERT_MAGIC.len()] == CERT_MAGIC {
            return Some(CertFormat::Binary);
        }
        // JSON / Compact: starts with `{`.
        if data[0] == b'{' {
            // Distinguish pretty JSON from compact by presence of newlines.
            if data.windows(1).any(|w| w[0] == b'\n') {
                return Some(CertFormat::Json);
            }
            return Some(CertFormat::Compact);
        }
        None
    }
}

impl Default for CertReader {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Minimal JSON whitespace stripping (outside of string literals).
fn compact_json(input: &str) -> String {
    let mut out = String::with_capacity(input.len());
    let mut in_string = false;
    let mut prev_char = '\0';
    for ch in input.chars() {
        if in_string {
            out.push(ch);
            if ch == '"' && prev_char != '\\' {
                in_string = false;
            }
        } else if ch == '"' {
            in_string = true;
            out.push(ch);
        } else if !ch.is_ascii_whitespace() {
            out.push(ch);
        }
        prev_char = ch;
    }
    out
}

/// Simple run-length encoding: `[byte, count_hi, count_lo]` triples.
fn rle_compress(data: &[u8]) -> Vec<u8> {
    if data.is_empty() {
        return Vec::new();
    }
    let mut out = Vec::new();
    let mut i = 0;
    while i < data.len() {
        let byte = data[i];
        let mut count: usize = 1;
        while i + count < data.len() && data[i + count] == byte && count < 65535 {
            count += 1;
        }
        out.push(byte);
        out.push((count >> 8) as u8);
        out.push((count & 0xFF) as u8);
        i += count;
    }
    out
}

/// Decompress RLE-encoded data.
fn rle_decompress(data: &[u8]) -> Result<Vec<u8>, SerializeError> {
    if data.is_empty() {
        return Ok(Vec::new());
    }
    if !data.len().is_multiple_of(3) {
        return Err(SerializeError::DeserializeFailed(
            "compressed data length is not a multiple of 3".to_string(),
        ));
    }
    let mut out = Vec::new();
    let mut i = 0;
    while i < data.len() {
        let byte = data[i];
        let count = ((data[i + 1] as usize) << 8) | (data[i + 2] as usize);
        if count == 0 {
            return Err(SerializeError::DeserializeFailed(
                "compressed data has zero-length run".to_string(),
            ));
        }
        out.extend(std::iter::repeat_n(byte, count));
        i += 3;
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE_CERT: &str = r#"{"function":"foo","hash":"abc123","status":"proved"}"#;

    fn default_config() -> SerializeConfig {
        SerializeConfig::default()
    }

    fn binary_config() -> SerializeConfig {
        SerializeConfig {
            format: CertFormat::Binary,
            compress: false,
            include_metadata: true,
            max_size_bytes: None,
        }
    }

    fn compact_config() -> SerializeConfig {
        SerializeConfig {
            format: CertFormat::Compact,
            compress: false,
            include_metadata: false,
            max_size_bytes: None,
        }
    }

    // -----------------------------------------------------------------------
    // CertWriter / CertReader roundtrip tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_json_roundtrip() {
        let writer = CertWriter::new(default_config());
        let reader = CertReader::new();

        let serialized = writer.serialize(SAMPLE_CERT).expect("serialize");
        assert_eq!(serialized.format, CertFormat::Json);
        assert!(!serialized.compressed);

        let restored = reader.deserialize(&serialized).expect("deserialize");
        assert!(restored.contains("foo"));
        assert!(restored.contains("abc123"));
    }

    #[test]
    fn test_binary_roundtrip() {
        let writer = CertWriter::new(binary_config());
        let reader = CertReader::new();

        let serialized = writer.serialize(SAMPLE_CERT).expect("serialize");
        assert_eq!(serialized.format, CertFormat::Binary);

        let restored = reader.deserialize(&serialized).expect("deserialize");
        assert_eq!(restored, SAMPLE_CERT);
    }

    #[test]
    fn test_compact_roundtrip() {
        let writer = CertWriter::new(compact_config());
        let reader = CertReader::new();

        let serialized = writer.serialize(SAMPLE_CERT).expect("serialize");
        assert_eq!(serialized.format, CertFormat::Compact);

        let restored = reader.deserialize(&serialized).expect("deserialize");
        assert_eq!(restored, SAMPLE_CERT);
    }

    #[test]
    fn test_json_with_metadata() {
        let config = SerializeConfig {
            format: CertFormat::Json,
            include_metadata: true,
            ..default_config()
        };
        let writer = CertWriter::new(config);
        let serialized = writer.serialize(SAMPLE_CERT).expect("serialize");
        let text = String::from_utf8(serialized.data.clone()).expect("utf8");
        assert!(text.contains("trust-cert"));
        assert!(text.contains("version"));
    }

    #[test]
    fn test_compact_with_metadata() {
        let config = SerializeConfig {
            format: CertFormat::Compact,
            include_metadata: true,
            ..default_config()
        };
        let writer = CertWriter::new(config);
        let serialized = writer.serialize(SAMPLE_CERT).expect("serialize");
        let text = String::from_utf8(serialized.data.clone()).expect("utf8");
        assert!(text.contains("\"format\":\"trust-cert\""));
        assert!(!text.contains('\n'));
    }

    // -----------------------------------------------------------------------
    // Compression tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_compressed_json_roundtrip() {
        let config = SerializeConfig {
            format: CertFormat::Json,
            compress: true,
            include_metadata: false,
            max_size_bytes: None,
        };
        let writer = CertWriter::new(config);
        let reader = CertReader::new();

        let serialized = writer.serialize(SAMPLE_CERT).expect("serialize");
        assert!(serialized.compressed);

        let restored = reader.deserialize(&serialized).expect("deserialize");
        assert_eq!(restored, SAMPLE_CERT);
    }

    #[test]
    fn test_compressed_binary_roundtrip() {
        let config = SerializeConfig {
            format: CertFormat::Binary,
            compress: true,
            include_metadata: true,
            max_size_bytes: None,
        };
        let writer = CertWriter::new(config);
        let reader = CertReader::new();

        let serialized = writer.serialize(SAMPLE_CERT).expect("serialize");
        assert!(serialized.compressed);
        assert!(serialized.original_size > 0);

        let restored = reader.deserialize(&serialized).expect("deserialize");
        assert_eq!(restored, SAMPLE_CERT);
    }

    #[test]
    fn test_rle_compress_decompress() {
        let data = b"aaabbbcccc";
        let compressed = rle_compress(data);
        let decompressed = rle_decompress(&compressed).expect("decompress");
        assert_eq!(decompressed, data);
    }

    #[test]
    fn test_rle_empty() {
        let compressed = rle_compress(b"");
        assert!(compressed.is_empty());
        let decompressed = rle_decompress(&compressed).expect("decompress");
        assert!(decompressed.is_empty());
    }

    // -----------------------------------------------------------------------
    // Size limit tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_size_limit_exceeded() {
        let config = SerializeConfig {
            format: CertFormat::Json,
            compress: false,
            include_metadata: true,
            max_size_bytes: Some(10), // very small
        };
        let writer = CertWriter::new(config);

        let err = writer.serialize(SAMPLE_CERT).expect_err("should exceed limit");
        match err {
            SerializeError::SizeLimitExceeded { actual, limit } => {
                assert!(actual > 10);
                assert_eq!(limit, 10);
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_size_limit_ok() {
        let config = SerializeConfig {
            format: CertFormat::Compact,
            compress: false,
            include_metadata: false,
            max_size_bytes: Some(10_000),
        };
        let writer = CertWriter::new(config);
        let serialized = writer.serialize(SAMPLE_CERT).expect("should fit");
        assert!(serialized.data.len() <= 10_000);
    }

    // -----------------------------------------------------------------------
    // Error cases
    // -----------------------------------------------------------------------

    #[test]
    fn test_serialize_empty_data() {
        let writer = CertWriter::new(default_config());
        let err = writer.serialize("").expect_err("empty should fail");
        match err {
            SerializeError::InvalidData(msg) => assert!(msg.contains("empty")),
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_deserialize_corrupt_binary() {
        let reader = CertReader::new();
        let bad = SerializedCert {
            data: vec![b't', b'R', b'C'], // too short for binary
            format: CertFormat::Binary,
            original_size: 3,
            compressed: false,
        };
        let err = reader.deserialize(&bad).expect_err("should fail");
        match err {
            SerializeError::DeserializeFailed(msg) => {
                assert!(msg.contains("corrupt") || msg.contains("too short"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_rle_decompress_invalid_length() {
        // Not a multiple of 3.
        let err = rle_decompress(&[1, 2]).expect_err("should fail");
        match err {
            SerializeError::DeserializeFailed(msg) => {
                assert!(msg.contains("multiple of 3"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // CertReader utilities
    // -----------------------------------------------------------------------

    #[test]
    fn test_detect_format_binary() {
        let reader = CertReader::new();
        let data = b"tRCS\x01\x00some-payload";
        assert_eq!(reader.detect_format(data), Some(CertFormat::Binary));
    }

    #[test]
    fn test_detect_format_json() {
        let reader = CertReader::new();
        let data = b"{\n  \"format\": \"trust-cert\"\n}";
        assert_eq!(reader.detect_format(data), Some(CertFormat::Json));
    }

    #[test]
    fn test_detect_format_compact() {
        let reader = CertReader::new();
        let data = b"{\"format\":\"trust-cert\"}";
        assert_eq!(reader.detect_format(data), Some(CertFormat::Compact));
    }

    #[test]
    fn test_detect_format_unknown() {
        let reader = CertReader::new();
        assert_eq!(reader.detect_format(b""), None);
        assert_eq!(reader.detect_format(b"random data"), None);
    }

    // -----------------------------------------------------------------------
    // Size estimate
    // -----------------------------------------------------------------------

    #[test]
    fn test_cert_size_estimate() {
        let writer = CertWriter::new(binary_config());
        let estimate = writer.cert_size_estimate(SAMPLE_CERT);
        // Binary overhead is magic(4) + version(1) + flags(1) = 6
        assert_eq!(estimate, SAMPLE_CERT.len() + 6);
    }

    #[test]
    fn test_cert_size_estimate_json_no_metadata() {
        let config = SerializeConfig {
            format: CertFormat::Json,
            include_metadata: false,
            ..default_config()
        };
        let writer = CertWriter::new(config);
        let estimate = writer.cert_size_estimate(SAMPLE_CERT);
        assert_eq!(estimate, SAMPLE_CERT.len());
    }

    // -----------------------------------------------------------------------
    // Validate on deserialize
    // -----------------------------------------------------------------------

    #[test]
    fn test_validate_empty_data() {
        let reader = CertReader::new();
        assert!(!reader.validate_on_deserialize(b""));
    }

    #[test]
    fn test_validate_binary_too_short() {
        let reader = CertReader::new();
        // Has magic but no version/flags.
        assert!(!reader.validate_on_deserialize(b"tRCS"));
    }

    #[test]
    fn test_validate_valid_binary() {
        let reader = CertReader::new();
        assert!(reader.validate_on_deserialize(b"tRCS\x01\x00data"));
    }

    #[test]
    fn test_validate_json_data() {
        let reader = CertReader::new();
        assert!(reader.validate_on_deserialize(b"{\"valid\":true}"));
    }

    // -----------------------------------------------------------------------
    // compact_json helper
    // -----------------------------------------------------------------------

    #[test]
    fn test_compact_json_strips_whitespace() {
        let input = "{ \"key\" : \"value\" , \"num\" : 42 }";
        let result = compact_json(input);
        assert_eq!(result, "{\"key\":\"value\",\"num\":42}");
    }

    #[test]
    fn test_compact_json_preserves_string_whitespace() {
        let input = r#"{"msg": "hello world"}"#;
        let result = compact_json(input);
        assert_eq!(result, r#"{"msg":"hello world"}"#);
    }

    // -------------------------------------------------------------------
    // tRust #667: proptest roundtrip — deserialize(serialize(data)) == data
    // -------------------------------------------------------------------

    mod proptest_roundtrip {
        use super::*;
        use proptest::prelude::*;

        /// Strategy for generating arbitrary CertFormat values.
        fn arb_cert_format() -> impl Strategy<Value = CertFormat> {
            prop_oneof![
                Just(CertFormat::Binary),
                Just(CertFormat::Json),
                Just(CertFormat::Compact),
            ]
        }

        /// Strategy for generating arbitrary SerializeConfig values.
        fn arb_config() -> impl Strategy<Value = SerializeConfig> {
            (arb_cert_format(), any::<bool>(), any::<bool>()).prop_map(
                |(format, compress, include_metadata)| SerializeConfig {
                    format,
                    compress,
                    include_metadata,
                    max_size_bytes: None, // no limit for roundtrip tests
                },
            )
        }

        /// Strategy for generating non-empty certificate data strings.
        /// Uses valid JSON-like strings since the serializer treats input as text.
        fn arb_cert_data() -> impl Strategy<Value = String> {
            prop_oneof![
                // Simple JSON objects (common case)
                ("[a-z]{1,8}", "[a-z0-9]{1,16}").prop_map(|(k, v)| {
                    format!("{{\"{}\":\"{}\"}}", k, v)
                }),
                // Nested JSON
                ("[a-z]{1,4}", "[a-z]{1,4}", 0i32..1000).prop_map(|(k1, k2, n)| {
                    format!("{{\"{k1}\":{{\"{k2}\":{n}}}}}")
                }),
                // Plain alphanumeric strings (valid for Binary format)
                "[a-zA-Z0-9_]{1,64}",
            ]
        }

        proptest! {
            #![proptest_config(ProptestConfig::with_cases(300))]

            /// Roundtrip property: for Binary format without metadata wrapping,
            /// deserialize(serialize(data)) == data.
            ///
            /// For Json/Compact with metadata, the writer wraps the input in
            /// a JSON envelope, so the roundtrip returns the envelope, not the
            /// original. We test the raw-data path (no metadata) for exact
            /// roundtrip equality, and the metadata path for content inclusion.
            #[test]
            fn test_binary_roundtrip_proptest(data in arb_cert_data()) {
                let config = SerializeConfig {
                    format: CertFormat::Binary,
                    compress: false,
                    include_metadata: true,
                    max_size_bytes: None,
                };
                let writer = CertWriter::new(config);
                let reader = CertReader::new();

                let serialized = writer.serialize(&data).expect("serialize");
                let restored = reader.deserialize(&serialized).expect("deserialize");
                prop_assert_eq!(restored, data, "Binary roundtrip must be exact");
            }

            /// Compressed Binary roundtrip is exact.
            #[test]
            fn test_binary_compressed_roundtrip_proptest(data in arb_cert_data()) {
                let config = SerializeConfig {
                    format: CertFormat::Binary,
                    compress: true,
                    include_metadata: true,
                    max_size_bytes: None,
                };
                let writer = CertWriter::new(config);
                let reader = CertReader::new();

                let serialized = writer.serialize(&data).expect("serialize");
                prop_assert!(serialized.compressed);
                let restored = reader.deserialize(&serialized).expect("deserialize");
                prop_assert_eq!(restored, data, "Compressed Binary roundtrip must be exact");
            }

            /// Json/Compact without metadata: exact roundtrip for Compact,
            /// exact for Json (no wrapper added).
            #[test]
            fn test_json_no_metadata_roundtrip_proptest(data in arb_cert_data()) {
                let config = SerializeConfig {
                    format: CertFormat::Json,
                    compress: false,
                    include_metadata: false,
                    max_size_bytes: None,
                };
                let writer = CertWriter::new(config);
                let reader = CertReader::new();

                let serialized = writer.serialize(&data).expect("serialize");
                let restored = reader.deserialize(&serialized).expect("deserialize");
                prop_assert_eq!(restored, data, "Json (no metadata) roundtrip must be exact");
            }

            /// Compact without metadata: roundtrip preserves compacted form.
            #[test]
            fn test_compact_no_metadata_roundtrip_proptest(data in arb_cert_data()) {
                let config = SerializeConfig {
                    format: CertFormat::Compact,
                    compress: false,
                    include_metadata: false,
                    max_size_bytes: None,
                };
                let writer = CertWriter::new(config);
                let reader = CertReader::new();

                let serialized = writer.serialize(&data).expect("serialize");
                let restored = reader.deserialize(&serialized).expect("deserialize");
                // Compact strips whitespace outside strings, so restored ==
                // compact_json(data).
                let expected = compact_json(&data);
                prop_assert_eq!(
                    restored, expected,
                    "Compact (no metadata) roundtrip must equal compacted input"
                );
            }

            /// With metadata: roundtrip output contains the original data.
            #[test]
            fn test_metadata_roundtrip_contains_data_proptest(
                data in arb_cert_data(),
                format in prop_oneof![Just(CertFormat::Json), Just(CertFormat::Compact)],
                compress in any::<bool>(),
            ) {
                let config = SerializeConfig {
                    format,
                    compress,
                    include_metadata: true,
                    max_size_bytes: None,
                };
                let writer = CertWriter::new(config);
                let reader = CertReader::new();

                let serialized = writer.serialize(&data).expect("serialize");
                let restored = reader.deserialize(&serialized).expect("deserialize");
                // The metadata wrapper includes the original data.
                prop_assert!(
                    restored.contains(&data) || restored.contains(&compact_json(&data)),
                    "metadata roundtrip must contain original data"
                );
            }

            /// RLE compress/decompress roundtrip on arbitrary byte sequences.
            #[test]
            fn test_rle_roundtrip_proptest(data in proptest::collection::vec(any::<u8>(), 0..256)) {
                let compressed = rle_compress(&data);
                let decompressed = rle_decompress(&compressed).expect("decompress");
                prop_assert_eq!(decompressed, data, "RLE roundtrip must be exact");
            }
        }
    }
}
