// trust-cache/src/integrity.rs: HMAC-SHA256 integrity protection for cache files
//
// Computes HMAC-SHA256 over serialized cache entries using a key derived from
// the tRust executable hash and machine hostname. This prevents an attacker
// with filesystem write access from modifying cached results (e.g., changing
// "failed" to "proved") without detection.
//
// tRust #725: Cache integrity protection.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use hmac::{Hmac, Mac};
use sha2::{Digest, Sha256};

type HmacSha256 = Hmac<Sha256>;

/// Derive an HMAC key from the current executable's content hash and machine hostname.
///
/// The key is SHA-256(executable_hash || hostname), providing machine-local binding:
/// a cache file copied to another machine (different hostname or different tRust
/// binary) will fail HMAC verification.
#[must_use]
pub fn derive_cache_key() -> [u8; 32] {
    let exe_hash = executable_hash();
    let hostname = machine_hostname();

    let mut hasher = Sha256::new();
    hasher.update(exe_hash.as_bytes());
    hasher.update(b"\x00");
    hasher.update(hostname.as_bytes());
    let result = hasher.finalize();
    let mut key = [0u8; 32];
    key.copy_from_slice(&result);
    key
}

/// Compute HMAC-SHA256 over the given data using the provided key.
///
/// Returns a hex-encoded HMAC tag (64 characters).
#[must_use]
pub fn compute_hmac(key: &[u8; 32], data: &[u8]) -> String {
    let mut mac =
        HmacSha256::new_from_slice(key).expect("HMAC-SHA256 accepts any key length");
    mac.update(data);
    let result = mac.finalize();
    format!("{:x}", result.into_bytes())
}

/// Verify an HMAC-SHA256 tag over the given data.
///
/// Returns `true` if the tag matches, `false` if tampered or wrong key.
/// Uses constant-time comparison to prevent timing attacks.
pub fn verify_hmac(key: &[u8; 32], data: &[u8], expected_hex: &str) -> bool {
    let mut mac =
        HmacSha256::new_from_slice(key).expect("HMAC-SHA256 accepts any key length");
    mac.update(data);

    // Decode the expected hex tag
    let expected_bytes = match hex_decode(expected_hex) {
        Some(b) => b,
        None => return false,
    };

    // hmac::Mac::verify_slice uses constant-time comparison
    mac.verify_slice(&expected_bytes).is_ok()
}

/// SHA-256 hash of the current executable binary, hex-encoded.
///
/// Falls back to the executable path hash if the binary cannot be read
/// (e.g., deleted after launch). The fallback is less secure but still
/// provides machine-local binding.
fn executable_hash() -> String {
    let exe_path = std::env::current_exe().unwrap_or_default();
    match std::fs::read(&exe_path) {
        Ok(bytes) => {
            let mut hasher = Sha256::new();
            hasher.update(&bytes);
            format!("{:x}", hasher.finalize())
        }
        Err(_) => {
            // Fallback: hash the path itself
            let mut hasher = Sha256::new();
            hasher.update(exe_path.to_string_lossy().as_bytes());
            format!("{:x}", hasher.finalize())
        }
    }
}

/// Machine hostname, or "unknown" if unavailable.
///
/// Uses `std::env::var("HOSTNAME")` with fallback to `gethostname()` via
/// `std::process::Command`. No external crate dependency.
fn machine_hostname() -> String {
    // Try HOSTNAME env var first (set on most Linux/macOS systems)
    if let Ok(h) = std::env::var("HOSTNAME")
        && !h.is_empty()
    {
        return h;
    }
    // Fallback: call `hostname` command
    std::process::Command::new("hostname")
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "unknown".to_string())
}

/// Decode a hex string to bytes. Returns `None` on invalid hex.
fn hex_decode(hex: &str) -> Option<Vec<u8>> {
    if !hex.len().is_multiple_of(2) {
        return None;
    }
    let mut bytes = Vec::with_capacity(hex.len() / 2);
    for chunk in hex.as_bytes().chunks(2) {
        let high = hex_nibble(chunk[0])?;
        let low = hex_nibble(chunk[1])?;
        bytes.push((high << 4) | low);
    }
    Some(bytes)
}

/// Convert a single hex ASCII byte to its nibble value.
fn hex_nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_derive_cache_key_deterministic() {
        let k1 = derive_cache_key();
        let k2 = derive_cache_key();
        assert_eq!(k1, k2, "key derivation must be deterministic");
    }

    #[test]
    fn test_derive_cache_key_nonzero() {
        let key = derive_cache_key();
        assert_ne!(key, [0u8; 32], "derived key must not be all zeros");
    }

    #[test]
    fn test_compute_hmac_deterministic() {
        let key = [0xABu8; 32];
        let data = b"cache entry data";
        let h1 = compute_hmac(&key, data);
        let h2 = compute_hmac(&key, data);
        assert_eq!(h1, h2, "HMAC must be deterministic");
    }

    #[test]
    fn test_compute_hmac_hex_length() {
        let key = [0x42u8; 32];
        let hmac = compute_hmac(&key, b"test");
        assert_eq!(hmac.len(), 64, "HMAC-SHA256 hex is 64 chars");
        assert!(hmac.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn test_verify_hmac_valid() {
        let key = [0x42u8; 32];
        let data = b"important cache data";
        let tag = compute_hmac(&key, data);
        assert!(verify_hmac(&key, data, &tag), "valid HMAC must verify");
    }

    #[test]
    fn test_verify_hmac_tampered_data() {
        let key = [0x42u8; 32];
        let data = b"original data";
        let tag = compute_hmac(&key, data);
        let tampered = b"tampered data";
        assert!(
            !verify_hmac(&key, tampered, &tag),
            "tampered data must fail verification"
        );
    }

    #[test]
    fn test_verify_hmac_wrong_key() {
        let key1 = [0x42u8; 32];
        let key2 = [0x43u8; 32];
        let data = b"cache data";
        let tag = compute_hmac(&key1, data);
        assert!(
            !verify_hmac(&key2, data, &tag),
            "wrong key must fail verification"
        );
    }

    #[test]
    fn test_verify_hmac_invalid_hex() {
        let key = [0x42u8; 32];
        let data = b"test";
        assert!(!verify_hmac(&key, data, "not-hex!"), "invalid hex must fail");
        assert!(!verify_hmac(&key, data, "abc"), "odd-length hex must fail");
    }

    #[test]
    fn test_verify_hmac_empty_tag() {
        let key = [0x42u8; 32];
        let data = b"test";
        assert!(
            !verify_hmac(&key, data, ""),
            "empty tag must fail verification"
        );
    }

    #[test]
    fn test_different_data_different_hmac() {
        let key = [0x42u8; 32];
        let h1 = compute_hmac(&key, b"data1");
        let h2 = compute_hmac(&key, b"data2");
        assert_ne!(h1, h2, "different data must produce different HMACs");
    }

    #[test]
    fn test_hex_decode_roundtrip() {
        let key = [0x42u8; 32];
        let tag = compute_hmac(&key, b"test");
        let decoded = hex_decode(&tag);
        assert!(decoded.is_some());
        assert_eq!(decoded.unwrap().len(), 32, "SHA-256 HMAC is 32 bytes");
    }
}
