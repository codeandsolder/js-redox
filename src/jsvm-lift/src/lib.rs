pub mod har_project;

pub mod effect_shape;

pub mod numeric;

pub mod pipeline;

/// Return the SHA-256 digest of `bytes` as lowercase hexadecimal.
#[must_use]
pub fn sha256_hex(bytes: &[u8]) -> String {
    use sha2::{Digest, Sha256};

    const HEX: &[u8; 16] = b"0123456789abcdef";
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(digest.len() * 2);
    for byte in digest {
        out.push(char::from(HEX[usize::from(byte >> 4)]));
        out.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    out
}

pub mod forwarding_alias;

pub mod forwarding_semantics;

pub mod wasm_import_semantics;

pub mod source_directive;
