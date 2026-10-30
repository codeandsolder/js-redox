pub mod ast_utils;
pub mod source_text;
pub mod state_flatten;

pub mod har_project;

pub mod bundle_unpack;

pub mod browser_decode;

pub mod cfg_order;

pub mod effect_shape;

pub mod numeric;

pub mod pipeline;

/// Stable FNV-1a 64-bit hash used by persisted js-redox shape/identity formats.
#[must_use]
pub fn fnv1a64(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf2_9ce4_8422_2325_u64, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x0100_0000_01b3)
    })
}

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

pub mod receiver_identity;

pub mod registry_identity;

pub mod table_vm;

pub(crate) mod global_builtin;

pub mod wasm_import_semantics;

pub mod source_directive;

pub mod semantic_ir;

pub mod api_surface;

pub mod static_bytes;
pub mod structural_signals;
pub mod sus_scan;
