pub mod analysis_artifacts;
pub mod browser_script_types;
pub mod capture_import;
pub mod capture_project;
pub mod content_dedup;

mod har_project;
pub mod js_format;
pub mod js_refs;

pub mod bundle_materialize;
pub mod bundle_unpack;

pub mod browser_decode;

pub mod effect_shape;

pub mod numeric;
pub mod parse_int;
pub mod project_api_surface;
pub mod project_js_refs;
pub mod project_readme;
pub mod source_materialize;
pub mod vm_materialize;
pub mod wasm_materialize;
pub mod wasm_resource_provenance;

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

pub(crate) mod global_builtin;

pub mod wasm_import_semantics;

pub mod source_directive;

pub mod semantic_ir;

pub mod api_surface;

pub mod static_bytes;
pub mod structural_signals;
pub mod sus_scan;
