//! Decoder primitives used only after a decoder's surrounding structure has
//! already been proven safe.
//!
//! Standards-shaped Base64 is delegated to the mature `base64` crate.  The
//! fixed 65-symbol decoder stays bespoke because it models an observed
//! JavaScript `charAt`/`indexOf` implementation whose missing-character and
//! sentinel behavior is not RFC 4648 Base64.

use base64::{
    alphabet::Alphabet,
    engine::{
        general_purpose::{GeneralPurpose, GeneralPurposeConfig},
        DecodePaddingMode,
    },
    Engine as _,
};
use std::{collections::HashSet, sync::LazyLock};

const FORGIVING_CONFIG: GeneralPurposeConfig = GeneralPurposeConfig::new()
    .with_decode_padding_mode(DecodePaddingMode::Indifferent)
    .with_decode_allow_trailing_bits(true);
const STANDARD_ENGINE: GeneralPurpose =
    GeneralPurpose::new(&base64::alphabet::STANDARD, FORGIVING_CONFIG);
static LOWER_ENGINE: LazyLock<Option<GeneralPurpose>> = LazyLock::new(|| {
    Alphabet::new("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+/")
        .ok()
        .map(|alphabet| GeneralPurpose::new(&alphabet, FORGIVING_CONFIG))
});

fn lower_engine() -> Option<&'static GeneralPurpose> {
    LOWER_ENGINE.as_ref()
}

pub(super) fn decode_standard_base64_latin1(input: &str) -> Option<String> {
    // Match browser/atob-style ASCII whitespace handling before delegating the
    // actual alphabet and bit decoding.  Keep the pre-validation explicit so
    // internal/overlong padding remains rejected exactly as before.
    let compact = input
        .chars()
        .filter(|ch| !matches!(ch, ' ' | '\t' | '\n' | '\r' | '\x0c'))
        .collect::<String>();
    if compact.len() % 4 == 1 {
        return None;
    }

    let padding = compact.chars().rev().take_while(|ch| *ch == '=').count();
    if padding > 2 {
        return None;
    }
    if padding > 0 {
        if compact.len() % 4 != 0 || compact[..compact.len() - padding].contains('=') {
            return None;
        }
    } else if compact.contains('=') {
        return None;
    }

    let bytes = STANDARD_ENGINE.decode(compact).ok()?;
    Some(bytes.into_iter().map(char::from).collect())
}

pub(super) fn decode_lower_alphabet_base64_uri(input: &str) -> Option<String> {
    // The observed decoder stops at its first `=` sentinel rather than parsing
    // the suffix.  A final lone sextet contributes no complete byte, so drop it
    // before asking the standards engine to decode the useful prefix.
    let mut encoded = input.split_once('=').map_or(input, |(prefix, _)| prefix);
    if encoded.len() % 4 == 1 {
        encoded = &encoded[..encoded.len().checked_sub(1)?];
    }
    String::from_utf8(lower_engine()?.decode(encoded).ok()?).ok()
}

pub(super) fn decode_fixed_base64_latin1(input: &str, alphabet: &str) -> Option<String> {
    let alphabet = alphabet.chars().collect::<Vec<_>>();
    if alphabet.len() != 65 {
        return None;
    }
    let unique = alphabet.iter().copied().collect::<HashSet<_>>();
    if unique.len() != 65 {
        return None;
    }

    // Match the observed decoder rather than treating the alphabet as a
    // generic RFC 4648 alphabet: it first strips everything outside this
    // character class, then decodes in groups of four. Missing charAt()
    // positions become "", and alphabet.indexOf("") is 0 in JavaScript.
    let filtered = input
        .chars()
        .filter(|ch| ch.is_ascii_alphanumeric() || matches!(ch, '+' | '/' | '='))
        .collect::<Vec<_>>();

    let mut out = String::with_capacity(filtered.len().div_ceil(4) * 3);
    let mut index = 0usize;
    while index < filtered.len() {
        let symbol = |offset: usize| -> Option<usize> {
            match filtered.get(index + offset) {
                Some(ch) => alphabet.iter().position(|candidate| candidate == ch),
                None => Some(0),
            }
        };
        let a = symbol(0)?;
        let b = symbol(1)?;
        let c = symbol(2)?;
        let d = symbol(3)?;

        let mut push_code_unit = |value: usize| -> Option<()> {
            // String.fromCharCode applies ToUint16. These decoder expressions
            // are small, but mask explicitly so the modeled primitive is exact.
            out.push(char::from_u32((value & 0xffff) as u32)?);
            Some(())
        };
        push_code_unit((a << 2) | (b >> 4))?;
        if c != 64 {
            push_code_unit(((b & 15) << 4) | (c >> 2))?;
        }
        if d != 64 {
            push_code_unit(((c & 3) << 6) | d)?;
        }
        index += 4;
    }

    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn standard_decoder_keeps_atob_compatibility_edges() {
        assert_eq!(
            decode_standard_base64_latin1("SGVsbG8="),
            Some("Hello".into())
        );
        assert_eq!(
            decode_standard_base64_latin1(" S G\tV\nsbG8=\r"),
            Some("Hello".into())
        );
        assert_eq!(
            decode_standard_base64_latin1("SGVsbG8"),
            Some("Hello".into())
        );
        // Non-zero unused bits are accepted by forgiving-base64 / the previous
        // bit accumulator and still decode to the same complete byte.
        assert_eq!(decode_standard_base64_latin1("Zh=="), Some("f".into()));
        assert_eq!(decode_standard_base64_latin1("A"), None);
        assert_eq!(decode_standard_base64_latin1("SG=VsbG8="), None);
    }

    #[test]
    fn lower_first_alphabet_uses_library_engine_without_changing_sentinel_shape() {
        let encoded = lower_engine()
            .map(|engine| engine.encode("hello"))
            .unwrap_or_default();
        assert_eq!(
            decode_lower_alphabet_base64_uri(&encoded),
            Some("hello".into())
        );
        assert_eq!(decode_lower_alphabet_base64_uri("a"), Some(String::new()));
        let with_ignored_suffix = format!("{encoded}not-part-of-the-decoder");
        if encoded.contains('=') {
            assert_eq!(
                decode_lower_alphabet_base64_uri(&with_ignored_suffix),
                Some("hello".into())
            );
        }
    }
}
