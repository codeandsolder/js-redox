//! Source rewriting after proof collection.
//!
//! `string_wizard` owns original-byte-indexed edit storage/materialization.
//! This module retains the deobfuscator-specific policy layered on top:
//! largest-span overlap arbitration, transform/proof accounting, and the
//! lexical separators required when an otherwise-safe rewrite would join
//! JavaScript tokens into a different token.

use crate::ArithmeticStateProof;
use std::collections::BTreeMap;
use string_wizard::{MagicString, TextEdit};

#[derive(Debug, Clone)]
pub(super) struct Replacement {
    pub(super) start: usize,
    pub(super) end: usize,
    pub(super) text: String,
    pub(super) kind: &'static str,
    pub(super) arithmetic_state_proof: Option<ArithmeticStateProof>,
}

#[derive(Default)]
pub(super) struct Counts(BTreeMap<String, usize>);

impl Counts {
    fn bump(&mut self, kind: &str) {
        *self.0.entry(kind.to_string()).or_default() += 1;
    }

    pub(super) fn into_inner(self) -> BTreeMap<String, usize> {
        self.0
    }
}

fn js_word_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'$') || byte >= 0x80
}

fn needs_lexical_separator(left: u8, right: u8) -> bool {
    (js_word_byte(left) && js_word_byte(right))
        || (left == b'+' && right == b'+')
        || (left == b'-' && right == b'-')
        || (left == b'/' && matches!(right, b'/' | b'*'))
        || (left.is_ascii_digit() && right == b'.')
}

fn select_replacements(mut replacements: Vec<Replacement>) -> Vec<Replacement> {
    replacements.sort_by(|a, b| {
        (b.end - b.start)
            .cmp(&(a.end - a.start))
            .then_with(|| a.start.cmp(&b.start))
    });

    let mut selected: Vec<Replacement> = Vec::new();
    'next: for candidate in replacements {
        for existing in &selected {
            if candidate.start < existing.end && existing.start < candidate.end {
                continue 'next;
            }
        }
        selected.push(candidate);
    }
    selected.sort_by_key(|replacement| replacement.start);
    selected
}

#[derive(Clone, Copy)]
enum PieceOwner {
    Source,
    Replacement(usize),
}

struct Piece<'a> {
    owner: PieceOwner,
    text: &'a str,
}

/// Add only the separator bytes the old piecewise writer would have emitted.
///
/// A non-empty replacement can carry a leading/trailing separator itself. If
/// a deletion exposes a risky source/source boundary, the deleted range is
/// replaced by one space instead of the empty string. This leaves all edit
/// positions in original-source byte coordinates for `MagicString`.
fn lexically_safe_texts(source: &str, selected: &[Replacement]) -> Option<Vec<String>> {
    let mut adjusted = selected
        .iter()
        .map(|replacement| replacement.text.clone())
        .collect::<Vec<_>>();
    let mut pieces = Vec::with_capacity(selected.len() * 2 + 1);
    let mut cursor = 0usize;

    for (index, replacement) in selected.iter().enumerate() {
        pieces.push(Piece {
            owner: PieceOwner::Source,
            text: source.get(cursor..replacement.start)?,
        });
        pieces.push(Piece {
            owner: PieceOwner::Replacement(index),
            text: &replacement.text,
        });
        cursor = replacement.end;
    }
    pieces.push(Piece {
        owner: PieceOwner::Source,
        text: source.get(cursor..)?,
    });

    let nonempty = pieces
        .iter()
        .enumerate()
        .filter_map(|(index, piece)| (!piece.text.is_empty()).then_some(index))
        .collect::<Vec<_>>();

    for pair in nonempty.windows(2) {
        let left_index = pair[0];
        let right_index = pair[1];
        let left = &pieces[left_index];
        let right = &pieces[right_index];
        let (Some(left_byte), Some(right_byte)) = (
            left.text.as_bytes().last().copied(),
            right.text.as_bytes().first().copied(),
        ) else {
            continue;
        };
        if !needs_lexical_separator(left_byte, right_byte) {
            continue;
        }

        match (left.owner, right.owner) {
            (_, PieceOwner::Replacement(index)) => adjusted[index].insert(0, ' '),
            (PieceOwner::Replacement(index), PieceOwner::Source) => adjusted[index].push(' '),
            (PieceOwner::Source, PieceOwner::Source) => {
                let replacement_index =
                    pieces[left_index + 1..right_index]
                        .iter()
                        .find_map(|piece| match piece.owner {
                            PieceOwner::Replacement(index) => Some(index),
                            PieceOwner::Source => None,
                        })?;
                adjusted[replacement_index].push(' ');
            }
        }
    }

    Some(adjusted)
}

pub(super) fn apply(
    source: &str,
    replacements: Vec<Replacement>,
    counts: &mut Counts,
    arithmetic_state_proofs: &mut Vec<ArithmeticStateProof>,
    iteration: usize,
) -> Option<String> {
    let mut selected = select_replacements(replacements);
    let adjusted = lexically_safe_texts(source, &selected)?;
    let mut magic = MagicString::try_new(source).ok()?;
    magic
        .apply_edits(
            selected
                .iter()
                .zip(adjusted)
                .map(|(replacement, text)| TextEdit::new(replacement.start, replacement.end, text)),
        )
        .ok()?;

    // Do not publish accounting/proof side effects until every edit was
    // accepted. A malformed range therefore fails closed as one transaction.
    for replacement in &mut selected {
        counts.bump(replacement.kind);
        if let Some(mut proof) = replacement.arithmetic_state_proof.take() {
            proof.iteration = iteration;
            arithmetic_state_proofs.push(proof);
        }
    }

    Some(magic.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn replacement(start: usize, end: usize, text: &str) -> Replacement {
        Replacement {
            start,
            end,
            text: text.to_string(),
            kind: "test",
            arithmetic_state_proof: None,
        }
    }

    fn rewrite(source: &str, replacements: Vec<Replacement>) -> String {
        let rewritten = apply(
            source,
            replacements,
            &mut Counts::default(),
            &mut Vec::new(),
            1,
        );
        assert!(rewritten.is_some(), "rewrite failed for {source:?}");
        rewritten.unwrap_or_default()
    }

    #[test]
    fn preserves_overlap_and_lexical_boundary_policy() {
        assert_eq!(
            rewrite(
                "abcdefgh",
                vec![replacement(2, 4, "x"), replacement(1, 6, "Y")],
            ),
            "a Y gh"
        );
        assert_eq!(rewrite("fooXXbar", vec![replacement(3, 5, "")]), "foo bar");
        assert_eq!(rewrite("a+XX+b", vec![replacement(2, 4, "")]), "a+ +b");
        assert_eq!(rewrite("a-XX-b", vec![replacement(2, 4, "")]), "a- -b");
        assert_eq!(rewrite("a/XX/b", vec![replacement(2, 4, "")]), "a/ /b");
        assert_eq!(rewrite("a/XX*b", vec![replacement(2, 4, "")]), "a/ *b");
        assert_eq!(rewrite("1XX.foo", vec![replacement(1, 3, "")]), "1 .foo");
        assert_eq!(
            rewrite(
                "fooXXYYbar",
                vec![replacement(3, 5, ""), replacement(5, 7, "")],
            ),
            "foo bar"
        );
    }

    #[test]
    fn uses_oxc_compatible_utf8_byte_offsets() {
        let source = "ππfooXXbar";
        assert_eq!(
            rewrite(
                source,
                vec![replacement("ππfoo".len(), "ππfooXX".len(), "")],
            ),
            "ππfoo bar"
        );
    }

    #[test]
    fn malformed_spans_fail_before_accounting() {
        let mut counts = Counts::default();
        let mut proofs = Vec::new();
        assert!(apply(
            "πx",
            vec![replacement(1, 2, "y")],
            &mut counts,
            &mut proofs,
            1
        )
        .is_none());
        assert!(counts.into_inner().is_empty());
        assert!(proofs.is_empty());
    }
}
