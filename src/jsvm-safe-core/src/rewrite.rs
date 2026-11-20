//! Source rewriting after proof collection.
//!
//! `string_wizard` owns original-byte-indexed edit storage/materialization.
//! This module retains the deobfuscator-specific policy layered on top:
//! largest-span overlap arbitration, transform/proof accounting, and the
//! lexical separators required when an otherwise-safe rewrite would join
//! JavaScript tokens into a different token.

use crate::ArithmeticStateProof;
use oxc_ast::ast::{FunctionBody, Program, Statement};
use oxc_ast_visit::{walk, Visit};
use oxc_span::GetSpan;
use std::collections::{BTreeMap, HashSet};
use string_wizard::{MagicString, TextEdit};

#[derive(Debug, Clone)]
pub struct Replacement {
    pub(super) start: usize,
    pub(super) end: usize,
    pub(super) text: String,
    pub(super) kind: &'static str,
    pub(super) arithmetic_state_proof: Option<ArithmeticStateProof>,
}

#[derive(Default)]
pub struct Counts(BTreeMap<String, usize>);

impl Counts {
    fn bump(&mut self, kind: &str) {
        *self.0.entry(kind.to_string()).or_default() += 1;
    }

    pub(super) fn into_inner(self) -> BTreeMap<String, usize> {
        self.0
    }
}

const fn js_word_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'$') || byte >= 0x80
}

const fn needs_lexical_separator(left: u8, right: u8) -> bool {
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
    let mut occupied = BTreeMap::<usize, usize>::new();
    for candidate in replacements {
        // Selected non-empty intervals never overlap, so the selected interval
        // with the greatest start before candidate.end is the only one that can
        // overlap this candidate. This preserves the largest-span greedy policy
        // without the previous quadratic scan over every selected replacement.
        if candidate.start < candidate.end {
            if occupied
                .range(..candidate.end)
                .next_back()
                .is_some_and(|(_, end)| *end > candidate.start)
            {
                continue;
            }
            occupied.insert(candidate.start, candidate.end);
            selected.push(candidate);
            continue;
        }

        // Zero-width candidates sort after every non-empty interval. The old
        // overlap predicate rejects a point strictly inside a selected span,
        // while allowing points on either boundary and multiple points at the
        // same offset.
        if occupied
            .range(..candidate.start)
            .next_back()
            .is_some_and(|(_, end)| *end > candidate.start)
        {
            continue;
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

/// Statement-list source boundaries and true ECMAScript directive prologues.
/// Removing a statement or changing its leading token can invalidate a
/// previously implicit semicolon, even though the new program still parses.
#[derive(Default)]
struct StatementBoundaries {
    prologue_ends: HashSet<usize>,
    implicit_left: HashSet<usize>,
    nonempty_statements: HashSet<(usize, usize)>,
}

impl StatementBoundaries {
    fn record_prologue_end(
        &mut self,
        directives: &[oxc_ast::ast::Directive<'_>],
        body: &[Statement<'_>],
        source: &str,
    ) {
        if let Some(first) = body.first() {
            let start = first.span().start as usize;
            self.prologue_ends.insert(start);
            if let Some(last) = directives.last() {
                if !crate::fragment(source, last.span())
                    .trim_end()
                    .ends_with(';')
                {
                    self.implicit_left.insert(start);
                }
            }
        }
    }

    fn possible_directive(text: &str) -> bool {
        let text = text.trim_start();
        text.starts_with("<!--")
            || text.starts_with("-->")
            || text
                .chars()
                .next()
                .is_none_or(|first| matches!(first, '\'' | '"' | '/' | '\u{feff}'))
    }

    fn protect(&self, source: &str, replacements: &mut Vec<Replacement>) {
        for replacement in &mut *replacements {
            if replacement.text.is_empty()
                && self
                    .nonempty_statements
                    .contains(&(replacement.start, replacement.end))
            {
                // This either terminates the preceding statement or becomes
                // an empty statement, which can be cleaned up on a later pass.
                replacement.text.push(';');
            }
            let prologue_risk = self.prologue_ends.contains(&replacement.start)
                && Self::possible_directive(&replacement.text);
            let left_risk = self.implicit_left.contains(&replacement.start)
                && !replacement.text.is_empty()
                && !replacement.text.trim_start().starts_with(';');
            if prologue_risk || left_risk {
                // The new first token may join the preceding expression, or
                // create/destroy a directive. Source spans establish the
                // insertion is before an actual direct-list statement.
                replacement.text.insert_str(0, ";\n");
            }
        }
        // Do not repeat an attempted removal of a prologue terminator.
        replacements.retain(|replacement| {
            source
                .get(replacement.start..replacement.end)
                .is_none_or(|original| {
                    original != replacement.text
                        && !(original == ";" && replacement.text.trim() == ";")
                })
        });
    }
}

struct BoundaryCollector<'s> {
    source: &'s str,
    boundaries: StatementBoundaries,
}

impl<'a> Visit<'a> for BoundaryCollector<'_> {
    fn visit_program(&mut self, program: &Program<'a>) {
        self.boundaries
            .record_prologue_end(&program.directives, &program.body, self.source);
        walk::walk_program(self, program);
    }

    fn visit_function_body(&mut self, body: &FunctionBody<'a>) {
        self.boundaries
            .record_prologue_end(&body.directives, &body.statements, self.source);
        walk::walk_function_body(self, body);
    }

    fn visit_statements(&mut self, statements: &oxc_allocator::Vec<'a, Statement<'a>>) {
        let mut previous = None;
        for statement in statements {
            let span = statement.span();
            if previous
                .is_some_and(|span| !crate::fragment(self.source, span).trim_end().ends_with(';'))
            {
                self.boundaries.implicit_left.insert(span.start as usize);
            }
            if !matches!(statement, Statement::EmptyStatement(_)) {
                self.boundaries
                    .nonempty_statements
                    .insert((span.start as usize, span.end as usize));
            }
            previous = Some(span);
            self.visit_statement(statement);
        }
    }
}

pub fn apply(
    program: &Program<'_>,
    mut replacements: Vec<Replacement>,
    counts: &mut Counts,
    arithmetic_state_proofs: &mut Vec<ArithmeticStateProof>,
    iteration: usize,
) -> Option<String> {
    let mut collector = BoundaryCollector {
        source: program.source_text,
        boundaries: StatementBoundaries::default(),
    };
    collector.visit_program(program);
    collector
        .boundaries
        .protect(program.source_text, &mut replacements);
    if replacements.is_empty() {
        return Some(program.source_text.to_owned());
    }
    apply_raw(
        program.source_text,
        replacements,
        counts,
        arithmetic_state_proofs,
        iteration,
    )
}

fn apply_raw(
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
        let rewritten = apply_raw(
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

    fn quadratic_select_reference(mut replacements: Vec<Replacement>) -> Vec<Replacement> {
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

    fn selection_shape(replacements: Vec<Replacement>) -> Vec<(usize, usize, String)> {
        replacements
            .into_iter()
            .map(|replacement| (replacement.start, replacement.end, replacement.text))
            .collect()
    }

    #[test]
    fn indexed_selection_matches_quadratic_policy() {
        let mut state = 0x1234_5678_9abc_def0_u64;
        let mut replacements = Vec::new();
        for index in 0..2_000 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1);
            let Ok(start) = usize::try_from(state % 5_000) else {
                unreachable!();
            };
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1);
            let Ok(width) = usize::try_from(state % 80) else {
                unreachable!();
            };
            replacements.push(replacement(start, start + width, &format!("r{index}")));
        }

        let expected = selection_shape(quadratic_select_reference(replacements.clone()));
        let actual = selection_shape(select_replacements(replacements));
        assert_eq!(actual, expected);
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
        assert!(apply_raw(
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
