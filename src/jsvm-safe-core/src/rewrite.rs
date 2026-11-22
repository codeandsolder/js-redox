//! Source rewriting after proof collection.
//!
//! `string_wizard` owns original-byte-indexed edit storage/materialization.
//! This module retains the deobfuscator-specific policy layered on top:
//! largest-span overlap arbitration, transform/proof accounting, and the
//! lexical separators required when an otherwise-safe rewrite would join
//! JavaScript tokens into a different token.

use crate::ArithmeticStateProof;
use oxc_ast::ast::{Expression, FunctionBody, Program, Statement};
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
    // Match MagicString's original-byte ordering: insertions must precede
    // a nonempty edit starting at the same offset. Preserve input order
    // between multiple insertions at one offset.
    selected.sort_by_key(|replacement| (replacement.start, replacement.end));
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
    // An implicit directive terminator and the empty statement that prevents
    // another directive are independent boundaries. A single semicolon can
    // terminate the directive without terminating its prologue.
    implicit_directive_left: HashSet<usize>,
    implicit_left: HashSet<usize>,
    nonempty_statements: HashSet<(usize, usize)>,
    // A leading empty run may be redundant if its first nonempty statement
    // cannot be a directive and the entire prologue prefix remains unchanged.
    leading_empty_statements: HashSet<(usize, usize)>,
    releasable_prologues: BTreeMap<usize, (usize, usize)>,
}

impl StatementBoundaries {
    fn record_prologue_end(
        &mut self,
        directives: &[oxc_ast::ast::Directive<'_>],
        body: &[Statement<'_>],
        source: &str,
        body_start: usize,
    ) {
        let Some(first) = body.first() else {
            return;
        };
        let start = first.span().start as usize;
        self.prologue_ends.insert(start);
        if directives.last().is_some_and(|last| {
            !crate::fragment(source, last.span())
                .trim_end()
                .ends_with(';')
        }) {
            self.implicit_directive_left.insert(start);
            return;
        }
        if !matches!(first, Statement::EmptyStatement(_)) {
            return;
        }

        let mut prefix_end = first.span().end as usize;
        for statement in body {
            let span = statement.span();
            prefix_end = span.end as usize;
            if matches!(statement, Statement::EmptyStatement(_)) {
                self.leading_empty_statements
                    .insert((span.start as usize, prefix_end));
                continue;
            }
            // A bare string literal expression would become a directive.
            // Other expression shapes and other statements terminate a
            // directive prologue without requiring an empty statement.
            if matches!(statement, Statement::ExpressionStatement(expr)
                if matches!(expr.expression, Expression::StringLiteral(_)))
            {
                return;
            }
            break;
        }
        self.releasable_prologues
            .insert(start, (body_start, prefix_end));
    }

    fn removes_leading_empty(&self, edit: &Replacement) -> bool {
        edit.text.is_empty()
            && self
                .leading_empty_statements
                .contains(&(edit.start, edit.end))
    }

    /// Index every competing edit, including insertions and edits later
    /// rejected by overlap arbitration. A prefix is releasable only when
    /// its existing syntax remains intact apart from empty-run deletion.
    fn releasable_starts(&self, replacements: &[Replacement]) -> HashSet<usize> {
        if self.releasable_prologues.is_empty() {
            return HashSet::new();
        }
        let mut competing = BTreeMap::<usize, usize>::new();
        for edit in replacements {
            if !self.removes_leading_empty(edit) {
                let end = competing.entry(edit.start).or_default();
                *end = (*end).max(edit.end);
            }
        }
        let mut furthest_end = 0;
        for end in competing.values_mut() {
            furthest_end = furthest_end.max(*end);
            *end = furthest_end;
        }
        self.releasable_prologues
            .iter()
            .filter_map(|(&start, &(left, right))| {
                let touched = competing
                    .range(..=right)
                    .next_back()
                    .is_some_and(|(_, end)| *end >= left);
                (!touched).then_some(start)
            })
            .collect()
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
        let releasable = self.releasable_starts(replacements);
        for replacement in &mut *replacements {
            let releases_empty_prologue =
                releasable.contains(&replacement.start) && self.removes_leading_empty(replacement);
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
                && !releases_empty_prologue
                && Self::possible_directive(&replacement.text);
            if prologue_risk {
                // An empty statement prevents a newly exposed string from
                // joining the original directive prologue.
                replacement.text.insert_str(0, ";\n");
            }
            let left_risk = self.implicit_directive_left.contains(&replacement.start)
                || (self.implicit_left.contains(&replacement.start)
                    && !replacement.text.is_empty()
                    && !replacement.text.trim_start().starts_with(';'));
            if left_risk {
                // An existing directive without an explicit semicolon must
                // receive its own terminator, even if the replacement now
                // begins with an empty statement. Otherwise ASI absorbs that
                // empty statement and exposes a new directive.
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
        self.boundaries.record_prologue_end(
            &program.directives,
            &program.body,
            self.source,
            program.span.start as usize,
        );
        walk::walk_program(self, program);
    }

    fn visit_function_body(&mut self, body: &FunctionBody<'a>) {
        self.boundaries.record_prologue_end(
            &body.directives,
            &body.statements,
            self.source,
            body.span.start as usize,
        );
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
    // Validate every candidate before span-width subtraction or overlap
    // arbitration. A malformed candidate must not panic or silently vanish
    // behind a larger, valid overlapping replacement.
    if replacements
        .iter()
        .any(|edit| source.get(edit.start..edit.end).is_none())
    {
        return None;
    }
    let mut selected = select_replacements(replacements);
    let adjusted = lexically_safe_texts(source, &selected)?;
    let mut magic = MagicString::try_new(source).ok()?;
    magic
        .apply_edits(selected.iter().zip(&adjusted).map(|(replacement, text)| {
            TextEdit::new(replacement.start, replacement.end, text.as_str())
        }))
        .ok()?;

    // Do not publish accounting/proof side effects until every edit was
    // accepted. A malformed range therefore fails closed as one transaction.
    // Lexical repair can also restore the original text of an edit, or
    // multiple edits can cancel. Neither changes the source nor proves a
    // transformation occurred.
    let rewritten = magic.to_string();
    if rewritten == source {
        return Some(rewritten);
    }
    for (replacement, text) in selected.iter_mut().zip(&adjusted) {
        if source.get(replacement.start..replacement.end) == Some(text.as_str()) {
            continue;
        }
        counts.bump(replacement.kind);
        if let Some(mut proof) = replacement.arithmetic_state_proof.take() {
            proof.iteration = iteration;
            arithmetic_state_proofs.push(proof);
        }
    }

    Some(rewritten)
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

    fn rewrite_script(source: &str, edits: Vec<Replacement>) -> String {
        let allocator = oxc_allocator::Allocator::default();
        let program = crate::parse_as(&allocator, source, oxc_span::SourceType::cjs())
            .unwrap_or_else(|| unreachable!());
        apply(&program, edits, &mut Counts::default(), &mut Vec::new(), 1)
            .unwrap_or_else(|| unreachable!())
    }

    #[test]
    fn leading_empty_run_can_disappear_before_an_unchanged_nondirective() {
        for (source, expected) in [
            (";;work();", "work();"),
            (";;'x'+work();", "'x'+work();"),
            (";;('x');", "('x');"),
            (";;", ""),
            (";;; 'use strict';", "; 'use strict';"),
        ] {
            let edits = (0..source.bytes().take_while(|byte| *byte == b';').count())
                .map(|index| replacement(index, index + 1, ""))
                .collect();
            assert_eq!(rewrite_script(source, edits), expected);
        }
    }

    #[test]
    fn implicit_directive_termination_is_independent_of_prologue_barrier() {
        for (source, old, text) in [
            ("'other'\n{}\n'use strict';", "{}", ""),
            ("'other'\n0;\n'use strict';", "0;", ""),
            (
                "'other'\n'use ' + 'strict';",
                "'use ' + 'strict'",
                "\"use strict\"",
            ),
            ("'other'\n{}\n'use strict';", "{}", ";"),
        ] {
            let Some(start) = source.find(old) else {
                unreachable!();
            };
            let rewritten =
                rewrite_script(source, vec![replacement(start, start + old.len(), text)]);
            let allocator = oxc_allocator::Allocator::default();
            let program = crate::parse_as(&allocator, &rewritten, oxc_span::SourceType::cjs())
                .unwrap_or_else(|| unreachable!());
            assert_eq!(program.directives.len(), 1, "{rewritten}");
            assert_eq!(program.directives[0].directive, "other");
            assert!(
                matches!(program.body.first(), Some(Statement::EmptyStatement(_))),
                "{rewritten}"
            );
        }
    }

    #[test]
    fn competing_rewrite_cannot_turn_an_exposed_statement_into_a_directive() {
        let source = ";;work();";
        let edits = vec![
            replacement(0, 1, ""),
            replacement(1, 2, ""),
            replacement(2, source.len(), "'use strict';"),
        ];
        assert_eq!(rewrite_script(source, edits), ";'use strict';");

        let edits = vec![
            replacement(0, 1, ""),
            replacement(1, 2, ""),
            replacement(2, 2, "'use strict';"),
        ];
        assert_eq!(rewrite_script(source, edits), ";'use strict';work();");
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
        selected.sort_by_key(|replacement| (replacement.start, replacement.end));
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
    fn orders_boundary_insertions_before_same_start_replacements() {
        assert_eq!(
            rewrite(
                "()",
                vec![
                    replacement(0, 1, "["),
                    replacement(0, 0, "{"),
                    replacement(0, 0, "("),
                    replacement(1, 2, "]"),
                    replacement(2, 2, ")"),
                    replacement(2, 2, "}"),
                ],
            ),
            "{([])}"
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

    fn replacement_with_proof(start: usize, end: usize, text: &str) -> Replacement {
        let mut edit = replacement(start, end, text);
        edit.arithmetic_state_proof = Some(ArithmeticStateProof {
            iteration: 0,
            input_start: start,
            input_end: end,
            state_var: "state".to_owned(),
            state_path: vec!["1".to_owned()],
            termination: "test".to_owned(),
            register_reads_rewritten: 0,
            branch_test: None,
            branch_paths: Vec::new(),
            branch_terminations: Vec::new(),
        });
        edit
    }

    #[test]
    fn only_counts_effective_edits_after_lexical_repair() {
        let mut counts = Counts::default();
        let mut proofs = Vec::new();
        assert_eq!(
            apply_raw(
                "a b",
                vec![replacement_with_proof(1, 2, "")],
                &mut counts,
                &mut proofs,
                1,
            )
            .as_deref(),
            Some("a b")
        );
        assert!(counts.0.is_empty());
        assert!(proofs.is_empty());
        assert_eq!(
            apply_raw(
                "a b; 7",
                vec![
                    replacement_with_proof(1, 2, ""),
                    replacement_with_proof(5, 6, "8")
                ],
                &mut counts,
                &mut proofs,
                2,
            )
            .as_deref(),
            Some("a b; 8")
        );
        assert_eq!(
            counts.into_inner(),
            BTreeMap::from([("test".to_owned(), 1)])
        );
        assert_eq!(proofs.len(), 1);
        assert_eq!(proofs[0].input_start, 5);
        assert_eq!(proofs[0].iteration, 2);
    }

    #[test]
    fn cancelling_edits_do_not_publish_accounting() {
        let mut counts = Counts::default();
        assert_eq!(
            apply_raw(
                "()",
                vec![replacement(0, 0, "("), replacement(0, 1, "")],
                &mut counts,
                &mut Vec::new(),
                1,
            )
            .as_deref(),
            Some("()")
        );
        assert!(counts.into_inner().is_empty());
    }

    #[test]
    fn malformed_spans_fail_before_accounting() {
        let mut counts = Counts::default();
        let mut proofs = Vec::new();
        for edits in [
            vec![replacement(1, 2, "y")],
            vec![replacement(2, 0, "y")],
            vec![replacement(2, 4, "y")],
            vec![replacement(0, 3, "z"), replacement(1, 2, "y")],
        ] {
            assert!(apply_raw("πx", edits, &mut counts, &mut proofs, 1).is_none());
        }
        assert!(counts.into_inner().is_empty());
        assert!(proofs.is_empty());
    }
}
