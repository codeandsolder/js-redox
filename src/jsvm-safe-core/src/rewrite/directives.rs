//! Validate directive prologues of retained lexical bodies against the exact
//! selected edit transaction. Parser acceptance alone does not establish
//! that strictness and other directive semantics remained unchanged.

use super::Replacement;
use oxc_allocator::Allocator;
use oxc_ast::ast::{Directive, FunctionBody, Program};
use oxc_ast_visit::{walk, Visit};
use std::collections::BTreeMap;

#[derive(Debug, PartialEq, Eq)]
struct DirectiveIdentity<'a> {
    raw: &'a str,
    // Oxc's canonical WTF-8 representation preserves every JavaScript
    // UTF-16 code unit, including lone surrogates. Comparing these arena
    // slices requires neither a lossy UTF-8 conversion nor a UTF-16 copy.
    cooked: &'a [u8],
}

impl<'a> From<&Directive<'a>> for DirectiveIdentity<'a> {
    fn from(directive: &Directive<'a>) -> Self {
        Self {
            raw: directive.directive.as_str(),
            cooked: directive.expression.value.as_bytes(),
        }
    }
}

fn identities<'a>(directives: &[Directive<'a>]) -> Vec<DirectiveIdentity<'a>> {
    directives.iter().map(DirectiveIdentity::from).collect()
}

fn same_directives(expected: &[DirectiveIdentity<'_>], actual: &[Directive<'_>]) -> bool {
    expected.len() == actual.len()
        && expected
            .iter()
            .zip(actual)
            .all(|(expected, actual)| *expected == DirectiveIdentity::from(actual))
}

fn brace_anchors(body: &FunctionBody<'_>, source: &str) -> Option<(usize, usize)> {
    let start = body.span.start as usize;
    let end = (body.span.end as usize).checked_sub(1)?;
    (source.as_bytes().get(start) == Some(&b'{')
        && source.as_bytes().get(end) == Some(&b'}')
        && start < end)
        .then_some((start, end))
}

/// Root directives and function bodies with actual source brace anchors.
/// Expression-bodied arrows have synthesized `FunctionBody` nodes without
/// brace anchors and cannot contain directive prologues.
#[derive(Default)]
pub(super) struct DirectiveInventory<'a> {
    root: Vec<DirectiveIdentity<'a>>,
    bodies: BTreeMap<(usize, usize), Vec<DirectiveIdentity<'a>>>,
}

impl<'a> DirectiveInventory<'a> {
    pub(super) fn record_program(&mut self, program: &Program<'a>) {
        self.root = identities(&program.directives);
    }

    pub(super) fn record_body(&mut self, body: &FunctionBody<'a>, source: &str) {
        if let Some(anchors) = brace_anchors(body, source) {
            self.bodies.insert(anchors, identities(&body.directives));
        }
    }

    /// Check the root and every function body whose exact original braces
    /// survive and still delimit a function body in the candidate parse.
    /// A transform replacing a function's delimiters owns its semantic
    /// obligations separately; this contract does not infer function identity
    /// from names, order, or textual resemblance.
    pub(super) fn preserves(
        &self,
        original: &Program<'_>,
        candidate: &str,
        edits: &[Replacement],
    ) -> bool {
        let Some(coordinates) = EditCoordinates::new(edits) else {
            return false;
        };
        let allocator = Allocator::default();
        let Some(program) = crate::parse_as(&allocator, candidate, original.source_type) else {
            return false;
        };
        if !same_directives(&self.root, &program.directives) {
            return false;
        }

        // Preserved byte coordinates are strictly order-preserving, so the
        // original BTreeMap order also sorts the mapped anchor pairs. Store
        // references to expectations rather than building a second inventory
        // of all candidate functions and their directive strings.
        let mapped = self
            .bodies
            .iter()
            .filter_map(|(&(start, end), expected)| {
                let anchors = coordinates
                    .preserved_byte(start)
                    .zip(coordinates.preserved_byte(end))?;
                Some((anchors, expected.as_slice()))
            })
            .collect::<Vec<_>>();
        let mut visitor = DirectiveValidator {
            source: candidate,
            mapped: &mapped,
            valid: true,
        };
        visitor.visit_program(&program);
        visitor.valid
    }
}

type MappedDirectiveBody<'inventory, 'source> =
    ((usize, usize), &'inventory [DirectiveIdentity<'source>]);

struct DirectiveValidator<'inventory, 'original, 'candidate> {
    source: &'candidate str,
    mapped: &'inventory [MappedDirectiveBody<'inventory, 'original>],
    valid: bool,
}

impl<'candidate> Visit<'candidate> for DirectiveValidator<'_, '_, 'candidate> {
    fn visit_function_body(&mut self, body: &FunctionBody<'candidate>) {
        if !self.valid {
            return;
        }
        if let Some(anchors) = brace_anchors(body, self.source) {
            if let Ok(index) = self.mapped.binary_search_by_key(&anchors, |(key, _)| *key) {
                self.valid = same_directives(self.mapped[index].1, &body.directives);
            }
        }
        if self.valid {
            walk::walk_function_body(self, body);
        }
    }
}

#[cfg(test)]
struct InventoryVisitor<'a> {
    source: &'a str,
    inventory: DirectiveInventory<'a>,
}

#[cfg(test)]
impl<'a> Visit<'a> for InventoryVisitor<'a> {
    fn visit_program(&mut self, program: &Program<'a>) {
        self.inventory.record_program(program);
        walk::walk_program(self, program);
    }

    fn visit_function_body(&mut self, body: &FunctionBody<'a>) {
        self.inventory.record_body(body, self.source);
        walk::walk_function_body(self, body);
    }
}

/// Original byte positions after a sorted, non-overlapping edit transaction.
/// Both inserted text and lexical-repair bytes are already included in text.
/// Zero-width insertions at an anchor precede the retained source byte.
struct EditCoordinates<'a> {
    edits: &'a [Replacement],
    prefix: Vec<(usize, usize)>,
}

impl<'a> EditCoordinates<'a> {
    fn new(edits: &'a [Replacement]) -> Option<Self> {
        let mut prefix = vec![(0usize, 0usize)];
        let (mut removed, mut inserted) = (0usize, 0usize);
        for edit in edits {
            removed = removed.checked_add(edit.end.checked_sub(edit.start)?)?;
            inserted = inserted.checked_add(edit.text.len())?;
            prefix.push((removed, inserted));
        }
        Some(Self { edits, prefix })
    }

    fn preserved_byte(&self, original: usize) -> Option<usize> {
        let count = self.edits.partition_point(|edit| edit.end <= original);
        if self
            .edits
            .get(count)
            .is_some_and(|edit| edit.start <= original)
        {
            return None;
        }
        let (removed, inserted) = *self.prefix.get(count)?;
        original.checked_sub(removed)?.checked_add(inserted)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn edit(start: usize, end: usize, text: &str) -> Replacement {
        Replacement {
            start,
            end,
            text: text.to_owned(),
            kind: "test",
            arithmetic_state_proof: None,
        }
    }

    fn accepts(original: &str, candidate: &str, edits: &[Replacement]) -> bool {
        let allocator = Allocator::default();
        let program = crate::parse_as(&allocator, original, oxc_span::SourceType::cjs())
            .unwrap_or_else(|| unreachable!());
        let mut visitor = InventoryVisitor {
            source: original,
            inventory: DirectiveInventory::default(),
        };
        visitor.visit_program(&program);
        visitor.inventory.preserves(&program, candidate, edits)
    }

    #[test]
    fn rejects_changed_root_directives_even_when_both_sources_parse() {
        assert!(!accepts(
            ";;'use strict';",
            "'use strict';",
            &[edit(0, 2, "")]
        ));
        assert!(!accepts(
            "'other';work();",
            "'another';work();",
            &[edit(0, 7, "'another'")]
        ));
        assert!(accepts(
            "'other';work();",
            "'other';work(1);",
            &[edit(13, 13, "1")]
        ));
    }

    #[test]
    fn directive_identity_preserves_lone_surrogates_and_raw_escape_spelling() {
        for original in [
            r"'\ud800';work();",
            r"'\udfff';work();",
            r"'\ud83d\ude00';work();",
            "'😀';work();",
            r"'use\x20strict';work();",
        ] {
            assert!(accepts(original, original, &[]));
        }

        let original = r"'\ud800';work();";
        let changed = r"'\udfff';work();";
        assert!(!accepts(original, changed, &[edit(0, 8, r"'\udfff'")]));

        let original = r"'use\x20strict';work();";
        let changed = "'use strict';work();";
        let Some(end) = original.find(';') else {
            unreachable!();
        };
        assert!(!accepts(original, changed, &[edit(0, end, "'use strict'")]));
    }

    #[test]
    fn verifies_retained_nested_body_after_other_edits_shift_coordinates() {
        let original = "/*π*/function f(){function g(){;'use strict';return this;}}";
        let Some(barrier) = original.find(";'use strict'") else {
            unreachable!();
        };
        let edits = [edit(0, 0, "/*new*/"), edit(barrier, barrier + 1, "")];
        let candidate = format!(
            "/*new*/{}{}",
            &original[..barrier],
            &original[barrier + 1..]
        );
        assert!(!accepts(original, &candidate, &edits));

        let candidate = format!("/*new*/{original}");
        assert!(accepts(original, &candidate, &[edit(0, 0, "/*new*/")]));
    }

    #[test]
    fn compares_only_mapped_function_bodies_among_inserted_and_removed_functions() {
        let original = "function discarded(){'gone';}function first(){'a';function nested(){'b';}}function last(){;'use strict';}";
        let Some(remove_end) = original.find("function first") else {
            unreachable!();
        };
        let Some(last) = original.find("function last") else {
            unreachable!();
        };
        let Some(barrier) = original.rfind(";'use strict'") else {
            unreachable!();
        };
        let insertion = "function inserted(){'new';}";
        let edits = [edit(0, remove_end, ""), edit(last, last, insertion)];
        let candidate = format!(
            "{}{insertion}{}",
            &original[remove_end..last],
            &original[last..]
        );
        assert!(accepts(original, &candidate, &edits));

        // The final original function retains its braces but acquires a new
        // directive. Unmatched inserted/removed bodies must not hide that.
        let bad_edits = [
            edit(0, remove_end, ""),
            edit(last, last, insertion),
            edit(barrier, barrier + 1, ""),
        ];
        let candidate = format!(
            "{}{insertion}{}{}",
            &original[remove_end..last],
            &original[last..barrier],
            &original[barrier + 1..]
        );
        assert!(!accepts(original, &candidate, &bad_edits));
    }

    #[test]
    fn replacing_a_complete_function_does_not_claim_the_old_body_identity() {
        let original = "function unused(){'use strict';}work();";
        let Some(end) = original.find("work()") else {
            unreachable!();
        };
        assert!(accepts(original, "work();", &[edit(0, end, "")]));
    }

    #[test]
    fn coordinate_map_matches_a_tagged_byte_reference() -> Result<(), std::num::TryFromIntError> {
        const LENGTH: usize = 128;
        let mut state = 0x4abc_13d5_u64;
        for _ in 0..64 {
            let mut edits = Vec::new();
            let mut cursor = 0usize;
            let mut tagged = Vec::new();
            while cursor < LENGTH {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1);
                let gap = usize::try_from(state % 5)?;
                let start = (cursor + gap).min(LENGTH);
                tagged.extend((cursor..start).map(Some));
                state = state.rotate_left(17);
                let end = (start + usize::try_from(state % 7)?).min(LENGTH);
                state = state.rotate_left(23);
                let inserted = usize::try_from(state % 6)?;
                edits.push(edit(start, end, &"x".repeat(inserted)));
                tagged.extend(std::iter::repeat_n(None, inserted));
                cursor = end;
                if start == cursor && cursor < LENGTH {
                    tagged.push(Some(cursor));
                    cursor += 1;
                }
            }
            let map = EditCoordinates::new(&edits).unwrap_or_else(|| unreachable!());
            for original in 0..LENGTH {
                assert_eq!(
                    map.preserved_byte(original),
                    tagged.iter().position(|byte| *byte == Some(original))
                );
            }
        }
        Ok(())
    }

    #[test]
    fn maps_retained_bytes_with_adjacent_replacements_and_insertions() {
        let edits = [
            edit(0, 2, "π"),
            edit(2, 2, "x"),
            edit(2, 3, ""),
            edit(4, 4, "abc"),
        ];
        let coordinates = EditCoordinates::new(&edits).unwrap_or_else(|| unreachable!());
        assert_eq!(coordinates.preserved_byte(0), None);
        assert_eq!(coordinates.preserved_byte(2), None);
        assert_eq!(coordinates.preserved_byte(3), Some(3));
        assert_eq!(coordinates.preserved_byte(4), Some(7));
    }
}
