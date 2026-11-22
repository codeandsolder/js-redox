//! Validate directive prologues of retained lexical bodies against the exact
//! selected edit transaction. Parser acceptance alone does not establish
//! that strictness and other directive semantics remained unchanged.

use super::Replacement;
use oxc_allocator::Allocator;
use oxc_ast::ast::{Directive, FunctionBody, Program};
use oxc_ast_visit::{walk, Visit};
use std::collections::BTreeMap;

#[derive(Debug, PartialEq, Eq)]
struct DirectiveIdentity {
    raw: String,
    cooked: String,
}

fn identities(directives: &[Directive<'_>]) -> Vec<DirectiveIdentity> {
    directives
        .iter()
        .map(|directive| DirectiveIdentity {
            raw: directive.directive.to_string(),
            cooked: directive.expression.value.to_string(),
        })
        .collect()
}

/// Root directives and function bodies with actual source brace anchors.
/// Expression-bodied arrows have synthesized FunctionBody nodes without
/// brace anchors and cannot contain directive prologues.
#[derive(Default)]
pub(super) struct DirectiveInventory {
    root: Vec<DirectiveIdentity>,
    bodies: BTreeMap<(usize, usize), Vec<DirectiveIdentity>>,
}

impl DirectiveInventory {
    pub(super) fn record_program(&mut self, program: &Program<'_>) {
        self.root = identities(&program.directives);
    }

    pub(super) fn record_body(&mut self, body: &FunctionBody<'_>, source: &str) {
        let start = body.span.start as usize;
        let Some(end) = (body.span.end as usize).checked_sub(1) else {
            return;
        };
        if source.as_bytes().get(start) == Some(&b'{')
            && source.as_bytes().get(end) == Some(&b'}')
            && start < end
        {
            self.bodies
                .insert((start, end), identities(&body.directives));
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
        let mut visitor = InventoryVisitor {
            source: candidate,
            inventory: Self::default(),
        };
        visitor.visit_program(&program);
        let actual = visitor.inventory;
        self.root == actual.root
            && self.bodies.iter().all(|(&(start, end), expected)| {
                let Some(mapped) = coordinates
                    .preserved_byte(start)
                    .zip(coordinates.preserved_byte(end))
                else {
                    return true;
                };
                actual
                    .bodies
                    .get(&mapped)
                    .is_none_or(|found| found == expected)
            })
    }
}

struct InventoryVisitor<'s> {
    source: &'s str,
    inventory: DirectiveInventory,
}

impl<'a> Visit<'a> for InventoryVisitor<'_> {
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
