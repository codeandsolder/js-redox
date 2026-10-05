use crate::source_text::preview;
use oxc_ast::ast::{Argument, ArrayExpression, ArrayExpressionElement, CallExpression, Expression};
use oxc_span::GetSpan;
use serde::Serialize;
use std::collections::BTreeSet;

#[derive(Debug, Clone, Serialize)]
pub struct WidthHint {
    pub width: usize,
    pub opcode_unique: usize,
    pub opcode_max: u64,
    pub operand_max: u64,
    pub score: i32,
}

#[derive(Debug, Clone, Serialize)]
pub struct ArrayCandidate {
    pub start: u32,
    pub end: u32,
    pub elements: usize,
    pub numeric: usize,
    pub byte_values: usize,
    pub numeric_ratio: f64,
    pub width_hints: Vec<WidthHint>,
    pub preview: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct BuilderUnknown {
    pub index: usize,
    pub preview: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct PushBuilderCandidate {
    pub start: u32,
    pub end: u32,
    pub receiver: String,
    pub arguments: usize,
    pub numeric_literals: usize,
    pub byte_literals: usize,
    pub call_arguments: usize,
    pub other_arguments: usize,
    pub width_hints: Vec<WidthHint>,
    pub values: Vec<Option<u64>>,
    pub unknowns: Vec<BuilderUnknown>,
    pub preview: String,
}

pub struct DetectedPushBuilder {
    pub candidate: PushBuilderCandidate,
    pub receiver_ident: Option<String>,
}

fn target_ident(target: &oxc_ast::ast::AssignmentTarget<'_>) -> Option<String> {
    match target {
        oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(id) => Some(id.name.to_string()),
        _ => None,
    }
}

fn builder_receiver_ident(expr: &Expression<'_>) -> Option<String> {
    match expr {
        Expression::Identifier(id) => Some(id.name.to_string()),
        Expression::AssignmentExpression(assign) if assign.operator.is_assign() => {
            target_ident(&assign.left)
        }
        Expression::ParenthesizedExpression(paren) => builder_receiver_ident(&paren.expression),
        _ => None,
    }
}

pub fn detect_push_builder(source: &str, call: &CallExpression<'_>) -> Option<DetectedPushBuilder> {
    let Expression::StaticMemberExpression(member) = &call.callee else {
        return None;
    };
    if member.property.name.as_str() != "push" || call.arguments.len() < 16 {
        return None;
    }

    let mut numeric_literals = 0usize;
    let mut byte_literals = 0usize;
    let mut call_arguments = 0usize;
    let mut other_arguments = 0usize;
    let mut values = Vec::with_capacity(call.arguments.len());
    let mut unknowns = Vec::new();

    for (arg_index, arg) in call.arguments.iter().enumerate() {
        match arg {
            Argument::NumericLiteral(n) => {
                numeric_literals += 1;
                if n.value.is_finite() && n.value >= 0.0 && n.value.fract() == 0.0 {
                    let value = n.value as u64;
                    if value <= 255 {
                        byte_literals += 1;
                    }
                    values.push(Some(value));
                } else {
                    values.push(None);
                }
            }
            Argument::CallExpression(_) => {
                call_arguments += 1;
                values.push(None);
                let span = arg.span();
                unknowns.push(BuilderUnknown {
                    index: arg_index,
                    preview: preview(source, span.start, span.end, 120),
                });
            }
            _ => {
                other_arguments += 1;
                values.push(None);
                let span = arg.span();
                unknowns.push(BuilderUnknown {
                    index: arg_index,
                    preview: preview(source, span.start, span.end, 120),
                });
            }
        }
    }

    let recognized = numeric_literals + call_arguments;
    if recognized * 4 < call.arguments.len() * 3 {
        return None;
    }

    let mut width_hints = Vec::new();
    for width in 2usize..=8 {
        if call.arguments.len() < width * 8 || !call.arguments.len().is_multiple_of(width) {
            continue;
        }
        let instructions = call.arguments.len() / width;
        let mut opcode_values = BTreeSet::new();
        let mut opcode_max = 0u64;
        let mut operand_max = 0u64;
        let mut known_opcodes = 0usize;

        for (i, value) in values.iter().enumerate() {
            let Some(value) = value else { continue };
            if i % width == 0 {
                known_opcodes += 1;
                opcode_values.insert(*value);
                opcode_max = opcode_max.max(*value);
            } else {
                operand_max = operand_max.max(*value);
            }
        }

        if known_opcodes * 2 < instructions {
            continue;
        }

        let mut score = 2i32;
        if known_opcodes * 4 >= instructions * 3 {
            score += 3;
        } else {
            score += 1;
        }
        if opcode_max <= 63 {
            score += 4;
        } else if opcode_max <= 127 {
            score += 2;
        }
        if opcode_values.len() <= 64 {
            score += 2;
        }
        if opcode_values.len() * 2 <= instructions {
            score += 1;
        }
        if operand_max > opcode_max.saturating_mul(2) {
            score += 2;
        }

        if score >= 7 {
            width_hints.push(WidthHint {
                width,
                opcode_unique: opcode_values.len(),
                opcode_max,
                operand_max,
                score,
            });
        }
    }
    width_hints.sort_by_key(|hint| std::cmp::Reverse(hint.score));

    let receiver_ident = builder_receiver_ident(&member.object);
    let span = member.object.span();
    Some(DetectedPushBuilder {
        candidate: PushBuilderCandidate {
            start: call.span.start,
            end: call.span.end,
            receiver: preview(source, span.start, span.end, 96),
            arguments: call.arguments.len(),
            numeric_literals,
            byte_literals,
            call_arguments,
            other_arguments,
            width_hints,
            values,
            unknowns,
            preview: preview(source, call.span.start, call.span.end, 140),
        },
        receiver_ident,
    })
}

pub fn detect_numeric_array(source: &str, array: &ArrayExpression<'_>) -> Option<ArrayCandidate> {
    let n = array.elements.len();
    if n < 16 {
        return None;
    }

    let mut numeric = 0usize;
    let mut byte_values = 0usize;
    let mut values = Vec::with_capacity(n);
    for element in &array.elements {
        match element {
            ArrayExpressionElement::NumericLiteral(value)
                if value.value.is_finite() && value.value >= 0.0 =>
            {
                let integer = value.value as u64;
                if (integer as f64 - value.value).abs() < f64::EPSILON {
                    numeric += 1;
                    if integer <= 255 {
                        byte_values += 1;
                    }
                    values.push(Some(integer));
                } else {
                    values.push(None);
                }
            }
            _ => values.push(None),
        }
    }

    if numeric * 4 < n * 3 {
        return None;
    }

    let mut hints = Vec::new();
    if numeric == n && n >= 32 {
        for width in 2usize..=8 {
            if n < width * 8 {
                continue;
            }
            let mut opcodes = BTreeSet::new();
            let mut opcode_max = 0u64;
            let mut operand_max = 0u64;
            let mut complete = true;
            for (i, value) in values.iter().enumerate() {
                let Some(value) = value else {
                    complete = false;
                    break;
                };
                if i % width == 0 {
                    opcodes.insert(*value);
                    opcode_max = opcode_max.max(*value);
                } else {
                    operand_max = operand_max.max(*value);
                }
            }
            if !complete {
                continue;
            }
            let instructions = n / width;
            let mut score = 0i32;
            if n.is_multiple_of(width) {
                score += 2;
            }
            if opcode_max <= 63 {
                score += 4;
            } else if opcode_max <= 127 {
                score += 2;
            }
            if operand_max > opcode_max.saturating_mul(2) {
                score += 2;
            }
            if opcodes.len() <= 64 {
                score += 2;
            }
            if opcodes.len() * 2 <= instructions {
                score += 1;
            }
            if score >= 5 {
                hints.push(WidthHint {
                    width,
                    opcode_unique: opcodes.len(),
                    opcode_max,
                    operand_max,
                    score,
                });
            }
        }
        hints.sort_by_key(|hint| std::cmp::Reverse(hint.score));
    }

    Some(ArrayCandidate {
        start: array.span.start,
        end: array.span.end,
        elements: n,
        numeric,
        byte_values,
        numeric_ratio: numeric as f64 / n as f64,
        width_hints: hints,
        preview: preview(source, array.span.start, array.span.end, 120),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use oxc_allocator::Allocator;
    use oxc_ast_visit::{walk, Visit};
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;

    #[derive(Default)]
    struct Harness<'s> {
        source: &'s str,
        arrays: Vec<ArrayCandidate>,
        builders: Vec<DetectedPushBuilder>,
    }

    impl<'a> Visit<'a> for Harness<'_> {
        fn visit_array_expression(&mut self, array: &ArrayExpression<'a>) {
            if let Some(candidate) = detect_numeric_array(self.source, array) {
                self.arrays.push(candidate);
            }
            walk::walk_array_expression(self, array);
        }

        fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
            if let Some(candidate) = detect_push_builder(self.source, call) {
                self.builders.push(candidate);
            }
            walk::walk_call_expression(self, call);
        }
    }

    fn scan(source: &str) -> Harness<'_> {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let mut harness = Harness {
            source,
            ..Harness::default()
        };
        harness.visit_program(&parsed.program);
        harness
    }

    #[test]
    fn recovers_numeric_array_width_hints() {
        let source = "const code = [0,200,1,201,2,202,3,203,0,204,1,205,2,206,3,207,0,208,1,209,2,210,3,211,0,212,1,213,2,214,3,215];";
        let result = scan(source);
        assert_eq!(result.arrays.len(), 1);
        let array = &result.arrays[0];
        assert_eq!(array.elements, 32);
        assert_eq!(array.numeric, 32);
        assert_eq!(array.byte_values, 32);
        assert!(array.width_hints.iter().any(|hint| hint.width == 2));
    }

    #[test]
    fn recovers_push_builder_and_receiver() {
        let source = "let code = []; code.push(0,200,1,201,2,202,3,203,0,204,1,205,2,206,3,207);";
        let result = scan(source);
        assert_eq!(result.builders.len(), 1);
        let builder = &result.builders[0];
        assert_eq!(builder.receiver_ident.as_deref(), Some("code"));
        assert_eq!(builder.candidate.arguments, 16);
        assert_eq!(builder.candidate.numeric_literals, 16);
        assert_eq!(builder.candidate.byte_literals, 16);
        assert!(builder
            .candidate
            .width_hints
            .iter()
            .any(|hint| hint.width == 2));
    }
}
