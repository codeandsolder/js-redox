use crate::source_text::preview;
use oxc_ast::ast::{
    ArrayExpression, ArrayExpressionElement, Expression, ObjectExpression, ObjectPropertyKind,
    Statement, SwitchStatement,
};
use oxc_span::GetSpan;
use serde::Serialize;

#[derive(Debug, Clone, Serialize)]
pub struct HandlerTableCandidate {
    pub start: u32,
    pub end: u32,
    pub container_kind: String,
    pub properties: usize,
    pub function_values: usize,
    pub async_function_values: usize,
    pub preview: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct DirectSwitchHandler {
    pub key: Option<u64>,
    pub key_source: Option<String>,
    pub semantic: Vec<String>,
    pub terminal: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct DirectSwitchMapCandidate {
    pub parent_function_id: String,
    pub start: u32,
    pub end: u32,
    pub selector: String,
    pub numeric_cases: usize,
    pub opcode_max: u64,
    pub vm_evidence_score: u32,
    pub vm_reasons: Vec<String>,
    pub confirmed_vm: bool,
    pub handlers: Vec<DirectSwitchHandler>,
}

fn numeric_u64(expr: &Expression<'_>) -> Option<u64> {
    match expr {
        Expression::NumericLiteral(n)
            if n.value.is_finite() && n.value >= 0.0 && n.value.fract() == 0.0 =>
        {
            Some(n.value as u64)
        }
        Expression::ParenthesizedExpression(paren) => numeric_u64(&paren.expression),
        _ => None,
    }
}

pub fn detect_direct_switch(
    source: &str,
    parent_function_id: &str,
    switch: &SwitchStatement<'_>,
    indexed_selector: bool,
    call_selector: bool,
) -> Option<DirectSwitchMapCandidate> {
    if switch.cases.len() < 8 || (!indexed_selector && !call_selector) {
        return None;
    }

    let mut handlers = Vec::with_capacity(switch.cases.len());
    let mut numeric_cases = 0usize;
    let mut opcode_max = 0u64;
    for case in &switch.cases {
        let key = case.test.as_ref().and_then(numeric_u64);
        if let Some(value) = key {
            numeric_cases += 1;
            opcode_max = opcode_max.max(value);
        }
        let key_source = case
            .test
            .as_ref()
            .map(|expr| preview(source, expr.span().start, expr.span().end, usize::MAX));

        let mut semantic = Vec::new();
        let mut terminal = "fallthrough".to_string();
        for stmt in &case.consequent {
            match stmt {
                Statement::BreakStatement(_) => terminal = "break".to_string(),
                Statement::ContinueStatement(_) => terminal = "continue".to_string(),
                Statement::ReturnStatement(_) => {
                    terminal = "return".to_string();
                    semantic.push(preview(
                        source,
                        stmt.span().start,
                        stmt.span().end,
                        usize::MAX,
                    ));
                }
                Statement::ThrowStatement(_) => {
                    terminal = "throw".to_string();
                    semantic.push(preview(
                        source,
                        stmt.span().start,
                        stmt.span().end,
                        usize::MAX,
                    ));
                }
                _ => semantic.push(preview(
                    source,
                    stmt.span().start,
                    stmt.span().end,
                    usize::MAX,
                )),
            }
        }
        handlers.push(DirectSwitchHandler {
            key,
            key_source,
            semantic,
            terminal,
        });
    }

    if numeric_cases < 8 || numeric_cases * 4 < switch.cases.len() * 3 {
        return None;
    }

    let selector = preview(
        source,
        switch.discriminant.span().start,
        switch.discriminant.span().end,
        usize::MAX,
    );
    let semantic_fragments = handlers
        .iter()
        .flat_map(|handler| handler.semantic.iter())
        .collect::<Vec<_>>();
    let stack_ops = semantic_fragments
        .iter()
        .filter(|text| {
            text.contains(".push(") || text.contains(".pop(") || text.contains(".splice(")
        })
        .count();
    let cursor_ops = semantic_fragments
        .iter()
        .filter(|text| {
            (text.contains("++") || text.contains("--"))
                && (text.contains('[') || text.contains(".length"))
        })
        .count();
    let continue_handlers = handlers
        .iter()
        .filter(|handler| handler.terminal == "continue")
        .count();

    let mut vm_evidence_score = 0u32;
    let mut vm_reasons = Vec::new();
    if numeric_cases >= 16 {
        vm_evidence_score += 2;
        vm_reasons.push(format!("{numeric_cases} numeric opcode-like cases"));
    }
    if stack_ops >= 3 {
        vm_evidence_score += 3;
        vm_reasons.push(format!("{stack_ops} stack-like handler effects"));
    }
    if cursor_ops >= 4 {
        vm_evidence_score += 2;
        vm_reasons.push(format!("{cursor_ops} indexed cursor/stack mutations"));
    }
    if continue_handlers >= 3 {
        vm_evidence_score += 2;
        vm_reasons.push(format!(
            "{continue_handlers} handlers continue dispatch loop"
        ));
    }
    if call_selector && !indexed_selector {
        vm_reasons.push("opcode selector is produced by a call".to_string());
    }

    Some(DirectSwitchMapCandidate {
        parent_function_id: parent_function_id.to_string(),
        start: switch.span.start,
        end: switch.span.end,
        selector,
        numeric_cases,
        opcode_max,
        vm_evidence_score,
        vm_reasons,
        confirmed_vm: vm_evidence_score >= 5,
        handlers,
    })
}

pub fn detect_object_handler_table(
    source: &str,
    object: &ObjectExpression<'_>,
) -> Option<HandlerTableCandidate> {
    let properties = object.properties.len();
    if properties < 8 {
        return None;
    }
    let mut function_values = 0usize;
    let mut async_function_values = 0usize;
    for property in &object.properties {
        let ObjectPropertyKind::ObjectProperty(property) = property else {
            continue;
        };
        match &property.value {
            Expression::FunctionExpression(function) => {
                function_values += 1;
                if function.r#async {
                    async_function_values += 1;
                }
            }
            Expression::ArrowFunctionExpression(function) => {
                function_values += 1;
                if function.r#async {
                    async_function_values += 1;
                }
            }
            _ => {}
        }
    }
    if function_values < 8 || function_values * 2 < properties {
        return None;
    }
    Some(HandlerTableCandidate {
        start: object.span.start,
        end: object.span.end,
        container_kind: "object".to_string(),
        properties,
        function_values,
        async_function_values,
        preview: preview(source, object.span.start, object.span.end, 120),
    })
}

pub fn detect_array_handler_table(
    source: &str,
    array: &ArrayExpression<'_>,
) -> Option<HandlerTableCandidate> {
    let properties = array.elements.len();
    if properties < 4 {
        return None;
    }
    let mut function_values = 0usize;
    let mut async_function_values = 0usize;
    for element in &array.elements {
        match element {
            ArrayExpressionElement::FunctionExpression(function) => {
                function_values += 1;
                if function.r#async {
                    async_function_values += 1;
                }
            }
            ArrayExpressionElement::ArrowFunctionExpression(function) => {
                function_values += 1;
                if function.r#async {
                    async_function_values += 1;
                }
            }
            _ => {}
        }
    }
    if function_values < 4 || function_values * 2 < properties {
        return None;
    }
    Some(HandlerTableCandidate {
        start: array.span.start,
        end: array.span.end,
        container_kind: "array".to_string(),
        properties,
        function_values,
        async_function_values,
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
        switches: Vec<DirectSwitchMapCandidate>,
        objects: Vec<HandlerTableCandidate>,
        arrays: Vec<HandlerTableCandidate>,
    }

    impl<'a> Visit<'a> for Harness<'_> {
        fn visit_switch_statement(&mut self, switch: &SwitchStatement<'a>) {
            if let Some(candidate) =
                detect_direct_switch(self.source, "fn@test", switch, true, false)
            {
                self.switches.push(candidate);
            }
            walk::walk_switch_statement(self, switch);
        }

        fn visit_object_expression(&mut self, object: &ObjectExpression<'a>) {
            if let Some(candidate) = detect_object_handler_table(self.source, object) {
                self.objects.push(candidate);
            }
            walk::walk_object_expression(self, object);
        }

        fn visit_array_expression(&mut self, array: &ArrayExpression<'a>) {
            if let Some(candidate) = detect_array_handler_table(self.source, array) {
                self.arrays.push(candidate);
            }
            walk::walk_array_expression(self, array);
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
    fn detects_confirmed_numeric_dispatch_switch() {
        let source = r#"
            while (true) {
                switch (code[ip++]) {
                    case 0: stack.push(a); continue;
                    case 1: stack.pop(); continue;
                    case 2: stack.push(b); continue;
                    case 3: x++; break;
                    case 4: x++; break;
                    case 5: x++; break;
                    case 6: x++; break;
                    case 7: x++; break;
                    case 8: x++; break;
                    case 9: x++; break;
                    case 10: x++; break;
                    case 11: x++; break;
                    case 12: x++; break;
                    case 13: x++; break;
                    case 14: x++; break;
                    case 15: x++; break;
                }
            }
        "#;
        let result = scan(source);
        assert_eq!(result.switches.len(), 1);
        let switch = &result.switches[0];
        assert_eq!(switch.numeric_cases, 16);
        assert_eq!(switch.opcode_max, 15);
        assert!(switch.confirmed_vm);
        assert!(switch.vm_evidence_score >= 5);
    }

    #[test]
    fn detects_function_handler_tables() {
        let source = r#"
            const objectHandlers = {
                a: function(){}, b: function(){}, c: function(){}, d: function(){},
                e: function(){}, f: function(){}, g: function(){}, h: function(){}
            };
            const arrayHandlers = [()=>0, ()=>1, ()=>2, ()=>3];
        "#;
        let result = scan(source);
        assert_eq!(result.objects.len(), 1);
        assert_eq!(result.objects[0].function_values, 8);
        assert_eq!(result.arrays.len(), 1);
        assert_eq!(result.arrays[0].function_values, 4);
    }
}
