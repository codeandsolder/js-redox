use crate::{ast_utils::numeric_u64, source_text::preview};
use oxc_ast::ast::{
    ArrayExpression, ArrayExpressionElement, Expression, ObjectExpression, ObjectPropertyKind,
    Statement, SwitchCase, SwitchStatement,
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

fn direct_switch_handler(source: &str, case: &SwitchCase<'_>) -> DirectSwitchHandler {
    let key = case.test.as_ref().and_then(numeric_u64);
    let key_source = case
        .test
        .as_ref()
        .map(|expr| preview(source, expr.span().start, expr.span().end, usize::MAX));
    let mut semantic = Vec::new();
    let mut terminal = "fallthrough";

    for statement in &case.consequent {
        terminal = match statement {
            Statement::BreakStatement(_) => "break",
            Statement::ContinueStatement(_) => "continue",
            Statement::ReturnStatement(_) => {
                semantic.push(preview(
                    source,
                    statement.span().start,
                    statement.span().end,
                    usize::MAX,
                ));
                "return"
            }
            Statement::ThrowStatement(_) => {
                semantic.push(preview(
                    source,
                    statement.span().start,
                    statement.span().end,
                    usize::MAX,
                ));
                "throw"
            }
            _ => {
                semantic.push(preview(
                    source,
                    statement.span().start,
                    statement.span().end,
                    usize::MAX,
                ));
                terminal
            }
        };
    }

    DirectSwitchHandler {
        key,
        key_source,
        semantic,
        terminal: terminal.to_string(),
    }
}

fn direct_switch_evidence(
    handlers: &[DirectSwitchHandler],
    numeric_cases: usize,
    indexed_selector: bool,
    call_selector: bool,
) -> (u32, Vec<String>) {
    let stack_ops = handlers
        .iter()
        .flat_map(|handler| &handler.semantic)
        .filter(|text| {
            text.contains(".push(") || text.contains(".pop(") || text.contains(".splice(")
        })
        .count();
    let cursor_ops = handlers
        .iter()
        .flat_map(|handler| &handler.semantic)
        .filter(|text| {
            (text.contains("++") || text.contains("--"))
                && (text.contains('[') || text.contains(".length"))
        })
        .count();
    let continue_handlers = handlers
        .iter()
        .filter(|handler| handler.terminal == "continue")
        .count();

    let mut score = 0u32;
    let mut reasons = Vec::new();
    if numeric_cases >= 16 {
        score += 2;
        reasons.push(format!("{numeric_cases} numeric opcode-like cases"));
    }
    if stack_ops >= 3 {
        score += 3;
        reasons.push(format!("{stack_ops} stack-like handler effects"));
    }
    if cursor_ops >= 4 {
        score += 2;
        reasons.push(format!("{cursor_ops} indexed cursor/stack mutations"));
    }
    if continue_handlers >= 3 {
        score += 2;
        reasons.push(format!(
            "{continue_handlers} handlers continue dispatch loop"
        ));
    }
    if call_selector && !indexed_selector {
        reasons.push("opcode selector is produced by a call".to_string());
    }
    (score, reasons)
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

    let handlers = switch
        .cases
        .iter()
        .map(|case| direct_switch_handler(source, case))
        .collect::<Vec<_>>();
    let numeric_cases = handlers
        .iter()
        .filter(|handler| handler.key.is_some())
        .count();
    if numeric_cases < 8 || numeric_cases * 4 < switch.cases.len() * 3 {
        return None;
    }
    let opcode_max = handlers
        .iter()
        .filter_map(|handler| handler.key)
        .max()
        .unwrap_or(0);
    let selector = preview(
        source,
        switch.discriminant.span().start,
        switch.discriminant.span().end,
        usize::MAX,
    );
    let (vm_evidence_score, vm_reasons) =
        direct_switch_evidence(&handlers, numeric_cases, indexed_selector, call_selector);

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
        let source = r"
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
        ";
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
        let source = r"
            const objectHandlers = {
                a: function(){}, b: function(){}, c: function(){}, d: function(){},
                e: function(){}, f: function(){}, g: function(){}, h: function(){}
            };
            const arrayHandlers = [()=>0, ()=>1, ()=>2, ()=>3];
        ";
        let result = scan(source);
        assert_eq!(result.objects.len(), 1);
        assert_eq!(result.objects[0].function_values, 8);
        assert_eq!(result.arrays.len(), 1);
        assert_eq!(result.arrays[0].function_values, 4);
    }
}
