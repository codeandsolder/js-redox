use oxc_ast::{
    ast::{
        ArrayExpressionElement, AssignmentTarget, BindingPattern, CallExpression, Expression,
        ObjectPropertyKind,
    },
    AstKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_span::{GetSpan, Span};
use serde::Serialize;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, Serialize)]
pub struct HandlerFunctionSlot {
    pub key: String,
    pub start: u32,
    pub end: u32,
    pub params: usize,
    pub r#async: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct DetailedHandlerTableCandidate {
    pub binding: String,
    pub start: u32,
    pub end: u32,
    pub scope_function_id: Option<String>,
    pub scope_start: u32,
    pub scope_end: u32,
    pub container_kind: String,
    pub entries: usize,
    pub function_values: usize,
    pub handlers: Vec<HandlerFunctionSlot>,
}

#[derive(Debug, Clone, Serialize)]
pub struct ByteTransducerCandidate {
    pub function_id: String,
    pub binding: Option<String>,
    pub start: u32,
    pub end: u32,
    pub transition_table: String,
    pub state_source: String,
    pub byte_stream: String,
    pub pc_source: String,
    pub result_binding: String,
    pub state_target: String,
    pub state_result_index: usize,
    pub opcode_result_index: usize,
    pub preview: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct TableVmCandidate {
    pub dispatcher_function_id: String,
    pub handler_table: String,
    pub handler_count: usize,
    pub handler_index: String,
    pub dispatcher_start: u32,
    pub dispatcher_end: u32,
    pub producer_method: Option<String>,
    pub linked_transducer_function_id: Option<String>,
    pub architecture: String,
}

#[derive(Debug, Clone, Serialize, Default)]
pub struct TableVmAnalysis {
    pub handler_function_tables: Vec<DetailedHandlerTableCandidate>,
    pub byte_transducers: Vec<ByteTransducerCandidate>,
    pub table_vms: Vec<TableVmCandidate>,
}

#[derive(Debug, Clone)]
struct TransitionDraft {
    start: u32,
    end: u32,
    transition_table: String,
    state_source: String,
    byte_stream: String,
    pc_source: String,
    result_binding: String,
    state_target: Option<String>,
    state_result_index: Option<usize>,
    opcode_result_index: Option<usize>,
}

#[derive(Debug, Clone)]
struct HandlerCall {
    table: String,
    index: String,
    start: u32,
    end: u32,
    schedule_backed: bool,
}

#[derive(Debug, Clone)]
struct ProducerCall {
    target: String,
    method: String,
}

#[derive(Debug, Clone)]
struct FunctionState {
    id: String,
    start: u32,
    end: u32,
    loops: usize,
    transitions: HashMap<String, TransitionDraft>,
    handler_calls: Vec<HandlerCall>,
    handler_aliases: HashMap<String, HandlerCall>,
    producers: Vec<ProducerCall>,
    numeric_schedules: HashSet<String>,
}

#[derive(Debug, Clone)]
struct FunctionSummary {
    id: String,
    start: u32,
    end: u32,
    loops: usize,
    handler_calls: Vec<HandlerCall>,
    producers: Vec<ProducerCall>,
}

struct Analyzer<'s> {
    source: &'s str,
    function_stack: Vec<FunctionState>,
    function_aliases: HashMap<(u32, u32), String>,
    tables: Vec<DetailedHandlerTableCandidate>,
    registry_handlers: HashMap<(u32, u32, String), Vec<HandlerFunctionSlot>>,
    registry_spans: HashMap<(u32, u32, String), (u32, u32)>,
    registry_sources: HashMap<(u32, u32, String), String>,
    transducers: Vec<ByteTransducerCandidate>,
    functions: Vec<FunctionSummary>,
}

fn fragment(source: &str, span: Span) -> String {
    let start = span.start as usize;
    let end = (span.end as usize).min(source.len());
    source
        .get(start..end)
        .unwrap_or_default()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

fn root_ident(expr: &Expression<'_>) -> Option<String> {
    match expr {
        Expression::Identifier(id) => Some(id.name.to_string()),
        Expression::ComputedMemberExpression(cm) => root_ident(&cm.object),
        Expression::StaticMemberExpression(sm) => root_ident(&sm.object),
        Expression::PrivateFieldExpression(pf) => root_ident(&pf.object),
        Expression::ParenthesizedExpression(p) => root_ident(&p.expression),
        _ => None,
    }
}

fn unwrap_parens<'a>(mut expr: &'a Expression<'a>) -> &'a Expression<'a> {
    while let Expression::ParenthesizedExpression(p) = expr {
        expr = &p.expression;
    }
    expr
}

fn numeric_index(expr: &Expression<'_>) -> Option<usize> {
    match unwrap_parens(expr) {
        Expression::NumericLiteral(n)
            if n.value.is_finite() && n.value >= 0.0 && n.value.fract() == 0.0 =>
        {
            Some(n.value as usize)
        }
        _ => None,
    }
}

fn result_index(expr: &Expression<'_>) -> Option<(String, usize)> {
    let Expression::ComputedMemberExpression(cm) = unwrap_parens(expr) else {
        return None;
    };
    let Expression::Identifier(id) = unwrap_parens(&cm.object) else {
        return None;
    };
    Some((id.name.to_string(), numeric_index(&cm.expression)?))
}

fn nested_transition(
    source: &str,
    expr: &Expression<'_>,
) -> Option<(u32, u32, String, String, String, String)> {
    let Expression::ComputedMemberExpression(outer) = unwrap_parens(expr) else {
        return None;
    };
    let Expression::ComputedMemberExpression(state_lookup) = unwrap_parens(&outer.object) else {
        return None;
    };
    let Expression::ComputedMemberExpression(byte_lookup) = unwrap_parens(&outer.expression) else {
        return None;
    };

    let transition_table = root_ident(&state_lookup.object)?;
    let byte_stream = root_ident(&byte_lookup.object)?;

    Some((
        outer.span.start,
        outer.span.end,
        transition_table,
        fragment(source, state_lookup.expression.span()),
        byte_stream,
        fragment(source, byte_lookup.expression.span()),
    ))
}

fn target_source(source: &str, target: &AssignmentTarget<'_>) -> String {
    fragment(source, target.span())
}

fn target_ident(target: &AssignmentTarget<'_>) -> Option<String> {
    match target {
        AssignmentTarget::AssignmentTargetIdentifier(id) => Some(id.name.to_string()),
        _ => None,
    }
}

fn static_method(call: &CallExpression<'_>) -> Option<String> {
    match unwrap_parens(&call.callee) {
        Expression::StaticMemberExpression(sm) => Some(sm.property.name.to_string()),
        Expression::ComputedMemberExpression(cm) => match unwrap_parens(&cm.expression) {
            Expression::StringLiteral(value) => Some(value.value.to_string()),
            _ => None,
        },
        _ => None,
    }
}

fn function_expr_meta(expr: &Expression<'_>) -> Option<(u32, u32, usize, bool)> {
    match unwrap_parens(expr) {
        Expression::FunctionExpression(f) => {
            Some((f.span.start, f.span.end, f.params.items.len(), f.r#async))
        }
        Expression::ArrowFunctionExpression(f) => {
            Some((f.span.start, f.span.end, f.params.items.len(), f.r#async))
        }
        _ => None,
    }
}

struct NumericScheduleUseVisitor<'s> {
    schedules: &'s HashSet<String>,
    found: bool,
}

impl<'a> Visit<'a> for NumericScheduleUseVisitor<'_> {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        if self.found {
            return;
        }
        let AstKind::ComputedMemberExpression(cm) = kind else {
            return;
        };
        if root_ident(&cm.object)
            .as_ref()
            .is_some_and(|root| self.schedules.contains(root))
        {
            self.found = true;
        }
    }
}

fn expression_uses_numeric_schedule(expr: &Expression<'_>, schedules: &HashSet<String>) -> bool {
    if schedules.is_empty() {
        return false;
    }
    let mut visitor = NumericScheduleUseVisitor {
        schedules,
        found: false,
    };
    visitor.visit_expression(expr);
    visitor.found
}

impl<'s> Analyzer<'s> {
    fn new(source: &'s str) -> Self {
        Self {
            source,
            function_stack: Vec::new(),
            function_aliases: HashMap::new(),
            tables: Vec::new(),
            registry_handlers: HashMap::new(),
            registry_spans: HashMap::new(),
            registry_sources: HashMap::new(),
            transducers: Vec::new(),
            functions: Vec::new(),
        }
    }

    fn current_mut(&mut self) -> Option<&mut FunctionState> {
        self.function_stack.last_mut()
    }

    fn current_scope(&self) -> (Option<String>, u32, u32) {
        self.function_stack
            .last()
            .map(|f| (Some(f.id.clone()), f.start, f.end))
            .unwrap_or((None, 0, self.source.len().min(u32::MAX as usize) as u32))
    }

    fn registry_scope_key(&self, binding: String) -> (u32, u32, String) {
        if binding.starts_with("this.") || binding.starts_with("this[") {
            return (0, self.source.len().min(u32::MAX as usize) as u32, binding);
        }
        let (_, start, end) = self.current_scope();
        (start, end, binding)
    }

    fn record_transition(&mut self, binding: String, expr: &Expression<'_>) {
        let Some((start, end, transition_table, state_source, byte_stream, pc_source)) =
            nested_transition(self.source, expr)
        else {
            return;
        };
        if let Some(cur) = self.current_mut() {
            cur.transitions.insert(
                binding.clone(),
                TransitionDraft {
                    start,
                    end,
                    transition_table,
                    state_source,
                    byte_stream,
                    pc_source,
                    result_binding: binding,
                    state_target: None,
                    state_result_index: None,
                    opcode_result_index: None,
                },
            );
        }
    }

    fn record_array_table(&mut self, binding: &str, arr: &oxc_ast::ast::ArrayExpression<'_>) {
        let mut handlers = Vec::new();
        for (i, el) in arr.elements.iter().enumerate() {
            let meta = match el {
                ArrayExpressionElement::FunctionExpression(f) => {
                    Some((f.span.start, f.span.end, f.params.items.len(), f.r#async))
                }
                ArrayExpressionElement::ArrowFunctionExpression(f) => {
                    Some((f.span.start, f.span.end, f.params.items.len(), f.r#async))
                }
                _ => None,
            };
            if let Some((start, end, params, r#async)) = meta {
                handlers.push(HandlerFunctionSlot {
                    key: i.to_string(),
                    start,
                    end,
                    params,
                    r#async,
                });
            }
        }

        let n = arr.elements.len();
        if handlers.len() >= 4 && handlers.len() * 2 >= n {
            let (scope_function_id, scope_start, scope_end) = self.current_scope();
            self.tables.push(DetailedHandlerTableCandidate {
                binding: binding.to_string(),
                start: arr.span.start,
                end: arr.span.end,
                scope_function_id,
                scope_start,
                scope_end,
                container_kind: "array".into(),
                entries: n,
                function_values: handlers.len(),
                handlers,
            });
        }
    }

    fn record_object_table(&mut self, binding: &str, obj: &oxc_ast::ast::ObjectExpression<'_>) {
        let mut handlers = Vec::new();
        for (i, item) in obj.properties.iter().enumerate() {
            let ObjectPropertyKind::ObjectProperty(prop) = item else {
                continue;
            };
            let Some((start, end, params, r#async)) = function_expr_meta(&prop.value) else {
                continue;
            };
            handlers.push(HandlerFunctionSlot {
                key: i.to_string(),
                start,
                end,
                params,
                r#async,
            });
        }

        let n = obj.properties.len();
        if handlers.len() >= 8 && handlers.len() * 2 >= n {
            let (scope_function_id, scope_start, scope_end) = self.current_scope();
            self.tables.push(DetailedHandlerTableCandidate {
                binding: binding.to_string(),
                start: obj.span.start,
                end: obj.span.end,
                scope_function_id,
                scope_start,
                scope_end,
                container_kind: "object".into(),
                entries: n,
                function_values: handlers.len(),
                handlers,
            });
        }
    }

    fn record_registry_assignment(&mut self, assign: &oxc_ast::ast::AssignmentExpression<'_>) {
        let AssignmentTarget::ComputedMemberExpression(dst) = &assign.left else {
            return;
        };
        let receiver = fragment(self.source, dst.object.span());
        let key = fragment(self.source, dst.expression.span());
        let scope_key = self.registry_scope_key(receiver.clone());

        if let Some((start, end, params, r#async)) = function_expr_meta(&assign.right) {
            self.registry_handlers
                .entry(scope_key.clone())
                .or_default()
                .push(HandlerFunctionSlot {
                    key,
                    start,
                    end,
                    params,
                    r#async,
                });
            self.registry_spans
                .entry(scope_key)
                .and_modify(|span| {
                    span.0 = span.0.min(assign.span.start);
                    span.1 = span.1.max(assign.span.end);
                })
                .or_insert((assign.span.start, assign.span.end));
            return;
        }

        let Expression::CallExpression(call) = unwrap_parens(&assign.right) else {
            return;
        };
        let bind_object = match unwrap_parens(&call.callee) {
            Expression::StaticMemberExpression(bind) if bind.property.name.as_str() == "bind" => {
                &bind.object
            }
            Expression::ComputedMemberExpression(bind) => {
                let Expression::StringLiteral(property) = unwrap_parens(&bind.expression) else {
                    return;
                };
                if property.value.as_str() != "bind" {
                    return;
                }
                &bind.object
            }
            _ => return,
        };
        let Expression::ComputedMemberExpression(src) = unwrap_parens(bind_object) else {
            return;
        };
        let source_table = fragment(self.source, src.object.span());
        self.registry_sources
            .insert(scope_key.clone(), source_table);
        self.registry_spans
            .entry(scope_key)
            .and_modify(|span| {
                span.0 = span.0.min(assign.span.start);
                span.1 = span.1.max(assign.span.end);
            })
            .or_insert((assign.span.start, assign.span.end));
    }

    fn finish_function(&mut self) {
        let Some(state) = self.function_stack.pop() else {
            return;
        };

        let alias = self
            .function_aliases
            .get(&(state.start, state.end))
            .cloned();

        for draft in state.transitions.values() {
            let (Some(state_target), Some(state_result_index), Some(opcode_result_index)) = (
                draft.state_target.clone(),
                draft.state_result_index,
                draft.opcode_result_index,
            ) else {
                continue;
            };
            if state_result_index == opcode_result_index {
                continue;
            }
            self.transducers.push(ByteTransducerCandidate {
                function_id: state.id.clone(),
                binding: alias.clone(),
                start: draft.start,
                end: draft.end,
                transition_table: draft.transition_table.clone(),
                state_source: draft.state_source.clone(),
                byte_stream: draft.byte_stream.clone(),
                pc_source: draft.pc_source.clone(),
                result_binding: draft.result_binding.clone(),
                state_target,
                state_result_index,
                opcode_result_index,
                preview: fragment(self.source, Span::new(state.start, state.end))
                    .chars()
                    .take(240)
                    .collect(),
            });
        }

        self.functions.push(FunctionSummary {
            id: state.id,
            start: state.start,
            end: state.end,
            loops: state.loops,
            handler_calls: state.handler_calls,
            producers: state.producers,
        });
    }

    fn finish(mut self) -> TableVmAnalysis {
        for ((scope_start, scope_end, binding), handlers) in self.registry_handlers.drain() {
            if handlers.len() < 4 {
                continue;
            }
            let key = (scope_start, scope_end, binding.clone());
            let (start, end) = self.registry_spans.get(&key).copied().unwrap_or((0, 0));
            let scope_function_id = self
                .functions
                .iter()
                .find(|f| f.start == scope_start && f.end == scope_end)
                .map(|f| f.id.clone());
            self.tables.push(DetailedHandlerTableCandidate {
                binding,
                start,
                end,
                scope_function_id,
                scope_start,
                scope_end,
                container_kind: "registry".into(),
                entries: handlers.len(),
                function_values: handlers.len(),
                handlers,
            });
        }

        for ((scope_start, scope_end, binding), source) in &self.registry_sources {
            let key = (*scope_start, *scope_end, binding.clone());
            let Some((start, end)) = self.registry_spans.get(&key).copied() else {
                continue;
            };
            // The assignment proves where the source handler table is consumed.
            // An installed instance registry can then be used by sibling methods,
            // so inherit the source table's enclosing scope instead of widening
            // to the physical file boundary.
            let Some(source_table) = self
                .tables
                .iter()
                .filter(|table| table.binding == *source)
                .filter(|table| table.scope_start <= start && table.scope_end >= end)
                .min_by_key(|table| table.scope_end.saturating_sub(table.scope_start))
                .cloned()
            else {
                continue;
            };
            self.tables.push(DetailedHandlerTableCandidate {
                binding: binding.clone(),
                start,
                end,
                scope_function_id: source_table.scope_function_id.clone(),
                scope_start: source_table.scope_start,
                scope_end: source_table.scope_end,
                container_kind: "derived-registry".into(),
                entries: source_table.entries,
                function_values: source_table.function_values,
                handlers: source_table.handlers.clone(),
            });
        }

        self.tables.sort_by(|a, b| {
            (&a.binding, a.scope_start, a.scope_end, a.start, a.end).cmp(&(
                &b.binding,
                b.scope_start,
                b.scope_end,
                b.start,
                b.end,
            ))
        });
        self.tables.dedup_by(|a, b| {
            a.binding == b.binding
                && a.scope_start == b.scope_start
                && a.scope_end == b.scope_end
                && a.start == b.start
                && a.end == b.end
        });
        self.transducers.sort_by(|a, b| {
            (&a.function_id, a.start, a.end).cmp(&(&b.function_id, b.start, b.end))
        });
        self.transducers.dedup_by(|a, b| {
            a.function_id == b.function_id && a.start == b.start && a.end == b.end
        });

        let mut table_vms = Vec::new();
        for function in &self.functions {
            if function.loops == 0 {
                continue;
            }
            for call in &function.handler_calls {
                // A VM dispatcher chooses a handler from runtime state. Calls
                // through a fixed numeric slot are ordinary helper-table calls,
                // not dispatch, even when they occur in a loop.
                let index_text = call.index.trim();
                let static_numeric_index = index_text.parse::<u64>().is_ok()
                    || index_text
                        .strip_prefix("0x")
                        .or_else(|| index_text.strip_prefix("0X"))
                        .is_some_and(|hex| u64::from_str_radix(hex, 16).is_ok());
                if static_numeric_index {
                    continue;
                }

                let Some(table) = self
                    .tables
                    .iter()
                    .filter(|table| table.binding == call.table)
                    .filter(|table| {
                        table.scope_start <= function.start && table.scope_end >= function.end
                    })
                    .min_by_key(|table| table.scope_end.saturating_sub(table.scope_start))
                else {
                    continue;
                };
                if table.function_values < 4 {
                    continue;
                }

                let index_ident = call
                    .index
                    .trim()
                    .chars()
                    .all(|c| c == '_' || c == '$' || c.is_ascii_alphanumeric())
                    .then(|| call.index.trim().to_string());

                let producer = index_ident
                    .as_ref()
                    .and_then(|target| function.producers.iter().find(|p| &p.target == target));

                let linked_by_name = producer.as_ref().and_then(|producer| {
                    self.transducers.iter().find(|t| {
                        t.binding.as_deref().is_some_and(|binding| {
                            binding == producer.method
                                || binding.ends_with(&format!(".{}", producer.method))
                        })
                    })
                });
                // Obfuscators often install the decoder method through a generic
                // property-definition helper, erasing the lexical method name.
                // When the file has exactly one structurally complete byte
                // transducer and this dispatcher has an opcode producer, the
                // architecture link is still unambiguous without protector names.
                let linked = linked_by_name.or_else(|| {
                    if producer.is_some() && self.transducers.len() == 1 {
                        self.transducers.first()
                    } else {
                        None
                    }
                });

                // Function tables also implement ordinary module registries and
                // schedulers. A VM candidate needs provenance for its dynamic
                // handler index from a decoder-like producer or numeric schedule.
                if linked.is_none() && producer.is_none() && !call.schedule_backed {
                    continue;
                }

                table_vms.push(TableVmCandidate {
                    dispatcher_function_id: function.id.clone(),
                    handler_table: call.table.clone(),
                    handler_count: table.function_values,
                    handler_index: call.index.clone(),
                    dispatcher_start: call.start,
                    dispatcher_end: call.end,
                    producer_method: producer.map(|p| p.method.clone()),
                    linked_transducer_function_id: linked.map(|t| t.function_id.clone()),
                    architecture: if linked.is_some() {
                        "stateful-byte-transducer+function-table".into()
                    } else {
                        "function-table-dispatch".into()
                    },
                });
            }
        }

        table_vms.sort_by(|a, b| {
            (
                &a.dispatcher_function_id,
                &a.handler_table,
                a.dispatcher_start,
            )
                .cmp(&(
                    &b.dispatcher_function_id,
                    &b.handler_table,
                    b.dispatcher_start,
                ))
        });
        table_vms.dedup_by(|a, b| {
            a.dispatcher_function_id == b.dispatcher_function_id
                && a.handler_table == b.handler_table
                && a.dispatcher_start == b.dispatcher_start
        });

        TableVmAnalysis {
            handler_function_tables: self.tables,
            byte_transducers: self.transducers,
            table_vms,
        }
    }
}

impl<'a> Visit<'a> for Analyzer<'_> {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        match kind {
            AstKind::Function(f) => {
                let id = format!("fn@{:x}-{:x}", f.span.start, f.span.end);
                if let Some(name) = f.id.as_ref() {
                    self.function_aliases
                        .insert((f.span.start, f.span.end), name.name.to_string());
                }
                self.function_stack.push(FunctionState {
                    id,
                    start: f.span.start,
                    end: f.span.end,
                    loops: 0,
                    transitions: HashMap::new(),
                    handler_calls: Vec::new(),
                    handler_aliases: HashMap::new(),
                    producers: Vec::new(),
                    numeric_schedules: HashSet::new(),
                });
            }
            AstKind::ArrowFunctionExpression(f) => {
                self.function_stack.push(FunctionState {
                    id: format!("fn@{:x}-{:x}", f.span.start, f.span.end),
                    start: f.span.start,
                    end: f.span.end,
                    loops: 0,
                    transitions: HashMap::new(),
                    handler_calls: Vec::new(),
                    handler_aliases: HashMap::new(),
                    producers: Vec::new(),
                    numeric_schedules: HashSet::new(),
                });
            }
            AstKind::ForStatement(_)
            | AstKind::WhileStatement(_)
            | AstKind::DoWhileStatement(_)
            | AstKind::ForInStatement(_)
            | AstKind::ForOfStatement(_) => {
                if let Some(cur) = self.current_mut() {
                    cur.loops += 1;
                }
            }
            AstKind::VariableDeclarator(v) => {
                let BindingPattern::BindingIdentifier(id) = &v.id else {
                    return;
                };
                let Some(init) = v.init.as_ref() else {
                    return;
                };
                let name = id.name.to_string();

                match unwrap_parens(init) {
                    Expression::ArrayExpression(arr) => {
                        self.record_array_table(&name, arr);
                        if arr.elements.len() >= 4
                            && arr
                                .elements
                                .iter()
                                .all(|el| matches!(el, ArrayExpressionElement::NumericLiteral(_)))
                        {
                            if let Some(cur) = self.current_mut() {
                                cur.numeric_schedules.insert(name.clone());
                            }
                        }
                    }
                    Expression::ObjectExpression(obj) => self.record_object_table(&name, obj),
                    Expression::FunctionExpression(f) => {
                        self.function_aliases
                            .insert((f.span.start, f.span.end), name.clone());
                    }
                    Expression::ArrowFunctionExpression(f) => {
                        self.function_aliases
                            .insert((f.span.start, f.span.end), name.clone());
                    }
                    _ => {}
                }

                self.record_transition(name.clone(), init);

                if let Expression::ComputedMemberExpression(cm) = unwrap_parens(init) {
                    let schedules = self
                        .function_stack
                        .last()
                        .map(|cur| cur.numeric_schedules.clone())
                        .unwrap_or_default();
                    let alias = HandlerCall {
                        table: fragment(self.source, cm.object.span()),
                        index: fragment(self.source, cm.expression.span()),
                        start: cm.span.start,
                        end: cm.span.end,
                        schedule_backed: expression_uses_numeric_schedule(
                            &cm.expression,
                            &schedules,
                        ),
                    };
                    if let Some(cur) = self.current_mut() {
                        cur.handler_aliases.insert(name.clone(), alias);
                    }
                }

                if let Expression::CallExpression(call) = unwrap_parens(init) {
                    if let Some(method) = static_method(call) {
                        if let Some(cur) = self.current_mut() {
                            cur.producers.push(ProducerCall {
                                target: name,
                                method,
                            });
                        }
                    }
                }
            }
            AstKind::AssignmentExpression(assign) => {
                self.record_registry_assignment(assign);

                if let Expression::FunctionExpression(f) = unwrap_parens(&assign.right) {
                    self.function_aliases.insert(
                        (f.span.start, f.span.end),
                        target_source(self.source, &assign.left),
                    );
                } else if let Expression::ArrowFunctionExpression(f) = unwrap_parens(&assign.right)
                {
                    self.function_aliases.insert(
                        (f.span.start, f.span.end),
                        target_source(self.source, &assign.left),
                    );
                }

                if let Some(name) = target_ident(&assign.left) {
                    self.record_transition(name.clone(), &assign.right);
                    if let Expression::ComputedMemberExpression(cm) = unwrap_parens(&assign.right) {
                        let schedules = self
                            .function_stack
                            .last()
                            .map(|cur| cur.numeric_schedules.clone())
                            .unwrap_or_default();
                        let alias = HandlerCall {
                            table: fragment(self.source, cm.object.span()),
                            index: fragment(self.source, cm.expression.span()),
                            start: cm.span.start,
                            end: cm.span.end,
                            schedule_backed: expression_uses_numeric_schedule(
                                &cm.expression,
                                &schedules,
                            ),
                        };
                        if let Some(cur) = self.current_mut() {
                            cur.handler_aliases.insert(name.clone(), alias);
                        }
                    }
                    if let Expression::CallExpression(call) = unwrap_parens(&assign.right) {
                        if let Some(method) = static_method(call) {
                            if let Some(cur) = self.current_mut() {
                                cur.producers.push(ProducerCall {
                                    target: name,
                                    method,
                                });
                            }
                        }
                    }
                }

                let Some((result, index)) = result_index(&assign.right) else {
                    return;
                };
                let target = target_source(self.source, &assign.left);
                if let Some(cur) = self.current_mut() {
                    if let Some(draft) = cur.transitions.get_mut(&result) {
                        draft.state_target = Some(target);
                        draft.state_result_index = Some(index);
                    }
                }
            }
            AstKind::ReturnStatement(ret) => {
                let Some(arg) = ret.argument.as_ref() else {
                    return;
                };
                let Some((result, index)) = result_index(arg) else {
                    return;
                };
                if let Some(cur) = self.current_mut() {
                    if let Some(draft) = cur.transitions.get_mut(&result) {
                        draft.opcode_result_index = Some(index);
                    }
                }
            }
            AstKind::CallExpression(call) => match unwrap_parens(&call.callee) {
                Expression::ComputedMemberExpression(cm) => {
                    let table = fragment(self.source, cm.object.span());
                    if table.is_empty() {
                        return;
                    }
                    let index = fragment(self.source, cm.expression.span());
                    let schedules = self
                        .function_stack
                        .last()
                        .map(|cur| cur.numeric_schedules.clone())
                        .unwrap_or_default();
                    let schedule_backed =
                        expression_uses_numeric_schedule(&cm.expression, &schedules);
                    if let Some(cur) = self.current_mut() {
                        cur.handler_calls.push(HandlerCall {
                            table,
                            index,
                            start: call.span.start,
                            end: call.span.end,
                            schedule_backed,
                        });
                    }
                }
                Expression::Identifier(id) => {
                    let alias = self
                        .function_stack
                        .last()
                        .and_then(|cur| cur.handler_aliases.get(id.name.as_str()))
                        .cloned();
                    if let (Some(cur), Some(mut alias)) = (self.current_mut(), alias) {
                        alias.start = call.span.start;
                        alias.end = call.span.end;
                        cur.handler_calls.push(alias);
                    }
                }
                _ => {}
            },
            _ => {}
        }
    }

    fn leave_node(&mut self, kind: AstKind<'a>) {
        match kind {
            AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) => self.finish_function(),
            _ => {}
        }
    }

    fn visit_program(&mut self, program: &oxc_ast::ast::Program<'a>) {
        walk::walk_program(self, program);
    }
}

pub fn analyze(source: &str, program: &oxc_ast::ast::Program<'_>) -> TableVmAnalysis {
    let mut analyzer = Analyzer::new(source);
    analyzer.visit_program(program);
    analyzer.finish()
}
