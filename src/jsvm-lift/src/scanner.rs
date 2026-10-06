use crate::{
    bytecode::{detect_numeric_array, detect_push_builder, ArrayCandidate, PushBuilderCandidate},
    decoder::{
        complete_selector_masks, expr_ident, index_shape, observed_opcodes, origin_ident,
        origin_u64, resolve_alias, target_ident, BuilderSite, DecoderCandidate, IndexedAccess,
    },
    dispatch::{
        detect_array_handler_table, detect_direct_switch, detect_object_handler_table,
        DirectSwitchMapCandidate, HandlerTableCandidate,
    },
    embedded::{detect_function_constructor, detect_literal_string_join, EmbeddedCodeCandidate},
    function_analysis::{
        evidence_reaches_computed, expression_evidence, FunctionMetrics, FunctionState,
    },
    source_text::preview,
    state_flatten::{
        self, detect_for_state_machines, IfLadderStateMachineCandidate, OpcodeMapCandidate,
        StateMachineCandidate, StateMachineInfo,
    },
    table_vm,
};
use oxc_allocator::Allocator;
use oxc_ast::ast::{ArrayExpressionElement, Expression};
use oxc_ast_visit::{walk, Visit};
use oxc_span::SourceType;
use oxc_syntax::scope::ScopeFlags;
use rolldown_redox::ecmascript::parse_program;
use std::collections::{BTreeSet, HashMap};

struct Scanner<'s> {
    source: &'s str,
    arrays: Vec<ArrayCandidate>,
    push_builders: Vec<PushBuilderCandidate>,
    decoder_candidates: Vec<DecoderCandidate>,
    state_machines: Vec<StateMachineCandidate>,
    if_ladder_state_machines: Vec<IfLadderStateMachineCandidate>,
    opcode_maps: Vec<OpcodeMapCandidate>,
    direct_switch_maps: Vec<DirectSwitchMapCandidate>,
    handler_tables: Vec<HandlerTableCandidate>,
    functions: Vec<FunctionMetrics>,
    embedded_code: Vec<EmbeddedCodeCandidate>,
    stack: Vec<FunctionState>,
}

impl<'s> Scanner<'s> {
    fn new(source: &'s str) -> Self {
        Self {
            source,
            arrays: Vec::new(),
            push_builders: Vec::new(),
            decoder_candidates: Vec::new(),
            state_machines: Vec::new(),
            if_ladder_state_machines: Vec::new(),
            opcode_maps: Vec::new(),
            direct_switch_maps: Vec::new(),
            handler_tables: Vec::new(),
            functions: Vec::new(),
            embedded_code: Vec::new(),
            stack: Vec::new(),
        }
    }

    fn push_function(&mut self, kind: &str, name: Option<String>, start: u32, end: u32) {
        self.stack.push(FunctionState::new(kind, name, start, end));
    }

    fn analyze_opcode_maps(&mut self, function: &oxc_ast::ast::Function<'_>) {
        let Some(current) = self.stack.last() else {
            return;
        };
        let parent_function_id = current.m.id.clone();
        let decoders = current.decoder_controls(&self.push_builders);
        if decoders.is_empty() {
            return;
        }

        let machines: Vec<StateMachineInfo> = self
            .state_machines
            .iter()
            .filter(|machine| machine.function_id == parent_function_id)
            .map(|machine| StateMachineInfo {
                start: machine.start,
                end: machine.end,
                state_var: machine.state_var.clone(),
                init_state: machine.init_state,
                mask: machine.mask,
                shift: machine.shift,
                selector_var: machine.selector_var.clone(),
            })
            .collect();
        if machines.is_empty() {
            return;
        }

        let mut maps = state_flatten::analyze_function(
            self.source,
            function,
            &parent_function_id,
            &decoders,
            &machines,
        );
        self.opcode_maps.append(&mut maps);
    }

    fn finish_function(&mut self) {
        let Some(mut function) = self.stack.pop() else {
            return;
        };

        function.finalize_decoders();
        let switch_from_indexed_state = self
            .direct_switch_maps
            .iter()
            .any(|map| map.parent_function_id == function.m.id && map.confirmed_vm);
        let large_handler_table_present = self
            .handler_tables
            .iter()
            .any(|table| table.function_values >= 16);
        function.finalize_metrics(switch_from_indexed_state, large_handler_table_present);

        let propagated_decoders = function.decoder_candidates.clone();
        let propagated_local_accesses = function.indexed_accesses.clone();
        self.functions.push(function.m);
        if let Some(parent) = self.stack.last_mut() {
            parent.decoder_candidates.extend(propagated_decoders);
            parent
                .child_indexed_accesses
                .extend(propagated_local_accesses);
        } else {
            self.decoder_candidates.extend(propagated_decoders);
        }
    }

    fn record_push_builder(&mut self, call: &oxc_ast::ast::CallExpression<'_>) {
        let Some(detected) = detect_push_builder(self.source, call) else {
            return;
        };
        if let Some(name) = &detected.receiver_ident {
            if let Some(current) = self.stack.last_mut() {
                current.push_builder_vars.insert(name.clone());
                current.push_builder_sites.insert(
                    name.clone(),
                    BuilderSite {
                        start: detected.candidate.start,
                        end: detected.candidate.end,
                        arguments: detected.candidate.arguments,
                        width_hints: detected.candidate.width_hints.clone(),
                    },
                );
            }
        }
        self.push_builders.push(detected.candidate);
    }

    fn record_direct_switch(&mut self, switch: &oxc_ast::ast::SwitchStatement<'_>) {
        if switch.cases.len() < 8 {
            return;
        }
        let Some(current) = self.stack.last() else {
            return;
        };
        if current.m.loops == 0 {
            return;
        }
        let evidence = expression_evidence(self.source, &switch.discriminant);
        let indexed_selector = evidence_reaches_computed(&evidence, &current.vars);
        let call_selector = evidence.calls > 0;
        if let Some(candidate) = detect_direct_switch(
            self.source,
            &current.m.id,
            switch,
            indexed_selector,
            call_selector,
        ) {
            self.direct_switch_maps.push(candidate);
        }
    }

    fn record_handler_table(&mut self, object: &oxc_ast::ast::ObjectExpression<'_>) {
        if let Some(candidate) = detect_object_handler_table(self.source, object) {
            self.handler_tables.push(candidate);
        }
    }

    fn record_array(&mut self, arr: &oxc_ast::ast::ArrayExpression<'_>) {
        let n = arr.elements.len();

        if n >= 4 {
            if arr
                .elements
                .iter()
                .all(|el| matches!(el, ArrayExpressionElement::NumericLiteral(_)))
            {
                if let Some(cur) = self.stack.last_mut() {
                    cur.local_numeric_array_lengths.push(n);
                }
            }

            if let Some(candidate) = detect_array_handler_table(self.source, arr) {
                if let Some(current) = self.stack.last_mut() {
                    current.local_function_table_lengths.push(n);
                }
                self.handler_tables.push(candidate);
            }
        }

        if let Some(candidate) = detect_numeric_array(self.source, arr) {
            self.arrays.push(candidate);
        }
    }
}

impl<'a> Visit<'a> for Scanner<'_> {
    fn visit_function(&mut self, function: &oxc_ast::ast::Function<'a>, flags: ScopeFlags) {
        let name = function.id.as_ref().map(|id| id.name.to_string());
        self.push_function("function", name, function.span.start, function.span.end);
        walk::walk_function(self, function, flags);
        self.analyze_opcode_maps(function);
        self.finish_function();
    }

    fn visit_arrow_function_expression(
        &mut self,
        function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
        self.push_function("arrow", None, function.span.start, function.span.end);
        walk::walk_arrow_function_expression(self, function);
        self.finish_function();
    }

    fn visit_object_expression(&mut self, object: &oxc_ast::ast::ObjectExpression<'a>) {
        self.record_handler_table(object);
        walk::walk_object_expression(self, object);
    }

    fn visit_array_expression(&mut self, array: &oxc_ast::ast::ArrayExpression<'a>) {
        self.record_array(array);
        if let Some(current) = self.stack.last_mut() {
            current.m.arrays += 1;
            if array.elements.len() >= 32 {
                current.m.large_arrays += 1;
            }
        }
        walk::walk_array_expression(self, array);
    }

    fn visit_switch_statement(&mut self, switch: &oxc_ast::ast::SwitchStatement<'a>) {
        self.record_direct_switch(switch);
        if let Some(current) = self.stack.last_mut() {
            current.m.switches += 1;
            current.m.switch_cases += switch.cases.len();
            current
                .switch_inputs
                .push(expression_evidence(self.source, &switch.discriminant));
        }
        walk::walk_switch_statement(self, switch);
    }

    fn visit_for_statement(&mut self, statement: &oxc_ast::ast::ForStatement<'a>) {
        if let Some(function_id) = self.stack.last().map(|current| current.m.id.as_str()) {
            let detected = detect_for_state_machines(self.source, function_id, statement);
            self.state_machines.extend(detected.switch_machines);
            self.if_ladder_state_machines
                .extend(detected.if_ladder_machines);
        }
        if let Some(current) = self.stack.last_mut() {
            current.m.loops += 1;
        }
        walk::walk_for_statement(self, statement);
    }

    fn visit_while_statement(&mut self, statement: &oxc_ast::ast::WhileStatement<'a>) {
        if let Some(current) = self.stack.last_mut() {
            current.m.loops += 1;
        }
        walk::walk_while_statement(self, statement);
    }

    fn visit_do_while_statement(&mut self, statement: &oxc_ast::ast::DoWhileStatement<'a>) {
        if let Some(current) = self.stack.last_mut() {
            current.m.loops += 1;
        }
        walk::walk_do_while_statement(self, statement);
    }

    fn visit_for_in_statement(&mut self, statement: &oxc_ast::ast::ForInStatement<'a>) {
        if let Some(current) = self.stack.last_mut() {
            current.m.loops += 1;
        }
        walk::walk_for_in_statement(self, statement);
    }

    fn visit_for_of_statement(&mut self, statement: &oxc_ast::ast::ForOfStatement<'a>) {
        if let Some(current) = self.stack.last_mut() {
            current.m.loops += 1;
        }
        walk::walk_for_of_statement(self, statement);
    }

    fn visit_conditional_expression(
        &mut self,
        expression: &oxc_ast::ast::ConditionalExpression<'a>,
    ) {
        if let Some(current) = self.stack.last_mut() {
            current.m.conditionals += 1;
        }
        walk::walk_conditional_expression(self, expression);
    }

    fn visit_computed_member_expression(
        &mut self,
        member: &oxc_ast::ast::ComputedMemberExpression<'a>,
    ) {
        let indexed_access = if let Expression::Identifier(object) = &member.object {
            index_shape(&member.expression).map(|shape| IndexedAccess {
                object: object.name.to_string(),
                shape,
                start: member.span.start,
                end: member.span.end,
                preview: preview(self.source, member.span.start, member.span.end, 160),
            })
        } else {
            None
        };

        if let Some(current) = self.stack.last_mut() {
            current.m.computed_members += 1;
            if let Some(access) = indexed_access {
                current.indexed_accesses.push(access);
            }
        }
        walk::walk_computed_member_expression(self, member);
    }

    fn visit_variable_declarator(&mut self, declarator: &oxc_ast::ast::VariableDeclarator<'a>) {
        let fetched_access = if let (
            oxc_ast::ast::BindingPattern::BindingIdentifier(id),
            Some(Expression::ComputedMemberExpression(member)),
        ) = (&declarator.id, &declarator.init)
        {
            if let Expression::Identifier(object) = &member.object {
                index_shape(&member.expression).map(|shape| {
                    (
                        id.name.to_string(),
                        IndexedAccess {
                            object: object.name.to_string(),
                            shape,
                            start: member.span.start,
                            end: member.span.end,
                            preview: preview(self.source, member.span.start, member.span.end, 160),
                        },
                    )
                })
            } else {
                None
            }
        } else {
            None
        };

        if let Some(current) = self.stack.last_mut() {
            if let oxc_ast::ast::BindingPattern::BindingIdentifier(id) = &declarator.id {
                if let Some(init) = &declarator.init {
                    let name = id.name.to_string();
                    current
                        .vars
                        .insert(name.clone(), expression_evidence(self.source, init));
                    if let Some(rhs) = expr_ident(init) {
                        current.aliases.insert(name.clone(), rhs);
                    } else {
                        current.aliases.remove(&name);
                    }
                }
            }
            if let Some((name, access)) = fetched_access {
                current.indexed_value_vars.insert(name, access);
            }
        }
        walk::walk_variable_declarator(self, declarator);
    }

    fn visit_call_expression(&mut self, call: &oxc_ast::ast::CallExpression<'a>) {
        self.record_push_builder(call);
        if let Some(candidate) = detect_literal_string_join(call) {
            self.embedded_code.push(candidate);
        }
        let is_function_ctor = matches!(
            &call.callee,
            Expression::Identifier(id) if id.name.as_str() == "Function"
        );
        if let Some(current) = self.stack.last_mut() {
            current.m.calls += 1;
            if let Expression::ComputedMemberExpression(member) = &call.callee {
                current.m.computed_calls += 1;
                current
                    .computed_call_indices
                    .push(expression_evidence(self.source, &member.expression));
            }
        }
        if is_function_ctor {
            if let Some(candidate) = detect_function_constructor(
                "Function",
                call.span.start,
                call.span.end,
                &call.arguments,
            ) {
                self.embedded_code.push(candidate);
            }
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_new_expression(&mut self, expression: &oxc_ast::ast::NewExpression<'a>) {
        if matches!(
            &expression.callee,
            Expression::Identifier(id) if id.name.as_str() == "Function"
        ) {
            if let Some(candidate) = detect_function_constructor(
                "new Function",
                expression.span.start,
                expression.span.end,
                &expression.arguments,
            ) {
                self.embedded_code.push(candidate);
            }
        }
        walk::walk_new_expression(self, expression);
    }

    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        let lhs = if assignment.operator.is_assign() {
            target_ident(&assignment.left)
        } else {
            None
        };
        let rhs = expr_ident(&assignment.right);
        let fetched_access = if let (Some(lhs_name), Expression::ComputedMemberExpression(member)) =
            (lhs.as_ref(), &assignment.right)
        {
            if let Expression::Identifier(object) = &member.object {
                index_shape(&member.expression).map(|shape| {
                    (
                        lhs_name.clone(),
                        IndexedAccess {
                            object: object.name.to_string(),
                            shape,
                            start: member.span.start,
                            end: member.span.end,
                            preview: preview(self.source, member.span.start, member.span.end, 160),
                        },
                    )
                })
            } else {
                None
            }
        } else {
            None
        };

        if let Some(current) = self.stack.last_mut() {
            current.m.assignments += 1;
            if let Some(lhs) = lhs {
                if let Some(rhs) = rhs {
                    current.aliases.insert(lhs, rhs);
                } else {
                    current.aliases.remove(&lhs);
                }
            }
            if let Some((name, access)) = fetched_access {
                current.indexed_value_vars.insert(name, access);
            }
        }
        walk::walk_assignment_expression(self, assignment);
    }

    fn visit_binary_expression(&mut self, binary: &oxc_ast::ast::BinaryExpression<'a>) {
        let bit_mask = if binary.operator.as_str() == "&" {
            if let (Some(name), Some(mask)) =
                (origin_ident(&binary.left), origin_u64(&binary.right))
            {
                Some((name, mask))
            } else if let (Some(mask), Some(name)) =
                (origin_u64(&binary.left), origin_ident(&binary.right))
            {
                Some((name, mask))
            } else {
                None
            }
        } else {
            None
        };

        if let Some(current) = self.stack.last_mut() {
            current.m.binary_exprs += 1;
            if let Some((name, mask)) = bit_mask {
                if mask.is_power_of_two() && mask <= (1u64 << 32) {
                    current
                        .bit_masks
                        .entry(name.clone())
                        .or_default()
                        .insert(mask);
                    let resolved = resolve_alias(&name, &current.aliases);
                    if resolved != name {
                        current.bit_masks.entry(resolved).or_default().insert(mask);
                    }
                }
            }
        }
        walk::walk_binary_expression(self, binary);
    }

    fn visit_unary_expression(&mut self, expression: &oxc_ast::ast::UnaryExpression<'a>) {
        if let Some(current) = self.stack.last_mut() {
            current.m.unary_exprs += 1;
        }
        walk::walk_unary_expression(self, expression);
    }

    fn visit_sequence_expression(&mut self, expression: &oxc_ast::ast::SequenceExpression<'a>) {
        if let Some(current) = self.stack.last_mut() {
            current.m.sequence_exprs += 1;
        }
        walk::walk_sequence_expression(self, expression);
    }

    fn visit_numeric_literal(&mut self, _literal: &oxc_ast::ast::NumericLiteral<'a>) {
        if let Some(current) = self.stack.last_mut() {
            current.m.numeric_literals += 1;
        }
    }

    fn visit_string_literal(&mut self, _literal: &oxc_ast::ast::StringLiteral<'a>) {
        if let Some(current) = self.stack.last_mut() {
            current.m.string_literals += 1;
        }
    }

    fn visit_try_statement(&mut self, statement: &oxc_ast::ast::TryStatement<'a>) {
        if let Some(current) = self.stack.last_mut() {
            current.m.tries += 1;
        }
        walk::walk_try_statement(self, statement);
    }

    fn visit_program(&mut self, program: &oxc_ast::ast::Program<'a>) {
        walk::walk_program(self, program);
    }
}

pub struct ScanCore {
    pub(crate) diagnostics: usize,
    pub(crate) panicked: bool,
    pub(crate) arrays: Vec<ArrayCandidate>,
    pub(crate) push_builders: Vec<PushBuilderCandidate>,
    pub(crate) decoder_candidates: Vec<DecoderCandidate>,
    pub(crate) state_machines: Vec<StateMachineCandidate>,
    pub(crate) if_ladder_state_machines: Vec<IfLadderStateMachineCandidate>,
    pub(crate) opcode_maps: Vec<OpcodeMapCandidate>,
    pub(crate) direct_switch_maps: Vec<DirectSwitchMapCandidate>,
    pub(crate) handler_tables: Vec<HandlerTableCandidate>,
    pub(crate) handler_function_tables: Vec<table_vm::DetailedHandlerTableCandidate>,
    pub(crate) byte_transducers: Vec<table_vm::ByteTransducerCandidate>,
    pub(crate) table_vms: Vec<table_vm::TableVmCandidate>,
    pub(crate) functions: Vec<FunctionMetrics>,
    pub(crate) embedded_code: Vec<EmbeddedCodeCandidate>,
}

fn suppress_nested_table_vms(
    scanner: &Scanner<'_>,
    table_analysis: &mut table_vm::TableVmAnalysis,
) {
    // A direct-switch interpreter may itself execute helper/function tables in
    // individual opcode handlers. Those are nested semantics, not a second
    // dispatcher architecture.
    let direct_switch_owner_spans: Vec<(u32, u32)> = scanner
        .direct_switch_maps
        .iter()
        .filter(|map| map.confirmed_vm)
        .filter_map(|map| {
            scanner
                .functions
                .iter()
                .find(|function| function.id == map.parent_function_id)
                .map(|function| (function.start, function.end))
        })
        .collect();
    let function_spans: HashMap<&str, (u32, u32)> = scanner
        .functions
        .iter()
        .map(|function| (function.id.as_str(), (function.start, function.end)))
        .collect();

    table_analysis.table_vms.retain(|vm| {
        let Some((start, end)) = function_spans.get(vm.dispatcher_function_id.as_str()) else {
            return true;
        };
        !direct_switch_owner_spans
            .iter()
            .any(|(owner_start, owner_end)| owner_start <= start && end <= owner_end)
    });
}

fn normalize_decoders(scanner: &mut Scanner<'_>) {
    scanner.decoder_candidates.sort_by(|a, b| {
        (
            a.start,
            &a.object,
            &a.base,
            &a.ip,
            a.width,
            std::cmp::Reverse(a.operand_offsets.len()),
        )
            .cmp(&(
                b.start,
                &b.object,
                &b.base,
                &b.ip,
                b.width,
                std::cmp::Reverse(b.operand_offsets.len()),
            ))
    });
    scanner.decoder_candidates.dedup_by(|a, b| {
        a.start == b.start
            && a.object == b.object
            && a.base == b.base
            && a.ip == b.ip
            && a.width == b.width
            && a.builder_var == b.builder_var
    });

    // Complete selector width only after every descendant decoder has had a
    // chance to link to its bytecode builder.
    complete_selector_masks(&mut scanner.decoder_candidates, &scanner.push_builders);
}

fn retain_nearest_opcode_maps(scanner: &mut Scanner<'_>) {
    // A decoder is propagated upward so a builder declared in an ancestor can
    // be linked. That must not create a second semantic map against an
    // unrelated ancestor state machine. Keep the smallest lexical parent that
    // produced a map for each decoder/selector identity.
    let function_bytes: HashMap<String, usize> = scanner
        .functions
        .iter()
        .map(|function| (function.id.clone(), function.bytes))
        .collect();
    scanner.opcode_maps.sort_by(|a, b| {
        (
            &a.decoder_function_id,
            &a.decoder_selector_var,
            function_bytes
                .get(&a.parent_function_id)
                .copied()
                .unwrap_or(usize::MAX),
            &a.parent_function_id,
        )
            .cmp(&(
                &b.decoder_function_id,
                &b.decoder_selector_var,
                function_bytes
                    .get(&b.parent_function_id)
                    .copied()
                    .unwrap_or(usize::MAX),
                &b.parent_function_id,
            ))
    });
    scanner.opcode_maps.dedup_by(|a, b| {
        a.decoder_function_id == b.decoder_function_id
            && a.decoder_selector_var == b.decoder_selector_var
    });
}

fn attach_observed_opcodes(scanner: &mut Scanner<'_>) {
    // Builder linkage and semantic-dispatch ownership are deliberately
    // independent: attach live bytecodes to the retained lexical map here.
    for map in &mut scanner.opcode_maps {
        let observed = scanner
            .decoder_candidates
            .iter()
            .filter(|decoder| {
                decoder.function_id == map.decoder_function_id
                    && decoder.selector_var.as_deref() == Some(map.decoder_selector_var.as_str())
                    && decoder.builder_start.is_some()
            })
            .max_by_key(|decoder| decoder.selector_masks.len())
            .map(|decoder| observed_opcodes(decoder, &scanner.push_builders))
            .unwrap_or_default();
        let observed_set: BTreeSet<u64> = observed.iter().copied().collect();
        map.observed_opcodes = observed;
        for handler in &mut map.handlers {
            handler.observed = observed_set.contains(&handler.opcode);
        }
    }
}

fn reconcile_dispatch_confirmation(
    scanner: &mut Scanner<'_>,
    table_analysis: &table_vm::TableVmAnalysis,
) {
    // The broad table heuristic is useful for candidate discovery, but final
    // confirmation must use the exact dispatcher -> table/registry link.
    let table_dispatchers: BTreeSet<&str> = table_analysis
        .table_vms
        .iter()
        .map(|vm| vm.dispatcher_function_id.as_str())
        .collect();
    for function in &mut scanner.functions {
        let switch_confirmed = function
            .dispatch_reasons
            .iter()
            .any(|reason| reason.starts_with("large switch discriminant"));
        let table_confirmed = table_dispatchers.contains(function.id.as_str());
        function.confirmed_dispatch = switch_confirmed || table_confirmed;
        function.dispatch_reasons.retain(|reason| {
            reason.starts_with("large switch discriminant")
                || (!reason.contains("handler table")
                    && !reason.contains("function table")
                    && !reason.contains("same-sized"))
        });
        if table_confirmed {
            function.dispatch_reasons.push(
                "looped computed call is linked to its concrete handler table/registry".into(),
            );
        }
    }
}

fn sort_scan_inventory(scanner: &mut Scanner<'_>) {
    scanner
        .functions
        .sort_by_key(|function| std::cmp::Reverse(function.score));
    scanner
        .arrays
        .sort_by_key(|array| std::cmp::Reverse(array.elements));
    scanner
        .handler_tables
        .sort_by_key(|table| std::cmp::Reverse(table.function_values));
}

pub fn scan_source_core(source: &str) -> ScanCore {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, SourceType::cjs());

    let mut scanner = Scanner::new(source);
    scanner.visit_program(&parsed.program);
    let mut table_analysis = table_vm::analyze(source, &parsed.program);

    suppress_nested_table_vms(&scanner, &mut table_analysis);
    normalize_decoders(&mut scanner);
    retain_nearest_opcode_maps(&mut scanner);
    attach_observed_opcodes(&mut scanner);
    reconcile_dispatch_confirmation(&mut scanner, &table_analysis);
    sort_scan_inventory(&mut scanner);

    ScanCore {
        diagnostics: parsed.diagnostics,
        panicked: parsed.panicked,
        arrays: scanner.arrays,
        push_builders: scanner.push_builders,
        decoder_candidates: scanner.decoder_candidates,
        state_machines: scanner.state_machines,
        if_ladder_state_machines: scanner.if_ladder_state_machines,
        opcode_maps: scanner.opcode_maps,
        direct_switch_maps: scanner.direct_switch_maps,
        handler_tables: scanner.handler_tables,
        handler_function_tables: table_analysis.handler_function_tables,
        byte_transducers: table_analysis.byte_transducers,
        table_vms: table_analysis.table_vms,
        functions: scanner.functions,
        embedded_code: scanner.embedded_code,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scanner_integrates_vm_detectors() {
        let source = r"
            function vm() {
                const code = [
                    0,200,1,201,2,202,3,203,4,204,5,205,6,206,7,207,
                    8,208,9,209,10,210,11,211,12,212,13,213,14,214,15,215
                ];
                let ip = 0;
                const stack = [];
                while (true) {
                    switch (code[ip++]) {
                        case 0: stack.push(1); continue;
                        case 1: stack.pop(); continue;
                        case 2: stack.push(2); continue;
                        case 3: ip++; break;
                        case 4: ip++; break;
                        case 5: ip++; break;
                        case 6: ip++; break;
                        case 7: ip++; break;
                        case 8: ip++; break;
                        case 9: ip++; break;
                        case 10: ip++; break;
                        case 11: ip++; break;
                        case 12: ip++; break;
                        case 13: ip++; break;
                        case 14: ip++; break;
                        case 15: ip++; break;
                    }
                }
            }
        ";

        let core = scan_source_core(source);
        assert!(!core.panicked);
        assert_eq!(core.diagnostics, 0);
        assert_eq!(core.arrays.len(), 1);
        assert_eq!(core.direct_switch_maps.len(), 1);
        assert!(core.direct_switch_maps[0].confirmed_vm);
        assert!(core
            .functions
            .iter()
            .any(|function| function.name.as_deref() == Some("vm") && function.confirmed_dispatch));
    }
}
