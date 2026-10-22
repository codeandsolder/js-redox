use super::{symbol_of, unparenthesized};
use crate::sha256_hex;
use base64::{engine::general_purpose::STANDARD, Engine as _};
use oxc_ast::ast::{
    Argument, AssignmentTarget, BindingPattern, Expression, ForStatementInit, Function, Program,
    Statement, VariableDeclaration,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_span::GetSpan;
use oxc_syntax::{scope::ScopeFlags, symbol::SymbolId};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, Eq, PartialEq)]
enum StaticWasmValue {
    Base64Module(String),
    BufferPair(String),
    Bytes(String),
    Module(String),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum HelperKind {
    Base64ArrayBufferPair,
    ArrayIdentity,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(super) struct ExactModuleSite {
    pub sha256: String,
    pub identity_kind: &'static str,
    pub standard_decode_builtins_required: bool,
}

fn compact(source: &str) -> String {
    source
        .chars()
        .filter(|character| !character.is_ascii_whitespace())
        .collect()
}

fn first_parameter_name<'a>(function: &'a Function<'a>) -> Option<&'a str> {
    let parameter = function.params.items.first()?;
    let BindingPattern::BindingIdentifier(identifier) = &parameter.pattern else {
        return None;
    };
    Some(identifier.name.as_str())
}

struct RequiredUnresolvedGlobals<'c> {
    scoping: &'c Scoping,
    required: HashSet<&'static str>,
    seen: HashSet<&'static str>,
    valid: bool,
}

impl<'a> Visit<'a> for RequiredUnresolvedGlobals<'_> {
    fn visit_identifier_reference(&mut self, identifier: &oxc_ast::ast::IdentifierReference<'a>) {
        let Some(required) = self
            .required
            .iter()
            .copied()
            .find(|name| *name == identifier.name.as_str())
        else {
            return;
        };
        let Some(reference_id) = identifier.reference_id.get() else {
            self.valid = false;
            return;
        };
        if self
            .scoping
            .get_reference(reference_id)
            .symbol_id()
            .is_some()
        {
            self.valid = false;
            return;
        }
        self.seen.insert(required);
    }
}

fn has_required_unresolved_globals(
    function: &Function<'_>,
    scoping: &Scoping,
    names: &[&'static str],
) -> bool {
    let mut probe = RequiredUnresolvedGlobals {
        scoping,
        required: names.iter().copied().collect(),
        seen: HashSet::new(),
        valid: true,
    };
    probe.visit_function(function, ScopeFlags::empty());
    probe.valid && probe.seen.len() == probe.required.len()
}

struct ExactNamedSymbolReferences<'c, 'n> {
    scoping: &'c Scoping,
    name: &'n str,
    symbol: SymbolId,
    seen: bool,
    valid: bool,
}

impl<'a> Visit<'a> for ExactNamedSymbolReferences<'_, '_> {
    fn visit_identifier_reference(&mut self, identifier: &oxc_ast::ast::IdentifierReference<'a>) {
        if identifier.name.as_str() != self.name {
            return;
        }
        let Some(reference_id) = identifier.reference_id.get() else {
            self.valid = false;
            return;
        };
        if self.scoping.get_reference(reference_id).symbol_id() != Some(self.symbol) {
            self.valid = false;
            return;
        }
        self.seen = true;
    }
}

fn function_references_name_only_as_symbol(
    function: &Function<'_>,
    scoping: &Scoping,
    name: &str,
    symbol: SymbolId,
) -> bool {
    let mut probe = ExactNamedSymbolReferences {
        scoping,
        name,
        symbol,
        seen: false,
        valid: true,
    };
    probe.visit_function(function, ScopeFlags::empty());
    probe.seen && probe.valid
}

fn compact_statement(source: &str, statement: &Statement<'_>) -> Option<String> {
    let span = statement.span();
    source
        .get(span.start as usize..span.end as usize)
        .map(compact)
}

fn binding_name<'a>(pattern: &'a BindingPattern<'a>) -> Option<&'a str> {
    let BindingPattern::BindingIdentifier(identifier) = pattern else {
        return None;
    };
    Some(identifier.name.as_str())
}

fn classify_base64_array_buffer_pair(
    source: &str,
    function: &Function<'_>,
    scoping: &Scoping,
    parameter: &str,
) -> bool {
    let Some(body) = &function.body else {
        return false;
    };
    let (flag, decode_if, copy_loop, fallback_return) = match body.statements.as_slice() {
        [decode_if, copy_loop, fallback_return] => (None, decode_if, copy_loop, fallback_return),
        [flag_declaration, decode_if, copy_loop, fallback_return] => {
            let Statement::VariableDeclaration(declaration) = flag_declaration else {
                return false;
            };
            let [declarator] = declaration.declarations.as_slice() else {
                return false;
            };
            let Some(flag) = binding_name(&declarator.id) else {
                return false;
            };
            let Some(flag_source) = compact_statement(source, flag_declaration) else {
                return false;
            };
            let expected =
                format!("var{flag}=arguments.length>1&&void0!==arguments[1]&&arguments[1];");
            if flag_source != expected {
                return false;
            }
            (Some(flag), decode_if, copy_loop, fallback_return)
        }
        _ => return false,
    };

    let Statement::IfStatement(_) = decode_if else {
        return false;
    };
    let Some(decode_if) = compact_statement(source, decode_if) else {
        return false;
    };
    let condition = flag.map_or_else(
        || "Uint8Array.fromBase64".to_string(),
        |flag| format!("Uint8Array.fromBase64&&!{flag}"),
    );
    let direct = format!("[Uint8Array.fromBase64({parameter}).buffer,false]");
    let expected_if = format!("if({condition})return{direct};");
    let expected_if_block = format!("if({condition}){{return{direct};}}");
    if decode_if != expected_if && decode_if != expected_if_block {
        return false;
    }

    let Statement::ForStatement(for_statement) = copy_loop else {
        return false;
    };
    let Some(ForStatementInit::VariableDeclaration(declaration)) = for_statement.init.as_ref()
    else {
        return false;
    };
    let [encoded, bytes, index] = declaration.declarations.as_slice() else {
        return false;
    };
    let (Some(encoded), Some(bytes), Some(index)) = (
        binding_name(&encoded.id),
        binding_name(&bytes.id),
        binding_name(&index.id),
    ) else {
        return false;
    };
    let Some(copy_loop) = compact_statement(source, copy_loop) else {
        return false;
    };
    let loop_core = format!(
        "for(var{encoded}=atob({parameter}),{bytes}=newUint8Array({encoded}.length),{index}=0;{index}<{encoded}.length;{index}++)"
    );
    let copy = format!("{bytes}[{index}]={encoded}.charCodeAt({index});");
    if copy_loop != format!("{loop_core}{copy}") && copy_loop != format!("{loop_core}{{{copy}}}") {
        return false;
    }

    let Statement::ReturnStatement(_) = fallback_return else {
        return false;
    };
    let Some(fallback_return) = compact_statement(source, fallback_return) else {
        return false;
    };
    let fallback = format!("return[{bytes}.buffer,false]");
    if fallback_return != fallback && fallback_return != format!("{fallback};") {
        return false;
    }

    has_required_unresolved_globals(function, scoping, &["Uint8Array", "atob"])
}

fn classify_array_identity(
    source: &str,
    function: &Function<'_>,
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
    parameter: &str,
) -> bool {
    let Some(body) = &function.body else {
        return false;
    };
    let [statement] = body.statements.as_slice() else {
        return false;
    };
    let Statement::ReturnStatement(_) = statement else {
        return false;
    };
    let Some(statement) = compact_statement(source, statement) else {
        return false;
    };
    let prefix = format!("returnfunction({parameter}){{");
    let suffix = format!("}}({parameter})||");
    let suffix_semicolon = format!(";}}({parameter})||");
    let has_shape = |guard: &str| {
        statement.starts_with(&format!("{prefix}{guard}"))
            && (statement.contains(&suffix) || statement.contains(&suffix_semicolon))
    };
    let local_alias_identity = global_aliases.keys().any(|symbol| {
        let alias = scoping.symbol_name(*symbol);
        has_shape(&format!(
            "if({alias}.Array.isArray({parameter}))return{parameter}"
        )) && function_references_name_only_as_symbol(function, scoping, alias, *symbol)
    });
    let direct_identity = has_shape(&format!("if(Array.isArray({parameter}))return{parameter}"))
        && has_required_unresolved_globals(function, scoping, &["Array"]);
    local_alias_identity || direct_identity
}

fn classify_helper(
    source: &str,
    function: &Function<'_>,
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
) -> Option<HelperKind> {
    if function.r#async || function.generator {
        return None;
    }
    let parameter = first_parameter_name(function)?;
    if classify_base64_array_buffer_pair(source, function, scoping, parameter) {
        return Some(HelperKind::Base64ArrayBufferPair);
    }
    classify_array_identity(source, function, scoping, global_aliases, parameter)
        .then_some(HelperKind::ArrayIdentity)
}

struct HelperCollector<'c, 's, 'g> {
    source: &'s str,
    scoping: &'c Scoping,
    global_aliases: &'g HashMap<SymbolId, String>,
    helpers: HashMap<SymbolId, HelperKind>,
}

impl<'a> Visit<'a> for HelperCollector<'_, '_, '_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if let Some(identifier) = &function.id {
            if let Some(symbol) = identifier.symbol_id.get() {
                if let Some(kind) =
                    classify_helper(self.source, function, self.scoping, self.global_aliases)
                {
                    self.helpers.insert(symbol, kind);
                }
            }
        }
        walk::walk_function(self, function, flags);
    }
}

fn collect_helpers(
    source: &str,
    program: &Program<'_>,
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
) -> HashMap<SymbolId, HelperKind> {
    let mut collector = HelperCollector {
        source,
        scoping,
        global_aliases,
        helpers: HashMap::new(),
    };
    collector.visit_program(program);
    collector.helpers
}

fn unresolved_global_identifier(
    scoping: &Scoping,
    expression: &Expression<'_>,
    expected: &str,
) -> bool {
    let Expression::Identifier(identifier) = unparenthesized(expression) else {
        return false;
    };
    if identifier.name.as_str() != expected {
        return false;
    }
    identifier
        .reference_id
        .get()
        .is_some_and(|reference_id| scoping.get_reference(reference_id).symbol_id().is_none())
}

fn webassembly_namespace_global(
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
    expression: &Expression<'_>,
) -> Option<String> {
    if unresolved_global_identifier(scoping, expression, "WebAssembly") {
        return Some("globalThis".to_string());
    }
    match unparenthesized(expression) {
        Expression::StaticMemberExpression(member)
            if !member.optional && member.property.name.as_str() == "WebAssembly" =>
        {
            global_aliases
                .get(&symbol_of(scoping, &member.object)?)
                .cloned()
        }
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Expression::StringLiteral(property) = unparenthesized(&member.expression) else {
                return None;
            };
            if property.value.as_str() != Some("WebAssembly") {
                return None;
            }
            global_aliases
                .get(&symbol_of(scoping, &member.object)?)
                .cloned()
        }
        _ => None,
    }
}

pub(super) fn webassembly_member_name<'a>(
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
    expression: &'a Expression<'a>,
) -> Option<(&'a str, String)> {
    match unparenthesized(expression) {
        Expression::StaticMemberExpression(member) if !member.optional => Some((
            member.property.name.as_str(),
            webassembly_namespace_global(scoping, global_aliases, &member.object)?,
        )),
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Expression::StringLiteral(property) = unparenthesized(&member.expression) else {
                return None;
            };
            Some((
                property.value.as_str()?,
                webassembly_namespace_global(scoping, global_aliases, &member.object)?,
            ))
        }
        _ => None,
    }
}

fn base64_module_value(value: &str) -> Option<StaticWasmValue> {
    if !value.starts_with("AGFzbQ") {
        return None;
    }
    let decoded = STANDARD.decode(value.as_bytes()).ok()?;
    decoded
        .starts_with(b"\0asm")
        .then(|| StaticWasmValue::Base64Module(sha256_hex(&decoded)))
}

struct Evaluator<'c, 'h, 'v, 'g> {
    scoping: &'c Scoping,
    helpers: &'h HashMap<SymbolId, HelperKind>,
    values: &'v HashMap<SymbolId, StaticWasmValue>,
    global_aliases: &'g HashMap<SymbolId, String>,
}

impl Evaluator<'_, '_, '_, '_> {
    fn expression(&self, expression: &Expression<'_>) -> Option<StaticWasmValue> {
        let expression = unparenthesized(expression);
        match expression {
            Expression::StringLiteral(literal) => base64_module_value(literal.value.as_str()?),
            Expression::Identifier(_) => self
                .values
                .get(&symbol_of(self.scoping, expression)?)
                .cloned(),
            Expression::ComputedMemberExpression(member) if !member.optional => {
                let Expression::NumericLiteral(index) = unparenthesized(&member.expression) else {
                    return None;
                };
                if index.value != 0.0 {
                    return None;
                }
                match self.expression(&member.object)? {
                    StaticWasmValue::BufferPair(sha256) => Some(StaticWasmValue::Bytes(sha256)),
                    _ => None,
                }
            }
            Expression::CallExpression(call)
                if !call.optional && !call.arguments.iter().any(Argument::is_spread) =>
            {
                let helper = self.helpers.get(&symbol_of(self.scoping, &call.callee)?)?;
                let first = call.arguments.first()?.as_expression()?;
                match (helper, self.expression(first)?) {
                    (HelperKind::Base64ArrayBufferPair, StaticWasmValue::Base64Module(sha256)) => {
                        Some(StaticWasmValue::BufferPair(sha256))
                    }
                    (HelperKind::ArrayIdentity, StaticWasmValue::BufferPair(sha256)) => {
                        Some(StaticWasmValue::BufferPair(sha256))
                    }
                    _ => None,
                }
            }
            Expression::NewExpression(new_expression)
                if !new_expression.arguments.iter().any(Argument::is_spread) =>
            {
                let (member, _) = webassembly_member_name(
                    self.scoping,
                    self.global_aliases,
                    &new_expression.callee,
                )?;
                if member != "Module" {
                    return None;
                }
                let [argument] = new_expression.arguments.as_slice() else {
                    return None;
                };
                match self.expression(argument.as_expression()?)? {
                    StaticWasmValue::Bytes(sha256) => Some(StaticWasmValue::Module(sha256)),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

#[derive(Default)]
struct WriteState {
    value: Option<StaticWasmValue>,
    unknown: bool,
    conflict: bool,
}

impl WriteState {
    fn record(&mut self, value: Option<StaticWasmValue>) {
        let Some(value) = value else {
            self.unknown = true;
            return;
        };
        match &self.value {
            None => self.value = Some(value),
            Some(existing) if existing == &value => {}
            Some(_) => self.conflict = true,
        }
    }

    fn proven(self) -> Option<StaticWasmValue> {
        (!self.unknown && !self.conflict)
            .then_some(self.value)
            .flatten()
    }
}

struct WriteCollector<'c, 'h, 'v, 'g> {
    evaluator: Evaluator<'c, 'h, 'v, 'g>,
    writes: HashMap<SymbolId, WriteState>,
}

impl WriteCollector<'_, '_, '_, '_> {
    fn record(&mut self, symbol: SymbolId, expression: Option<&Expression<'_>>) {
        let value = expression.and_then(|expression| self.evaluator.expression(expression));
        self.writes.entry(symbol).or_default().record(value);
    }
}

impl<'a> Visit<'a> for WriteCollector<'_, '_, '_, '_> {
    fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
        for declarator in &declaration.declarations {
            let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                continue;
            };
            if let Some(symbol) = identifier.symbol_id.get() {
                self.record(symbol, declarator.init.as_ref());
            }
        }
        walk::walk_variable_declaration(self, declaration);
    }

    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        if assignment.operator.as_str() == "=" {
            if let AssignmentTarget::AssignmentTargetIdentifier(identifier) = &assignment.left {
                if let Some(symbol) = identifier.reference_id.get().and_then(|reference_id| {
                    self.evaluator
                        .scoping
                        .get_reference(reference_id)
                        .symbol_id()
                }) {
                    self.record(symbol, Some(&assignment.right));
                }
            }
        }
        walk::walk_assignment_expression(self, assignment);
    }
}

#[derive(Debug, Clone)]
struct OrderedWrite {
    start: u32,
    value: Option<StaticWasmValue>,
}

struct OrderedWriteCollector<'c, 'h, 'v, 'g> {
    evaluator: Evaluator<'c, 'h, 'v, 'g>,
    writes: HashMap<SymbolId, Vec<OrderedWrite>>,
}

impl OrderedWriteCollector<'_, '_, '_, '_> {
    fn record(&mut self, symbol: SymbolId, start: u32, expression: &Expression<'_>) {
        let value = self.evaluator.expression(expression);
        self.writes
            .entry(symbol)
            .or_default()
            .push(OrderedWrite { start, value });
    }
}

impl<'a> Visit<'a> for OrderedWriteCollector<'_, '_, '_, '_> {
    fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
        for declarator in &declaration.declarations {
            let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                continue;
            };
            let Some(initializer) = declarator.init.as_ref() else {
                continue;
            };
            if let Some(symbol) = identifier.symbol_id.get() {
                self.record(symbol, declarator.span.start, initializer);
            }
        }
        walk::walk_variable_declaration(self, declaration);
    }

    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        if assignment.operator.as_str() == "=" {
            if let AssignmentTarget::AssignmentTargetIdentifier(identifier) = &assignment.left {
                if let Some(symbol) = identifier.reference_id.get().and_then(|reference_id| {
                    self.evaluator
                        .scoping
                        .get_reference(reference_id)
                        .symbol_id()
                }) {
                    self.record(symbol, assignment.span.start, &assignment.right);
                }
            }
        }
        walk::walk_assignment_expression(self, assignment);
    }
}

fn collect_static_values(
    program: &Program<'_>,
    scoping: &Scoping,
    helpers: &HashMap<SymbolId, HelperKind>,
    global_aliases: &HashMap<SymbolId, String>,
) -> HashMap<SymbolId, StaticWasmValue> {
    let mut values = HashMap::new();
    for _ in 0..16 {
        let evaluator = Evaluator {
            scoping,
            helpers,
            values: &values,
            global_aliases,
        };
        let mut collector = WriteCollector {
            evaluator,
            writes: HashMap::new(),
        };
        collector.visit_program(program);
        let next = collector
            .writes
            .into_iter()
            .filter_map(|(symbol, state)| state.proven().map(|value| (symbol, value)))
            .collect::<HashMap<_, _>>();
        if next == values {
            break;
        }
        values = next;
    }
    values
}

struct SiteCollector<'c, 'h, 'v, 'g, 'w> {
    evaluator: Evaluator<'c, 'h, 'v, 'g>,
    ordered_writes: &'w HashMap<SymbolId, Vec<OrderedWrite>>,
    sites: HashMap<(u32, u32), ExactModuleSite>,
}

impl SiteCollector<'_, '_, '_, '_, '_> {
    fn successful_value_before(
        &self,
        expression: &Expression<'_>,
        site_start: u32,
    ) -> Option<StaticWasmValue> {
        if let Some(value) = self.evaluator.expression(expression) {
            return Some(value);
        }
        let symbol = symbol_of(self.evaluator.scoping, expression)?;
        let mut proven = None;
        for write in self.ordered_writes.get(&symbol)? {
            if write.start >= site_start {
                continue;
            }
            let value = write.value.as_ref()?;
            match &proven {
                None => proven = Some(value.clone()),
                Some(existing) if existing == value => {}
                Some(_) => return None,
            }
        }
        proven
    }

    fn exact_sha_from_argument(
        &self,
        argument: &Argument<'_>,
        site_start: u32,
    ) -> Option<(String, &'static str)> {
        match self.successful_value_before(argument.as_expression()?, site_start)? {
            StaticWasmValue::Bytes(sha256) => Some((sha256, "exact_bytes")),
            StaticWasmValue::Module(sha256) => Some((sha256, "compiled_module")),
            _ => None,
        }
    }

    fn insert(&mut self, span: oxc_span::Span, sha256: String, identity_kind: &'static str) {
        self.sites.insert(
            (span.start, span.end),
            ExactModuleSite {
                sha256,
                identity_kind,
                standard_decode_builtins_required: true,
            },
        );
    }
}

impl<'a> Visit<'a> for SiteCollector<'_, '_, '_, '_, '_> {
    fn visit_call_expression(&mut self, call: &oxc_ast::ast::CallExpression<'a>) {
        if !call.optional && !call.arguments.iter().any(Argument::is_spread) {
            if let Some((member, _)) = webassembly_member_name(
                self.evaluator.scoping,
                self.evaluator.global_aliases,
                &call.callee,
            ) {
                if member == "instantiate" {
                    if let Some(argument) = call.arguments.first() {
                        if let Some((sha256, identity_kind)) =
                            self.exact_sha_from_argument(argument, call.span.start)
                        {
                            self.insert(call.span, sha256, identity_kind);
                        }
                    }
                }
            }
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_new_expression(&mut self, expression: &oxc_ast::ast::NewExpression<'a>) {
        if let Some((member, _)) = webassembly_member_name(
            self.evaluator.scoping,
            self.evaluator.global_aliases,
            &expression.callee,
        ) {
            if member == "Instance" && !expression.arguments.iter().any(Argument::is_spread) {
                if let Some(argument) = expression.arguments.first() {
                    if let Some((sha256, identity_kind)) =
                        self.exact_sha_from_argument(argument, expression.span.start)
                    {
                        self.insert(expression.span, sha256, identity_kind);
                    }
                }
            }
        }
        walk::walk_new_expression(self, expression);
    }
}

pub(super) fn collect_exact_module_sites(
    source: &str,
    program: &Program<'_>,
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
) -> HashMap<(u32, u32), ExactModuleSite> {
    let helpers = collect_helpers(source, program, scoping, global_aliases);
    let values = collect_static_values(program, scoping, &helpers, global_aliases);
    let evaluator = Evaluator {
        scoping,
        helpers: &helpers,
        values: &values,
        global_aliases,
    };
    let mut ordered_write_collector = OrderedWriteCollector {
        evaluator: Evaluator {
            scoping,
            helpers: &helpers,
            values: &values,
            global_aliases,
        },
        writes: HashMap::new(),
    };
    ordered_write_collector.visit_program(program);
    for writes in ordered_write_collector.writes.values_mut() {
        writes.sort_by_key(|write| write.start);
    }
    let mut collector = SiteCollector {
        evaluator,
        ordered_writes: &ordered_write_collector.writes,
        sites: HashMap::new(),
    };
    collector.visit_program(program);
    collector.sites
}
