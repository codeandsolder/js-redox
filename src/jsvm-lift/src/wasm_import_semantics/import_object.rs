use super::{assignment_property, module_identity::ExactModuleSite, symbol_of, unparenthesized};
use crate::global_builtin::namespace_member_name;
use oxc_ast::ast::{
    Argument, AssignmentTarget, BindingPattern, BlockStatement, CallExpression, Expression,
    Function, Program, Statement, SwitchCase,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_syntax::symbol::SymbolId;
use serde::Serialize;
use std::collections::HashMap;

/// A source-level WebAssembly instantiation site using one exact stable local import object.
///
/// `exact_module_identity_proven` is stronger than lexical site identity: when true, the first
/// argument has been statically tied to one exact decoded WASM SHA-256 by the conservative module
/// provenance evaluator. Platform WebAssembly semantics are still an explicit assumption.
#[derive(Debug, Clone, Eq, PartialEq, Serialize)]
pub struct WasmInstantiationSite {
    pub start: u32,
    pub end: u32,
    pub kind: &'static str,
    pub module_argument: usize,
    pub import_argument: usize,
    pub global_object: String,
    pub webassembly_builtin_reference_proven: bool,
    pub standard_webassembly_builtin_semantics_required: bool,
    pub exact_import_object_identity_proven: bool,
    pub import_object_identity_kind: &'static str,
    pub exact_module_identity_proven: bool,
    pub module_sha256: Option<String>,
    pub module_identity_kind: Option<&'static str>,
    pub standard_module_decode_builtins_required: bool,
}

/// Links an `imports.<module>.<name>` assignment root to later WebAssembly instantiation sites.
#[derive(Debug, Clone, Eq, PartialEq, Serialize)]
pub struct WasmImportObjectUsage {
    pub import_module: String,
    pub import_name: String,
    pub assignment_start: u32,
    pub assignment_end: u32,
    pub import_object: String,
    pub instantiation_sites: Vec<WasmInstantiationSite>,
}

fn identifier_symbol_and_name(
    scoping: &Scoping,
    expression: &Expression<'_>,
) -> Option<(SymbolId, String)> {
    let Expression::Identifier(identifier) = unparenthesized(expression) else {
        return None;
    };
    let symbol = scoping
        .get_reference(identifier.reference_id.get()?)
        .symbol_id()?;
    Some((symbol, identifier.name.to_string()))
}

fn module_member_root(
    scoping: &Scoping,
    expression: &Expression<'_>,
) -> Option<(SymbolId, String)> {
    match unparenthesized(expression) {
        Expression::StaticMemberExpression(member) if !member.optional => {
            identifier_symbol_and_name(scoping, &member.object)
        }
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Expression::StringLiteral(_) = unparenthesized(&member.expression) else {
                return None;
            };
            identifier_symbol_and_name(scoping, &member.object)
        }
        _ => None,
    }
}

pub(super) fn assignment_import_object(
    scoping: &Scoping,
    target: &AssignmentTarget<'_>,
) -> Option<(SymbolId, String, String, String)> {
    let (import_name, import_module) = assignment_property(target)?;
    let import_module = import_module?;
    let object = match target {
        AssignmentTarget::StaticMemberExpression(member) if !member.optional => &member.object,
        AssignmentTarget::ComputedMemberExpression(member) if !member.optional => &member.object,
        _ => return None,
    };
    let (symbol, name) = module_member_root(scoping, object)?;
    Some((
        symbol,
        name,
        import_module.to_string(),
        import_name.to_string(),
    ))
}

fn second_argument_symbol(scoping: &Scoping, arguments: &[Argument<'_>]) -> Option<SymbolId> {
    let [_, import_object] = arguments else {
        return None;
    };
    symbol_of(scoping, import_object.as_expression()?)
}

fn site_record(
    start: u32,
    end: u32,
    kind: &'static str,
    global_object: String,
    import_object_identity_kind: &'static str,
    exact_sites: &HashMap<(u32, u32), ExactModuleSite>,
) -> WasmInstantiationSite {
    let exact = exact_sites.get(&(start, end));
    WasmInstantiationSite {
        start,
        end,
        kind,
        module_argument: 0,
        import_argument: 1,
        global_object,
        webassembly_builtin_reference_proven: true,
        standard_webassembly_builtin_semantics_required: true,
        exact_import_object_identity_proven: true,
        import_object_identity_kind,
        exact_module_identity_proven: exact.is_some(),
        module_sha256: exact.map(|site| site.sha256.clone()),
        module_identity_kind: exact.map(|site| site.identity_kind),
        standard_module_decode_builtins_required: exact
            .is_some_and(|site| site.standard_decode_builtins_required),
    }
}

struct InstantiationSiteCollector<'c, 'g, 'm> {
    scoping: &'c Scoping,
    global_aliases: &'g HashMap<SymbolId, String>,
    exact_sites: &'m HashMap<(u32, u32), ExactModuleSite>,
    sites: HashMap<SymbolId, Vec<WasmInstantiationSite>>,
}

impl<'a> Visit<'a> for InstantiationSiteCollector<'_, '_, '_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            if let Some((member, global_object)) = namespace_member_name(
                self.scoping,
                self.global_aliases,
                &call.callee,
                "WebAssembly",
            ) {
                if matches!(member, "instantiate" | "instantiateStreaming") {
                    if let Some(symbol) = second_argument_symbol(self.scoping, &call.arguments) {
                        self.sites.entry(symbol).or_default().push(site_record(
                            call.span.start,
                            call.span.end,
                            if member == "instantiate" {
                                "WebAssembly.instantiate"
                            } else {
                                "WebAssembly.instantiateStreaming"
                            },
                            global_object,
                            "same_binding",
                            self.exact_sites,
                        ));
                    }
                }
            }
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_new_expression(&mut self, expression: &oxc_ast::ast::NewExpression<'a>) {
        if let Some((member, global_object)) = namespace_member_name(
            self.scoping,
            self.global_aliases,
            &expression.callee,
            "WebAssembly",
        ) {
            if member == "Instance" {
                if let Some(symbol) = second_argument_symbol(self.scoping, &expression.arguments) {
                    self.sites.entry(symbol).or_default().push(site_record(
                        expression.span.start,
                        expression.span.end,
                        "new WebAssembly.Instance",
                        global_object,
                        "same_binding",
                        self.exact_sites,
                    ));
                }
            }
        }
        walk::walk_new_expression(self, expression);
    }
}

fn returned_symbol(expression: &Expression<'_>, scoping: &Scoping) -> Option<SymbolId> {
    match unparenthesized(expression) {
        Expression::Identifier(_) => symbol_of(scoping, expression),
        Expression::SequenceExpression(sequence) => {
            symbol_of(scoping, sequence.expressions.last()?)
        }
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
struct RegionId {
    start: u32,
    end: u32,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
struct StatementPosition {
    region: RegionId,
    index: usize,
}

#[derive(Debug, Clone, Copy)]
struct FreshReturnedObject {
    object_symbol: SymbolId,
    region: RegionId,
    return_index: usize,
}

#[derive(Default)]
struct FunctionReturnCounter {
    function_depth: usize,
    returns: usize,
}

impl<'a> Visit<'a> for FunctionReturnCounter {
    fn visit_function(&mut self, function: &Function<'a>, flags: oxc_syntax::scope::ScopeFlags) {
        self.function_depth += 1;
        walk::walk_function(self, function, flags);
        self.function_depth -= 1;
    }

    fn visit_return_statement(&mut self, statement: &oxc_ast::ast::ReturnStatement<'a>) {
        if self.function_depth == 1 {
            self.returns += 1;
        }
        walk::walk_return_statement(self, statement);
    }
}

fn has_exactly_one_function_return(function: &Function<'_>) -> bool {
    let mut counter = FunctionReturnCounter::default();
    counter.visit_function(function, oxc_syntax::scope::ScopeFlags::empty());
    counter.returns == 1
}

fn fresh_returned_object(
    function: &Function<'_>,
    scoping: &Scoping,
) -> Option<FreshReturnedObject> {
    if !has_exactly_one_function_return(function) {
        return None;
    }
    let body = function.body.as_ref()?;
    let mut fresh_objects = Vec::new();
    let mut returns = Vec::new();
    for (index, statement) in body.statements.iter().enumerate() {
        match statement {
            Statement::VariableDeclaration(declaration) => {
                for declarator in &declaration.declarations {
                    let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                        continue;
                    };
                    if matches!(
                        declarator.init.as_ref(),
                        Some(Expression::ObjectExpression(_))
                    ) {
                        fresh_objects.push(identifier.symbol_id.get()?);
                    }
                }
            }
            Statement::ReturnStatement(statement) => {
                returns.push((
                    index,
                    returned_symbol(statement.argument.as_ref()?, scoping)?,
                ));
            }
            _ => {}
        }
    }
    let [(return_index, returned)] = returns.as_slice() else {
        return None;
    };
    fresh_objects
        .contains(returned)
        .then_some(FreshReturnedObject {
            object_symbol: *returned,
            region: RegionId {
                start: function.span.start,
                end: function.span.end,
            },
            return_index: *return_index,
        })
        .filter(|fresh| super::symbol_binding_is_stable(scoping, fresh.object_symbol))
}

struct ReturnedObjectFunctionCollector<'c> {
    scoping: &'c Scoping,
    functions: HashMap<SymbolId, FreshReturnedObject>,
}

impl<'a> Visit<'a> for ReturnedObjectFunctionCollector<'_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: oxc_syntax::scope::ScopeFlags) {
        if let Some(identifier) = &function.id {
            if let Some(function_symbol) = identifier.symbol_id.get() {
                if super::symbol_binding_is_stable(self.scoping, function_symbol) {
                    if let Some(object) = fresh_returned_object(function, self.scoping) {
                        self.functions.insert(function_symbol, object);
                    }
                }
            }
        }
        walk::walk_function(self, function, flags);
    }
}

fn collect_returned_object_functions(
    program: &Program<'_>,
    scoping: &Scoping,
) -> HashMap<SymbolId, FreshReturnedObject> {
    let mut collector = ReturnedObjectFunctionCollector {
        scoping,
        functions: HashMap::new(),
    };
    collector.visit_program(program);
    collector.functions
}

#[derive(Debug, Clone)]
struct DirectAssignment {
    span: (u32, u32),
    symbol: SymbolId,
    module: String,
    name: String,
    position: StatementPosition,
    return_prefix: bool,
}

#[derive(Debug, Clone)]
struct ReturnedObjectAlias {
    result_symbol: SymbolId,
    object_symbol: SymbolId,
    position: StatementPosition,
}

#[derive(Default)]
struct DirectExecutionFacts {
    assignments: Vec<DirectAssignment>,
    aliases: Vec<ReturnedObjectAlias>,
    site_positions: HashMap<(u32, u32), Vec<StatementPosition>>,
}

type ImportMemberKey = (SymbolId, String, String);

struct ImportMemberWriteCollector<'c> {
    scoping: &'c Scoping,
    counts: HashMap<ImportMemberKey, usize>,
}

impl<'a> Visit<'a> for ImportMemberWriteCollector<'_> {
    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        if let Some((symbol, _, module, name)) =
            assignment_import_object(self.scoping, &assignment.left)
        {
            *self.counts.entry((symbol, module, name)).or_default() += 1;
        }
        walk::walk_assignment_expression(self, assignment);
    }
}

fn collect_import_member_write_counts(
    program: &Program<'_>,
    scoping: &Scoping,
) -> HashMap<ImportMemberKey, usize> {
    let mut collector = ImportMemberWriteCollector {
        scoping,
        counts: HashMap::new(),
    };
    collector.visit_program(program);
    collector.counts
}

struct StatementSitePositionCollector<'f> {
    position: StatementPosition,
    site_positions: &'f mut HashMap<(u32, u32), Vec<StatementPosition>>,
}

impl<'a> Visit<'a> for StatementSitePositionCollector<'_> {
    fn visit_function(&mut self, _function: &Function<'a>, _flags: oxc_syntax::scope::ScopeFlags) {
        // A nested function is a separate execution region; do not attribute its sites
        // to the enclosing top-level statement.
    }

    fn visit_arrow_function_expression(
        &mut self,
        _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
        // Arrow bodies are likewise separate execution regions. They are intentionally
        // unsupported here until we model their invocation path explicitly.
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        self.site_positions
            .entry((call.span.start, call.span.end))
            .or_default()
            .push(self.position);
        walk::walk_call_expression(self, call);
    }

    fn visit_new_expression(&mut self, expression: &oxc_ast::ast::NewExpression<'a>) {
        self.site_positions
            .entry((expression.span.start, expression.span.end))
            .or_default()
            .push(self.position);
        walk::walk_new_expression(self, expression);
    }
}

fn record_statement_site_positions(
    statement: &Statement<'_>,
    position: StatementPosition,
    site_positions: &mut HashMap<(u32, u32), Vec<StatementPosition>>,
) {
    let mut collector = StatementSitePositionCollector {
        position,
        site_positions,
    };
    collector.visit_statement(statement);
}

fn record_direct_import_assignment(
    assignment: &oxc_ast::ast::AssignmentExpression<'_>,
    position: StatementPosition,
    return_prefix: bool,
    scoping: &Scoping,
    facts: &mut DirectExecutionFacts,
) {
    let Some((symbol, _, module, name)) = assignment_import_object(scoping, &assignment.left)
    else {
        return;
    };
    if !super::symbol_binding_is_stable(scoping, symbol) {
        return;
    }
    facts.assignments.push(DirectAssignment {
        span: (assignment.span.start, assignment.span.end),
        symbol,
        module,
        name,
        position,
        return_prefix,
    });
}

fn record_return_sequence_assignments(
    expression: &Expression<'_>,
    position: StatementPosition,
    scoping: &Scoping,
    facts: &mut DirectExecutionFacts,
) {
    let Expression::SequenceExpression(sequence) = unparenthesized(expression) else {
        return;
    };
    let Some((_, prefix)) = sequence.expressions.split_last() else {
        return;
    };
    for expression in prefix {
        if let Expression::AssignmentExpression(assignment) = unparenthesized(expression) {
            record_direct_import_assignment(assignment, position, true, scoping, facts);
        }
    }
}

fn returned_object_for_call(
    scoping: &Scoping,
    functions: &HashMap<SymbolId, FreshReturnedObject>,
    expression: &Expression<'_>,
) -> Option<FreshReturnedObject> {
    let Expression::CallExpression(call) = unparenthesized(expression) else {
        return None;
    };
    if call.optional || call.arguments.iter().any(Argument::is_spread) {
        return None;
    }
    functions.get(&symbol_of(scoping, &call.callee)?).copied()
}

fn record_region(
    statements: &[Statement<'_>],
    region: RegionId,
    scoping: &Scoping,
    functions: &HashMap<SymbolId, FreshReturnedObject>,
    facts: &mut DirectExecutionFacts,
) {
    for (index, statement) in statements.iter().enumerate() {
        let position = StatementPosition { region, index };
        record_statement_site_positions(statement, position, &mut facts.site_positions);
        match statement {
            Statement::ExpressionStatement(statement) => {
                let expression = unparenthesized(&statement.expression);
                if let Expression::AssignmentExpression(assignment) = expression {
                    record_direct_import_assignment(assignment, position, false, scoping, facts);
                }
            }
            Statement::VariableDeclaration(declaration) => {
                for declarator in &declaration.declarations {
                    let Some(initializer) = &declarator.init else {
                        continue;
                    };
                    let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                        continue;
                    };
                    let Some(result_symbol) = identifier.symbol_id.get() else {
                        continue;
                    };
                    let Some(returned) = returned_object_for_call(scoping, functions, initializer)
                    else {
                        continue;
                    };
                    if super::symbol_binding_is_stable(scoping, result_symbol) {
                        facts.aliases.push(ReturnedObjectAlias {
                            result_symbol,
                            object_symbol: returned.object_symbol,
                            position,
                        });
                    }
                }
            }
            Statement::ReturnStatement(statement) => {
                if let Some(argument) = &statement.argument {
                    record_return_sequence_assignments(argument, position, scoping, facts);
                }
            }
            _ => {}
        }
    }
}

struct FunctionRegionCollector<'c, 'f> {
    scoping: &'c Scoping,
    functions: &'f HashMap<SymbolId, FreshReturnedObject>,
    facts: DirectExecutionFacts,
}

impl<'a> Visit<'a> for FunctionRegionCollector<'_, '_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: oxc_syntax::scope::ScopeFlags) {
        if let Some(body) = &function.body {
            record_region(
                &body.statements,
                RegionId {
                    start: function.span.start,
                    end: function.span.end,
                },
                self.scoping,
                self.functions,
                &mut self.facts,
            );
        }
        walk::walk_function(self, function, flags);
    }

    fn visit_block_statement(&mut self, block: &BlockStatement<'a>) {
        record_region(
            &block.body,
            RegionId {
                start: block.span.start,
                end: block.span.end,
            },
            self.scoping,
            self.functions,
            &mut self.facts,
        );
        walk::walk_block_statement(self, block);
    }

    fn visit_switch_case(&mut self, case: &SwitchCase<'a>) {
        record_region(
            &case.consequent,
            RegionId {
                start: case.span.start,
                end: case.span.end,
            },
            self.scoping,
            self.functions,
            &mut self.facts,
        );
        walk::walk_switch_case(self, case);
    }
}

fn collect_direct_execution_facts(
    program: &Program<'_>,
    scoping: &Scoping,
    functions: &HashMap<SymbolId, FreshReturnedObject>,
) -> DirectExecutionFacts {
    let mut collector = FunctionRegionCollector {
        scoping,
        functions,
        facts: DirectExecutionFacts::default(),
    };
    record_region(
        &program.body,
        RegionId {
            start: program.span.start,
            end: program.span.end,
        },
        scoping,
        functions,
        &mut collector.facts,
    );
    collector.visit_program(program);
    collector.facts
}

fn later_in_same_region(left: StatementPosition, right: StatementPosition) -> bool {
    left.region == right.region && left.index < right.index
}

fn site_is_later_in_region(
    site_positions: &HashMap<(u32, u32), Vec<StatementPosition>>,
    site: &WasmInstantiationSite,
    earlier: StatementPosition,
) -> bool {
    site_positions
        .get(&(site.start, site.end))
        .is_some_and(|positions| {
            positions
                .iter()
                .copied()
                .any(|position| later_in_same_region(earlier, position))
        })
}

pub(super) fn collect_instantiation_sites(
    program: &Program<'_>,
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
    exact_sites: &HashMap<(u32, u32), ExactModuleSite>,
) -> HashMap<(u32, u32), Vec<WasmInstantiationSite>> {
    let mut collector = InstantiationSiteCollector {
        scoping,
        global_aliases,
        exact_sites,
        sites: HashMap::new(),
    };
    collector.visit_program(program);

    let returned_functions = collect_returned_object_functions(program, scoping);
    let facts = collect_direct_execution_facts(program, scoping, &returned_functions);
    let member_write_counts = collect_import_member_write_counts(program, scoping);
    let factories_by_object = returned_functions
        .values()
        .copied()
        .map(|factory| (factory.object_symbol, factory))
        .collect::<HashMap<_, _>>();

    let mut reachable = HashMap::<(u32, u32), Vec<WasmInstantiationSite>>::new();
    for assignment in &facts.assignments {
        if member_write_counts
            .get(&(
                assignment.symbol,
                assignment.module.clone(),
                assignment.name.clone(),
            ))
            .copied()
            != Some(1)
        {
            continue;
        }
        let output = reachable.entry(assignment.span).or_default();

        if let Some(sites) = collector.sites.get(&assignment.symbol) {
            output.extend(
                sites
                    .iter()
                    .filter(|site| {
                        site_is_later_in_region(&facts.site_positions, site, assignment.position)
                    })
                    .cloned(),
            );
        }

        if let Some(factory) = factories_by_object.get(&assignment.symbol) {
            let assignment_runs_before_return = assignment.position.region == factory.region
                && (assignment.position.index < factory.return_index
                    || (assignment.position.index == factory.return_index
                        && assignment.return_prefix));
            if assignment_runs_before_return {
                for alias in facts
                    .aliases
                    .iter()
                    .filter(|alias| alias.object_symbol == assignment.symbol)
                {
                    let Some(sites) = collector.sites.get(&alias.result_symbol) else {
                        continue;
                    };
                    output.extend(sites.iter().filter_map(|site| {
                        if !site_is_later_in_region(&facts.site_positions, site, alias.position) {
                            return None;
                        }
                        let mut site = site.clone();
                        site.import_object_identity_kind = "returned_object_call";
                        Some(site)
                    }));
                }
            }
        }

        output.sort_by(|left, right| {
            left.start
                .cmp(&right.start)
                .then_with(|| left.end.cmp(&right.end))
                .then_with(|| left.kind.cmp(right.kind))
        });
        output.dedup();
    }
    reachable.retain(|_, sites| !sites.is_empty());
    reachable
}
