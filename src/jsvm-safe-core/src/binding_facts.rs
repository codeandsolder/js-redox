//! Binding initialization and lexical exposure facts shared by rewrites.
//! Lexical containment alone does not establish execution order:
//! hoisted function declarations may be invoked before their textual site.
use oxc_ast::ast::{
    ArrowFunctionExpression, BindingPattern, CallExpression, CatchClause, Declaration, Expression,
    ForInStatement, ForOfStatement, ForStatement, ForStatementInit, ForStatementLeft,
    FormalParameters, Function, FunctionType, Statement, VariableDeclaration,
    VariableDeclarationKind,
};
use oxc_ast::AstKind;
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{ReferenceId, Scoping};
use oxc_span::{GetSpan, Span};
use oxc_syntax::{
    scope::{ScopeFlags, ScopeId},
    symbol::SymbolId,
};
use std::cell::Cell;
use std::collections::{HashMap, HashSet};

/// The result of a lexical identity proof, not a claim about the value
/// currently stored in a binding or about the integrity of host builtins.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReferenceIdentity {
    Lexical(SymbolId),
    Global,
    Dynamic,
}

#[derive(Debug, Clone, Copy)]
struct EvalSite {
    scope: ScopeId,
    span: Span,
}

/// Binding initialization, dynamic name resolution and eval exposure for
/// one immutable AST/semantic snapshot.
#[derive(Debug)]
pub struct BindingFacts {
    hoisted_vars: HashSet<SymbolId>,
    parameters: HashSet<SymbolId>,
    regions: HashMap<SymbolId, Vec<Span>>,
    node_spans: Vec<Span>,
    scope_entries: HashMap<ScopeId, u32>,
    hoisted_functions: HashSet<ScopeId>,
    hoisted_function_bindings: HashMap<ScopeId, SymbolId>,
    direct_calls: HashMap<ReferenceId, Span>,
    scopes: Vec<Option<ScopeId>>,
    eval_sites: Vec<EvalSite>,
    parameter_regions: HashMap<ScopeId, Span>,
    named_function_expressions: HashSet<SymbolId>,
    sloppy_eval_var_scopes: HashSet<ScopeId>,
    exported_bindings: HashSet<SymbolId>,
    ambient_root: bool,
}

impl BindingFacts {
    fn record_pattern(&mut self, pattern: &BindingPattern<'_>, region: Span) {
        for ident in pattern.get_binding_identifiers() {
            if let Some(symbol) = ident.symbol_id.get() {
                self.regions.entry(symbol).or_default().push(region);
            }
        }
    }

    fn record_declaration_regions(&mut self, declaration: &VariableDeclaration<'_>, end: u32) {
        if !matches!(
            declaration.kind,
            VariableDeclarationKind::Let
                | VariableDeclarationKind::Const
                | VariableDeclarationKind::Var
        ) {
            return;
        }
        for declarator in &declaration.declarations {
            if declaration.kind != VariableDeclarationKind::Var || declarator.init.is_some() {
                self.record_pattern(&declarator.id, Span::new(declarator.span.end, end));
            }
        }
    }

    fn record_iteration_binding(&mut self, left: &ForStatementLeft<'_>, body: Span) {
        if let ForStatementLeft::VariableDeclaration(declaration) = left {
            if matches!(
                declaration.kind,
                VariableDeclarationKind::Let | VariableDeclarationKind::Const
            ) {
                for declarator in &declaration.declarations {
                    self.record_pattern(&declarator.id, body);
                }
            }
        }
    }

    fn record_formal(&mut self, pattern: &BindingPattern<'_>, start: u32, end: u32) {
        self.parameters.extend(
            pattern
                .get_binding_identifiers()
                .into_iter()
                .filter_map(|id| id.symbol_id.get()),
        );
        self.record_pattern(pattern, Span::new(start, end));
    }

    fn record_parameters(&mut self, params: &FormalParameters<'_>, end: u32) {
        for parameter in &params.items {
            self.record_formal(&parameter.pattern, parameter.span.end, end);
        }
        if let Some(rest) = &params.rest {
            self.record_formal(&rest.rest.argument, rest.span.end, end);
        }
    }

    #[must_use]
    pub fn analyze(program: &oxc_ast::ast::Program<'_>, scoping: &Scoping) -> Self {
        let mut facts = Self {
            hoisted_vars: HashSet::new(),
            parameters: HashSet::new(),
            regions: HashMap::new(),
            node_spans: Vec::new(),
            scope_entries: HashMap::new(),
            hoisted_functions: HashSet::new(),
            hoisted_function_bindings: HashMap::new(),
            direct_calls: HashMap::new(),
            scopes: Vec::new(),
            eval_sites: Vec::new(),
            parameter_regions: HashMap::new(),
            named_function_expressions: HashSet::new(),
            sloppy_eval_var_scopes: HashSet::new(),
            exported_bindings: HashSet::new(),
            ambient_root: !program.source_type.is_module(),
        };
        facts.visit_program(program);
        // Non-strict direct eval may create var bindings in its caller's
        // variable environment. These bindings can shadow outer variables
        // even when the static symbol itself is immutable. Do not confuse
        // this with the ordinary DirectEval flag propagated to ancestors:
        // a sibling function's eval cannot introduce bindings here.
        facts.sloppy_eval_var_scopes = facts
            .eval_sites
            .iter()
            .filter(|site| !scoping.scope_flags(site.scope).is_strict_mode())
            .filter_map(|site| {
                scoping
                    .scope_ancestors(site.scope)
                    .find(|&ancestor| scoping.scope_flags(ancestor).is_var())
            })
            .collect();
        facts
    }

    fn resolve_scope(
        &self,
        scoping: &Scoping,
        scope: ScopeId,
        symbol: Option<SymbolId>,
    ) -> ReferenceIdentity {
        let owner = symbol.map(|symbol| scoping.symbol_scope_id(symbol));
        for ancestor in scoping.scope_ancestors(scope) {
            if Some(ancestor) == owner {
                return symbol.map_or(ReferenceIdentity::Dynamic, ReferenceIdentity::Lexical);
            }
            if self.sloppy_eval_var_scopes.contains(&ancestor)
                || scoping.scope_flags(ancestor).is_with()
            {
                return ReferenceIdentity::Dynamic;
            }
        }
        if symbol.is_none() {
            ReferenceIdentity::Global
        } else {
            ReferenceIdentity::Dynamic
        }
    }

    /// Resolve the identity at this exact reference. A missing static symbol
    /// is not sufficient evidence of a global lookup.
    #[must_use]
    pub fn resolve_reference(
        &self,
        scoping: &Scoping,
        reference_id: ReferenceId,
    ) -> ReferenceIdentity {
        let reference = scoping.get_reference(reference_id);
        self.resolve_scope(scoping, reference.scope_id(), reference.symbol_id())
    }

    #[must_use]
    pub fn resolved_symbol(
        &self,
        scoping: &Scoping,
        reference_id: ReferenceId,
    ) -> Option<SymbolId> {
        match self.resolve_reference(scoping, reference_id) {
            ReferenceIdentity::Lexical(symbol) => Some(symbol),
            ReferenceIdentity::Global | ReferenceIdentity::Dynamic => None,
        }
    }

    #[must_use]
    pub fn proves_global_reference(&self, scoping: &Scoping, reference_id: ReferenceId) -> bool {
        self.resolve_reference(scoping, reference_id) == ReferenceIdentity::Global
    }

    /// A static binding identity is stable only if lookup cannot encounter
    /// a dynamically introduced binding before reaching its owner.
    pub(crate) fn proves_reference_identity(
        &self,
        scoping: &Scoping,
        symbol: SymbolId,
        scope: ScopeId,
    ) -> bool {
        self.resolve_scope(scoping, scope, Some(symbol)) == ReferenceIdentity::Lexical(symbol)
    }

    /// Prove that resolving this identifier to an assignment Reference
    /// commutes with arbitrary RHS evaluation. A declarative binding's
    /// environment record does not become a different record just because
    /// its value changes. Sloppy direct eval can introduce a nearer binding
    /// and object-backed global environments can perform observable lookup,
    /// however. Those references must be evaluated in their original order.
    ///
    /// This is a reference-identity proof, not an initialized-value proof:
    /// simple assignment to an uninitialized or immutable declarative
    /// binding still evaluates the RHS before PutValue throws.
    pub(crate) fn fixed_assignment_reference(
        &self,
        scoping: &Scoping,
        reference_id: oxc_semantic::ReferenceId,
    ) -> Option<SymbolId> {
        let reference = scoping.get_reference(reference_id);
        let symbol = reference.symbol_id()?;
        if !reference.is_write()
            || !self.proves_reference_identity(scoping, symbol, reference.scope_id())
        {
            return None;
        }
        if self.ambient_root
            && scoping.symbol_scope_id(symbol) == scoping.root_scope_id()
            && !scoping.symbol_flags(symbol).intersects(
                oxc_semantic::SymbolFlags::BlockScoped | oxc_semantic::SymbolFlags::Import,
            )
        {
            return None;
        }
        Some(symbol)
    }

    /// Immutable bindings can be read by a later-created closure: once
    /// initialized, their value cannot be changed. A hoisted declaration is
    /// different; the enclosing lexical scope's entry (not the declaration's
    /// text) is its earliest creation site.
    pub fn proves_value_initialized(
        &self,
        scoping: &Scoping,
        symbol: SymbolId,
        scope: ScopeId,
        at: Span,
    ) -> bool {
        if !self.proves_reference_identity(scoping, symbol, scope) {
            return false;
        }
        let owner = scoping.symbol_scope_id(symbol);
        self.regions.get(&symbol).is_some_and(|regions| {
            regions.iter().any(|region| {
                if region.start > at.start || at.end > region.end {
                    return false;
                }
                for ancestor in scoping.scope_ancestors(scope) {
                    if ancestor == owner {
                        return true;
                    }
                    if self.hoisted_functions.contains(&ancestor) {
                        let Some(entry) = scoping
                            .scope_parent_id(ancestor)
                            .and_then(|parent| self.scope_entries.get(&parent))
                        else {
                            return false;
                        };
                        if *entry < region.start || *entry > region.end {
                            return false;
                        }
                    }
                }
                false
            })
        })
    }

    /// Discharge initialization at a specific use through a closed set of
    /// direct calls to private hoisted functions. All incoming calls must
    /// establish the same captured environment, not just one convenient
    /// call site. A reference used as a value, an exported function, or an
    /// ungrounded recursive cycle cannot provide this evidence.
    pub(crate) fn proves_initialized_through_calls(
        &self,
        scoping: &Scoping,
        symbol: SymbolId,
        scope: ScopeId,
        at: Span,
        budget: &work_budget::WorkBudget,
    ) -> Result<bool, work_budget::BudgetExceeded> {
        if self.proves_value_initialized(scoping, symbol, scope, at) {
            return Ok(true);
        }
        let owner = scoping.symbol_scope_id(symbol);
        let mut pending = vec![(scope, at)];
        let mut visited = HashSet::new();
        let mut grounded = false;
        while let Some((scope, at)) = pending.pop() {
            budget.checkpoint()?;
            if self.proves_value_initialized(scoping, symbol, scope, at) {
                grounded = true;
                continue;
            }
            let Some(function_scope) = scoping
                .scope_ancestors(scope)
                .take_while(|&ancestor| ancestor != owner)
                .find(|&ancestor| scoping.scope_flags(ancestor).is_function())
            else {
                return Ok(false);
            };
            if !visited.insert(function_scope) {
                continue;
            }
            let Some(&function) = self.hoisted_function_bindings.get(&function_scope) else {
                return Ok(false);
            };
            if !self.is_private(scoping, function)
                || !self.binding_has_stable_value(scoping, function)
                || !scoping
                    .scope_ancestors(scoping.symbol_scope_id(function))
                    .any(|ancestor| ancestor == owner)
            {
                return Ok(false);
            }
            let references = scoping.get_resolved_reference_ids(function);
            if references.is_empty() {
                return Ok(false);
            }
            budget.consume(u64::try_from(references.len()).unwrap_or(u64::MAX))?;
            for &reference in references {
                let Some(&span) = self.direct_calls.get(&reference) else {
                    return Ok(false);
                };
                if self.resolved_symbol(scoping, reference) != Some(function) {
                    return Ok(false);
                }
                pending.push((scoping.get_reference(reference).scope_id(), span));
            }
        }
        Ok(grounded)
    }

    /// Source-local table proofs do not extend to object-backed script
    /// globals or exported mutable allocations accessed by external code.
    pub(crate) fn source_local_data_binding(&self, scoping: &Scoping, symbol: SymbolId) -> bool {
        !self.exported_bindings.contains(&symbol)
            && !(self.ambient_root
                && scoping.symbol_scope_id(symbol) == scoping.root_scope_id()
                && !scoping.symbol_flags(symbol).is_block_scoped())
            && !self.is_eval_exposed(scoping, symbol)
            && self.binding_has_stable_value(scoping, symbol)
    }

    /// Can this binding's value or properties be exposed to unmodeled code
    /// without an ordinary reference? A classic script's global environment
    /// and directly exported module allocations are not private. A potential
    /// direct eval can access only bindings visible at its lexical call site.
    pub(crate) fn is_private(&self, scoping: &Scoping, symbol: SymbolId) -> bool {
        if (self.ambient_root && scoping.symbol_scope_id(symbol) == scoping.root_scope_id())
            || self.exported_bindings.contains(&symbol)
        {
            return false;
        }
        !self.is_eval_exposed(scoping, symbol)
    }

    /// Even strict direct eval can change an existing mutable binding.
    ///
    /// Oxc combines formal and body bindings in one scope table. A default
    /// parameter initializer executes in the parameter environment, before
    /// the separate body variable environment exists. Respect that boundary
    /// also for a closure created in a parameter initializer.
    #[must_use]
    pub fn is_eval_exposed(&self, scoping: &Scoping, symbol: SymbolId) -> bool {
        let name = scoping.symbol_name(symbol);
        self.eval_sites.iter().any(|site| {
            scoping.scope_ancestors(site.scope).find_map(|scope| {
                let candidate = scoping.get_binding(scope, name.into())?;
                let in_parameters = self.parameter_regions.get(&scope).is_some_and(|region| {
                    region.start <= site.span.start && site.span.end <= region.end
                });
                (!in_parameters
                    || self.parameters.contains(&candidate)
                    || self.named_function_expressions.contains(&candidate))
                .then_some(candidate)
            }) == Some(symbol)
        })
    }

    /// Binding value cannot be reassigned by potential direct eval.
    /// This does not prove the absence of ordinary writes or mutation of
    /// objects stored in the binding.
    #[must_use]
    pub fn binding_unmodified_by_eval(&self, scoping: &Scoping, symbol: SymbolId) -> bool {
        scoping.symbol_flags(symbol).is_const_variable() || !self.is_eval_exposed(scoping, symbol)
    }

    /// A single declaration and no known binding reassignment, including
    /// direct eval. Still requires an initialization proof at each use.
    #[must_use]
    pub fn binding_has_stable_value(&self, scoping: &Scoping, symbol: SymbolId) -> bool {
        scoping.symbol_redeclarations(symbol).is_empty()
            && self.binding_unmodified_by_eval(scoping, symbol)
            && scoping
                .get_resolved_reference_ids(symbol)
                .iter()
                .all(|&reference| !scoping.get_reference(reference).is_write())
    }

    pub(crate) fn stable_callable_symbol(
        &self,
        scoping: &Scoping,
        expression: &Expression<'_>,
    ) -> Option<SymbolId> {
        let Expression::Identifier(identifier) = expression else {
            return None;
        };
        let symbol = self.resolved_symbol(scoping, identifier.reference_id.get()?)?;
        self.binding_unmodified_by_eval(scoping, symbol)
            .then_some(symbol)
    }

    #[must_use]
    pub fn initialized_read(
        &self,
        scoping: &Scoping,
        expression: &Expression<'_>,
    ) -> Option<SymbolId> {
        let Expression::Identifier(identifier) = expression else {
            return None;
        };
        self.initialized_reference(scoping, identifier.reference_id.get()?, identifier.span)
    }

    /// The same initialized-read proof for callers already visiting an
    /// IdentifierReference rather than its containing Expression.
    #[must_use]
    pub fn initialized_reference(
        &self,
        scoping: &Scoping,
        reference: ReferenceId,
        span: Span,
    ) -> Option<SymbolId> {
        let symbol = self.resolved_symbol(scoping, reference)?;
        let reference = scoping.get_reference(reference);
        if !reference.is_read()
            || reference.is_write()
            || reference.flags().is_member_write_target()
        {
            return None;
        }
        self.proves_value_initialized(scoping, symbol, reference.scope_id(), span)
            .then_some(symbol)
    }

    pub(crate) fn proves_initialized(
        &self,
        scoping: &Scoping,
        symbol: SymbolId,
        scope: ScopeId,
        at: Span,
    ) -> bool {
        if !self.proves_reference_identity(scoping, symbol, scope) {
            return false;
        }
        if self.hoisted_vars.contains(&symbol) && !self.parameters.contains(&symbol) {
            return true;
        }
        // A closure might execute before the dominating source region is
        // entered. Never confuse lexical containment with execution order.
        if !crate::Collector::same_function_or_descendant_block_scope(
            scoping,
            scope,
            scoping.symbol_scope_id(symbol),
        ) {
            return false;
        }
        self.regions.get(&symbol).is_some_and(|regions| {
            regions
                .iter()
                .any(|region| region.start <= at.start && at.end <= region.end)
        })
    }
}

impl<'a> Visit<'a> for BindingFacts {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        self.node_spans.push(kind.span());
    }

    fn leave_node(&mut self, _: AstKind<'a>) {
        self.node_spans.pop();
    }

    fn enter_scope(&mut self, _: ScopeFlags, scope: &Cell<Option<ScopeId>>) {
        self.scopes.push(scope.get());
        if let (Some(scope), Some(span)) = (scope.get(), self.node_spans.last()) {
            self.scope_entries.insert(scope, span.start);
        }
    }

    fn leave_scope(&mut self) {
        self.scopes.pop();
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            if let Expression::Identifier(callee) = call.callee.without_parentheses() {
                if let Some(reference) = callee.reference_id.get() {
                    self.direct_calls.insert(reference, call.span);
                }
            }
        }
        if crate::is_potential_direct_eval(call) {
            if let Some(Some(scope)) = self.scopes.last() {
                self.eval_sites.push(EvalSite {
                    scope: *scope,
                    span: call.span,
                });
            }
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_statements(&mut self, statements: &oxc_allocator::Vec<'a, Statement<'a>>) {
        let Some(last) = statements.last() else {
            return;
        };
        let end = last.span().end;
        for statement in statements {
            // This is one actual statement list. A switch case's lexical
            // declaration does not dominate a separately selectable case.
            let declaration = match statement {
                Statement::VariableDeclaration(declaration) => Some(declaration.as_ref()),
                Statement::ExportDeclaration(export) => match &export.declaration {
                    Declaration::VariableDeclaration(declaration) => {
                        for declarator in &declaration.declarations {
                            self.exported_bindings.extend(
                                declarator
                                    .id
                                    .get_binding_identifiers()
                                    .into_iter()
                                    .filter_map(|id| id.symbol_id.get()),
                            );
                        }
                        Some(declaration.as_ref())
                    }
                    _ => None,
                },
                _ => None,
            };
            if let Some(declaration) = declaration {
                self.record_declaration_regions(declaration, end);
            }
            self.visit_statement(statement);
        }
    }

    fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
        if declaration.kind == VariableDeclarationKind::Var {
            for declarator in &declaration.declarations {
                self.hoisted_vars.extend(
                    declarator
                        .id
                        .get_binding_identifiers()
                        .into_iter()
                        .filter_map(|id| id.symbol_id.get()),
                );
            }
        }
        walk::walk_variable_declaration(self, declaration);
    }

    fn visit_function(&mut self, node: &Function<'a>, flags: ScopeFlags) {
        if node.r#type == FunctionType::FunctionDeclaration {
            if let Some(scope) = node.scope_id.get() {
                self.hoisted_functions.insert(scope);
                if let Some(symbol) = node.id.as_ref().and_then(|id| id.symbol_id.get()) {
                    self.hoisted_function_bindings.insert(scope, symbol);
                }
            }
        }
        if let Some(scope) = node.scope_id.get() {
            self.parameter_regions.insert(scope, node.params.span);
        }
        if node.r#type == FunctionType::FunctionExpression {
            if let Some(symbol) = node.id.as_ref().and_then(|id| id.symbol_id.get()) {
                self.named_function_expressions.insert(symbol);
            }
        }
        self.record_parameters(&node.params, node.span.end);
        walk::walk_function(self, node, flags);
    }

    fn visit_arrow_function_expression(&mut self, node: &ArrowFunctionExpression<'a>) {
        if let Some(scope) = node.scope_id.get() {
            self.parameter_regions.insert(scope, node.params.span);
        }
        self.record_parameters(&node.params, node.span.end);
        walk::walk_arrow_function_expression(self, node);
    }

    fn visit_for_statement(&mut self, node: &ForStatement<'a>) {
        if let Some(ForStatementInit::VariableDeclaration(declaration)) = &node.init {
            self.record_declaration_regions(declaration, node.span.end);
        }
        walk::walk_for_statement(self, node);
    }

    fn visit_for_in_statement(&mut self, node: &ForInStatement<'a>) {
        self.record_iteration_binding(&node.left, node.body.span());
        walk::walk_for_in_statement(self, node);
    }

    fn visit_for_of_statement(&mut self, node: &ForOfStatement<'a>) {
        self.record_iteration_binding(&node.left, node.body.span());
        walk::walk_for_of_statement(self, node);
    }

    fn visit_catch_clause(&mut self, node: &CatchClause<'a>) {
        if let Some(parameter) = &node.param {
            self.record_pattern(&parameter.pattern, node.body.span);
        }
        walk::walk_catch_clause(self, node);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use oxc_allocator::Allocator;
    use oxc_semantic::SemanticBuilder;
    use oxc_span::SourceType;

    #[test]
    fn identity_distinguishes_intercepted_global_and_lexical_references() {
        use oxc_ast::ast::IdentifierReference;
        struct Probe<'a> {
            scoping: &'a Scoping,
            facts: &'a BindingFacts,
            identities: Vec<ReferenceIdentity>,
        }
        impl<'a> Visit<'a> for Probe<'_> {
            fn visit_identifier_reference(&mut self, identifier: &IdentifierReference<'a>) {
                if matches!(identifier.name.as_str(), "missing" | "outer") {
                    let reference = identifier
                        .reference_id
                        .get()
                        .unwrap_or_else(|| unreachable!());
                    self.identities
                        .push(self.facts.resolve_reference(self.scoping, reference));
                }
            }
        }
        let source = r#"
            let outer = 1;
            function exposed() {
                (eval)("var missing = 3, outer = 2");
                missing;
                outer;
                { const outer = 4; outer; }
                (() => { "use strict"; missing; outer; })();
            }
            function sibling() { missing; outer; }
            function strict() { "use strict"; eval("var missing = 4"); missing; outer; }
            function dynamic(scope) { with(scope) { missing; outer; } }
        "#;
        let allocator = Allocator::default();
        let program = crate::parse_as(&allocator, source, SourceType::cjs())
            .unwrap_or_else(|| unreachable!("valid proof fixture"));
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&program);
        assert!(semantic.diagnostics.is_empty());
        let scoping = semantic.semantic.scoping();
        let facts = BindingFacts::analyze(&program, scoping);
        let mut probe = Probe {
            scoping,
            facts: &facts,
            identities: Vec::new(),
        };
        probe.visit_program(&program);
        let outer = scoping
            .get_binding(scoping.root_scope_id(), "outer".into())
            .unwrap_or_else(|| unreachable!());
        let ReferenceIdentity::Lexical(block_local) = probe.identities[2] else {
            unreachable!("block local must retain identity");
        };
        assert_ne!(block_local, outer);
        use ReferenceIdentity::{Dynamic, Global, Lexical};
        assert_eq!(
            probe.identities,
            [
                Dynamic,
                Dynamic,
                Lexical(block_local),
                Dynamic,
                Dynamic,
                Global,
                Lexical(outer),
                Global,
                Lexical(outer),
                Dynamic,
                Dynamic,
            ]
        );
    }

    #[test]
    fn parameter_eval_visibility_is_not_body_scope_visibility() {
        for (source, outer_exposed, inner_exposed) in [
            ("let x=1;function f(a=eval('x=2')){let x=3;}", true, false),
            (
                "let x=1;function f(a=()=>eval('x=2')){let x=3;return a();}",
                true,
                false,
            ),
            ("let x=1;function f(a=eval('x=2')){var x=3;}", true, false),
            ("let x=1;function f(x=1,a=eval('x=2')){}", false, true),
            ("let x=1;function f(){let x=3;eval('x=2');}", false, true),
            ("let x=1;function f(a=1){let x=3;eval('x=2');}", false, true),
            ("let x=1;const f=function x(a=eval('x=2')){};", false, true),
        ] {
            let allocator = Allocator::default();
            let program = crate::parse_as(&allocator, source, SourceType::cjs())
                .unwrap_or_else(|| unreachable!("{source}"));
            let semantic = SemanticBuilder::new()
                .with_check_syntax_error(true)
                .build(&program);
            assert!(semantic.diagnostics.is_empty(), "{source}");
            let scoping = semantic.semantic.scoping();
            let facts = BindingFacts::analyze(&program, scoping);
            let mut symbols = scoping
                .symbol_ids()
                .filter(|&symbol| scoping.symbol_name(symbol) == "x")
                .collect::<Vec<_>>();
            symbols.sort_by_key(|&symbol| scoping.symbol_span(symbol).start);
            let [outer, inner] = symbols.as_slice() else {
                unreachable!("{source}");
            };
            assert_eq!(
                facts.is_eval_exposed(scoping, *outer),
                outer_exposed,
                "{source}"
            );
            assert_eq!(
                facts.is_eval_exposed(scoping, *inner),
                inner_exposed,
                "{source}"
            );
        }
    }
}
