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
use oxc_semantic::Scoping;
use oxc_span::{GetSpan, Span};
use oxc_syntax::{
    scope::{ScopeFlags, ScopeId},
    symbol::SymbolId,
};
use std::cell::Cell;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Default)]
pub(crate) struct BindingFacts {
    hoisted_vars: HashSet<SymbolId>,
    parameters: HashSet<SymbolId>,
    regions: HashMap<SymbolId, Vec<Span>>,
    node_spans: Vec<Span>,
    scope_entries: HashMap<ScopeId, u32>,
    hoisted_functions: HashSet<ScopeId>,
    scopes: Vec<Option<ScopeId>>,
    dynamic_scopes: HashSet<ScopeId>,
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

    pub(crate) fn analyze(program: &oxc_ast::ast::Program<'_>, scoping: &Scoping) -> Self {
        let mut facts = Self {
            ambient_root: !program.source_type.is_module(),
            ..Self::default()
        };
        facts.visit_program(program);
        // Non-strict direct eval may create var bindings in its caller's
        // variable environment. These bindings can shadow outer variables
        // even when the static symbol itself is immutable. Do not confuse
        // this with the ordinary DirectEval flag propagated to ancestors:
        // a sibling function's eval cannot introduce bindings here.
        facts.sloppy_eval_var_scopes = facts
            .dynamic_scopes
            .iter()
            .filter(|&&scope| !scoping.scope_flags(scope).is_strict_mode())
            .filter_map(|&scope| {
                scoping
                    .scope_ancestors(scope)
                    .find(|&ancestor| scoping.scope_flags(ancestor).is_var())
            })
            .collect();
        facts
    }

    /// A static binding identity is stable only if lookup cannot encounter
    /// a dynamically introduced binding before reaching its owner.
    pub(crate) fn proves_reference_identity(
        &self,
        scoping: &Scoping,
        symbol: SymbolId,
        scope: ScopeId,
    ) -> bool {
        let owner = scoping.symbol_scope_id(symbol);
        for ancestor in scoping.scope_ancestors(scope) {
            if ancestor == owner {
                return true;
            }
            if self.sloppy_eval_var_scopes.contains(&ancestor)
                || scoping.scope_flags(ancestor).is_with()
            {
                return false;
            }
        }
        false
    }

    /// Immutable bindings can be read by a later-created closure: once
    /// initialized, their value cannot be changed. A hoisted declaration is
    /// different; the enclosing lexical scope's entry (not the declaration's
    /// text) is its earliest creation site.
    pub(crate) fn proves_value_initialized(
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
    pub(crate) fn is_eval_exposed(&self, scoping: &Scoping, symbol: SymbolId) -> bool {
        let name = scoping.symbol_name(symbol);
        self.dynamic_scopes
            .iter()
            .any(|&scope| scoping.find_binding(scope, name.into()) == Some(symbol))
    }

    pub(crate) fn stable_callable_symbol(
        &self,
        scoping: &Scoping,
        expression: &Expression<'_>,
    ) -> Option<SymbolId> {
        let Expression::Identifier(identifier) = expression else {
            return None;
        };
        let reference_id = identifier.reference_id.get()?;
        let symbol = crate::statically_resolved_symbol(scoping, reference_id)?;
        let scope = scoping.get_reference(reference_id).scope_id();
        (self.proves_reference_identity(scoping, symbol, scope)
            && (scoping.symbol_flags(symbol).is_const_variable()
                || !self.is_eval_exposed(scoping, symbol)))
        .then_some(symbol)
    }

    pub(crate) fn initialized_read(
        &self,
        scoping: &Scoping,
        expression: &Expression<'_>,
    ) -> Option<SymbolId> {
        let Expression::Identifier(identifier) = expression else {
            return None;
        };
        let reference = identifier.reference_id.get()?;
        let symbol = crate::statically_resolved_symbol(scoping, reference)?;
        if !crate::reference_is_statically_resolved_read(scoping, reference, symbol) {
            return None;
        }
        let scope = scoping.get_reference(reference).scope_id();
        self.proves_value_initialized(scoping, symbol, scope, identifier.span)
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
        if crate::is_potential_direct_eval(call) {
            if let Some(Some(scope)) = self.scopes.last() {
                self.dynamic_scopes.insert(*scope);
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
            }
        }
        self.record_parameters(&node.params, node.span.end);
        walk::walk_function(self, node, flags);
    }

    fn visit_arrow_function_expression(&mut self, node: &ArrowFunctionExpression<'a>) {
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
