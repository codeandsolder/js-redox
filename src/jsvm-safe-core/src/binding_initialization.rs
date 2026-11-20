//! Source regions dominated by binding initialization, used before deleting
//! writes to otherwise unused locals. A lexical binding can be resolved and
//! write-only yet still throw on PutValue in its temporal dead zone.
use oxc_ast::ast::{
    ArrowFunctionExpression, BindingPattern, CatchClause, ForInStatement, ForOfStatement,
    ForStatement, ForStatementInit, ForStatementLeft, FormalParameters, Function, Statement,
    VariableDeclaration, VariableDeclarationKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_span::{GetSpan, Span};
use oxc_syntax::{
    scope::{ScopeFlags, ScopeId},
    symbol::SymbolId,
};
use std::collections::{HashMap, HashSet};

#[derive(Default)]
pub(crate) struct BindingInitialization {
    hoisted_vars: HashSet<SymbolId>,
    parameters: HashSet<SymbolId>,
    regions: HashMap<SymbolId, Vec<Span>>,
}

impl BindingInitialization {
    fn record_pattern(&mut self, pattern: &BindingPattern<'_>, region: Span) {
        for ident in pattern.get_binding_identifiers() {
            if let Some(symbol) = ident.symbol_id.get() {
                self.regions.entry(symbol).or_default().push(region);
            }
        }
    }

    fn record_lexical_declarations(&mut self, declaration: &VariableDeclaration<'_>, end: u32) {
        if declaration.kind != VariableDeclarationKind::Let {
            return;
        }
        for declarator in &declaration.declarations {
            self.record_pattern(&declarator.id, Span::new(declarator.span.end, end));
        }
    }

    fn record_iteration_binding(&mut self, left: &ForStatementLeft<'_>, body: Span) {
        if let ForStatementLeft::VariableDeclaration(declaration) = left {
            if declaration.kind == VariableDeclarationKind::Let {
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

    pub(crate) fn analyze(program: &oxc_ast::ast::Program<'_>) -> Self {
        let mut facts = Self::default();
        facts.visit_program(program);
        facts
    }

    pub(crate) fn proves_initialized(
        &self,
        scoping: &Scoping,
        symbol: SymbolId,
        scope: ScopeId,
        at: Span,
    ) -> bool {
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

impl<'a> Visit<'a> for BindingInitialization {
    fn visit_statements(&mut self, statements: &oxc_allocator::Vec<'a, Statement<'a>>) {
        let Some(last) = statements.last() else {
            return;
        };
        let end = last.span().end;
        for statement in statements {
            // This is one actual statement list. A switch case's lexical
            // declaration does not dominate a separately selectable case.
            if let Statement::VariableDeclaration(declaration) = statement {
                self.record_lexical_declarations(declaration, end);
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
        self.record_parameters(&node.params, node.span.end);
        walk::walk_function(self, node, flags);
    }

    fn visit_arrow_function_expression(&mut self, node: &ArrowFunctionExpression<'a>) {
        self.record_parameters(&node.params, node.span.end);
        walk::walk_arrow_function_expression(self, node);
    }

    fn visit_for_statement(&mut self, node: &ForStatement<'a>) {
        if let Some(ForStatementInit::VariableDeclaration(declaration)) = &node.init {
            self.record_lexical_declarations(declaration, node.span.end);
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
