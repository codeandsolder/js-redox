//! Binding initialization and lexical exposure facts shared by rewrites.
//! Lexical containment alone does not establish execution order:
//! hoisted function declarations may be invoked before their textual site.
use oxc_ast::ast::{
    ArrowFunctionExpression, BindingPattern, CallExpression, CatchClause, Declaration,
    ExportDeclaration, ExportDefaultDeclaration, ExportDefaultDeclarationKind,
    ExportNamedDeclaration, Expression, ForInStatement, ForOfStatement, ForStatement,
    ForStatementInit, ForStatementLeft, FormalParameters, Function, FunctionType, ModuleExportName,
    Statement, VariableDeclaration, VariableDeclarationKind, VariableDeclarator,
};
use oxc_ast::AstKind;
use oxc_ast_visit::{walk, Visit};
use oxc_ecmascript::IsSimpleParameterList;
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
    var_initializer_scopes: HashMap<Span, ScopeId>,
    resource_scopes: HashSet<ScopeId>,
    parameters: HashSet<SymbolId>,
    simple_parameter_functions: HashSet<ScopeId>,
    arguments_references: Vec<ReferenceId>,
    mapped_arguments_exposed: HashSet<ScopeId>,
    regions: HashMap<SymbolId, Vec<Span>>,
    node_spans: Vec<Span>,
    scope_entries: HashMap<ScopeId, u32>,
    hoisted_functions: HashSet<ScopeId>,
    hoisted_function_bindings: HashMap<ScopeId, SymbolId>,
    statement_list_functions: HashMap<SymbolId, ScopeId>,
    statement_list_declarations: HashSet<ScopeId>,
    direct_calls: HashMap<ReferenceId, Span>,
    scopes: Vec<Option<ScopeId>>,
    eval_sites: Vec<EvalSite>,
    parameter_regions: HashMap<ScopeId, Span>,
    named_function_expressions: HashSet<SymbolId>,
    sloppy_eval_var_scopes: HashSet<ScopeId>,
    exported_bindings: HashSet<SymbolId>,
    exported_references: Vec<ReferenceId>,
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

    #[must_use = "Use the returned binding facts to justify lexical proofs"]
    pub fn analyze(program: &oxc_ast::ast::Program<'_>, scoping: &Scoping) -> Self {
        let mut facts = Self {
            hoisted_vars: HashSet::new(),
            var_initializer_scopes: HashMap::new(),
            resource_scopes: HashSet::new(),
            parameters: HashSet::new(),
            simple_parameter_functions: HashSet::new(),
            arguments_references: Vec::new(),
            mapped_arguments_exposed: HashSet::new(),
            regions: HashMap::new(),
            node_spans: Vec::new(),
            scope_entries: HashMap::new(),
            hoisted_functions: HashSet::new(),
            hoisted_function_bindings: HashMap::new(),
            statement_list_functions: HashMap::new(),
            statement_list_declarations: HashSet::new(),
            direct_calls: HashMap::new(),
            scopes: Vec::new(),
            eval_sites: Vec::new(),
            parameter_regions: HashMap::new(),
            named_function_expressions: HashSet::new(),
            sloppy_eval_var_scopes: HashSet::new(),
            exported_bindings: HashSet::new(),
            exported_references: Vec::new(),
            ambient_root: !program.source_type.is_module(),
        };
        facts.visit_program(program);
        // A var in a simple catch with the same name writes the catch
        // parameter, but its hoisted binding still belongs to the var scope.
        facts
            .hoisted_vars
            .extend(scoping.catch_var_bindings().map(|(_, owner)| owner));
        facts.exported_bindings.extend(
            std::mem::take(&mut facts.exported_references)
                .into_iter()
                .filter_map(|reference| scoping.get_reference(reference).symbol_id()),
        );
        // A sloppy ordinary function with simple parameters can expose its
        // parameter cells through the implicit arguments object. Arrow
        // references share their nearest ordinary function's object.
        let arguments_owner = |scope| {
            scoping.scope_ancestors(scope).find(|&ancestor| {
                let flags = scoping.scope_flags(ancestor);
                flags.is_function() && !flags.is_arrow()
            })
        };
        for reference in std::mem::take(&mut facts.arguments_references) {
            let reference = scoping.get_reference(reference);
            let Some(owner) = arguments_owner(reference.scope_id()) else {
                continue;
            };
            if reference.symbol_id().is_none_or(|symbol| {
                // var arguments shares the implicit binding, unlike a
                // separately scoped lexical name.
                scoping.symbol_scope_id(symbol) == owner
                    && scoping
                        .symbol_flags(symbol)
                        .is_function_scoped_declaration()
            }) {
                facts.mapped_arguments_exposed.insert(owner);
            }
        }
        for site in &facts.eval_sites {
            if let Some(owner) = arguments_owner(site.scope) {
                facts.mapped_arguments_exposed.insert(owner);
            }
        }
        facts.mapped_arguments_exposed.retain(|scope| {
            facts.simple_parameter_functions.contains(scope)
                && !scoping.scope_flags(*scope).is_strict_mode()
        });
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
    #[must_use = "Use the proven reference identity rather than assuming lexical resolution"]
    pub fn resolve_reference(
        &self,
        scoping: &Scoping,
        reference_id: ReferenceId,
    ) -> ReferenceIdentity {
        let reference = scoping.get_reference(reference_id);
        self.resolve_scope(scoping, reference.scope_id(), reference.symbol_id())
    }

    #[must_use = "Use the returned symbol only when its identity is resolved"]
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

    #[must_use = "Only a true result proves that this reference is global"]
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

    /// Declarative bindings have no accessor-backed `ResolveBinding` step.
    /// A script's object-backed global variables are not such bindings.
    pub(crate) fn has_declarative_storage(&self, scoping: &Scoping, symbol: SymbolId) -> bool {
        !self.ambient_root
            || scoping.symbol_scope_id(symbol) != scoping.root_scope_id()
            || scoping.symbol_flags(symbol).intersects(
                oxc_semantic::SymbolFlags::BlockScoped | oxc_semantic::SymbolFlags::Import,
            )
    }

    /// The declarator's binding identifier denotes the declaration, but
    /// a var initializer resolves its assignment target in the executing
    /// lexical environment. In particular with and simple catch parameters
    /// can affect that lookup. Establish the target before evaluating the RHS.
    pub(crate) fn var_initializer_target(
        &self,
        scoping: &Scoping,
        declarator: &VariableDeclarator<'_>,
    ) -> Option<SymbolId> {
        let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
            return None;
        };
        self.var_initializer_binding_target(scoping, declarator, identifier)
    }

    pub(crate) fn var_initializer_binding_target(
        &self,
        scoping: &Scoping,
        declarator: &VariableDeclarator<'_>,
        identifier: &oxc_ast::ast::BindingIdentifier<'_>,
    ) -> Option<SymbolId> {
        let scope = *self.var_initializer_scopes.get(&declarator.span)?;
        let symbol = scoping
            .scope_ancestors(scope)
            .find_map(|ancestor| scoping.get_binding(ancestor, identifier.name))?;
        (identifier.symbol_id.get() == Some(symbol)
            && self.has_declarative_storage(scoping, symbol)
            && self.proves_reference_identity(scoping, symbol, scope))
        .then_some(symbol)
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
    /// binding still evaluates the RHS before `PutValue` throws.
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
        self.has_declarative_storage(scoping, symbol)
            .then_some(symbol)
    }

    /// Immutable bindings can be read by a later-created closure: once
    /// initialized, their value cannot be changed. A hoisted declaration is
    /// different; the enclosing lexical scope's entry (not the declaration's
    /// text) is its earliest creation site.
    #[must_use = "Only a true result proves that the binding value is initialized"]
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
            regions
                .iter()
                .any(|&region| self.execution_region_contains(scoping, owner, region, scope, at))
        })
    }

    /// An execution region is entered only after an earlier operation has
    /// completed normally. Nested ordinary expressions inherit that ordering;
    /// hoisted closures, however, may be invoked before their textual position.
    pub(crate) fn execution_region_contains(
        &self,
        scoping: &Scoping,
        owner: ScopeId,
        region: Span,
        scope: ScopeId,
        at: Span,
    ) -> bool {
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
        self.proves_through_closed_calls(
            scoping,
            scoping.symbol_scope_id(symbol),
            scope,
            at,
            budget,
            |scope, at| self.proves_value_initialized(scoping, symbol, scope, at),
        )
    }

    pub(crate) fn proves_execution_region_through_calls(
        &self,
        scoping: &Scoping,
        owner: ScopeId,
        region: Span,
        site: (ScopeId, Span),
        budget: &work_budget::WorkBudget,
    ) -> Result<bool, work_budget::BudgetExceeded> {
        self.proves_through_closed_calls(scoping, owner, site.0, site.1, budget, |scope, at| {
            self.execution_region_contains(scoping, owner, region, scope, at)
        })
    }

    fn proves_through_closed_calls(
        &self,
        scoping: &Scoping,
        owner: ScopeId,
        scope: ScopeId,
        at: Span,
        budget: &work_budget::WorkBudget,
        established: impl Fn(ScopeId, Span) -> bool,
    ) -> Result<bool, work_budget::BudgetExceeded> {
        let mut pending = vec![(scope, at)];
        let mut visited = HashSet::new();
        let mut grounded = false;
        while let Some((scope, at)) = pending.pop() {
            budget.checkpoint()?;
            if established(scope, at) {
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

    /// Exported declarations and exact default/named export bindings can
    /// be observed by code outside this source snapshot.
    pub(crate) fn is_exported_binding(&self, symbol: SymbolId) -> bool {
        self.exported_bindings.contains(&symbol)
    }

    /// Source-local table proofs do not extend to object-backed script
    /// globals or exported mutable allocations accessed by external code.
    pub(crate) fn source_local_data_binding(&self, scoping: &Scoping, symbol: SymbolId) -> bool {
        let object_backed_global = self.ambient_root
            && scoping.symbol_scope_id(symbol) == scoping.root_scope_id()
            && !scoping.symbol_flags(symbol).is_block_scoped();
        !(self.is_exported_binding(symbol)
            || object_backed_global
            || self.is_eval_exposed(scoping, symbol))
            && self.binding_has_stable_value(scoping, symbol)
    }

    /// Can this binding's value or properties be exposed to unmodeled code
    /// without an ordinary reference? A classic script's global environment
    /// and directly exported module allocations are not private. A potential
    /// direct eval can access only bindings visible at its lexical call site.
    pub(crate) fn is_private(&self, scoping: &Scoping, symbol: SymbolId) -> bool {
        if (self.ambient_root && scoping.symbol_scope_id(symbol) == scoping.root_scope_id())
            || self.is_exported_binding(symbol)
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
    #[must_use = "Check whether direct eval can expose the binding"]
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

    /// Leaving this lexical scope can invoke a registered resource disposer.
    pub(crate) fn scope_may_dispose(&self, scope: ScopeId) -> bool {
        self.resource_scopes.contains(&scope)
    }

    /// In a sloppy ordinary activation, an observable implicit arguments
    /// object can expose the callable itself through its callee property.
    pub(crate) fn implicit_arguments_exposed(&self, scope: ScopeId) -> bool {
        self.mapped_arguments_exposed.contains(&scope)
    }

    pub(crate) fn is_parameter(&self, symbol: SymbolId) -> bool {
        self.parameters.contains(&symbol)
    }

    pub(crate) fn is_hoisted_var(&self, symbol: SymbolId) -> bool {
        self.hoisted_vars.contains(&symbol)
    }

    /// With parameter expressions, an unredeclared formal and the
    /// immutable named-expression binding remain in the outer environment.
    pub(crate) fn parameter_binding_survives_body(
        &self,
        scoping: &Scoping,
        symbol: SymbolId,
    ) -> bool {
        self.named_function_expressions.contains(&symbol)
            || (self.parameters.contains(&symbol)
                && !self.hoisted_vars.contains(&symbol)
                && !scoping.symbol_flags(symbol).is_function())
    }

    /// A parameter cell may be indirectly written through mapped arguments.
    /// This is a function-local property, including references in arrows.
    pub(crate) fn is_mapped_arguments_exposed(&self, scoping: &Scoping, symbol: SymbolId) -> bool {
        self.parameters.contains(&symbol)
            && self
                .mapped_arguments_exposed
                .contains(&scoping.symbol_scope_id(symbol))
    }

    /// Binding value cannot be reassigned by potential direct eval.
    /// This does not prove the absence of ordinary writes or mutation of
    /// objects stored in the binding.
    #[must_use = "Only a true result proves the binding is unmodified by eval"]
    pub fn binding_unmodified_by_eval(&self, scoping: &Scoping, symbol: SymbolId) -> bool {
        scoping.symbol_flags(symbol).is_const_variable() || !self.is_eval_exposed(scoping, symbol)
    }

    /// A single declaration and no known binding reassignment, including
    /// direct eval. Still requires an initialization proof at each use.
    #[must_use = "Only a true result proves the binding has a stable value"]
    pub fn binding_has_stable_value(&self, scoping: &Scoping, symbol: SymbolId) -> bool {
        scoping.symbol_redeclarations(symbol).is_empty()
            && self.binding_unmodified_by_eval(scoping, symbol)
            && !self.is_mapped_arguments_exposed(scoping, symbol)
            && scoping
                .get_resolved_reference_ids(symbol)
                .iter()
                .all(|&reference| !scoping.get_reference(reference).is_write())
    }

    /// A single literal var initializer can establish a two-value
    /// domain (undefined before execution, the initializer afterward).
    /// Parameters, implicit arguments, dynamic targets and function
    /// redeclarations do not have that initialization semantics.
    pub(crate) fn stable_var_initializer(
        &self,
        scoping: &Scoping,
        declarator: &VariableDeclarator<'_>,
    ) -> Option<SymbolId> {
        let symbol = self.var_initializer_target(scoping, declarator)?;
        (self.hoisted_vars.contains(&symbol)
            && !self.parameters.contains(&symbol)
            && scoping.symbol_name(symbol) != "arguments"
            && !scoping.symbol_flags(symbol).is_function()
            && self.binding_has_stable_value(scoping, symbol))
        .then_some(symbol)
    }

    /// A function declaration is installed when its actual lexical owner
    /// is instantiated. Annex B can instead create a var-like binding
    /// initialized only by executing the declaration's block or branch.
    /// The latter is not a stable hoisted callable.
    pub(crate) fn hoisted_callable_declaration(
        &self,
        scoping: &Scoping,
        symbol: SymbolId,
        function_scope: ScopeId,
    ) -> bool {
        self.instantiated_function_declaration(scoping, symbol, function_scope)
            && self.binding_has_stable_value(scoping, symbol)
    }

    /// Ordinary declaration instantiation installs a function even if its
    /// lexical binding is subsequently assigned. Stability is only needed
    /// when resolving calls without a reaching cell value.
    pub(crate) fn instantiated_function_declaration(
        &self,
        scoping: &Scoping,
        symbol: SymbolId,
        function_scope: ScopeId,
    ) -> bool {
        self.statement_list_functions.get(&symbol) == Some(&function_scope)
            && scoping.scope_parent_id(function_scope) == Some(scoping.symbol_scope_id(symbol))
            && self.has_declarative_storage(scoping, symbol)
            && !self.is_mapped_arguments_exposed(scoping, symbol)
    }

    /// A hoisted declaration's statement is inert in a function body or
    /// strict lexical block. Sloppy block declarations may additionally
    /// install an Annex B var binding when the statement executes.
    pub(crate) fn inert_function_declaration(
        &self,
        scoping: &Scoping,
        function: &Function<'_>,
    ) -> bool {
        let Some(symbol) = function.id.as_ref().and_then(|id| id.symbol_id.get()) else {
            return false;
        };
        let Some(scope) = function.scope_id.get() else {
            return false;
        };
        let owner = scoping.symbol_scope_id(symbol);
        let flags = scoping.scope_flags(owner);
        (flags.is_function() || flags.is_strict_mode())
            && self.statement_list_declarations.contains(&scope)
            && scoping.scope_parent_id(scope) == Some(owner)
            && self.has_declarative_storage(scoping, symbol)
    }

    /// Resolve an invocation to the already instantiated lexical function.
    /// A body's declaration does not exist in its owner's separate
    /// parameter environment, including closures created in defaults.
    pub(crate) fn hoisted_callable_at(
        &self,
        scoping: &Scoping,
        expression: &Expression<'_>,
        function_scope: ScopeId,
    ) -> Option<SymbolId> {
        let Expression::Identifier(identifier) = expression.without_parentheses() else {
            return None;
        };
        let symbol = self.resolved_symbol(scoping, identifier.reference_id.get()?)?;
        let owner = scoping.symbol_scope_id(symbol);
        let in_parameters = self.parameter_regions.get(&owner).is_some_and(|region| {
            region.start <= identifier.span.start && identifier.span.end <= region.end
        });
        (!in_parameters && self.hoisted_callable_declaration(scoping, symbol, function_scope))
            .then_some(symbol)
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

    #[must_use = "Use the returned evidence only when the read is initialized"]
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
    /// `IdentifierReference` rather than its containing Expression.
    #[must_use = "Use the returned evidence only when the reference is initialized"]
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

    fn visit_identifier_reference(&mut self, identifier: &oxc_ast::ast::IdentifierReference<'a>) {
        if identifier.name == "arguments" {
            self.arguments_references
                .extend(identifier.reference_id.get());
        }
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
            // Only statement-list declarations participate in ordinary
            // function declaration instantiation. Annex B single-statement
            // branches are not declarations in this list.
            let function = match statement {
                Statement::FunctionDeclaration(function) => Some(function.as_ref()),
                Statement::ExportDeclaration(export) => match &export.declaration {
                    Declaration::FunctionDeclaration(function) => Some(function.as_ref()),
                    _ => None,
                },
                Statement::ExportDefaultDeclaration(export) => match &export.declaration {
                    ExportDefaultDeclarationKind::FunctionDeclaration(function) => {
                        Some(function.as_ref())
                    }
                    _ => None,
                },
                _ => None,
            };
            if let Some(function) = function {
                if let (Some(symbol), Some(scope)) = (
                    function.id.as_ref().and_then(|id| id.symbol_id.get()),
                    function.scope_id.get(),
                ) {
                    self.statement_list_functions.insert(symbol, scope);
                    self.statement_list_declarations.insert(scope);
                }
            }
            // This is one actual statement list. A switch case's lexical
            // declaration does not dominate a separately selectable case.
            let declaration = match statement {
                Statement::VariableDeclaration(declaration) => Some(declaration.as_ref()),
                Statement::ExportDeclaration(export) => match &export.declaration {
                    Declaration::VariableDeclaration(declaration) => Some(declaration.as_ref()),
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

    fn visit_export_declaration(&mut self, export: &ExportDeclaration<'a>) {
        match &export.declaration {
            Declaration::VariableDeclaration(declaration) => {
                for declarator in &declaration.declarations {
                    self.exported_bindings.extend(
                        declarator
                            .id
                            .get_binding_identifiers()
                            .into_iter()
                            .filter_map(|identifier| identifier.symbol_id.get()),
                    );
                }
            }
            Declaration::FunctionDeclaration(function) => {
                self.exported_bindings
                    .extend(function.id.as_ref().and_then(|id| id.symbol_id.get()));
            }
            Declaration::ClassDeclaration(class) => {
                self.exported_bindings
                    .extend(class.id.as_ref().and_then(|id| id.symbol_id.get()));
            }
            _ => {}
        }
        walk::walk_export_declaration(self, export);
    }

    fn visit_export_named_declaration(&mut self, export: &ExportNamedDeclaration<'a>) {
        // Local named exports use IdentifierReference; re-exports from
        // another module are a different AST node and expose no local symbol.
        for specifier in &export.specifiers {
            if let ModuleExportName::IdentifierReference(identifier) = &specifier.local {
                self.exported_references
                    .extend(identifier.reference_id.get());
            }
        }
        walk::walk_export_named_declaration(self, export);
    }

    fn visit_export_default_declaration(&mut self, export: &ExportDefaultDeclaration<'a>) {
        match &export.declaration {
            ExportDefaultDeclarationKind::FunctionDeclaration(function) => {
                self.exported_bindings
                    .extend(function.id.as_ref().and_then(|id| id.symbol_id.get()));
            }
            ExportDefaultDeclarationKind::ClassDeclaration(class) => {
                self.exported_bindings
                    .extend(class.id.as_ref().and_then(|id| id.symbol_id.get()));
            }
            declaration => {
                // A default expression exports a value rather than a live
                // binding, but an exact identifier value still exposes the
                // referenced object or callable to importers.
                if let Some(Expression::Identifier(identifier)) = declaration
                    .as_expression()
                    .map(Expression::without_parentheses)
                {
                    self.exported_references
                        .extend(identifier.reference_id.get());
                }
            }
        }
        walk::walk_export_default_declaration(self, export);
    }

    fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
        if declaration.kind.is_using() {
            self.resource_scopes
                .extend(self.scopes.last().copied().flatten());
        }
        if declaration.kind == VariableDeclarationKind::Var {
            for declarator in &declaration.declarations {
                if declarator.init.is_some() {
                    if let Some(Some(scope)) = self.scopes.last() {
                        self.var_initializer_scopes.insert(declarator.span, *scope);
                    }
                }
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
            if node.params.is_simple_parameter_list()
                && !node.params.items.iter().any(|parameter| {
                    matches!(&parameter.pattern, BindingPattern::BindingIdentifier(id) if id.name == "arguments")
                })
            {
                self.simple_parameter_functions.insert(scope);
            }
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
        use ReferenceIdentity::{Dynamic, Global, Lexical};
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
    #[expect(
        clippy::literal_string_with_formatting_args,
        reason = "JavaScript fixture braces are source syntax, not Rust format placeholders"
    )]
    fn module_export_forms_mark_exact_externally_observable_bindings() {
        for (source, exposed) in [
            ("export const x=1;const y=2;", true),
            ("export let x=1;const y=2;", true),
            ("export var x=1;const y=2;", true),
            ("export const {x}={x:1};const y=2;", true),
            ("export function x(){}const y=2;", true),
            ("export class x{}const y=2;", true),
            ("export default function x(){}const y=2;", true),
            ("export default class x{}const y=2;", true),
            ("const x=1,y=2;export {x};", true),
            ("const x=1,y=2;export {x as other};", true),
            ("const x=1,y=2;export {x as default};", true),
            ("const x=1,y=2;export default x;", true),
            ("const x=1,y=2;export default (x);", true),
            ("const x=1,y=2;export {x as other} from 'external';", false),
            ("const x=1,y=2;export * as external from 'external';", false),
            ("const x=1,y=2;export {};", false),
        ] {
            let allocator = Allocator::default();
            let program = crate::parse_as(&allocator, source, SourceType::mjs())
                .unwrap_or_else(|| unreachable!("{source}"));
            let semantic = SemanticBuilder::new()
                .with_check_syntax_error(true)
                .build(&program);
            assert!(semantic.diagnostics.is_empty(), "{source}");
            let scoping = semantic.semantic.scoping();
            let facts = BindingFacts::analyze(&program, scoping);
            let x = scoping
                .get_binding(scoping.root_scope_id(), "x".into())
                .unwrap_or_else(|| unreachable!("{source}"));
            let y = scoping
                .get_binding(scoping.root_scope_id(), "y".into())
                .unwrap_or_else(|| unreachable!("{source}"));
            assert_eq!(!facts.is_private(scoping, x), exposed, "{source}");
            assert!(facts.is_private(scoping, y), "{source}");
        }
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
