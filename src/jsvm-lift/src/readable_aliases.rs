//! Intrinsic alias elimination for analyst-only JS. This assumes standard
//! builtins retain their native data properties throughout the program.
//! Never use this presentation transform for proof-gated executable output.
use jsvm_safe_core::statically_unresolved_global_reference;
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    BindingPattern, CallExpression, Expression, IdentifierReference, ObjectProperty, Program,
    Statement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::symbol::SymbolId;
use rolldown_redox::ecmascript::parse_program;
use std::collections::{BTreeMap, BTreeSet};

// Generic property-chain analysis, restricted to standard intrinsic roots:
// arbitrary object members may have getters or dynamic property mutations.
const INTRINSICS: &[&str] = &[
    "Array", "BigInt", "Boolean", "Date", "Error", "JSON", "Math", "Number", "Object", "Promise",
    "Reflect", "RegExp", "String", "Symbol",
];

fn intrinsic_path(expr: &Expression<'_>, scoping: &Scoping) -> bool {
    match expr {
        Expression::Identifier(id) => id.reference_id.get().is_some_and(|r| {
            INTRINSICS.contains(&id.name.as_str())
                && statically_unresolved_global_reference(scoping, r)
        }),
        Expression::ParenthesizedExpression(p) => intrinsic_path(&p.expression, scoping),
        Expression::StaticMemberExpression(m) => intrinsic_path(&m.object, scoping),
        Expression::ComputedMemberExpression(m) => {
            matches!(&m.expression, Expression::StringLiteral(s) if s.value.as_str().is_some())
                && intrinsic_path(&m.object, scoping)
        }
        _ => false,
    }
}
fn root_name<'a>(expr: &'a Expression<'_>) -> Option<&'a str> {
    match expr {
        Expression::Identifier(id) => Some(id.name.as_str()),
        Expression::ParenthesizedExpression(p) => root_name(&p.expression),
        Expression::StaticMemberExpression(m) => root_name(&m.object),
        Expression::ComputedMemberExpression(m) => root_name(&m.object),
        _ => None,
    }
}
fn candidate(expr: &Expression<'_>, scoping: &Scoping) -> bool {
    matches!(
        expr,
        Expression::StaticMemberExpression(_) | Expression::ComputedMemberExpression(_)
    ) && intrinsic_path(expr, scoping)
}
struct Alias {
    symbol: SymbolId,
    value: Span,
    binding: Span,
    declaration: u32,
    root: String,
}
struct Decl {
    span: Span,
    fragments: Vec<Span>,
}
struct Collect<'s> {
    scoping: &'s Scoping,
    aliases: Vec<Alias>,
    declarations: BTreeMap<u32, Decl>,
}
impl Collect<'_> {
    fn scan(&mut self, statements: &[Statement<'_>]) {
        for statement in statements {
            let Statement::VariableDeclaration(decl) = statement else {
                continue;
            };
            for var in &decl.declarations {
                let (BindingPattern::BindingIdentifier(id), Some(value)) =
                    (&var.id, var.init.as_ref())
                else {
                    continue;
                };
                if candidate(value, self.scoping) {
                    if let Some(symbol) = id.symbol_id.get() {
                        self.aliases.push(Alias {
                            symbol,
                            value: value.span(),
                            binding: id.span,
                            declaration: decl.span.start,
                            root: root_name(value).unwrap_or_default().to_owned(),
                        });
                    }
                }
            }
            self.declarations.insert(
                decl.span.start,
                Decl {
                    span: decl.span,
                    fragments: decl.declarations.iter().map(GetSpan::span).collect(),
                },
            );
        }
    }
}
impl<'a> Visit<'a> for Collect<'_> {
    fn visit_program(&mut self, p: &Program<'a>) {
        self.scan(&p.body);
        walk::walk_program(self, p);
    }
    fn visit_function_body(&mut self, b: &oxc_ast::ast::FunctionBody<'a>) {
        self.scan(&b.statements);
        walk::walk_function_body(self, b);
    }
}
#[derive(Default)]
struct Context {
    refs: BTreeMap<SymbolId, Vec<Span>>,
    reference_scopes: BTreeMap<u32, oxc_syntax::scope::ScopeId>,
    calls: BTreeSet<u32>,
    shorthand: BTreeMap<u32, String>,
    exported: BTreeSet<SymbolId>,
    tagged: BTreeSet<SymbolId>,
    modified_intrinsics: BTreeSet<String>,
    dynamic: bool,
}
struct References<'s> {
    scoping: &'s Scoping,
    ctx: Context,
}
impl References<'_> {
    fn symbol(&self, id: &IdentifierReference<'_>) -> Option<SymbolId> {
        self.scoping
            .get_reference(id.reference_id.get()?)
            .symbol_id()
    }
}
impl<'a> Visit<'a> for References<'_> {
    fn visit_identifier_reference(&mut self, id: &IdentifierReference<'a>) {
        if let Some(reference_id) = id.reference_id.get() {
            let reference = self.scoping.get_reference(reference_id);
            if let Some(symbol) = reference.symbol_id() {
                self.ctx.refs.entry(symbol).or_default().push(id.span);
                self.ctx
                    .reference_scopes
                    .insert(id.span.start, reference.scope_id());
            }
        }
    }
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if let Expression::Identifier(id) = &call.callee {
            if id.name == "eval" {
                self.ctx.dynamic = true;
            }
            self.ctx.calls.insert(id.span.start);
        }
        walk::walk_call_expression(self, call);
    }
    fn visit_object_property(&mut self, prop: &ObjectProperty<'a>) {
        if prop.shorthand {
            if let Expression::Identifier(id) = &prop.value {
                self.ctx
                    .shorthand
                    .insert(id.span.start, id.name.to_string());
            }
        }
        walk::walk_object_property(self, prop);
    }
    fn visit_export_specifier(&mut self, s: &oxc_ast::ast::ExportSpecifier<'a>) {
        if let oxc_ast::ast::ModuleExportName::IdentifierReference(id) = &s.local {
            if let Some(symbol) = self.symbol(id) {
                self.ctx.exported.insert(symbol);
            }
        }
        walk::walk_export_specifier(self, s);
    }
    fn visit_export_default_declaration(&mut self, d: &oxc_ast::ast::ExportDefaultDeclaration<'a>) {
        struct Mark<'s> {
            scoping: &'s Scoping,
            symbols: BTreeSet<SymbolId>,
        }
        impl<'a> Visit<'a> for Mark<'_> {
            fn visit_identifier_reference(&mut self, id: &IdentifierReference<'a>) {
                if let Some(sym) = id
                    .reference_id
                    .get()
                    .and_then(|r| self.scoping.get_reference(r).symbol_id())
                {
                    self.symbols.insert(sym);
                }
            }
        }
        let mut marks = Mark {
            scoping: self.scoping,
            symbols: BTreeSet::new(),
        };
        marks.visit_export_default_declaration(d);
        self.ctx.exported.extend(marks.symbols);
        walk::walk_export_default_declaration(self, d);
    }
    fn visit_tagged_template_expression(&mut self, t: &oxc_ast::ast::TaggedTemplateExpression<'a>) {
        if let Expression::Identifier(id) = &t.tag {
            if let Some(symbol) = self.symbol(id) {
                self.ctx.tagged.insert(symbol);
            }
        }
        walk::walk_tagged_template_expression(self, t);
    }
    fn visit_assignment_expression(&mut self, a: &oxc_ast::ast::AssignmentExpression<'a>) {
        use oxc_ast::ast::AssignmentTarget;
        let root = match &a.left {
            AssignmentTarget::StaticMemberExpression(m) => root_name(&m.object),
            AssignmentTarget::ComputedMemberExpression(m) => root_name(&m.object),
            AssignmentTarget::AssignmentTargetIdentifier(id) => Some(id.name.as_str()),
            _ => None,
        };
        if let Some(root) = root.filter(|root| INTRINSICS.contains(root)) {
            self.ctx.modified_intrinsics.insert(root.to_owned());
        }
        walk::walk_assignment_expression(self, a);
    }
    fn visit_update_expression(&mut self, u: &oxc_ast::ast::UpdateExpression<'a>) {
        use oxc_ast::ast::SimpleAssignmentTarget;
        let root = match &u.argument {
            SimpleAssignmentTarget::StaticMemberExpression(m) => root_name(&m.object),
            SimpleAssignmentTarget::ComputedMemberExpression(m) => root_name(&m.object),
            SimpleAssignmentTarget::AssignmentTargetIdentifier(id) => Some(id.name.as_str()),
            _ => None,
        };
        if let Some(root) = root.filter(|root| INTRINSICS.contains(root)) {
            self.ctx.modified_intrinsics.insert(root.to_owned());
        }
        walk::walk_update_expression(self, u);
    }
    fn visit_unary_expression(&mut self, u: &oxc_ast::ast::UnaryExpression<'a>) {
        if u.operator.as_str() == "delete" {
            if let Some(root) = root_name(&u.argument).filter(|root| INTRINSICS.contains(root)) {
                self.ctx.modified_intrinsics.insert(root.to_owned());
            }
        }
        walk::walk_unary_expression(self, u);
    }
    fn visit_with_statement(&mut self, w: &oxc_ast::ast::WithStatement<'a>) {
        self.ctx.dynamic = true;
        walk::walk_with_statement(self, w);
    }
}

/// Returns a different human-readable view, never an executable equivalence
/// certificate: aliases capture a value once, while substituted members are
/// looked up at their later use under the pristine-builtins assumption.
pub fn inline_readable_intrinsic_aliases(source: &str) -> Option<(String, usize)> {
    for source_type in [SourceType::mjs(), SourceType::cjs()] {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, source_type);
        if !parsed.is_clean() {
            continue;
        }
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        if !semantic.diagnostics.is_empty() {
            continue;
        }
        let scoping = semantic.semantic.scoping();
        let mut found = Collect {
            scoping,
            aliases: Vec::new(),
            declarations: BTreeMap::new(),
        };
        found.visit_program(&parsed.program);
        if found.aliases.is_empty() {
            continue;
        }
        let mut refs = References {
            scoping,
            ctx: Context::default(),
        };
        refs.visit_program(&parsed.program);
        if refs.ctx.dynamic {
            continue;
        }
        let mut accepted = BTreeMap::<u32, Vec<Span>>::new();
        let mut edits = Vec::<(usize, usize, String)>::new();
        let mut count = 0;
        for alias in &found.aliases {
            if refs.ctx.modified_intrinsics.contains(&alias.root)
                || refs.ctx.exported.contains(&alias.symbol)
                || refs.ctx.tagged.contains(&alias.symbol)
                || !scoping.symbol_redeclarations(alias.symbol).is_empty()
                || scoping
                    .get_resolved_reference_ids(alias.symbol)
                    .iter()
                    .any(|id| {
                        let r = scoping.get_reference(*id);
                        r.is_write() || r.flags().is_member_write_target()
                    })
            {
                continue;
            }
            let group = &found.declarations[&alias.declaration];
            let group_text = source.get(group.span.start as usize..group.span.end as usize)?;
            if group_text.contains("/*") || group_text.contains("//") {
                continue;
            }
            let Some(value) = source.get(alias.value.start as usize..alias.value.end as usize)
            else {
                continue;
            };
            let uses = refs
                .ctx
                .refs
                .get(&alias.symbol)
                .map_or(&[][..], Vec::as_slice);
            if uses.iter().any(|span| {
                span.start <= alias.value.end
                    || refs
                        .ctx
                        .reference_scopes
                        .get(&span.start)
                        .is_none_or(|scope| {
                            scoping
                                .find_binding(*scope, alias.root.as_str().into())
                                .is_some()
                        })
            }) {
                continue;
            }
            for span in uses {
                let replacement = if let Some(key) = refs.ctx.shorthand.get(&span.start) {
                    format!("{key}: {value}")
                } else if refs.ctx.calls.contains(&span.start) {
                    // Keep detached call receiver semantics (including optional calls).
                    format!("(0, {value})")
                } else {
                    format!("({value})")
                };
                edits.push((span.start as usize, span.end as usize, replacement));
            }
            accepted
                .entry(alias.declaration)
                .or_default()
                .push(alias.binding);
            count += 1;
        }
        if count == 0 {
            continue;
        }
        // An alias may be referenced in a surviving initializer of its own
        // declaration group. Incorporate those nested reference edits into
        // each retained declarator before replacing the whole group.
        // Overlapping absolute source edits would discard the whole pass.
        let mut group_edits = Vec::new();
        for (start, bindings) in accepted {
            let group = &found.declarations[&start];
            let remaining: Vec<_> = group
                .fragments
                .iter()
                .filter(|span| {
                    !bindings
                        .iter()
                        .any(|b| span.start <= b.start && b.end <= span.end)
                })
                .collect();
            let replacement = if remaining.is_empty() {
                ";".to_string()
            } else {
                let first = group.fragments.first()?;
                let last = group.fragments.last()?;
                let prefix = source.get(group.span.start as usize..first.start as usize)?;
                let suffix = source.get(last.end as usize..group.span.end as usize)?;
                let mut parts = Vec::with_capacity(remaining.len());
                for fragment in remaining {
                    let fragment_start = fragment.start as usize;
                    let fragment_end = fragment.end as usize;
                    let mut part = source.get(fragment_start..fragment_end)?.to_owned();
                    let mut nested_edits: Vec<_> = edits
                        .iter()
                        .filter(|(s, e, _)| *s >= fragment_start && *e <= fragment_end)
                        .collect();
                    nested_edits.sort_by_key(|(s, _, _)| std::cmp::Reverse(*s));
                    let mut right = fragment_end;
                    for (s, e, new_text) in nested_edits {
                        if *s > *e || *e > right {
                            return None;
                        }
                        part.replace_range(s - fragment_start..e - fragment_start, new_text);
                        right = *s;
                    }
                    parts.push(part);
                }
                format!("{prefix}{}{suffix}", parts.join(", "))
            };
            let group_start = group.span.start as usize;
            let group_end = group.span.end as usize;
            edits.retain(|(s, e, _)| !(*s >= group_start && *e <= group_end));
            group_edits.push((group_start, group_end, replacement));
        }
        edits.extend(group_edits);
        edits.sort_by_key(|(start, _, _)| std::cmp::Reverse(*start));
        let mut result = source.to_string();
        let mut right = source.len();
        for (start, end, replacement) in edits {
            if start > end || end > right {
                return None;
            }
            result.replace_range(start..end, &replacement);
            right = start;
        }
        let checked_allocator = Allocator::default();
        let checked = parse_program(&checked_allocator, &result, source_type);
        if checked.is_clean()
            && SemanticBuilder::new()
                .with_check_syntax_error(true)
                .build(&checked.program)
                .diagnostics
                .is_empty()
        {
            return Some((result, count));
        }
    }
    None
}
#[cfg(test)]
mod tests {
    use super::inline_readable_intrinsic_aliases as inline;
    fn rewrite(s: &str) -> String {
        inline(s).map_or_else(|| s.to_owned(), |(out, _)| out)
    }

    #[test]
    fn group_and_detached_calls() {
        let s = "function f(){var R=Object.create, z=Object.defineProperty, x=other(); return [R(null),z({},'a',{value:1}),x];}";
        let out = rewrite(s);
        assert!(out.contains("var x=other()"), "{out}");
        assert!(out.contains("(0, Object.create)(null)"), "{out}");
        assert!(out.contains("(0, Object.defineProperty)({},'a'"), "{out}");
    }
    #[test]
    fn inlines_uses_inside_retained_group_declarators() {
        let source = "function make(p){var R=Object.create, Z=Object.defineProperty, build=(q)=>Z(R(q),'x',{value:1}), keep=7; return build(p)+keep;}";
        let output = rewrite(source);
        assert!(!output.contains("R=Object.create"), "{output}");
        assert!(!output.contains("Z=Object.defineProperty"), "{output}");
        assert!(output.contains("var build=(q)=>(0, Object.defineProperty)((0, Object.create)(q),'x',{value:1}), keep=7;"), "{output}");
        assert!(output.contains("return build(p)+keep"), "{output}");
    }
    #[test]
    fn inlines_refs_in_separate_and_multiple_retained_declarators() {
        let source = "const f=Math.min, g=()=>f(1,2), h=()=>f(3,4); use(g(),h());";
        let output = rewrite(source);
        assert!(!output.contains("f=Math.min"), "{output}");
        assert!(
            output.contains("const g=()=>(0, Math.min)(1,2), h=()=>(0, Math.min)(3,4);"),
            "{output}"
        );
    }
    #[test]
    fn shorthand_and_shadowing() {
        let s = "const f=Math.min; const obj={f}; function g(f){ return f(2,3); } console.log(f(1,2),obj);";
        let out = rewrite(s);
        assert!(out.contains("f: Math.min"), "{out}");
        assert!(out.contains("function g(f){ return f(2,3); }"), "{out}");
        assert!(out.contains("(0, Math.min)(1,2)"), "{out}");
    }
    #[test]
    fn unsafe_cases_unchanged() {
        for s in [
            "let a = Object.create; a = other; a(null);",
            "const a = Object.create; export {a};",
            "if(flag){var a=Object.create;} a(null);",
            "const a=service.create; a();",
            "const a=Object.create; eval('a=0'); a(null);",
            "const a=Object.create; var a;",
            "function f(Object){const a=Object.create; return a(null);}",
            "f(); const f = Math.min;",
            "const f=Math.min; function g(Math){return f(1,2)}; f(2,3);",
            "const a=Object.create; Object.create = () => null; a(null);",
            "const a=Math.min; Math.min++; a(1,2);",
            "const a=Object.create; delete Object.create; a(null);",
        ] {
            assert_eq!(rewrite(s), s, "{s}");
        }
    }
}
