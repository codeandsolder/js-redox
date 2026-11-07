//! Exact source-resolved, caller-oriented JavaScript argument forwarding.
//!
//! This is an inspectable *source view*, never an in-place replacement. Direct
//! calls and constructions of uniquely resolved functions can be connected by
//! original lexical symbol identity. Forwarded parameters are traced only
//! when the referring binding is not written; other expressions are retained
//! as unknown/dynamic, not guessed as constant values.
use anyhow::{ensure, Result};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, AssignmentExpression, AssignmentTarget, BindingPattern, CallExpression, Expression,
    FormalParameters, Function, NewExpression, VariableDeclarator,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::{scope::ScopeFlags, symbol::SymbolId};
use rolldown_redox::ecmascript::parse_program;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

type FunctionKey = (u32, u32);

fn key(span: Span) -> FunctionKey {
    (span.start, span.end)
}
fn unparen<'e, 'a>(mut expr: &'e Expression<'a>) -> &'e Expression<'a> {
    while let Expression::ParenthesizedExpression(paren) = expr {
        expr = &paren.expression;
    }
    expr
}
fn fragment(src: &str, span: Span) -> &str {
    src.get(span.start as usize..span.end as usize)
        .unwrap_or("")
}

#[derive(Clone, Debug)]
struct Definition {
    label: String,
    params: Vec<(String, Option<SymbolId>)>,
    symbol: Option<SymbolId>,
    member: bool,
    initialized_by_assignment: bool,
}

fn definition(
    params: &FormalParameters<'_>,
    label: String,
    symbol: Option<SymbolId>,
    member: bool,
) -> Definition {
    let params = params
        .items
        .iter()
        .map(|parameter| match &parameter.pattern {
            BindingPattern::BindingIdentifier(id) if parameter.initializer.is_none() => {
                (id.name.to_string(), id.symbol_id.get())
            }
            _ => ("<pattern/default>".to_owned(), None),
        })
        .collect();
    Definition {
        label,
        params,
        symbol,
        member,
        initialized_by_assignment: false,
    }
}

fn defined_callable(
    expression: &Expression<'_>,
    label: String,
    symbol: Option<SymbolId>,
    member: bool,
) -> Option<(FunctionKey, Definition)> {
    match unparen(expression) {
        Expression::FunctionExpression(function) => Some((
            key(function.span),
            definition(&function.params, label, symbol, member),
        )),
        Expression::ArrowFunctionExpression(function) => Some((
            key(function.span),
            definition(&function.params, label, symbol, member),
        )),
        _ => None,
    }
}

struct Definitions<'s> {
    functions: BTreeMap<FunctionKey, Definition>,
    scoping: &'s Scoping,
}
impl<'a> Visit<'a> for Definitions<'_> {
    fn visit_variable_declarator(&mut self, it: &VariableDeclarator<'a>) {
        if let (BindingPattern::BindingIdentifier(id), Some(init)) = (&it.id, &it.init) {
            if let Some((key, def)) =
                defined_callable(init, id.name.to_string(), id.symbol_id.get(), false)
            {
                self.functions.insert(key, def);
            }
        }
        walk::walk_variable_declarator(self, it);
    }
    fn visit_assignment_expression(&mut self, it: &AssignmentExpression<'a>) {
        if it.operator.as_str() == "=" {
            let target = match &it.left {
                AssignmentTarget::AssignmentTargetIdentifier(id) => {
                    let symbol = id
                        .reference_id
                        .get()
                        .and_then(|reference| self.scoping.get_reference(reference).symbol_id());
                    Some((id.name.to_string(), symbol, false))
                }
                AssignmentTarget::StaticMemberExpression(member) if !member.optional => {
                    Some((format!(".{}", member.property.name), None, true))
                }
                _ => None,
            };
            if let Some((label, symbol, member)) = target {
                if let Some((key, mut def)) = defined_callable(&it.right, label, symbol, member) {
                    // `let fn; fn = expression` has one expected resolved
                    // write: the assignment establishing the function itself.
                    def.initialized_by_assignment = !member;
                    self.functions.insert(key, def);
                }
            }
        }
        walk::walk_assignment_expression(self, it);
    }
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if function.is_declaration() {
            if let Some(id) = &function.id {
                self.functions.insert(
                    key(function.span),
                    definition(
                        &function.params,
                        id.name.to_string(),
                        id.symbol_id.get(),
                        false,
                    ),
                );
            }
        }
        walk::walk_function(self, function, flags);
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct ArgumentLink {
    pub expression: String,
    pub caller_param_index: Option<usize>,
    pub caller_param: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct CallLink {
    pub caller: String,
    pub callee: String,
    pub kind: &'static str,
    pub span: [u32; 2],
    pub arguments: Vec<ArgumentLink>,
}

#[derive(Clone, Debug, Serialize)]
pub struct ForwardedParameter {
    pub param: String,
    pub index: usize,
    /// Root API function parameter index, if *every* edge forwards the same
    /// unchanged parameter without an intervening computed expression.
    pub from_entry_index: Option<usize>,
    pub from_entry: Option<String>,
    pub input_expression: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct CallerPath {
    pub functions: Vec<String>,
    pub function_spans: Vec<[u32; 2]>,
    pub links: Vec<CallLink>,
    pub leaf_parameters: Vec<ForwardedParameter>,
}

#[derive(Clone, Debug, Serialize)]
pub struct CallerView {
    pub entry: String,
    pub entry_span: [u32; 2],
    pub paths: Vec<CallerPath>,
    pub source: String,
}

struct Calls<'s> {
    source: &'s str,
    scoping: &'s Scoping,
    defs: &'s BTreeMap<FunctionKey, Definition>,
    symbols: &'s BTreeMap<SymbolId, FunctionKey>,
    stack: Vec<FunctionKey>,
    edges: BTreeMap<FunctionKey, Vec<(FunctionKey, CallLink)>>,
}
impl Calls<'_> {
    fn emit(
        &mut self,
        callee: &Expression<'_>,
        args: &[Argument<'_>],
        span: Span,
        kind: &'static str,
    ) {
        let Some(&caller_key) = self.stack.last() else {
            return;
        };
        let Expression::Identifier(id) = unparen(callee) else {
            return;
        };
        let Some(target_symbol) = id
            .reference_id
            .get()
            .and_then(|reference| self.scoping.get_reference(reference).symbol_id())
        else {
            return;
        };
        let Some(&callee_key) = self.symbols.get(&target_symbol) else {
            return;
        };
        let Some(caller) = self.defs.get(&caller_key) else {
            return;
        };
        let Some(target) = self.defs.get(&callee_key) else {
            return;
        };
        let arguments = args
            .iter()
            .map(|arg| {
                let arg_span = arg.span();
                let mut forward = None;
                if let Some(Expression::Identifier(value)) = arg.as_expression().map(unparen) {
                    if let Some(symbol) = value
                        .reference_id
                        .get()
                        .and_then(|reference| self.scoping.get_reference(reference).symbol_id())
                    {
                        if !self
                            .scoping
                            .get_resolved_reference_ids(symbol)
                            .iter()
                            .any(|reference| self.scoping.get_reference(*reference).is_write())
                        {
                            forward = caller.params.iter().enumerate().find_map(
                                |(index, (_, target))| (*target == Some(symbol)).then_some(index),
                            );
                        }
                    }
                }
                ArgumentLink {
                    expression: fragment(self.source, arg_span).to_owned(),
                    caller_param: forward.map(|idx| caller.params[idx].0.clone()),
                    caller_param_index: forward,
                }
            })
            .collect();
        let call = CallLink {
            caller: caller.label.clone(),
            callee: target.label.clone(),
            kind,
            span: [span.start, span.end],
            arguments,
        };
        self.edges
            .entry(caller_key)
            .or_default()
            .push((callee_key, call));
    }
}
impl<'a> Visit<'a> for Calls<'_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        self.stack.push(key(function.span));
        walk::walk_function(self, function, flags);
        self.stack.pop();
    }
    fn visit_arrow_function_expression(&mut self, it: &oxc_ast::ast::ArrowFunctionExpression<'a>) {
        self.stack.push(key(it.span));
        walk::walk_arrow_function_expression(self, it);
        self.stack.pop();
    }
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            self.emit(&call.callee, &call.arguments, call.span, "call");
        }
        walk::walk_call_expression(self, call);
    }
    fn visit_new_expression(&mut self, expr: &NewExpression<'a>) {
        self.emit(&expr.callee, &expr.arguments, expr.span, "new");
        walk::walk_new_expression(self, expr);
    }
}

struct PathWalker<'s> {
    defs: &'s BTreeMap<FunctionKey, Definition>,
    edges: &'s BTreeMap<FunctionKey, Vec<(FunctionKey, CallLink)>>,
    root: FunctionKey,
    output: Vec<CallerPath>,
}

impl PathWalker<'_> {
    fn walk(
        &mut self,
        current: FunctionKey,
        origin: &[Option<usize>],
        names: &mut Vec<String>,
        spans: &mut Vec<[u32; 2]>,
        links: &mut Vec<CallLink>,
        visited: &mut BTreeSet<FunctionKey>,
    ) {
        if links.len() >= 4 {
            return;
        }
        let Some(call_sites) = self.edges.get(&current) else {
            return;
        };
        for (next, edge) in call_sites {
            if !visited.insert(*next) {
                continue;
            }
            let Some(target) = self.defs.get(next) else {
                continue;
            };
            let root_params = &self.defs[&self.root].params;
            let next_origins = target
                .params
                .iter()
                .enumerate()
                .map(|(index, _)| {
                    edge.arguments.get(index).and_then(|argument| {
                        argument
                            .caller_param_index
                            .and_then(|i| origin.get(i).copied().flatten())
                    })
                })
                .collect::<Vec<_>>();
            names.push(target.label.clone());
            spans.push([next.0, next.1]);
            links.push(edge.clone());
            if links.len() >= 2 {
                let leaf_parameters = target
                    .params
                    .iter()
                    .enumerate()
                    .map(|(index, (name, _))| {
                        let from_entry_index = next_origins[index];
                        ForwardedParameter {
                            param: name.clone(),
                            index,
                            from_entry_index,
                            from_entry: from_entry_index.map(|i| root_params[i].0.clone()),
                            input_expression: edge
                                .arguments
                                .get(index)
                                .map_or_else(|| "<omitted>".into(), |a| a.expression.clone()),
                        }
                    })
                    .collect();
                self.output.push(CallerPath {
                    functions: names.clone(),
                    function_spans: spans.clone(),
                    links: links.clone(),
                    leaf_parameters,
                });
            }
            self.walk(*next, &next_origins, names, spans, links, visited);
            names.pop();
            spans.pop();
            links.pop();
            visited.remove(next);
        }
    }
}

impl CallerView {
    /// Render a focused subset of the full source-resolved graph. The JSON
    /// manifest can still retain all reachable paths for deeper inspection.
    #[must_use]
    pub fn render_paths(&self, original: &str, selected: &BTreeSet<usize>) -> String {
        let mut view = self.clone();
        view.paths = self
            .paths
            .iter()
            .enumerate()
            .filter(|(index, _)| selected.contains(index))
            .map(|(_, path)| path.clone())
            .collect();
        format_view(&view, original)
    }
}

fn format_view(view: &CallerView, original: &str) -> String {
    let mut output = format!("# Caller-oriented lexical forwarding: `{}`\n\n", view.entry);
    output.push_str("This is a **source-derived reading view**, not a rewritten executable. ");
    output.push_str("Edges resolve original Oxc lexical symbols and direct calls/constructors. ");
    output.push_str("Parameter arrows trace unchanged, directly forwarded bindings only. ");
    output.push_str("Potential indirect `eval`, mapped `arguments`, or dynamic mutations require runtime analysis before claiming values are invariant.\n\n");
    for path in &view.paths {
        output.push_str(&format!("## `{}`\n\n", path.functions.join(" → ")));
        for edge in &path.links {
            output.push_str(&format!(
                "- `{}` → `{}` (**{}** at source bytes {}..{})\n",
                edge.caller, edge.callee, edge.kind, edge.span[0], edge.span[1]
            ));
            for (idx, arg) in edge.arguments.iter().enumerate() {
                let prefix = arg.caller_param.as_ref().map_or_else(
                    || "dynamic expression".to_owned(),
                    |param| format!("caller parameter `{param}`"),
                );
                output.push_str(&format!(
                    "  - argument {idx}: `{}` ← {prefix}\n",
                    arg.expression
                ));
            }
        }
        output.push_str("\n**Leaf parameter provenance:**\n\n");
        for param in &path.leaf_parameters {
            match (&param.from_entry, &param.from_entry_index) {
                (Some(name), Some(index)) => output.push_str(&format!(
                    "- `{}` (parameter {}) ← entry `{}` (parameter {})\n",
                    param.param, param.index, name, index
                )),
                _ => output.push_str(&format!(
                    "- `{}` (parameter {}) ← dynamic/unknown (`{}`)\n",
                    param.param, param.index, param.input_expression
                )),
            }
        }
        output.push('\n');
    }
    output.push_str("## Original source excerpts\n\n");
    output.push_str(
        "These are **verbatim original function expressions**, not runnable copies; \
        the complete original program and separately reconstructed lexical helpers \
        remain in the source-tree output. Excerpts are truncated when large.\n\n",
    );
    let mut seen = BTreeSet::new();
    for path in &view.paths {
        for (label, span) in path.functions.iter().zip(&path.function_spans) {
            if !seen.insert(*span) {
                continue;
            }
            let raw = original
                .get(span[0] as usize..span[1] as usize)
                .unwrap_or("");
            let excerpt = raw.chars().take(1600).collect::<String>();
            let clipped = raw.chars().count() > 1600;
            // Embedded source may contain Markdown fences inside JS strings
            // or comments. Always choose a fence longer than any original
            // backtick run, keeping the browsing view structurally intact.
            let max_run = excerpt
                .split(|ch| ch != '`')
                .map(str::len)
                .max()
                .unwrap_or(0);
            let fence = "`".repeat(3.max(max_run + 1));
            output.push_str(&format!(
                "### `{label}` — bytes {}..{}\n\n{fence}js\n{excerpt}\n{fence}\n\n",
                span[0], span[1]
            ));
            if clipped {
                output.push_str("*Excerpt truncated; follow the original source / helper implementation link for the complete function.*\n\n");
            }
        }
    }
    output
}

/// Discover exported member-assigned entry functions and their exact direct
/// lexical call chains. `entry_member` optionally narrows to one member name;
/// matching applies to AST property declarations, not arbitrary text.
pub fn reconstruct_caller_views(
    source: &str,
    entry_member: Option<&str>,
) -> Result<Vec<CallerView>> {
    let arena = Allocator::default();
    let parsed = parse_program(&arena, source, SourceType::unambiguous());
    ensure!(
        parsed.is_clean(),
        "caller view original JavaScript is invalid"
    );
    let semantics = SemanticBuilder::new().build(&parsed.program);
    let scoping = semantics.semantic.scoping();
    let mut finder = Definitions {
        functions: BTreeMap::new(),
        scoping,
    };
    finder.visit_program(&parsed.program);
    let mut symbols = BTreeMap::new();
    let mut ambiguous = BTreeSet::new();
    for (key, def) in &finder.functions {
        if let Some(symbol) = def.symbol {
            if symbols.insert(symbol, *key).is_some() {
                ambiguous.insert(symbol);
            }
        }
    }
    for symbol in ambiguous {
        symbols.remove(&symbol);
    }
    for symbol in symbols.keys().copied().collect::<Vec<_>>() {
        let writes = scoping
            .get_resolved_reference_ids(symbol)
            .iter()
            .filter(|reference| scoping.get_reference(**reference).is_write())
            .count();
        let declaration_assignment = finder
            .functions
            .get(&symbols[&symbol])
            .is_some_and(|definition| definition.initialized_by_assignment);
        // A single assignment can establish a previously declared function;
        // any additional write means the call target can vary at runtime.
        if writes > usize::from(declaration_assignment) {
            symbols.remove(&symbol);
        }
    }
    let mut collector = Calls {
        source,
        scoping,
        defs: &finder.functions,
        symbols: &symbols,
        stack: Vec::new(),
        edges: BTreeMap::new(),
    };
    collector.visit_program(&parsed.program);
    let mut views = Vec::new();
    for (root, def) in &finder.functions {
        if !def.member || entry_member.is_some_and(|name| def.label.trim_start_matches('.') != name)
        {
            continue;
        }
        let origin = (0..def.params.len()).map(Some).collect::<Vec<_>>();
        let mut walker = PathWalker {
            defs: &finder.functions,
            edges: &collector.edges,
            root: *root,
            output: Vec::new(),
        };
        walker.walk(
            *root,
            &origin,
            &mut vec![def.label.clone()],
            &mut vec![[root.0, root.1]],
            &mut Vec::new(),
            &mut BTreeSet::from([*root]),
        );
        let mut paths = walker.output;
        if paths.is_empty() {
            continue;
        }
        // Stable display ordering and bounded, meaningful entries.
        paths.sort_by(|a, b| a.functions.cmp(&b.functions));
        let mut view = CallerView {
            entry: def.label.clone(),
            entry_span: [root.0, root.1],
            paths,
            source: String::new(),
        };
        view.source = format_view(&view, source);
        views.push(view);
    }
    Ok(views)
}

#[cfg(test)]
mod tests {
    use super::reconstruct_caller_views;

    #[test]
    fn forwards_an_entry_parameter_through_new_and_call_by_resolved_symbols() -> anyhow::Result<()>
    {
        let source = r#"function app(){
            const deep=function(a,b){return b;};
            const Wd=function(x,y){return deep(y,x);};
            const AV={}; AV.aoF_=function(J,Q){return new Wd(Q,J);};
        }"#;
        let views = reconstruct_caller_views(source, Some("aoF_"))?;
        assert_eq!(views.len(), 1, "{views:?}");
        let path = views[0]
            .paths
            .iter()
            .find(|path| path.functions.last().is_some_and(|name| name == "deep"))
            .ok_or_else(|| anyhow::anyhow!("missing 3-function path"))?;
        assert_eq!(path.functions, vec![".aoF_", "Wd", "deep"]);
        assert_eq!(path.leaf_parameters[0].from_entry_index, Some(0));
        assert_eq!(path.leaf_parameters[1].from_entry_index, Some(1));
        assert!(views[0]
            .source
            .contains("`a` (parameter 0) ← entry `J` (parameter 0)"));
        Ok(())
    }

    #[test]
    fn arrow_functions_and_initialized_lexical_assignments_work() -> anyhow::Result<()> {
        let source = r#"let middle;middle=(x)=>last(x);
          const last=(y)=>y; const service={};service.run=(arg)=>middle(arg);"#;
        let views = reconstruct_caller_views(source, Some("run"))?;
        assert_eq!(views.len(), 1);
        let path = views[0]
            .paths
            .iter()
            .find(|p| p.functions.last().is_some_and(|x| x == "last"))
            .ok_or_else(|| anyhow::anyhow!("arrow call chain absent"))?;
        assert_eq!(path.leaf_parameters[0].from_entry_index, Some(0));
        Ok(())
    }

    #[test]
    fn rejects_mutated_parameter_as_certain_forwarding() -> anyhow::Result<()> {
        let source = r#"const deep=function(p){return p;};const Wd=function(x){x=3;return deep(x);};const api={};api.m=function(arg){return new Wd(arg);};"#;
        let views = reconstruct_caller_views(source, Some("m"))?;
        assert_eq!(views.len(), 1);
        let path = &views[0].paths[0];
        assert_eq!(path.leaf_parameters[0].from_entry_index, None);
        Ok(())
    }
}
