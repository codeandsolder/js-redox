use anyhow::{Context, Result};
use jsvm_lift::state_flatten::{
    prove_function_if_ladder_states_before_event,
    prove_function_protected_if_ladder_event_unreachable_after_state,
    prove_function_structured_branch_event_unreachable_with_integer_parameters,
    structurally_proven_if_ladder_identifier_equalities_at_event,
};
use oxc_allocator::Allocator;
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::SemanticBuilder;
use oxc_span::{GetSpan, SourceType, Span};
use rolldown_redox::ecmascript::parse_program;
use serde_json::json;
use std::{collections::BTreeMap, env, fs, path::PathBuf};

fn arg_u32(args: &[std::ffi::OsString], prefix: &str) -> Result<u32> {
    args.iter()
        .find_map(|arg| arg.to_str()?.strip_prefix(prefix)?.parse::<u32>().ok())
        .with_context(|| format!("missing {prefix}<u32>"))
}

fn main() -> Result<()> {
    let args = env::args_os().skip(1).collect::<Vec<_>>();
    let path = args
        .iter()
        .find(|arg| !arg.to_string_lossy().starts_with("--"))
        .map(PathBuf::from)
        .context("missing JavaScript file")?;
    let function_start = arg_u32(&args, "--function-start=")?;
    let function_end = arg_u32(&args, "--function-end=")?;
    let event_start = arg_u32(&args, "--event-start=")?;
    let event_end = arg_u32(&args, "--event-end=")?;
    let identifier_equalities = args.iter().any(|arg| arg == "--identifier-equalities");
    let branch_ancestry = args.iter().any(|arg| arg == "--branch-ancestry");
    let structured_branch_unreachable = args
        .iter()
        .any(|arg| arg == "--structured-branch-unreachable");
    let integer_parameters = args
        .iter()
        .filter_map(|arg| {
            let value = arg.to_str()?.strip_prefix("--int-param=")?;
            let (index, value) = value.split_once(':')?;
            Some((index.parse::<usize>().ok()?, value.parse::<i64>().ok()?))
        })
        .collect::<BTreeMap<_, _>>();
    let after_state = args.iter().find_map(|arg| {
        arg.to_str()?
            .strip_prefix("--unreachable-after-state=")?
            .parse::<u64>()
            .ok()
    });
    let required_states = args
        .iter()
        .filter_map(|arg| {
            arg.to_str()?
                .strip_prefix("--required-state=")?
                .parse::<u64>()
                .ok()
        })
        .collect::<Vec<_>>();
    anyhow::ensure!(
        !required_states.is_empty()
            || identifier_equalities
            || after_state.is_some()
            || structured_branch_unreachable
            || branch_ancestry,
        "missing proof query (--required-state, --identifier-equalities, --unreachable-after-state, or --structured-branch-unreachable)"
    );

    let source =
        fs::read_to_string(&path).with_context(|| format!("reading {}", path.display()))?;
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, &source, SourceType::cjs());
    anyhow::ensure!(
        parsed.diagnostics == 0 && !parsed.fatal_error,
        "parse diagnostics"
    );
    let event = Span::new(event_start, event_end);
    let proven = (!required_states.is_empty()).then(|| {
        prove_function_if_ladder_states_before_event(
            &source,
            &parsed.program,
            function_start,
            function_end,
            &required_states,
            event,
        )
    });
    let unreachable_after_state = after_state.map(|state| {
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .build(&parsed.program);
        prove_function_protected_if_ladder_event_unreachable_after_state(
            &source,
            &parsed.program,
            &semantic.semantic,
            function_start,
            function_end,
            state,
            event,
        )
    });
    let structured_branch = structured_branch_unreachable.then(|| {
        let semantic = SemanticBuilder::new().build(&parsed.program);
        prove_function_structured_branch_event_unreachable_with_integer_parameters(
            &parsed.program,
            semantic.semantic.scoping(),
            function_start,
            function_end,
            event,
            &integer_parameters,
        )
    });
    let parameter_writes = if branch_ancestry {
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .build(&parsed.program);
        let scoping = semantic.semantic.scoping();
        struct Params<'s> {
            function_start: u32,
            function_end: u32,
            scoping: &'s oxc_semantic::Scoping,
            nodes: &'s oxc_semantic::AstNodes<'s>,
            output: Vec<serde_json::Value>,
        }
        impl<'a> Visit<'a> for Params<'_> {
            fn visit_function(
                &mut self,
                function: &oxc_ast::ast::Function<'a>,
                flags: oxc_syntax::scope::ScopeFlags,
            ) {
                if function.span.start == self.function_start
                    && function.span.end == self.function_end
                {
                    for (index, parameter) in function.params.items.iter().enumerate() {
                        let oxc_ast::ast::BindingPattern::BindingIdentifier(identifier) =
                            &parameter.pattern
                        else {
                            continue;
                        };
                        let Some(symbol) = identifier.symbol_id.get() else {
                            continue;
                        };
                        let writes = self
                            .scoping
                            .get_resolved_reference_ids(symbol)
                            .iter()
                            .filter_map(|reference_id| {
                                let reference = self.scoping.get_reference(*reference_id);
                                reference.is_write().then(|| {
                                    let span =
                                        self.nodes.get_node(reference.node_id()).kind().span();
                                    json!([span.start, span.end])
                                })
                            })
                            .collect::<Vec<_>>();
                        self.output.push(json!({
                            "index": index,
                            "name": identifier.name.as_str(),
                            "declaration": [identifier.span.start, identifier.span.end],
                            "writes": writes,
                        }));
                    }
                    return;
                }
                walk::walk_function(self, function, flags);
            }
        }
        let mut params = Params {
            function_start,
            function_end,
            scoping,
            nodes: semantic.semantic.nodes(),
            output: Vec::new(),
        };
        params.visit_program(&parsed.program);
        params.output
    } else {
        Vec::new()
    };
    let branch_guards = if branch_ancestry {
        struct Probe<'s> {
            source: &'s str,
            event: Span,
            guards: Vec<serde_json::Value>,
        }
        impl Probe<'_> {
            fn contains(span: Span, event: Span) -> bool {
                span.start <= event.start && event.end <= span.end
            }
            fn snippet(&self, span: Span) -> String {
                self.source
                    .get(span.start as usize..span.end as usize)
                    .unwrap_or_default()
                    .split_whitespace()
                    .collect::<Vec<_>>()
                    .join(" ")
            }
        }
        impl<'a> Visit<'a> for Probe<'_> {
            fn visit_logical_expression(
                &mut self,
                expression: &oxc_ast::ast::LogicalExpression<'a>,
            ) {
                if Self::contains(expression.span, self.event) {
                    self.guards.push(json!({
                        "kind": "logical",
                        "span": [expression.span.start, expression.span.end],
                        "operator": expression.operator.as_str(),
                        "left": self.snippet(expression.left.span()),
                        "right_contains_event": Self::contains(expression.right.span(), self.event),
                    }));
                }
                walk::walk_logical_expression(self, expression);
            }
            fn visit_if_statement(&mut self, statement: &oxc_ast::ast::IfStatement<'a>) {
                if Self::contains(statement.span, self.event) {
                    self.guards.push(json!({
                        "kind": "if",
                        "span": [statement.span.start, statement.span.end],
                        "test": self.snippet(statement.test.span()),
                    }));
                }
                walk::walk_if_statement(self, statement);
            }
            fn visit_conditional_expression(
                &mut self,
                expression: &oxc_ast::ast::ConditionalExpression<'a>,
            ) {
                if Self::contains(expression.span, self.event) {
                    self.guards.push(json!({
                        "kind": "conditional",
                        "span": [expression.span.start, expression.span.end],
                        "test": self.snippet(expression.test.span()),
                    }));
                }
                walk::walk_conditional_expression(self, expression);
            }
        }
        // The probe is span-based; nested function guards cannot contain an event span from another function.
        let mut probe = Probe {
            source: &source,
            event,
            guards: Vec::new(),
        };
        probe.visit_program(&parsed.program);
        probe.guards
    } else {
        Vec::new()
    };
    let equalities = if identifier_equalities {
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .build(&parsed.program);
        let scoping = semantic.semantic.scoping();
        structurally_proven_if_ladder_identifier_equalities_at_event(
            &source,
            &parsed.program,
            &semantic.semantic,
            function_start,
            function_end,
            event,
        )
        .into_iter()
        .map(|proof| {
            json!({
                "state": proof.state,
                "assignment": [proof.assignment_start, proof.assignment_end],
                "left": scoping.symbol_name(proof.left_symbol),
                "right": scoping.symbol_name(proof.right_symbol),
            })
        })
        .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "function": [function_start, function_end],
            "event": [event_start, event_end],
            "required_states": required_states,
            "proven": proven,
            "identifier_equalities": equalities,
            "unreachable_after_state": unreachable_after_state,
            "structured_branch_unreachable": structured_branch,
            "integer_parameters": integer_parameters,
            "branch_ancestry": branch_guards,
            "parameter_writes": parameter_writes,
        }))?
    );
    Ok(())
}
