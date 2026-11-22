//! Proof-bounded correspondence between a concrete debugger pause and an AST
//! control guard in the exact original script. Never specialize the shared JS.
use super::{verified_sha, RuntimeIdentityIndex};
use crate::{
    runtime_identity::script_id_text, source_text::SourceLineIndex,
    trace_identity::same_observed_call_stack,
};
use anyhow::Result;
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    ConditionalExpression, DoWhileStatement, ForStatement, IfStatement, WhileStatement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_parser::Parser;
use oxc_span::{GetSpan, SourceType, Span};
use serde_json::{json, Value};
use std::{collections::HashMap, fs, path::Path};
use work_budget::WorkBudget;

#[derive(Clone, Copy)]
struct Guard {
    kind: &'static str,
    site: Span,
    test: Span,
    consequent: Option<Span>,
    alternate: Option<Span>,
}

#[derive(Default)]
struct Guards(Vec<Guard>);

impl<'a> Visit<'a> for Guards {
    fn visit_if_statement(&mut self, node: &IfStatement<'a>) {
        self.0.push(Guard {
            kind: "if",
            site: node.span(),
            test: node.test.span(),
            consequent: Some(node.consequent.span()),
            alternate: node.alternate.as_ref().map(GetSpan::span),
        });
        walk::walk_if_statement(self, node);
    }
    fn visit_conditional_expression(&mut self, node: &ConditionalExpression<'a>) {
        self.0.push(Guard {
            kind: "ternary",
            site: node.span(),
            test: node.test.span(),
            consequent: Some(node.consequent.span()),
            alternate: Some(node.alternate.span()),
        });
        walk::walk_conditional_expression(self, node);
    }
    fn visit_while_statement(&mut self, node: &WhileStatement<'a>) {
        self.0.push(Guard {
            kind: "while",
            site: node.span(),
            test: node.test.span(),
            consequent: Some(node.body.span()),
            alternate: None,
        });
        walk::walk_while_statement(self, node);
    }
    fn visit_do_while_statement(&mut self, node: &DoWhileStatement<'a>) {
        self.0.push(Guard {
            kind: "do_while",
            site: node.span(),
            test: node.test.span(),
            consequent: Some(node.body.span()),
            alternate: None,
        });
        walk::walk_do_while_statement(self, node);
    }
    fn visit_for_statement(&mut self, node: &ForStatement<'a>) {
        if let Some(test) = node.test.as_ref() {
            self.0.push(Guard {
                kind: "for",
                site: node.span(),
                test: test.span(),
                consequent: Some(node.body.span()),
                alternate: None,
            });
        }
        walk::walk_for_statement(self, node);
    }
}

fn parse_guards(source: &str) -> Option<Vec<Guard>> {
    let allocator = Allocator::default();
    for mode in [SourceType::mjs(), SourceType::cjs()] {
        let parsed = Parser::new(&allocator, source, mode).parse();
        if !parsed.fatal_error && parsed.diagnostics.is_empty() {
            let mut visitor = Guards::default();
            visitor.visit_program(&parsed.program);
            return Some(visitor.0);
        }
    }
    None
}

struct GuardSource {
    source: String,
    lines: SourceLineIndex,
    guards: Vec<Guard>,
}

fn top_frame(step: &Value) -> Option<&Value> {
    step.get("frames")?.as_array()?.first()
}

/// Only the original captured source, exact (CDP session, script, SHA), and
/// observations at the guard's executing pause can produce a guard witness.
/// A next pause in an AST arm is additional evidence, never a claim about all
/// possible inputs or a complete path.
pub(super) fn observe(
    project: &Path,
    identities: &RuntimeIdentityIndex,
    session: Option<&str>,
    steps: &[Value],
    budget: &WorkBudget,
) -> Result<Vec<Value>> {
    let Some(session) = session else {
        return Ok(Vec::new());
    };
    let mut by_sha: HashMap<String, Option<GuardSource>> = HashMap::new();
    let mut out = Vec::new();
    for (step_index, step) in steps.iter().enumerate() {
        budget.consume(1)?;
        let Some(frame) = top_frame(step) else {
            continue;
        };
        if frame.get("source_identity").and_then(Value::as_str) != Some("exact") {
            continue;
        }
        let Some(script) = frame.pointer("/location/scriptId").and_then(script_id_text) else {
            continue;
        };
        let Some(sha) = frame.get("sourceSha256").and_then(verified_sha) else {
            continue;
        };
        let Some(identity) = identities.get(session, &script) else {
            continue;
        };
        if identity.sha256 != sha || identity.capture_instrumentation != Some(false) {
            continue;
        }
        let (Some(start_line), Some(start_column)) = (identity.start_line, identity.start_column)
        else {
            continue;
        };
        let (Some(line), Some(column)) = (
            frame
                .pointer("/location/lineNumber")
                .and_then(Value::as_u64),
            frame
                .pointer("/location/columnNumber")
                .and_then(Value::as_u64),
        ) else {
            continue;
        };
        if !by_sha.contains_key(sha) {
            let bytes = fs::read(project.join(format!("resources/runtime-scripts/{sha}.js")))?;
            if super::sha256_hex(&bytes) != sha {
                anyhow::bail!("observed guard original source hash mismatch {sha}");
            }
            budget.consume(u64::try_from(bytes.len().div_ceil(1024)).unwrap_or(u64::MAX))?;
            budget.checkpoint()?;
            let source = String::from_utf8(bytes)?;
            let guards = parse_guards(&source);
            budget.checkpoint()?;
            by_sha.insert(
                sha.to_owned(),
                guards.map(|guards| GuardSource {
                    lines: SourceLineIndex::new(&source),
                    source,
                    guards,
                }),
            );
        }
        let Some(Some(GuardSource {
            source,
            lines,
            guards,
        })) = by_sha.get(sha)
        else {
            continue;
        };
        let Some(position) = lines.cdp_byte_offset(source, line, column, start_line, start_column)
        else {
            continue;
        };
        for expression in step
            .get("expressions")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            if expression.get("status").and_then(Value::as_str) != Some("observed")
                || expression.pointer("/value/type").and_then(Value::as_str) != Some("boolean")
            {
                continue;
            }
            let (Some(condition), Some(value)) = (
                expression.get("expression").and_then(Value::as_str),
                expression.pointer("/value/value").and_then(Value::as_bool),
            ) else {
                continue;
            };
            budget.consume(u64::try_from(guards.len()).unwrap_or(u64::MAX))?;
            let matches: Vec<&Guard> = guards
                .iter()
                .filter(|guard| {
                    let test = guard.test;
                    let site = guard.site;
                    site.start as usize <= position
                        && position <= test.end as usize
                        && source
                            .get(test.start as usize..test.end as usize)
                            .is_some_and(|code| code.trim() == condition.trim())
                })
                .collect();
            // Multiple equally matching guards are ambiguous.
            let [guard] = matches.as_slice() else {
                continue;
            };
            let mut next_pause_arm = None;
            if let Some(next) = steps
                .get(step_index + 1)
                .filter(|next| same_observed_call_stack(step, next))
            {
                if let Some(next_frame) = top_frame(next) {
                    let next_script = next_frame
                        .pointer("/location/scriptId")
                        .and_then(script_id_text);
                    let next_sha = next_frame.get("sourceSha256").and_then(Value::as_str);
                    let next_line = next_frame
                        .pointer("/location/lineNumber")
                        .and_then(Value::as_u64);
                    let next_column = next_frame
                        .pointer("/location/columnNumber")
                        .and_then(Value::as_u64);
                    if next_script.as_deref() == Some(script.as_ref()) && next_sha == Some(sha) {
                        if let (Some(line), Some(column)) = (next_line, next_column) {
                            if let Some(at) = lines.cdp_byte_offset(
                                source,
                                line,
                                column,
                                start_line,
                                start_column,
                            ) {
                                let arm = if value {
                                    guard.consequent
                                } else {
                                    guard.alternate
                                };
                                if arm.is_some_and(|span| {
                                    span.start as usize <= at && at < span.end as usize
                                }) {
                                    next_pause_arm =
                                        Some(if value { "consequent" } else { "alternate" });
                                }
                            }
                        }
                    }
                }
            }
            out.push(json!({
                "step_index":step_index, "kind":guard.kind,
                "script_id":script, "source_sha256":sha,
                "guard_start_byte":guard.site.start, "test_start_byte":guard.test.start,
                "test_end_byte":guard.test.end,
                "expression":condition, "observed_value":value,
                "next_pause_in_selected_arm":next_pause_arm,
                "evidence":"exact_source_ast_and_boolean_pause",
                "concrete_observation_only":true, "complete_execution_path":false,
            }));
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_boolean_guard_and_next_selected_arm_are_distinct_evidence() -> Result<()> {
        use tempfile::TempDir;

        let temp = TempDir::new()?;
        let project = temp.path();
        fs::create_dir_all(project.join("resources/runtime-scripts"))?;
        let source = "function f(value) {\n  if (value === 34) return 42; else return -1;\n}\n";
        let sha = crate::sha256_hex(source.as_bytes());
        fs::write(
            project.join(format!("resources/runtime-scripts/{sha}.js")),
            source,
        )?;
        let mut identities = RuntimeIdentityIndex::default();
        identities.register(
            "main",
            "7",
            super::super::RuntimeSourceIdentity {
                sha256: sha.clone(),
                start_line: Some(10),
                start_column: Some(0),
                capture_instrumentation: Some(false),
                origin: crate::runtime_identity::ScriptOriginContext {
                    url: None,
                    execution_context_id: None,
                },
            },
        );
        let frame = |col| {
            json!({
                "functionName":"f",
                "functionLocation":{"scriptId":"7","lineNumber":10,"columnNumber":0},
                "location":{"scriptId":"7","lineNumber":11,"columnNumber":col},
                "source_identity":"exact", "sourceSha256":sha,
            })
        };
        let guard = json!({
            "frames":[frame(2)],
            "expressions":[{"expression":"value === 34","status":"observed",
                            "value":{"type":"boolean","value":true}}]
        });
        let consequent = json!({"frames":[frame(20)], "expressions":[]});
        let budget = crate::analysis_budget::AnalysisBudgets::standard("guard-test").scope("guard");
        let witnesses = observe(
            project,
            &identities,
            Some("main"),
            &[guard.clone(), consequent],
            &budget,
        )?;
        assert_eq!(witnesses.len(), 1);
        assert_eq!(witnesses[0]["kind"], "if");
        assert_eq!(witnesses[0]["observed_value"], true);
        assert_eq!(witnesses[0]["next_pause_in_selected_arm"], "consequent");
        assert_eq!(witnesses[0]["complete_execution_path"], false);

        let mut false_guard = guard.clone();
        false_guard["expressions"][0]["value"]["value"] = json!(false);
        let else_column = source
            .lines()
            .nth(1)
            .and_then(|line| line.find("return -1"))
            .ok_or_else(|| anyhow::anyhow!("test alternate not found"))?;
        let alternate = json!({"frames":[frame(else_column)], "expressions":[]});
        let false_witnesses = observe(
            project,
            &identities,
            Some("main"),
            &[false_guard, alternate],
            &budget,
        )?;
        assert_eq!(
            false_witnesses[0]["next_pause_in_selected_arm"],
            "alternate"
        );

        // A side-effect-checked value alone is not a witnessed taken arm.
        let none = observe(
            project,
            &identities,
            Some("main"),
            std::slice::from_ref(&guard),
            &budget,
        )?;
        assert!(none[0]["next_pause_in_selected_arm"].is_null());

        // Inspector expressions unrelated to the actual AST test are not guards.
        let mut unrelated = guard.clone();
        unrelated["expressions"][0]["expression"] = json!("value !== 34");
        assert_eq!(
            observe(project, &identities, Some("main"), &[unrelated], &budget)?.len(),
            0
        );

        // No source-triple identity: no path claims.
        let mut unresolved = guard;
        unresolved["frames"][0]["source_identity"] = json!("unresolved");
        assert_eq!(
            observe(project, &identities, Some("main"), &[unresolved], &budget)?.len(),
            0
        );
        Ok(())
    }

    #[test]
    fn guards_detect_all_conditional_control_constructs() -> Result<()> {
        let code = "if (a) x(); else y();\nwhile (b) x();\ndo x(); while (c);\nfor (;d;) x();\nconst k = e ? 1 : 2;";
        let guards = parse_guards(code).ok_or_else(|| anyhow::anyhow!("parse failed"))?;
        assert_eq!(
            guards.iter().map(|g| g.kind).collect::<Vec<_>>(),
            ["if", "while", "do_while", "for", "ternary"]
        );
        Ok(())
    }
}
