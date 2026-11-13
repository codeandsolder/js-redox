//! Ordered evaluation phases for long, nested JavaScript assignments.
//! No executable rewrite, inferred branch outcome or runtime trace.
use oxc_ast::ast::{
    AssignmentExpression, AssignmentTarget, ComputedMemberExpression, Expression, Program,
    SimpleAssignmentTarget,
};
use oxc_ast_visit::{walk, Visit};
use oxc_span::{GetSpan, Span};
use oxc_syntax::operator::AssignmentOperator;
use std::collections::BTreeSet;

use crate::source_tree_navigation::long_assignment_roots;

struct Phase {
    span: Span,
    kind: &'static str,
    detail: String,
    guards: Vec<String>,
}
struct Plan<'s> {
    source: &'s str,
    guards: Vec<String>,
    phases: Vec<Phase>,
}
impl<'s> Plan<'s> {
    fn new(source: &'s str) -> Self {
        Self {
            source,
            guards: Vec::new(),
            phases: Vec::new(),
        }
    }
    fn mark(&mut self, span: Span, kind: &'static str, detail: impl Into<String>) {
        self.phases.push(Phase {
            span,
            kind,
            detail: detail.into(),
            guards: self.guards.clone(),
        });
    }
    fn snippet(&self, span: Span) -> String {
        let text = self
            .source
            .get(span.start as usize..span.end as usize)
            .unwrap_or("");
        let single = text.split_whitespace().collect::<Vec<_>>().join(" ");
        if single.chars().count() > 64 {
            format!("{}…", single.chars().take(64).collect::<String>())
        } else {
            single
        }
    }
    fn opaque(&mut self, span: Span, kind: &str) {
        let snippet = self.snippet(span);
        self.mark(
            span,
            "opaque expression",
            format!("{kind}: {snippet}; internal effects/writes/throws unexpanded"),
        );
    }
    fn guarded(&mut self, guard: &str, f: impl FnOnce(&mut Self)) {
        self.guards.push(guard.to_owned());
        f(self);
        self.guards.pop();
    }
    fn computed_reference(&mut self, member: &ComputedMemberExpression<'_>) {
        self.expression(&member.object);
        self.expression(&member.expression);
        // The reference retains an uncoerced key. ToPropertyKey runs on
        // GetValue or PutValue, possibly after a simple assignment's RHS.
        self.mark(
            member.span,
            "form reference",
            "base + uncoerced key; property not yet read",
        );
    }

    fn assignment_key(target: &AssignmentTarget<'_>) -> Option<(Span, Span)> {
        match target {
            AssignmentTarget::ComputedMemberExpression(member) if !member.optional => {
                Some((member.object.span(), member.expression.span()))
            }
            _ => None,
        }
    }

    fn key_coercion(&mut self, key: Option<(Span, Span)>) {
        if let Some((base, key)) = key {
            // GetValue/PutValue first runs ToObject(base). A nullish base
            // throws before converting an object-valued property key.
            self.mark(base, "ToObject base", "throws for null/undefined");
            self.mark(
                key,
                "ToPropertyKey",
                "key conversion may invoke Symbol.toPrimitive or valueOf",
            );
        }
    }
    fn assignment_target(&mut self, target: &AssignmentTarget<'_>) -> bool {
        match target {
            AssignmentTarget::AssignmentTargetIdentifier(_) => {
                let name = self.snippet(target.span());
                self.mark(target.span(), "resolve reference", name);
            }
            AssignmentTarget::StaticMemberExpression(member) if !member.optional => {
                self.expression(&member.object);
                self.mark(
                    target.span(),
                    "form reference",
                    format!("static property .{}", member.property.name),
                );
            }
            AssignmentTarget::ComputedMemberExpression(member) if !member.optional => {
                self.computed_reference(member)
            }
            AssignmentTarget::PrivateFieldExpression(member) if !member.optional => {
                self.expression(&member.object);
                self.mark(
                    target.span(),
                    "form private reference",
                    "private-brand check",
                );
            }
            _ => return false,
        }
        true
    }
    fn simple_target(&mut self, target: &SimpleAssignmentTarget<'_>) -> bool {
        match target {
            SimpleAssignmentTarget::AssignmentTargetIdentifier(_) => {
                let name = self.snippet(target.span());
                self.mark(target.span(), "resolve reference", name);
            }
            SimpleAssignmentTarget::StaticMemberExpression(member) if !member.optional => {
                self.expression(&member.object);
                self.mark(
                    target.span(),
                    "form reference",
                    format!("static property .{}", member.property.name),
                );
            }
            SimpleAssignmentTarget::ComputedMemberExpression(member) if !member.optional => {
                self.computed_reference(member)
            }
            SimpleAssignmentTarget::PrivateFieldExpression(member) if !member.optional => {
                self.expression(&member.object);
                self.mark(
                    target.span(),
                    "form private reference",
                    "private-brand check",
                );
            }
            _ => return false,
        }
        true
    }
    fn assignment(&mut self, assign: &AssignmentExpression<'_>) {
        // Destructuring assigns AFTER RHS evaluation and requires iterator/
        // property semantics. Never portray it as a pre-RHS simple reference.
        let simple = matches!(
            &assign.left,
            AssignmentTarget::AssignmentTargetIdentifier(_)
                | AssignmentTarget::StaticMemberExpression(_)
                | AssignmentTarget::ComputedMemberExpression(_)
                | AssignmentTarget::PrivateFieldExpression(_)
        );
        if !simple {
            self.opaque(assign.span, "destructuring/extended assignment");
            return;
        }
        if !self.assignment_target(&assign.left) {
            self.opaque(assign.span, "extended assignment target");
            return;
        }
        let op = assign.operator;
        let key = Self::assignment_key(&assign.left);
        let target = self.snippet(assign.left.span());
        if !op.is_assign() {
            self.key_coercion(key);
        }
        if !op.is_assign() {
            self.mark(
                assign.left.span(),
                "GetValue target",
                format!("{target}; getter/dynamic resolution/TDZ can throw before RHS"),
            );
        }
        if op.is_logical() {
            let guard = match op {
                AssignmentOperator::LogicalAnd => "target truthy",
                AssignmentOperator::LogicalOr => "target falsy",
                AssignmentOperator::LogicalNullish => "target nullish",
                _ => unreachable!(),
            };
            self.guarded(guard, |plan| {
                plan.expression(&assign.right);
                // Re-convert the original reference's object-valued key for
                // PutValue; GetValue's conversion was not cached into it.
                plan.key_coercion(key);
                plan.mark(
                    assign.left.span(),
                    "PutValue target",
                    format!("{target} {} (setter may run)", op.as_str()),
                );
            });
        } else {
            self.expression(&assign.right);
            if op.is_assign() {
                self.key_coercion(key);
            }
            if !op.is_assign() {
                self.mark(assign.span, "apply assignment operator", op.as_str());
                self.key_coercion(key);
            }
            self.mark(
                assign.left.span(),
                "PutValue target",
                format!("{target} {} (setter may run)", op.as_str()),
            );
        }
    }
    fn expression(&mut self, expr: &Expression<'_>) {
        match expr {
            Expression::ParenthesizedExpression(paren) => self.expression(&paren.expression),
            Expression::SequenceExpression(sequence) => {
                for item in &sequence.expressions {
                    self.expression(item);
                }
            }
            Expression::AssignmentExpression(assign) => self.assignment(assign),
            Expression::ConditionalExpression(cond) => {
                self.expression(&cond.test);
                self.guarded("test truthy", |p| p.expression(&cond.consequent));
                self.guarded("test falsy", |p| p.expression(&cond.alternate));
            }
            Expression::LogicalExpression(logical) => {
                self.expression(&logical.left);
                let guard = match logical.operator.as_str() {
                    "&&" => "left truthy",
                    "||" => "left falsy",
                    "??" => "left nullish",
                    _ => "logical branch",
                };
                self.guarded(guard, |p| p.expression(&logical.right));
            }
            Expression::BinaryExpression(binary) => {
                self.expression(&binary.left);
                self.expression(&binary.right);
                self.mark(
                    binary.span,
                    "apply binary operator",
                    format!(
                        "{} (coercion follows both operands)",
                        binary.operator.as_str()
                    ),
                );
            }
            Expression::StaticMemberExpression(member) if !member.optional => {
                self.expression(&member.object);
                self.mark(
                    member.span,
                    "GetValue member",
                    format!(
                        "property .{} (getter/Proxy trap may run)",
                        member.property.name
                    ),
                );
            }
            Expression::ComputedMemberExpression(member) if !member.optional => {
                self.computed_reference(member);
                self.key_coercion(Some((member.object.span(), member.expression.span())));
                self.mark(member.span, "GetValue member", "getter/Proxy trap may run");
            }
            Expression::PrivateFieldExpression(member) if !member.optional => {
                self.expression(&member.object);
                self.mark(member.span, "GetValue private field", "private-brand check");
            }
            Expression::Identifier(id) => {
                self.mark(id.span, "GetValue identifier", id.name.to_string());
            }
            Expression::UpdateExpression(update) => {
                if self.simple_target(&update.argument) {
                    if let SimpleAssignmentTarget::ComputedMemberExpression(member) =
                        &update.argument
                    {
                        self.key_coercion(Some((member.object.span(), member.expression.span())));
                    }
                    self.mark(update.argument.span(), "GetValue target", "getter may run");
                    self.mark(update.span, "numeric update", update.operator.as_str());
                    if let SimpleAssignmentTarget::ComputedMemberExpression(member) =
                        &update.argument
                    {
                        self.key_coercion(Some((member.object.span(), member.expression.span())));
                    }
                    self.mark(update.argument.span(), "PutValue target", "setter may run");
                } else {
                    self.opaque(update.span, "extended update expression");
                }
            }
            // Unary delete/typeof, calls, optional chains, constructors,
            // object/array literals, templates, deferred function bodies, etc.
            // remain one opaque phase, even if they contain nested writes.
            _ => self.opaque(expr.span(), "unexpanded AST subtree"),
        }
    }
}
struct Collector<'s> {
    source: &'s str,
    roots: BTreeSet<(u32, u32)>,
    sections: Vec<(Span, Vec<Phase>)>,
}
impl<'a> Visit<'a> for Collector<'_> {
    fn visit_assignment_expression(&mut self, assign: &AssignmentExpression<'a>) {
        if self.roots.contains(&(assign.span.start, assign.span.end)) {
            let mut plan = Plan::new(self.source);
            plan.assignment(assign);
            self.sections.push((assign.span, plan.phases));
        }
        walk::walk_assignment_expression(self, assign);
    }
}
fn cell(s: &str) -> String {
    s.replace('|', "\\|")
        .replace(['\n', '\r'], " ")
        .replace(char::from(96), "'")
}
fn line_col(source: &str, start: usize) -> (usize, usize) {
    let pre = source.get(..start).unwrap_or("");
    (
        pre.bytes().filter(|b| *b == b'\n').count() + 1,
        pre.rsplit('\n').next().unwrap_or("").chars().count() + 1,
    )
}
pub(super) fn ordered_assignment_phases(source: &str, program: &Program<'_>) -> Option<String> {
    let roots = long_assignment_roots(source, program);
    if roots.is_empty() {
        return None;
    }
    let mut collector = Collector {
        source,
        roots,
        sections: Vec::new(),
    };
    collector.visit_program(program);
    if collector.sections.is_empty() {
        return None;
    }
    let mut out = String::from(
        "# Ordered evaluation phases of nested assignments\n\n\
         This is a **static phase plan**, not an observed trace or executable \
         rewrite. Rows are ordered only **within one possible path**; guarded \
         alternative arms are mutually exclusive, and any phase may throw. \
         Opaque expressions may contain nested calls, writes, getters, \
         coercions and exceptions: their internal order is not expanded. \
         The separate assignment outline shows AST containment. A simple \
         assignment evaluates its target reference before RHS without \
         reading its target property, then PutValue may invoke a setter. \
         A computed member reference retains an uncoerced key; ToPropertyKey \
         occurs separately at GetValue and PutValue. Simple assignment \
         converts after RHS at PutValue. Compound/logical assignments convert \
         before RHS at GetValue and AGAIN after RHS at PutValue; the same \
         object key can yield different names. Logical assignments gate \
         RHS/PutValue. \
         Spans refer to the derived readable helper, not the captured source.\n\n",
    );
    collector.sections.sort_by_key(|(span, _)| span.start);
    for (root, phases) in &collector.sections {
        let (line, col) = line_col(source, root.start as usize);
        out.push_str(&format!(
            "## Assignment at {line}:{col} (source bytes {}–{})\n\n",
            root.start, root.end
        ));
        out.push_str(
            "| Phase | Path guard | Step | Details | Source bytes |\n|---:|---|---|---|---|\n",
        );
        for (i, phase) in phases.iter().enumerate() {
            let guard = if phase.guards.is_empty() {
                "unguarded".to_owned()
            } else {
                phase.guards.join(" and ")
            };
            out.push_str(&format!(
                "| {} | {} | {} | {} | {}–{} |\n",
                i + 1,
                cell(&guard),
                phase.kind,
                cell(&phase.detail),
                phase.span.start,
                phase.span.end
            ));
        }
        out.push('\n');
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::ordered_assignment_phases;
    use oxc_allocator::Allocator;
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;

    fn plan(source: &str) -> String {
        let arena = Allocator::default();
        let parsed = parse_program(&arena, source, SourceType::unambiguous());
        assert!(parsed.is_clean(), "{source}");
        let result = ordered_assignment_phases(source, &parsed.program);
        assert!(result.is_some(), "{source}");
        result.unwrap_or_default()
    }

    fn long_effects() -> String {
        (0..24)
            .map(|index| format!("side.member{index}={index}"))
            .collect::<Vec<_>>()
            .join(",")
    }

    fn position(text: &str, fragment: &str) -> usize {
        let index = text.find(fragment);
        assert!(index.is_some(), "missing {fragment} in {text}");
        index.unwrap_or(usize::MAX)
    }

    #[test]
    fn computed_target_coercion_waits_until_simple_assignment_putvalue() {
        let code = format!(
            "function f(obj,key,rhs,inner,side){{\
             outer = obj[key()] = (inner.x = rhs(), {});}}",
            long_effects()
        );
        let phases = plan(&code);
        let key_call = position(&phases, "key()");
        let to_property_key = position(&phases, "| ToPropertyKey |");
        let nested_target = position(&phases, "static property .x");
        let rhs_call = position(&phases, "rhs()");
        let nested_write = position(&phases, "inner.x = (setter may run)");
        let outer_write = position(&phases, "obj[key()] = (setter may run)");
        assert!(
            key_call < nested_target
                && nested_target < rhs_call
                && rhs_call < nested_write
                && nested_write < to_property_key
                && to_property_key < outer_write,
            "{phases}"
        );
    }

    #[test]
    fn compound_assignment_reads_before_rhs_and_putvalue() {
        let code = format!(
            "function f(obj,side){{root=obj.value += (side.effect=1,{});}}",
            long_effects()
        );
        let phases = plan(&code);
        let get = position(&phases, "obj.value; getter/dynamic resolution");
        let rhs = position(&phases, "side.effect = (setter may run)");
        let operator = position(&phases, "| apply assignment operator | += |");
        let put = position(&phases, "obj.value += (setter may run)");
        assert!(get < rhs && rhs < operator && operator < put, "{phases}");
    }

    #[test]
    fn logical_assignment_marks_conditional_rhs_and_setter() {
        let code = format!(
            "function f(obj,side){{root=obj.value &&= (side.effect=1,{});}}",
            long_effects()
        );
        let phases = plan(&code);
        let get = position(&phases, "obj.value; getter/dynamic resolution");
        let rhs = position(&phases, "| target truthy |");
        let put = position(&phases, "obj.value &&= (setter may run)");
        assert!(get < rhs && rhs < put, "{phases}");
        assert!(
            !phases.contains("| apply assignment operator | &&="),
            "{phases}"
        );
    }

    #[test]
    fn conditional_assignments_are_different_paths() {
        let code = format!(
            "function f(obj,side,flag){{root=flag?(obj.left=1):(obj.right=2,{});}}",
            long_effects()
        );
        let phases = plan(&code);
        assert!(phases.contains("| test truthy |"), "{phases}");
        assert!(phases.contains("| test falsy |"), "{phases}");
        let left = position(&phases, "obj.left = (setter may run)");
        let right = position(&phases, "obj.right = (setter may run)");
        assert!(left < right, "{phases}");
    }

    #[test]
    fn arbitrary_call_and_destructuring_are_opaque_not_fabricated() {
        let call = format!(
            "function f(obj,side){{root = call((obj.inner=1), {});}}",
            long_effects()
        );
        let phases = plan(&call);
        assert!(phases.contains("opaque expression"), "{phases}");
        assert!(!phases.contains("obj.inner = (setter may run)"), "{phases}");
        let destructuring = format!(
            "function f(obj,side){{([obj.x,obj.y] = (side.inner=1,{}));}}",
            long_effects()
        );
        let phases = plan(&destructuring);
        assert!(
            phases.contains("destructuring/extended assignment"),
            "{phases}"
        );
        assert!(
            !phases.contains("side.inner = (setter may run)"),
            "{phases}"
        );
    }

    #[test]
    fn computed_compound_and_logical_assignment_convert_key_before_rhs() {
        for operator in ["+=", "&&=", "??="] {
            let source = format!(
                "function f(obj,key,side){{root = obj[key()] {operator} (side.effect=1,{});}}",
                long_effects()
            );
            let phases = plan(&source);
            let key_call = position(&phases, "key()");
            let to_object = position(&phases, "| ToObject base |");
            let key_coercion = position(&phases, "| ToPropertyKey |");
            let target_get = position(&phases, "obj[key()]; getter/dynamic resolution");
            let rhs = position(&phases, "side.effect = (setter may run)");
            let second_key_coercion = phases.rfind("| ToPropertyKey |").unwrap_or(usize::MAX);
            let put = position(&phases, &format!("obj[key()] {operator} (setter may run)"));
            assert!(
                key_call < to_object
                    && to_object < key_coercion
                    && key_coercion < target_get
                    && target_get < rhs
                    && rhs < second_key_coercion
                    && second_key_coercion < put,
                "{operator}: {phases}"
            );
            if operator != "+=" {
                assert!(phases.contains("| target "), "{phases}");
            }
        }
    }

    #[test]
    fn computed_member_get_coerces_before_outer_rhs() {
        let source = format!(
            "function f(obj,key,side){{root=(obj[key()]+1)+(side.effect=1,{});}}",
            long_effects()
        );
        let phases = plan(&source);
        let to_object = position(&phases, "| ToObject base |");
        let key_coercion = position(&phases, "| ToPropertyKey |");
        let read = position(&phases, "| GetValue member |");
        let rhs = position(&phases, "side.effect = (setter may run)");
        assert!(
            to_object < key_coercion && key_coercion < read && read < rhs,
            "{phases}"
        );
    }

    #[test]
    #[ignore = "requires installed Node; differential runtime oracle"]
    fn node_confirms_computed_key_getvalue_vs_putvalue_coercion_order() -> anyhow::Result<()> {
        use std::process::Command;
        let script = r#"
const result = [];
function run(mode) {
  const events = [];
  const object = new Proxy({p:2}, {
    get(o,k){events.push('get:'+k);return Reflect.get(o,k)},
    set(o,k,v){events.push('set:'+k);return Reflect.set(o,k,v)}
  });
  const key = () => {
    events.push('key-expr');
    return {[Symbol.toPrimitive](){events.push('key-coercion');return 'p'}};
  };
  function rhs(){events.push('rhs');return 3}
  if(mode==='simple') object[key()] = rhs();
  if(mode==='compound') object[key()] += rhs();
  if(mode==='logical') object[key()] &&= rhs();
  if(mode==='nullish') { const o = null; try {o[key()] = rhs()} catch {events.push('throw')} }
  result.push(events);
}
for(const mode of ['simple','compound','logical','nullish'])run(mode);
console.log(JSON.stringify(result));
"#;
        let output = Command::new("node").arg("-e").arg(script).output()?;
        assert!(output.status.success(), "{output:?}");
        let actual: serde_json::Value = serde_json::from_slice(&output.stdout)?;
        assert_eq!(
            actual,
            serde_json::json!([
                ["key-expr", "rhs", "key-coercion", "set:p"],
                [
                    "key-expr",
                    "key-coercion",
                    "get:p",
                    "rhs",
                    "key-coercion",
                    "set:p"
                ],
                [
                    "key-expr",
                    "key-coercion",
                    "get:p",
                    "rhs",
                    "key-coercion",
                    "set:p"
                ],
                ["key-expr", "rhs", "throw"]
            ])
        );
        Ok(())
    }
}
