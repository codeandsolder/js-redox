//! Ordered evaluation phases for long, nested JavaScript assignments.
//! No executable rewrite, inferred branch outcome or runtime trace.
use oxc_ast::ast::{
    Argument, ArrayExpression, ArrayExpressionElement, AssignmentExpression, AssignmentTarget,
    CallExpression, ChainElement, ChainExpression, ComputedMemberExpression, Expression,
    MemberExpression, NewExpression, ObjectExpression, ObjectPropertyKind, Program,
    SimpleAssignmentTarget, TaggedTemplateExpression, TemplateLiteral, UnaryExpression,
};
use oxc_ast_visit::{walk, Visit};
use oxc_span::{GetSpan, Span};
use oxc_syntax::operator::{AssignmentOperator, UnaryOperator};
use std::collections::BTreeSet;
use std::fmt::Write as _;

use crate::{
    report_markdown::literal_text,
    source_text::{collapsed_whitespace, SourceLineIndex},
    source_tree_navigation::long_assignment_roots,
};

struct Phase {
    span: Span,
    kind: &'static str,
    detail: String,
    guards: Vec<String>,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Access {
    Read,
    Delete,
}

/// Computed property references retain the evaluated key value across
/// GetValue and PutValue; a super reference also retains its original this.
#[derive(Clone, Copy)]
struct ComputedKey {
    base: Span,
    key: Span,
    super_reference: bool,
}

impl ComputedKey {
    fn new(member: &ComputedMemberExpression<'_>) -> Self {
        Self {
            base: member.object.span(),
            key: member.expression.span(),
            super_reference: member.object.is_super(),
        }
    }
}

struct Plan<'s> {
    source: &'s str,
    guards: Vec<String>,
    phases: Vec<Phase>,
}
impl<'s> Plan<'s> {
    const fn new(source: &'s str) -> Self {
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
        let mut chars = collapsed_whitespace(text);
        let mut single = chars.by_ref().take(64).collect::<String>();
        if chars.next().is_some() {
            single.push('…');
        }
        single
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
        self.computed_reference_after_base(member);
    }

    fn computed_reference_after_base(&mut self, member: &ComputedMemberExpression<'_>) {
        self.expression(&member.expression);
        // The reference retains an uncoerced key. ToPropertyKey runs on
        // GetValue or PutValue, possibly after a simple assignment's RHS.
        self.mark(
            member.span,
            "form reference",
            "base + uncoerced key; property not yet read",
        );
    }

    fn assignment_key(target: &AssignmentTarget<'_>) -> Option<ComputedKey> {
        match target {
            AssignmentTarget::ComputedMemberExpression(member) if !member.optional => {
                Some(ComputedKey::new(member))
            }
            _ => None,
        }
    }

    fn update_key(target: &SimpleAssignmentTarget<'_>) -> Option<ComputedKey> {
        match target {
            SimpleAssignmentTarget::ComputedMemberExpression(member) if !member.optional => {
                Some(ComputedKey::new(member))
            }
            _ => None,
        }
    }

    fn is_super_target(target: &SimpleAssignmentTarget<'_>) -> bool {
        match target {
            SimpleAssignmentTarget::StaticMemberExpression(member) => member.object.is_super(),
            SimpleAssignmentTarget::ComputedMemberExpression(member) => member.object.is_super(),
            _ => false,
        }
    }

    fn key_coercion(&mut self, key: Option<ComputedKey>) {
        if let Some(key) = key {
            // GetValue/PutValue first runs ToObject on the reference base,
            // which for super is GetSuperBase (not the original this receiver).
            // Both operations may convert the original object-valued key.
            self.mark(
                key.base,
                "ToObject base",
                if key.super_reference {
                    "GetSuperBase result; nullish throws; original this remains receiver"
                } else {
                    "throws for null/undefined"
                },
            );
            self.mark(
                key.key,
                "ToPropertyKey",
                "key conversion may invoke Symbol.toPrimitive or valueOf",
            );
        }
    }

    fn super_this_binding(&mut self, span: Span) {
        self.mark(
            span,
            "GetThisBinding super",
            "resolve this before property key; uninitialized this throws ReferenceError",
        );
    }

    fn form_super_reference(&mut self, span: Span) {
        self.mark(
            span,
            "form super reference",
            "GetSuperBase; preserve original this as receiver and uncoerced key",
        );
    }
    fn assignment_target(&mut self, target: &AssignmentTarget<'_>) -> bool {
        // OXC only exposes a simple view for the shared assignment-target
        // variants. Destructuring and other unsupported targets remain opaque.
        target
            .as_simple_assignment_target()
            .is_some_and(|simple| self.simple_target(simple))
    }
    fn simple_target(&mut self, target: &SimpleAssignmentTarget<'_>) -> bool {
        match target {
            SimpleAssignmentTarget::AssignmentTargetIdentifier(_) => {
                let name = self.snippet(target.span());
                self.mark(target.span(), "resolve reference", name);
            }
            SimpleAssignmentTarget::StaticMemberExpression(member) if !member.optional => {
                if member.object.is_super() {
                    self.super_this_binding(member.object.span());
                    self.form_super_reference(member.span);
                } else {
                    self.expression(&member.object);
                    self.mark(
                        target.span(),
                        "form reference",
                        format!("static property .{}", member.property.name),
                    );
                }
            }
            SimpleAssignmentTarget::ComputedMemberExpression(member) if !member.optional => {
                if member.object.is_super() {
                    self.super_this_binding(member.object.span());
                    self.expression(&member.expression);
                    self.form_super_reference(member.span);
                } else {
                    self.computed_reference(member);
                }
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
    fn receiver_kind(callee: &Expression<'_>, direct_eval_possible: bool) -> &'static str {
        let callee = callee.without_parentheses();
        if let Some(member) = callee.as_member_expression() {
            if member.object().is_super() {
                return "super member receiver is the original this binding";
            }
            return match member {
                MemberExpression::StaticMemberExpression(_) => {
                    "member receiver from evaluated reference"
                }
                MemberExpression::ComputedMemberExpression(_) => {
                    "computed member receiver from evaluated reference"
                }
                MemberExpression::PrivateFieldExpression(_) => {
                    "private member receiver from evaluated reference"
                }
            };
        }
        match callee {
            Expression::ChainExpression(chain) if chain.expression.is_member_expression() =>
                "member receiver if the chain reaches its final reference; otherwise undefined value",
            Expression::Identifier(id) if direct_eval_possible && id.name == "eval" => {
                "direct eval candidate: lexical environment remains observable"
            }
            Expression::SequenceExpression(_) => "sequence value; member receiver discarded",
            _ => "callee reference/receiver determined by original expression; not inferred",
        }
    }

    fn call(&mut self, call: &CallExpression<'_>) {
        if call.optional || call.callee.is_super() {
            self.opaque(call.span, "optional/super call outside chain plan");
            return;
        }
        self.expression(&call.callee);
        self.call_after_callee(call);
    }

    fn call_after_callee(&mut self, call: &CallExpression<'_>) {
        self.mark(
            call.callee.span(),
            "callee ready",
            Self::receiver_kind(&call.callee, !call.optional),
        );
        self.arguments(&call.arguments);
        self.mark(
            call.span,
            "Call",
            format!(
                "{}; invoke once with evaluated arguments and original receiver; body/effects opaque",
                self.snippet(call.callee.span()),
            ),
        );
    }

    fn member(&mut self, member: &MemberExpression<'_>, access: Access) {
        if member.object().is_super() {
            self.super_this_binding(member.object().span());
        } else {
            self.expression(member.object());
        }
        self.member_after_base(member, access);
    }

    fn member_after_base(&mut self, member: &MemberExpression<'_>, access: Access) {
        if let MemberExpression::ComputedMemberExpression(computed) = member {
            if member.object().is_super() {
                self.expression(&computed.expression);
            } else {
                self.computed_reference_after_base(computed);
            }
        }
        if member.object().is_super() {
            self.form_super_reference(member.span());
        }
        // IsSuperReference is checked before ToObject, ToPropertyKey and
        // [[Delete]]. Evaluating the computed key expression can run user
        // code, but converting its resulting object must not.
        if access == Access::Delete && member.object().is_super() {
            self.mark(
                member.span(),
                "super delete ReferenceError",
                "throw before key coercion, GetValue, getter or delete trap",
            );
            return;
        }
        if let MemberExpression::ComputedMemberExpression(computed) = member {
            self.key_coercion(Some(ComputedKey::new(computed)));
        }
        if access == Access::Delete {
            self.mark(member.span(), "DeleteProperty",
                "delete reference without GetValue; nullish base throws; Proxy delete trap and strict failure are dynamic");
            return;
        }
        match member {
            MemberExpression::StaticMemberExpression(member) => self.mark(
                member.span,
                "GetValue member",
                format!(
                    "property .{} (getter/Proxy trap may run)",
                    member.property.name
                ),
            ),
            MemberExpression::ComputedMemberExpression(member) => {
                self.mark(member.span, "GetValue member", "getter/Proxy trap may run");
            }
            MemberExpression::PrivateFieldExpression(member) => {
                self.mark(
                    member.span,
                    "GetValue private field",
                    "private-brand check; private accessor may run",
                );
            }
        }
    }

    /// Append a guard for the rest of THIS chain, rather than just the
    /// optional link. A nested `ChainExpression` has its own guard lifetime.
    fn optional_guard(&mut self, value: Span, link: Span, access: Access) {
        let site = format!("optional link {}–{}", link.start, link.end);
        self.mark(
            value,
            "nullish check",
            format!("{site}: test evaluated value for null or undefined"),
        );
        self.guarded(&format!("{site} nullish"), |plan| {
            plan.mark(
                link,
                "short circuit chain",
                match access {
                    Access::Read => "skip remaining chain links; produce undefined",
                    Access::Delete => "skip remaining chain links; delete yields true",
                },
            );
        });
        self.guards.push(format!("{site} non-nullish"));
    }

    /// Descend only through the unparenthesized member/call spine. Other
    /// expressions (including nested chains) use normal value evaluation.
    fn chain_operand(&mut self, expr: &Expression<'_>, access: Access) {
        if let Some(member) = expr.as_member_expression() {
            self.chain_member(member, Access::Read, access);
        } else if let Expression::CallExpression(call) = expr {
            self.chain_call(call, access);
        } else {
            self.expression(expr);
        }
    }

    fn chain_member(
        &mut self,
        member: &MemberExpression<'_>,
        member_access: Access,
        chain_access: Access,
    ) {
        if member.object().is_super() {
            self.member(member, member_access);
            return;
        }
        self.chain_operand(member.object(), chain_access);
        if member.optional() {
            self.optional_guard(member.object().span(), member.span(), chain_access);
        }
        self.member_after_base(member, member_access);
    }

    fn chain_call(&mut self, call: &CallExpression<'_>, access: Access) {
        if call.callee.is_super() {
            self.call(call);
            return;
        }
        self.chain_operand(&call.callee, access);
        if call.optional {
            self.optional_guard(call.callee.span(), call.span, access);
        }
        self.call_after_callee(call);
    }

    fn chain(&mut self, chain: &ChainExpression<'_>, access: Access) {
        let outer_guards = self.guards.len();
        if let Some(member) = chain.expression.as_member_expression() {
            self.chain_member(member, access, access);
        } else if let ChainElement::CallExpression(call) = &chain.expression {
            self.chain_call(call, access);
            if access == Access::Delete {
                self.mark(call.span, "delete value", "non-reference call result; true");
            }
        } else {
            self.opaque(chain.span, "unmodeled chain element");
        }
        self.guards.truncate(outer_guards);
    }

    fn delete(&mut self, arg: &Expression<'_>) {
        let arg = arg.without_parentheses();
        if let Some(member) = arg.as_member_expression() {
            self.member(member, Access::Delete);
        } else {
            match arg {
                Expression::ChainExpression(chain) => self.chain(chain, Access::Delete),
                Expression::Identifier(id) => self.mark(id.span, "delete binding",
                    "resolve reference without GetValue; unresolvable yields true, bound name deletion depends on environment"),
                other => {
                    self.expression(other);
                    self.mark(other.span(), "delete value", "non-reference result; true after operand evaluation");
                }
            }
        }
    }

    /// Evaluate a constructor reference and its value before the arguments.
    /// Unlike a Call, Construct does not use a property receiver as this.
    /// A non-constructor is rejected *after* evaluating all argument
    /// expressions and consuming every spread (including possible throws).
    fn construct(&mut self, construct: &NewExpression<'_>) {
        self.expression(&construct.callee);
        self.mark(
            construct.callee.span(),
            "constructor ready",
            format!(
                "{}; GetValue complete; no member receiver is passed to Construct",
                self.snippet(construct.callee.span()),
            ),
        );
        self.arguments(&construct.arguments);
        self.mark(
            construct.callee.span(),
            "IsConstructor",
            "check after argument evaluation; non-constructible values throw TypeError here",
        );
        self.mark(
            construct.span,
            "Construct",
            "construct with evaluated arguments and newTarget; Proxy trap, allocation, prototype lookup, constructor effects and returned-object override are dynamic",
        );
    }

    fn arguments(&mut self, arguments: &[Argument<'_>]) {
        for (index, argument) in arguments.iter().enumerate() {
            match argument {
                Argument::SpreadElement(spread) => {
                    self.expression(&spread.argument);
                    self.mark(
                        spread.span,
                        "expand spread argument",
                        format!(
                            "argument {}: iterator acquisition, steps, values and abrupt completion opaque",
                            index + 1
                        ),
                    );
                }
                other => {
                    if let Some(expression) = other.as_expression() {
                        self.expression(expression);
                    } else {
                        self.opaque(other.span(), "unmodeled call argument");
                    }
                }
            }
        }
    }

    fn array(&mut self, array: &ArrayExpression<'_>) {
        self.mark(
            array.span,
            "create array",
            "fresh array for ordered element evaluation",
        );
        for (index, item) in array.elements.iter().enumerate() {
            match item {
                ArrayExpressionElement::SpreadElement(spread) => {
                    self.expression(&spread.argument);
                    self.mark(
                        spread.span,
                        "expand array spread",
                        format!(
                            "element {}: iterate now (next/getter/abrupt behavior opaque)",
                            index + 1
                        ),
                    );
                }
                ArrayExpressionElement::Elision(hole) => {
                    self.mark(
                        hole.span,
                        "array hole",
                        format!("element {} is absent", index + 1),
                    );
                }
                other => {
                    if let Some(expression) = other.as_expression() {
                        self.expression(expression);
                        self.mark(
                            other.span(),
                            "append array element",
                            format!("element {}: evaluated value", index + 1),
                        );
                    } else {
                        self.opaque(other.span(), "unmodeled array element");
                    }
                }
            }
        }
    }

    fn object(&mut self, object: &ObjectExpression<'_>) {
        self.mark(
            object.span,
            "create object",
            "fresh object; property order follows source",
        );
        for property in &object.properties {
            match property {
                ObjectPropertyKind::SpreadProperty(spread) => {
                    self.expression(&spread.argument);
                    self.mark(
                        spread.span,
                        "CopyDataProperties",
                        "ownKeys/descriptors/getters/Proxy traps execute before next property; opaque",
                    );
                }
                ObjectPropertyKind::ObjectProperty(entry) => {
                    if entry.computed {
                        if let Some(key) = entry.key.as_expression() {
                            self.expression(key);
                            self.mark(
                                entry.key.span(),
                                "ToPropertyKey",
                                "object literal computed key converted before its value",
                            );
                        } else {
                            self.opaque(entry.span, "unmodeled computed object property");
                            continue;
                        }
                    }
                    self.expression(&entry.value);
                    self.mark(
                        entry.span,
                        "define object property",
                        "data/method/accessor definition; static __proto__ may set prototype",
                    );
                }
            }
        }
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
        let super_target = assign
            .left
            .as_simple_assignment_target()
            .is_some_and(Self::is_super_target);
        let target = self.snippet(assign.left.span());
        let receiver = if super_target {
            "; super accessor receiver is original this (not base prototype)"
        } else {
            ""
        };
        if !op.is_assign() {
            self.key_coercion(key);
        }
        if !op.is_assign() {
            self.mark(
                assign.left.span(),
                "GetValue target",
                format!("{target}; getter/dynamic resolution/TDZ can throw before RHS{receiver}"),
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
                    format!("{target} {} (setter may run){receiver}", op.as_str()),
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
                format!("{target} {} (setter may run){receiver}", op.as_str()),
            );
        }
    }
    fn update(&mut self, update: &oxc_ast::ast::UpdateExpression<'_>) {
        if self.simple_target(&update.argument) {
            let key = Self::update_key(&update.argument);
            let receiver = Self::is_super_target(&update.argument);
            self.key_coercion(key);
            self.mark(
                update.argument.span(),
                "GetValue target",
                if receiver {
                    "getter may run with original this as super receiver"
                } else {
                    "getter may run"
                },
            );
            self.mark(update.span, "numeric update", update.operator.as_str());
            self.key_coercion(key);
            self.mark(
                update.argument.span(),
                "PutValue target",
                if receiver {
                    "setter may run with original this as super receiver"
                } else {
                    "setter may run"
                },
            );
        } else {
            self.opaque(update.span, "extended update expression");
        }
    }

    fn template(&mut self, template: &TemplateLiteral<'_>) {
        for substitution in &template.expressions {
            self.expression(substitution);
            self.mark(substitution.span(), "ToString substitution",
                "convert before evaluating the next substitution; object coercion may invoke user code; Symbol throws");
        }
        self.mark(
            template.span,
            "template value",
            "combine cooked segments and converted substitutions",
        );
    }

    fn tagged_template(&mut self, tagged: &TaggedTemplateExpression<'_>) {
        self.expression(&tagged.tag);
        self.mark(
            tagged.tag.span(),
            "tag ready",
            Self::receiver_kind(&tagged.tag, false),
        );
        self.mark(
            tagged.quasi.span,
            "GetTemplateObject",
            "site-specific cached frozen template object; raw segments preserved, invalid cooked escapes yield undefined",
        );
        for substitution in &tagged.quasi.expressions {
            self.expression(substitution);
        }
        self.mark(tagged.span, "Call tag",
            "check callability after substitutions and invoke with original receiver, template object and uncoerced values; effects opaque");
    }

    fn unary(&mut self, unary: &UnaryExpression<'_>) {
        if unary.operator == UnaryOperator::Delete {
            self.delete(&unary.argument);
            return;
        }
        if let (UnaryOperator::Typeof, Expression::Identifier(id)) =
            (unary.operator, unary.argument.without_parentheses())
        {
            self.mark(id.span, "typeof identifier",
                format!("{}; unresolvable reference yields undefined string, but TDZ and binding access can throw", id.name));
            return;
        }
        self.expression(&unary.argument);
        let (kind, detail) = match unary.operator {
            UnaryOperator::Void => (
                "discard value",
                "void produces undefined only if its operand completes",
            ),
            UnaryOperator::Typeof => (
                "typeof value",
                "classify value without numeric or string coercion",
            ),
            UnaryOperator::LogicalNot => (
                "ToBoolean",
                "negate truthiness without invoking user coercion",
            ),
            UnaryOperator::UnaryPlus => (
                "ToNumber",
                "unary +; object coercion can run user code; BigInt and Symbol throw",
            ),
            UnaryOperator::UnaryNegation => (
                "ToNumeric",
                "unary -; numeric coercion then Number or BigInt negation",
            ),
            UnaryOperator::BitwiseNot => (
                "ToNumeric",
                "unary ~; numeric coercion then Number ToInt32 or BigInt complement",
            ),
            UnaryOperator::Delete => return,
        };
        self.mark(unary.span, kind, detail);
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
            Expression::CallExpression(call) => self.call(call),
            Expression::NewExpression(construct) => self.construct(construct),
            Expression::ArrayExpression(array) => self.array(array),
            Expression::ObjectExpression(object) => self.object(object),
            Expression::FunctionExpression(_) | Expression::ArrowFunctionExpression(_) => {
                self.mark(
                    expr.span(),
                    "create function",
                    "body deferred; named evaluation may set the function name",
                );
            }
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
            Expression::ChainExpression(chain) => self.chain(chain, Access::Read),
            expr if expr.is_member_expression() => {
                if let Some(member) = expr.as_member_expression() {
                    self.member(member, Access::Read);
                }
            }
            Expression::Identifier(id) => {
                self.mark(id.span, "GetValue identifier", id.name.to_string());
            }
            // Evaluating a primitive literal neither reads a binding nor
            // invokes user code. Preserve it in the phase sequence as an
            // effect-free value instead of calling it an opaque side effect.
            Expression::BooleanLiteral(_)
            | Expression::NullLiteral(_)
            | Expression::NumericLiteral(_)
            | Expression::BigIntLiteral(_)
            | Expression::StringLiteral(_) => {
                self.mark(expr.span(), "inert literal", self.snippet(expr.span()));
            }
            Expression::RegExpLiteral(_) => {
                // A RegExp literal creates a fresh object; don't conflate
                // allocation/identity with a primitive constant or callback.
                self.mark(expr.span(), "create regexp", "fresh RegExp literal value");
            }
            Expression::UnaryExpression(unary) => self.unary(unary),
            Expression::TemplateLiteral(template) => self.template(template),
            Expression::TaggedTemplateExpression(tagged) => self.tagged_template(tagged),
            Expression::UpdateExpression(update) => self.update(update),
            // Unexpanded expressions retain their original effects.
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
pub fn ordered_assignment_phases(
    source: &str,
    program: &Program<'_>,
    lines: &SourceLineIndex,
) -> Option<String> {
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
         RHS/PutValue. Super references resolve the original this before \
         computed-key evaluation and retain that receiver across getter and \
         setter calls; GetSuperBase is distinct from the receiver. \
         Primitive literals are marked inert, while RegExp literals create \
         distinct objects. The void operator evaluates its operand (including \
         calls, binding reads and exceptions) before discarding its value; \
         typeof preserves its special unresolvable-reference behavior; numeric unary \
         operators distinguish ToNumber from ToNumeric. Delete uses a reference without a getter. \
         Optional-chain guards identify the evaluated link by source bytes; a nullish value \
         skips the remainder of that chain, but parentheses terminate propagation. \
         Optional calls inspect the callee value before arguments; optional member access \
         checks the base before computed-key evaluation. Untagged \
         templates convert each substitution immediately; tags receive uncoerced values \
         and a site-specific template object with the original receiver. New expressions evaluate the constructor \
         value and argument list (including spreads) before IsConstructor \
         validation and Construct; a member receiver is not forwarded. \
         Spans refer to the derived readable helper, not captured source.\n\n",
    );
    collector.sections.sort_by_key(|(span, _)| span.start);
    for (root, phases) in &collector.sections {
        let (line, col) = lines.character_line_column(source, root.start as usize)?;
        let _ = write!(
            out,
            "## Assignment at {line}:{col} (source bytes {}–{})\n\n",
            root.start, root.end
        );
        out.push_str(
            "| Phase | Path guard | Step | Details | Source bytes |\n|---:|---|---|---|---|\n",
        );
        for (i, phase) in phases.iter().enumerate() {
            let guard = if phase.guards.is_empty() {
                "unguarded".to_owned()
            } else {
                phase.guards.join(" and ")
            };
            let _ = writeln!(
                out,
                "| {} | {} | {} | {} | {}–{} |",
                i + 1,
                literal_text(&guard),
                phase.kind,
                literal_text(&phase.detail),
                phase.span.start,
                phase.span.end
            );
        }
        out.push('\n');
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::{literal_text, ordered_assignment_phases, SourceLineIndex};
    use oxc_allocator::Allocator;
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;

    fn plan(source: &str) -> String {
        let arena = Allocator::default();
        let parsed = parse_program(&arena, source, SourceType::unambiguous());
        assert!(parsed.is_clean(), "{source}");
        let result =
            ordered_assignment_phases(source, &parsed.program, &SourceLineIndex::new(source));
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
        let key_call = position(&phases, "| Call | key;");
        let to_property_key = position(&phases, "| ToPropertyKey |");
        let nested_target = position(&phases, "static property .x");
        let rhs_call = position(&phases, "| Call | rhs;");
        let nested_write = position(&phases, "inner.x = (setter may run)");
        let outer_write = position(&phases, &literal_text("obj[key()] = (setter may run)"));
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
    fn call_arguments_are_evaluated_but_destructuring_remains_opaque() {
        let call = format!(
            "function f(obj,side){{root = call((obj.inner=1), {});}}",
            long_effects()
        );
        let phases = plan(&call);
        let inner = position(&phases, "obj.inner = (setter may run)");
        let call_step = position(&phases, "| Call | call;");
        assert!(inner < call_step, "{phases}");
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
            let key_call = position(&phases, "| Call | key;");
            let to_object = position(&phases, "| ToObject base |");
            let key_coercion = position(&phases, "| ToPropertyKey |");
            let target_get = position(
                &phases,
                &literal_text("obj[key()]; getter/dynamic resolution"),
            );
            let rhs = position(&phases, "side.effect = (setter may run)");
            let second_key_coercion = phases.rfind("| ToPropertyKey |").unwrap_or(usize::MAX);
            let put = position(
                &phases,
                &literal_text(&format!("obj[key()] {operator} (setter may run)")),
            );
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
    fn call_evaluates_receiver_lookup_before_arguments_and_spreads_in_order() {
        let source = format!(
            "function f(obj,key,iter,side){{root=obj[key()]((side.first=1),...iter,side.last=3,{});}}",
            long_effects()
        );
        let phases = plan(&source);
        let key = position(&phases, "| Call | key;");
        let coerced = position(&phases, "| ToPropertyKey |");
        let getter = position(&phases, "| GetValue member |");
        let ready = position(&phases, "| callee ready | computed member receiver");
        let first = position(&phases, "side.first = (setter may run)");
        let spread = position(&phases, "| expand spread argument |");
        let last = position(&phases, "side.last = (setter may run)");
        let call = phases.rfind("| Call |").unwrap_or(usize::MAX);
        let root_write = position(&phases, "root = (setter may run)");
        assert!(
            key < coerced
                && coerced < getter
                && getter < ready
                && ready < first
                && first < spread
                && spread < last
                && last < call
                && call < root_write,
            "{phases}"
        );
    }

    #[test]
    fn call_parentheses_preserve_receiver_but_sequence_discards_it() {
        let source = format!(
            "function f(obj,side){{root=((obj.run))((side.first=1),{});}}",
            long_effects()
        );
        let view = plan(&source);
        assert!(
            view.contains("| callee ready | member receiver from evaluated reference"),
            "{view}"
        );
        let source = format!(
            "function f(obj,side){{root=(0,obj.run)((side.first=1),{});}}",
            long_effects()
        );
        let view = plan(&source);
        assert!(
            view.contains("| callee ready | sequence value; member receiver discarded"),
            "{view}"
        );
        let source = format!(
            "function f(side){{root=eval((side.first=1),{});}}",
            long_effects()
        );
        let view = plan(&source);
        assert!(view.contains("direct eval candidate"), "{view}");
    }

    #[test]
    fn array_holes_and_spread_iterate_before_later_elements() {
        let source = format!(
            "function f(iter,side){{root=[side.first=1,,...iter,side.last=2,{}];}}",
            long_effects()
        );
        let phases = plan(&source);
        let create = position(&phases, "| create array |");
        let first = position(&phases, "side.first = (setter may run)");
        let hole = position(&phases, "| array hole |");
        let spread = position(&phases, "| expand array spread |");
        let last = position(&phases, "side.last = (setter may run)");
        let put = position(&phases, "root = (setter may run)");
        assert!(
            create < first && first < hole && hole < spread && spread < last && last < put,
            "{phases}"
        );
    }

    #[test]
    fn object_computed_key_then_value_spread_then_later_property() {
        let source = format!(
            "function f(key,from,side){{root={{[key()]:side.value=1,...from,\
             after:side.after=2,get deferred(){{side.hidden=3;}},tail:({})}};}}",
            long_effects()
        );
        let phases = plan(&source);
        let create = position(&phases, "| create object |");
        let key = position(&phases, "| Call | key;");
        let coerce = position(&phases, "| ToPropertyKey |");
        let value = position(&phases, "side.value = (setter may run)");
        let spread = position(&phases, "| CopyDataProperties |");
        let later = position(&phases, "side.after = (setter may run)");
        let deferral = position(&phases, "| create function |");
        let end = position(&phases, "root = (setter may run)");
        assert!(
            create < key
                && key < coerce
                && coerce < value
                && value < spread
                && spread < later
                && later < deferral
                && deferral < end,
            "{phases}"
        );
        assert!(
            !phases.contains("side.hidden = (setter may run)"),
            "getter bodies are deferred: {phases}"
        );
    }

    #[test]
    fn optional_call_guards_arguments_and_regular_constructor_is_expanded() {
        let source = format!(
            "function f(obj,side){{root=obj?.method((side.bad=1,{}));}}",
            long_effects()
        );
        let phases = plan(&source);
        let check = position(&phases, "| nullish check |");
        let short = position(&phases, "| short circuit chain |");
        let nested = position(&phases, "side.bad = (setter may run)");
        assert!(check < short && short < nested, "{phases}");
        assert!(
            phases
                .lines()
                .any(|line| line.contains("non-nullish")
                    && line.contains("side.bad = (setter may run)")),
            "{phases}"
        );
        assert!(!phases.contains("| opaque expression |"), "{phases}");
        let source = format!(
            "function f(C,side){{root=new C((side.bad=1,{}));}}",
            long_effects()
        );
        let phases = plan(&source);
        let ready = position(&phases, "| constructor ready | C;");
        let nested = position(&phases, "side.bad = (setter may run)");
        let check = position(&phases, "| IsConstructor |");
        let construct = position(&phases, "| Construct |");
        let root = position(&phases, "root = (setter may run)");
        assert!(
            ready < nested && nested < check && check < construct && construct < root,
            "{phases}"
        );
        assert!(!phases.contains("| opaque expression |"), "{phases}");
    }

    fn phase_row<'a>(phases: &'a str, fragment: &str) -> &'a str {
        let row = phases
            .lines()
            .find(|line| line.starts_with("| ") && line.contains(fragment));
        assert!(row.is_some(), "missing {fragment}: {phases}");
        row.unwrap_or_default()
    }

    #[test]
    fn optional_chain_guards_entire_suffix_but_not_grouped_outer_call() {
        let source = format!(
            "function f(o,k,a,b,side){{root=(side.x=o?.[k()]?.m(a()).z,side.y=(o?.m)(b()),side.end=1,{});}}",
            long_effects()
        );
        let phases = plan(&source);
        let key = phase_row(&phases, "| Call | k;");
        let arg = phase_row(&phases, "| Call | a;");
        let last = phase_row(&phases, "property .z (getter");
        let grouped_arg = phase_row(&phases, "| Call | b;");
        let outer = phase_row(&phases, "side.end = (setter may run)");
        assert_eq!(key.matches("non-nullish").count(), 1, "{key}");
        assert_eq!(arg.matches("non-nullish").count(), 2, "{arg}");
        assert_eq!(last.matches("non-nullish").count(), 2, "{last}");
        assert!(grouped_arg.contains("| unguarded |"), "{grouped_arg}");
        assert!(outer.contains("| unguarded |"), "{outer}");
        assert!(
            phases.contains("member receiver if the chain reaches its final reference"),
            "{phases}"
        );
        assert_eq!(
            phases.matches("| short circuit chain |").count(),
            3,
            "{phases}"
        );
        let second = phases
            .lines()
            .filter(|line| line.contains("| short circuit chain |"))
            .nth(1)
            .unwrap_or_default();
        assert_eq!(second.matches("non-nullish").count(), 1, "{second}");
        assert!(second.contains(" nullish |"), "{second}");
    }

    #[test]
    fn nested_key_chain_guards_do_not_escape_the_key_expression() {
        let source = format!(
            "function f(o,p,side){{root=(side.x=o?.[p?.key(inner())].m(outer()),side.y=after(),{});}}",
            long_effects()
        );
        let phases = plan(&source);
        assert_eq!(
            phase_row(&phases, "| Call | inner;")
                .matches("non-nullish")
                .count(),
            2
        );
        assert_eq!(
            phase_row(&phases, "| ToPropertyKey |")
                .matches("non-nullish")
                .count(),
            1
        );
        assert_eq!(
            phase_row(&phases, "| Call | outer;")
                .matches("non-nullish")
                .count(),
            1
        );
        assert!(phase_row(&phases, "| Call | after;").contains("| unguarded |"));
    }

    #[test]
    fn optional_calls_check_callee_without_direct_eval_and_before_spread() {
        let source = format!(
            "function f(o,it,side){{root=(side.a=o.m?.(first(),...it,last()),side.b=eval?.('x'),side.c=eval('x')?.x,{});}}",
            long_effects()
        );
        let phases = plan(&source);
        let getter = position(&phases, "property .m (getter");
        let check = position(&phases, "| nullish check |");
        let first = position(&phases, "| Call | first;");
        let spread = position(&phases, "| expand spread argument |");
        let last = position(&phases, "| Call | last;");
        assert!(
            getter < check && check < first && first < spread && spread < last,
            "{phases}"
        );
        assert!(phase_row(&phases, "| expand spread argument |").contains("non-nullish"));
        assert_eq!(phases.matches("direct eval candidate:").count(), 1);
    }

    #[test]
    fn super_simple_assignment_defers_key_coercion_until_after_rhs() {
        let source = format!(
            "class Base{{}}class Derived extends Base{{run(key,rhs,side){{root=(side.x=super[key()] = (side.rhs=rhs()),{});}}}}",
            long_effects()
        );
        let phases = plan(&source);
        let this = position(&phases, "| GetThisBinding super |");
        let key = position(&phases, "| Call | key;");
        let formed = position(&phases, "| form super reference |");
        let rhs = position(&phases, "| Call | rhs;");
        let object = position(&phases, "| ToObject base |");
        let coerced = position(&phases, "| ToPropertyKey |");
        let put = position(&phases, "super[key()] = (setter may run)");
        assert!(
            this < key
                && key < formed
                && formed < rhs
                && rhs < object
                && object < coerced
                && coerced < put,
            "{phases}"
        );
        assert_eq!(phases.matches("| ToPropertyKey |").count(), 1);
        assert!(
            phases.contains("GetSuperBase result; nullish throws; original this remains receiver")
        );
        assert!(phase_row(&phases, "super[key()] = (setter may run)")
            .contains("super accessor receiver is original this"));
        assert!(!phases.contains("| GetValue target |"), "{phases}");
    }

    #[test]
    fn super_compound_assignment_converts_original_key_twice_and_reads_before_rhs() {
        let source = format!(
            "class Base{{}}class Derived extends Base{{run(key,rhs,side){{root=(side.x=super[key()] += (side.rhs=rhs()),{});}}}}",
            long_effects()
        );
        let phases = plan(&source);
        let coercions = phases
            .match_indices("| ToPropertyKey |")
            .map(|(i, _)| i)
            .collect::<Vec<_>>();
        let objects = phases
            .match_indices("| ToObject base |")
            .map(|(i, _)| i)
            .collect::<Vec<_>>();
        assert_eq!(coercions.len(), 2, "{phases}");
        assert_eq!(objects.len(), 2, "{phases}");
        let this = position(&phases, "| GetThisBinding super |");
        let key = position(&phases, "| Call | key;");
        let formed = position(&phases, "| form super reference |");
        let read = position(&phases, "| GetValue target |");
        let rhs = position(&phases, "| Call | rhs;");
        let applied = position(&phases, "| apply assignment operator |");
        let put = position(&phases, "| PutValue target |");
        assert!(
            this < key
                && key < formed
                && formed < objects[0]
                && objects[0] < coercions[0]
                && coercions[0] < read
                && read < rhs
                && rhs < applied
                && applied < objects[1]
                && objects[1] < coercions[1]
                && coercions[1] < put,
            "{phases}"
        );
        assert!(phase_row(&phases, "| GetValue target |").contains("super accessor receiver"));
        assert!(phase_row(&phases, "| PutValue target |").contains("super accessor receiver"));
    }

    #[test]
    fn super_logical_assignments_guard_rhs_second_conversion_and_putvalue() {
        for (op, guard) in [
            ("&&=", "target truthy"),
            ("||=", "target falsy"),
            ("??=", "target nullish"),
        ] {
            let source = format!(
                "class Base{{}}class Derived extends Base{{run(key,rhs,side){{root=(side.x=super[key()] {op} (side.rhs=rhs()),{});}}}}",
                long_effects()
            );
            let phases = plan(&source);
            let coerced = phases
                .match_indices("| ToPropertyKey |")
                .map(|(i, _)| i)
                .collect::<Vec<_>>();
            assert_eq!(coerced.len(), 2, "{phases}");
            let read = position(&phases, "| GetValue target |");
            let rhs = position(&phases, "| Call | rhs;");
            let put = position(&phases, "| PutValue target |");
            assert!(
                coerced[0] < read && read < rhs && rhs < coerced[1] && coerced[1] < put,
                "{phases}"
            );
            for row in phases
                .lines()
                .filter(|row| row.contains("| Call | rhs;") || row.contains("| PutValue target |"))
            {
                assert!(row.contains(guard), "{row}");
            }
            assert!(phase_row(&phases, "| GetValue target |").contains("| unguarded |"));
            assert!(
                !phases.contains("| apply assignment operator |"),
                "{phases}"
            );
        }
    }

    #[test]
    fn super_prefix_and_postfix_update_read_convert_and_write_with_this_receiver() {
        for expression in [
            "super[key()]++",
            "++super[key()]",
            "super[key()]--",
            "--super[key()]",
        ] {
            let source = format!(
                "class Base{{}}class Derived extends Base{{run(key,side){{root=(side.x={expression},{});}}}}",
                long_effects()
            );
            let phases = plan(&source);
            let coercions = phases
                .match_indices("| ToPropertyKey |")
                .map(|(i, _)| i)
                .collect::<Vec<_>>();
            assert_eq!(coercions.len(), 2, "{phases}");
            let this = position(&phases, "| GetThisBinding super |");
            let key = position(&phases, "| Call | key;");
            let formed = position(&phases, "| form super reference |");
            let read = position(&phases, "| GetValue target |");
            let update = position(&phases, "| numeric update |");
            let put = position(&phases, "| PutValue target |");
            assert!(
                this < key
                    && key < formed
                    && formed < coercions[0]
                    && coercions[0] < read
                    && read < update
                    && update < coercions[1]
                    && coercions[1] < put,
                "{phases}"
            );
            assert!(phase_row(&phases, "| GetValue target |").contains("original this"));
            assert!(phase_row(&phases, "| PutValue target |").contains("original this"));
            assert!(!phases.contains("| opaque expression |"), "{phases}");
        }
    }

    #[test]
    #[ignore = "requires installed Node; super assignment operator family oracle"]
    fn node_confirms_super_assignment_update_and_logical_operator_events() -> anyhow::Result<()> {
        use std::process::Command;
        let source = r"
const log=[];
const key={ [Symbol.toPrimitive](){log.push('coerce');return 'x'} };
class Base {
  get x(){log.push('get:'+this.value+':'+this.id);return this.value}
  set x(value){log.push('set:'+String(value)+':'+this.id);this.value=value}
}
class Derived extends Base {
  constructor(){super();this.id='derived';this.value=3}
  run(){
    super[key]=(log.push('simple-rhs'),4);
    super[key]+=(log.push('compound-rhs'),5);
    super[key] &&= (log.push('and-rhs'),7);
    super[key] ||= (log.push('or-rhs'),11);
    super[key] ??= (log.push('nullish-rhs'),13);
    super[key]++;
    ++super[key];
    this.value=null;
    super[key] ??= (log.push('nullish-rhs2'),12);
    this.value=0;
    super[key] ||= (log.push('or-rhs2'),14);
    super[key] &&= (log.push('and-rhs2'),99);
    return this.value;
  }
}
const value=new Derived().run();
console.log(JSON.stringify([value,log]));
";
        let result = Command::new("node").arg("-e").arg(source).output()?;
        assert!(result.status.success(), "{result:?}");
        let actual: serde_json::Value = serde_json::from_slice(&result.stdout)?;
        assert_eq!(
            actual,
            serde_json::json!([
                99,
                [
                    "simple-rhs",
                    "coerce",
                    "set:4:derived",
                    "coerce",
                    "get:4:derived",
                    "compound-rhs",
                    "coerce",
                    "set:9:derived",
                    "coerce",
                    "get:9:derived",
                    "and-rhs",
                    "coerce",
                    "set:7:derived",
                    "coerce",
                    "get:7:derived",
                    "coerce",
                    "get:7:derived",
                    "coerce",
                    "get:7:derived",
                    "coerce",
                    "set:8:derived",
                    "coerce",
                    "get:8:derived",
                    "coerce",
                    "set:9:derived",
                    "coerce",
                    "get:null:derived",
                    "nullish-rhs2",
                    "coerce",
                    "set:12:derived",
                    "coerce",
                    "get:0:derived",
                    "or-rhs2",
                    "coerce",
                    "set:14:derived",
                    "coerce",
                    "get:14:derived",
                    "and-rhs2",
                    "coerce",
                    "set:99:derived"
                ]
            ])
        );
        Ok(())
    }

    #[test]
    #[ignore = "requires installed Node; super reference early-this and original-base oracle"]
    fn node_confirms_super_reference_initialization_and_original_receiver() -> anyhow::Result<()> {
        use std::process::Command;
        let source = r"
const log=[];
const key={ [Symbol.toPrimitive](){log.push('key-coerce');return 'x'} };
class Base {
  set x(v){log.push('base:'+v+':'+this.tag)}
}
class Derived extends Base {
  constructor(){super();this.tag='derived'}
  run(){
    super[key]=(log.push('rhs'),17);
  }
}
new Derived().run();
class Uninitialized extends Base {
  constructor(){
    try{super[(log.push('should-not-eval-key'),key)] = (log.push('should-not-eval-rhs'),42)}
    catch(e){log.push(e.name)}
    super();
  }
}
new Uninitialized();
console.log(JSON.stringify(log));
";
        let result = Command::new("node").arg("-e").arg(source).output()?;
        assert!(result.status.success(), "{result:?}");
        let actual: serde_json::Value = serde_json::from_slice(&result.stdout)?;
        assert_eq!(
            actual,
            serde_json::json!(["rhs", "key-coerce", "base:17:derived", "ReferenceError"])
        );
        Ok(())
    }

    #[test]
    fn super_optional_call_preserves_receiver_and_this_check_order() {
        let source = format!(
            "class Base{{m(){{}}}}class Derived extends Base{{run(key,arg,side){{root=(side.x=super[key()]?.(arg()),side.y=super.m?.(arg()),{});}}}}",
            long_effects()
        );
        let phases = plan(&source);
        let this = position(&phases, "| GetThisBinding super |");
        let key = position(&phases, "| Call | key;");
        let form = position(&phases, "| form super reference |");
        let convert = position(&phases, "| ToPropertyKey |");
        let getter = position(&phases, "| GetValue member |");
        let check = position(&phases, "| nullish check |");
        let arg = position(&phases, "| Call | arg;");
        assert!(
            this < key
                && key < form
                && form < convert
                && convert < getter
                && getter < check
                && check < arg,
            "{phases}"
        );
        assert_eq!(
            phases.matches("| GetThisBinding super |").count(),
            2,
            "{phases}"
        );
        assert_eq!(
            phases
                .matches("super member receiver is the original this binding")
                .count(),
            2,
            "{phases}"
        );
        assert!(phase_row(&phases, "| Call | arg;").contains("non-nullish"));
        assert!(!phases.contains("| opaque expression |"), "{phases}");
    }

    #[test]
    #[ignore = "requires installed Node; super property reference ordering oracle"]
    fn node_confirms_super_optional_receiver_and_early_this_throw() -> anyhow::Result<()> {
        use std::process::Command;
        let source = r"
const log=[];
class Base {
  get method(){log.push('getter');return function(x){'use strict';log.push('receiver:'+String(this instanceof Derived)+':'+x);return x}}
}
class Derived extends Base {
  run(){const key={toString(){log.push('coerce');return 'method'}};
    return [
      super[(log.push('key'),key)]?.((log.push('arg'),7)),
      super.method?.((log.push('arg2'),8))
    ]}
}
const d=new Derived();
const values=d.run();
class Uninitialized extends Base {
  constructor(){
    try{super[(log.push('should-not-run'),'method')]}catch(e){log.push(e.name)}
    super()
  }
}
new Uninitialized();
console.log(JSON.stringify([values,log]));
";
        let result = Command::new("node").arg("-e").arg(source).output()?;
        assert!(result.status.success(), "{result:?}");
        let actual: serde_json::Value = serde_json::from_slice(&result.stdout)?;
        assert_eq!(
            actual,
            serde_json::json!([
                [7, 8],
                [
                    "key",
                    "coerce",
                    "getter",
                    "arg",
                    "receiver:true:7",
                    "getter",
                    "arg2",
                    "receiver:true:8",
                    "ReferenceError"
                ]
            ])
        );
        Ok(())
    }

    #[test]
    fn deleting_super_reference_throws_after_key_value_but_without_coercion() {
        let source = format!(
            "class A{{}}class B extends A{{run(side){{root=(side.one=delete super[(side.key=1,key())],side.two=delete super.x,{});}}}}",
            long_effects()
        );
        let phases = plan(&source);
        let this = position(&phases, "| GetThisBinding super |");
        let key_side_effect = position(&phases, "side.key = (setter may run)");
        let key_call = position(&phases, "| Call | key;");
        let super_reference = position(&phases, "| form super reference |");
        let abrupt = position(&phases, "| super delete ReferenceError |");
        assert!(
            this < key_side_effect
                && key_side_effect < key_call
                && key_call < super_reference
                && super_reference < abrupt,
            "{phases}"
        );
        assert_eq!(phases.matches("| super delete ReferenceError |").count(), 2);
        assert!(!phases.contains("| ToPropertyKey |"), "{phases}");
        assert!(!phases.contains("| DeleteProperty |"), "{phases}");
    }

    #[test]
    #[ignore = "requires installed Node; deletion of super reference ordering oracle"]
    fn node_confirms_delete_super_skips_key_coercion_and_delete_traps() -> anyhow::Result<()> {
        use std::process::Command;

        let source = r"
const events=[];
const key={toString(){events.push('coerce');return 'x'}};
const base=new Proxy(Object.create(null),{deleteProperty(){events.push('delete-trap');return true}});
class A {}
Object.setPrototypeOf(A.prototype,base);
class B extends A {
  run(){
    try { delete super[(events.push('key-expression'),key)] }
    catch(e){events.push(e.name)}
    try { delete super.x }
    catch(e){events.push(e.name)}
    return events;
  }
}
console.log(JSON.stringify(new B().run()));
";
        let result = Command::new("node").arg("-e").arg(source).output()?;
        assert!(result.status.success(), "{result:?}");
        let actual: serde_json::Value = serde_json::from_slice(&result.stdout)?;
        assert_eq!(
            actual,
            serde_json::json!(["key-expression", "ReferenceError", "ReferenceError"])
        );
        Ok(())
    }

    #[test]
    fn optional_delete_preserves_reference_not_final_getter() {
        let source = format!(
            "function f(o,side){{root=(side.x=delete o?.a[key()],side.y=delete (o?.b).c,side.z=delete o?.m(),side.w=delete (0,o.d),{});}}",
            long_effects()
        );
        let phases = plan(&source);
        assert!(phase_row(&phases, "property .a (getter").contains("non-nullish"));
        assert!(phase_row(&phases, "| Call | key;").contains("non-nullish"));
        let deletes: Vec<_> = phases
            .lines()
            .filter(|line| line.contains("| DeleteProperty |"))
            .collect();
        assert_eq!(deletes.len(), 2, "{phases}");
        assert!(deletes
            .first()
            .is_some_and(|row| row.contains("non-nullish")));
        assert!(deletes
            .last()
            .is_some_and(|row| row.contains("| unguarded |")));
        assert!(!phases.contains("property .c (getter"));
        assert!(phases.contains("property .d (getter"));
        assert_eq!(phases.matches("delete yields true").count(), 2);
        assert_eq!(phases.matches("| delete value |").count(), 2);
    }

    #[test]
    #[ignore = "requires installed Node; optional chain evaluation oracle"]
    fn node_confirms_optional_chain_path_receiver_and_delete_order() -> anyhow::Result<()> {
        use std::process::Command;
        let source = r"
const log=[];
const nil=null;
const key=()=>{log.push('key');return {[Symbol.toPrimitive](){log.push('coerce');return 'm'}}};
const arg=()=>{log.push('arg');return 7};
const obj={
  get m(){log.push('get');return function(x){'use strict';log.push('call:'+String(this===obj)+':'+x);return {z:1}}},
  get n(){log.push('get:n');return null}
};
const out=[];
out.push(nil?.[key()]?.(arg()).z);
out.push(obj?.[key()]?.(arg()).z);
out.push(obj.n?.(arg()).z);
try{(nil?.m)(arg())}catch(e){log.push(e.name)}
out.push((obj?.m)(arg()).z);
out.push((0,obj?.m)(arg()).z);
try{nil?.m.x.z; (nil?.m)[key()]}catch(e){log.push(e.name)}
const target=new Proxy({get m(){log.push('unexpected getter');return 0}},{
    deleteProperty(t,k){log.push('delete:'+k);return Reflect.deleteProperty(t,k)}
});
out.push(delete nil?.[key()]);
out.push(delete target?.[key()]);
try{delete (nil?.m).x}catch(e){log.push(e.name)}
function e(){const onlyLocal=1;return [eval('typeof onlyLocal'),eval?.('typeof onlyLocal')]}
out.push(e());
class Base {method(x){log.push('super:'+String(this instanceof Derived)+':'+x)}}
class Derived extends Base {
    #method(x){log.push('private:'+x)}
    run(o){o?.#method?.(arg());super.method?.(arg())}
}
const d=new Derived();d.run(null);d.run(d);
console.log(JSON.stringify([out,log]));
";
        let result = Command::new("node").arg("-e").arg(source).output()?;
        assert!(result.status.success(), "{result:?}");
        let actual: serde_json::Value = serde_json::from_slice(&result.stdout)?;
        assert_eq!(
            actual,
            serde_json::json!([
                [null, 1, null, 1, 1, true, true, ["number", "undefined"]],
                [
                    "key",
                    "coerce",
                    "get",
                    "arg",
                    "call:true:7",
                    "get:n",
                    "arg",
                    "TypeError",
                    "get",
                    "arg",
                    "call:true:7",
                    "get",
                    "arg",
                    "call:false:7",
                    "key",
                    "TypeError",
                    "key",
                    "coerce",
                    "delete:m",
                    "TypeError",
                    "arg",
                    "super:true:7",
                    "arg",
                    "private:7",
                    "arg",
                    "super:true:7"
                ]
            ])
        );
        Ok(())
    }

    #[test]
    fn constructor_lookup_key_and_getter_precede_arguments_and_spread() {
        let source = format!(
            "function f(holder,key,iter,side){{root = new (holder[key()])             (side.first=1,...iter,side.last=2,{});}}",
            long_effects()
        );
        let phases = plan(&source);
        let get_key = position(&phases, "| Call | key;");
        let coercion = position(&phases, "| ToPropertyKey |");
        let getter = position(&phases, "| GetValue member |");
        let ready = position(&phases, "| constructor ready |");
        let first_write = position(&phases, "side.first = (setter may run)");
        let spread = position(&phases, "| expand spread argument |");
        let last_write = position(&phases, "side.last = (setter may run)");
        let check = position(&phases, "| IsConstructor |");
        let construct = position(&phases, "| Construct |");
        let root = position(&phases, "root = (setter may run)");
        assert!(
            get_key < coercion
                && coercion < getter
                && getter < ready
                && ready < first_write
                && first_write < spread
                && spread < last_write
                && last_write < check
                && check < construct
                && construct < root,
            "{phases}"
        );
        assert!(
            phases.contains("no member receiver is passed to Construct"),
            "{phases}"
        );
    }

    #[test]
    fn nested_construct_and_call_evaluate_inside_outer_argument_list() {
        let source = format!(
            "function f(C,D,side){{root=new C(side.first=1, new D(side.nested=2),             side.last=3,{});}}",
            long_effects()
        );
        let phases = plan(&source);
        let outer_ready = position(&phases, "| constructor ready | C;");
        let first = position(&phases, "side.first = (setter may run)");
        let inner_ready = position(&phases, "| constructor ready | D;");
        let inner_write = position(&phases, "side.nested = (setter may run)");
        let first_construct = position(&phases, "| Construct |");
        let last = position(&phases, "side.last = (setter may run)");
        let second_construct = phases.rfind("| Construct |").unwrap_or(usize::MAX);
        assert!(
            outer_ready < first
                && first < inner_ready
                && inner_ready < inner_write
                && inner_write < first_construct
                && first_construct < last
                && last < second_construct,
            "{phases}"
        );
        assert_eq!(phases.matches("| Construct |").count(), 2, "{phases}");
    }

    #[test]
    fn constructor_with_no_explicit_args_and_conditional_callee() {
        let source = format!(
            "function f(side,C,D,choose){{root=(side.pre=1,              new (choose?C:D), {});}}",
            long_effects()
        );
        let phases = plan(&source);
        assert!(phases.contains("| test truthy |"), "{phases}");
        assert!(phases.contains("| test falsy |"), "{phases}");
        let check = position(&phases, "| IsConstructor |");
        let construct = position(&phases, "| Construct |");
        assert!(check < construct, "{phases}");
        assert_eq!(phases.matches("| Construct |").count(), 1, "{phases}");
    }

    #[test]
    #[ignore = "requires Node; ECMAScript constructor evaluation-order oracle"]
    fn node_confirms_construct_after_spreads_and_invalid_callee_args() -> anyhow::Result<()> {
        use std::process::Command;
        let script = r"
const output=[];
function scenario(name,run) {
  const events=[];
  const mark=(tag,value)=>{events.push(tag);return value;};
  const iter={ [Symbol.iterator](){events.push('iterator');let i=0;return{
    next(){events.push('next:'+i);return i++<2?{value:i,done:false}:{done:true};}
  }}};
  class C { constructor(...args){events.push('ctor:'+args.length);} }
  const holder={get C(){events.push('getter');return C}};
  try {run({events,mark,iter,C,holder})}
  catch(e) {events.push('throw:'+e.name)}
  output.push([name,events]);
}
scenario('member',({mark,iter,holder})=>{
  new (holder.C)(mark('first',1),...iter,mark('last',4));
});
scenario('not-a-constructor',({mark})=>{
  new (mark('ctor-value',null))(mark('argument',1));
});
scenario('nonconstructible-function',({mark})=>{
  new (mark('ctor-value',()=>{}))(mark('argument',1));
});
scenario('callee-throws',({mark})=>{
  new (function(){throw Error('lookup')}())(mark('argument',1));
});
scenario('arg-throws',({mark})=>{
  new (mark('ctor-value',null))((()=>{throw Error('arg')})());
});
scenario('proxy',({events,mark,iter,C})=>{
  const p=new Proxy(C,{construct(t,a,n){
    events.push('construct-trap:'+a.length);
    return Reflect.construct(t,a,n);
  }});
  new (mark('ctor-value',p))(...iter,mark('last',5));
});
scenario('no-args',({mark,C})=>{
  new (mark('ctor-value',C));
});
console.log(JSON.stringify(output));
";
        let result = Command::new("node").arg("-e").arg(script).output()?;
        assert!(result.status.success(), "{result:?}");
        let actual: serde_json::Value = serde_json::from_slice(&result.stdout)?;
        assert_eq!(
            actual,
            serde_json::json!([
                [
                    "member",
                    [
                        "getter", "first", "iterator", "next:0", "next:1", "next:2", "last",
                        "ctor:4"
                    ]
                ],
                [
                    "not-a-constructor",
                    ["ctor-value", "argument", "throw:TypeError"]
                ],
                [
                    "nonconstructible-function",
                    ["ctor-value", "argument", "throw:TypeError"]
                ],
                ["callee-throws", ["throw:Error"]],
                ["arg-throws", ["ctor-value", "throw:Error"]],
                [
                    "proxy",
                    [
                        "ctor-value",
                        "iterator",
                        "next:0",
                        "next:1",
                        "next:2",
                        "last",
                        "construct-trap:3",
                        "ctor:3"
                    ]
                ],
                ["no-args", ["ctor-value", "ctor:0"]]
            ])
        );
        Ok(())
    }

    #[test]
    fn literal_values_and_void_operands_have_distinct_evaluation_phases() {
        let source = format!(
            "function f(side,emit){{root=(side.a=0,side.b=false,side.c='name',             side.d=null,side.e=12n,side.f=/a/g,side.g=void 0,             side.h=void (side.inner=emit(),1),{});}}",
            long_effects()
        );
        let phases = plan(&source);
        let literals = phases.matches("| inert literal |").count();
        assert!(literals >= 5, "missing primitive literal phases: {phases}");
        assert!(phases.contains("| inert literal | false |"), "{phases}");
        assert!(phases.contains("| inert literal | 'name' |"), "{phases}");
        assert!(phases.contains("| inert literal | null |"), "{phases}");
        assert!(phases.contains("| inert literal | 12n |"), "{phases}");
        assert!(phases.contains("| create regexp |"), "{phases}");
        assert_eq!(phases.matches("| discard value |").count(), 2, "{phases}");
        let call = position(&phases, "| Call | emit;");
        let inner = position(&phases, "side.inner = (setter may run)");
        let discard = phases.rfind("| discard value |").unwrap_or(usize::MAX);
        let outer_write = position(&phases, "side.h = (setter may run)");
        assert!(
            call < inner && inner < discard && discard < outer_write,
            "{phases}"
        );
        assert!(!phases.contains("unexpanded AST subtree: void"), "{phases}");
    }

    #[test]
    fn unary_operands_preserve_reference_and_coercion_distinctions() {
        let source = format!(
            "function f(obj,side){{root=(side.a=void missing,             side.b=typeof missing,side.c=delete obj.x,             side.d=+obj,side.e=void obj.value,{});}}",
            long_effects()
        );
        let phases = plan(&source);
        let missing = position(&phases, "| GetValue identifier | missing |");
        let first_discard = position(&phases, "| discard value |");
        assert!(missing < first_discard, "{phases}");
        assert!(
            phases.contains("| typeof identifier | missing; unresolvable reference"),
            "{phases}"
        );
        assert!(phases.contains("| DeleteProperty |"), "{phases}");
        let read = position(&phases, "| GetValue identifier | obj |");
        let coercion = position(&phases, "| ToNumber | unary +;");
        assert!(read < coercion, "{phases}");
        let getter = position(&phases, "| GetValue member | property .value");
        let last_discard = phases.rfind("| discard value |").unwrap_or(usize::MAX);
        assert!(getter < last_discard, "{phases}");
    }

    #[test]
    fn templates_distinguish_conversion_order_from_tag_invocation() {
        let source = format!(
            "function f(obj,side){{root=(side.a=`a${{first()}}b${{second()}}`,side.b=obj.tag`a${{third()}}b${{fourth()}}`,{});}}",
            long_effects()
        );
        let phases = plan(&source);
        let first = position(&phases, "| Call | first;");
        let first_conversion = position(&phases, "| ToString substitution |");
        let second = position(&phases, "| Call | second;");
        let last_conversion = phases
            .rfind("| ToString substitution |")
            .unwrap_or(usize::MAX);
        let getter = position(&phases, "| GetValue member | property .tag");
        let tag = position(&phases, "| tag ready | member receiver");
        let object = position(&phases, "| GetTemplateObject |");
        let third = position(&phases, "| Call | third;");
        let fourth = position(&phases, "| Call | fourth;");
        let call = position(&phases, "| Call tag |");
        let ordered = [
            first,
            first_conversion,
            second,
            last_conversion,
            getter,
            tag,
            object,
            third,
            fourth,
            call,
        ];
        assert!(ordered.windows(2).all(|pair| pair[0] < pair[1]), "{phases}");
        assert_eq!(
            phases.matches("| ToString substitution |").count(),
            2,
            "{phases}"
        );
    }

    #[test]
    fn tagged_eval_is_not_a_direct_eval_candidate() {
        let source = format!(
            "function f(side){{root=(side.a=eval('x'),side.b=eval`x`,side.c=(0,obj.tag)`x`,{});}}",
            long_effects()
        );
        let phases = plan(&source);
        assert_eq!(
            phases.matches("direct eval candidate:").count(),
            1,
            "{phases}"
        );
        assert!(
            phases.contains("| tag ready | sequence value; member receiver discarded"),
            "{phases}"
        );
        assert_eq!(
            phases.matches("| GetTemplateObject |").count(),
            2,
            "{phases}"
        );
    }

    #[test]
    fn unary_type_and_numeric_phases_follow_operand_evaluation() {
        let source = format!(
            "function f(obj,side){{root=(side.a=typeof (missing),side.b=typeof (0,other),side.c=!first(),side.d=-second(),side.e=~third(),{});}}",
            long_effects()
        );
        let phases = plan(&source);
        let ordered = [
            position(&phases, "| typeof identifier | missing;"),
            position(&phases, "| GetValue identifier | other |"),
            position(&phases, "| typeof value |"),
            position(&phases, "| Call | first;"),
            position(&phases, "| ToBoolean |"),
            position(&phases, "| Call | second;"),
            position(&phases, "| ToNumeric | unary -;"),
            position(&phases, "| Call | third;"),
            position(
                &phases,
                &format!("| ToNumeric | {};", literal_text("unary ~")),
            ),
        ];
        assert!(ordered.windows(2).all(|pair| pair[0] < pair[1]), "{phases}");
        assert!(
            !phases.contains("| GetValue identifier | missing |"),
            "{phases}"
        );
    }

    #[test]
    #[ignore = "requires installed Node; template and unary order oracle"]
    fn node_confirms_template_and_unary_conversion_order() -> anyhow::Result<()> {
        use std::process::Command;
        let source = r"
const log = [];
function value(label) {
    log.push('eval:'+label);
    return {[Symbol.toPrimitive](hint){log.push('convert:'+label+':'+hint); return 3}};
}
const obj = {get tag(){
    log.push('get:tag');
    return function(t,a,b){log.push('tag:'+(this===obj)+':'+t.raw[0]+':'+typeof a+':'+typeof b)};
}};
const out = `x${value('a')}y${value('b')}`;
obj.tag`raw${value('c')}${value('d')}`;
try {`${Symbol()}${value('unreachable')}`} catch(e) {log.push(e.name)}
const plus = +value('plus');
const neg = -value('neg');
const bit = ~value('bit');
const not = !value('not');
log.push('typeof:'+typeof (noSuchBindingOfAnyKind));
try {typeof tdz; let tdz} catch(e) {log.push(e.name)}
console.log(JSON.stringify([out,plus,neg,bit,not,log]));
";
        let result = Command::new("node").arg("-e").arg(source).output()?;
        assert!(result.status.success(), "{result:?}");
        let values: serde_json::Value = serde_json::from_slice(&result.stdout)?;
        assert_eq!(
            values,
            serde_json::json!([
                "x3y3",
                3,
                -3,
                -4,
                false,
                [
                    "eval:a",
                    "convert:a:string",
                    "eval:b",
                    "convert:b:string",
                    "get:tag",
                    "eval:c",
                    "eval:d",
                    "tag:true:raw:object:object",
                    "TypeError",
                    "eval:plus",
                    "convert:plus:number",
                    "eval:neg",
                    "convert:neg:number",
                    "eval:bit",
                    "convert:bit:number",
                    "eval:not",
                    "typeof:undefined",
                    "ReferenceError"
                ]
            ])
        );
        Ok(())
    }

    #[test]
    #[ignore = "requires installed Node; void and getter runtime oracle"]
    fn node_confirms_void_evaluates_reads_calls_setters_and_can_throw() -> anyhow::Result<()> {
        use std::process::Command;
        let source = r"
const log = [];
const target = new Proxy({}, {
  set(o,k,v){ log.push('set:'+k);return Reflect.set(o,k,v);}
});
const obj = {get value(){log.push('getter');return 4}};
const emit = () => {log.push('call');return 9};
const value = void (obj.value, emit(), target.out = 3);
log.push('result:'+String(value));
try {void noSuchBindingOfAnyKind} catch(e) {log.push('throw:'+e.name)}
log.push('typeof:'+typeof noSuchBindingOfAnyKind);
console.log(JSON.stringify(log));
";
        let result = Command::new("node").arg("-e").arg(source).output()?;
        assert!(result.status.success(), "{result:?}");
        let values: serde_json::Value = serde_json::from_slice(&result.stdout)?;
        assert_eq!(
            values,
            serde_json::json!([
                "getter",
                "call",
                "set:out",
                "result:undefined",
                "throw:ReferenceError",
                "typeof:undefined"
            ])
        );
        Ok(())
    }

    #[test]
    #[ignore = "requires installed Node; direct evaluation-order oracle"]
    fn node_confirms_call_spread_array_and_object_evaluation_phases() -> anyhow::Result<()> {
        use std::process::Command;
        let script = r"
const events=[];
const mark=(name,val)=>{events.push(name);return val;};
const obj=new Proxy({run(...args){
  events.push(this===obj?'call:this-ok':'call:this-lost');return args.length;
}}, {get(t,k,r){events.push('get:'+String(k));return Reflect.get(t,k,r)}});
const iterable={
  [Symbol.iterator](){events.push('iterator');let i=0;return{
    next(){events.push('next:'+i);return i++<2?{value:i,done:false}:{done:true};}
  }}
};
obj[mark('key-expr','run')](mark('arg1',1),...iterable,mark('arg3',3));
const call=events.splice(0);
const key={ [Symbol.toPrimitive](){events.push('key-coerce');return 'a';}};
const src=new Proxy({get b(){events.push('spread-get');return 2;}},{
  ownKeys(t){events.push('spread-keys');return Reflect.ownKeys(t)},
  getOwnPropertyDescriptor(t,k){events.push('spread-desc');return Reflect.getOwnPropertyDescriptor(t,k)},
  get(t,k){events.push('spread-proxy-get');return Reflect.get(t,k)}
});
const object={[mark('keyexpr',key)]:mark('value',1),...src,
  after:mark('after',3), get deferred(){events.push('deferred-body');return 4;}};
const objectTrace=events.splice(0);
const array=[mark('array-first',1),...iterable,mark('array-last',4)];
const arrayTrace=events.splice(0);
const other={get run(){events.push('get-fn');return function(){
  events.push(this===other?'receiver-ok':'receiver-lost');
}}};
(other.run)(mark('arg',1));
const memberTrace=events.splice(0);
(0,other.run)(mark('arg',1));
const sequenceTrace=events.splice(0);
try{null.run(mark('should-not-run',1))}catch{events.push('throw')}
const nullTrace=events.splice(0);
const optional=null;
optional?.run(mark('should-not-run',1));
const optionalTrace=events.splice(0);
console.log(JSON.stringify({call,objectTrace,arrayTrace,memberTrace,
  sequenceTrace,nullTrace,optionalTrace,objectKeys:Object.keys(object),array}));
";
        let result = Command::new("node").arg("-e").arg(script).output()?;
        assert!(result.status.success(), "{result:?}");
        let value: serde_json::Value = serde_json::from_slice(&result.stdout)?;
        assert_eq!(
            value["call"],
            serde_json::json!([
                "key-expr",
                "get:run",
                "arg1",
                "iterator",
                "next:0",
                "next:1",
                "next:2",
                "arg3",
                "call:this-ok"
            ])
        );
        assert_eq!(
            value["objectTrace"],
            serde_json::json!([
                "keyexpr",
                "key-coerce",
                "value",
                "spread-keys",
                "spread-desc",
                "spread-proxy-get",
                "spread-get",
                "after"
            ])
        );
        assert_eq!(
            value["arrayTrace"],
            serde_json::json!([
                "array-first",
                "iterator",
                "next:0",
                "next:1",
                "next:2",
                "array-last"
            ])
        );
        assert_eq!(
            value["memberTrace"],
            serde_json::json!(["get-fn", "arg", "receiver-ok"])
        );
        assert_eq!(
            value["sequenceTrace"],
            serde_json::json!(["get-fn", "arg", "receiver-lost"])
        );
        assert_eq!(value["nullTrace"], serde_json::json!(["throw"]));
        assert_eq!(value["optionalTrace"], serde_json::json!([]));
        assert_eq!(
            value["objectKeys"],
            serde_json::json!(["a", "b", "after", "deferred"])
        );
        assert_eq!(value["array"], serde_json::json!([1, 1, 2, 4]));
        Ok(())
    }

    #[test]
    #[ignore = "requires installed Node; differential runtime oracle"]
    #[expect(
        clippy::literal_string_with_formatting_args,
        reason = "JavaScript fixture braces are source syntax, not Rust format placeholders"
    )]
    fn node_confirms_computed_key_getvalue_vs_putvalue_coercion_order() -> anyhow::Result<()> {
        use std::process::Command;
        let script = r"
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
";
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
