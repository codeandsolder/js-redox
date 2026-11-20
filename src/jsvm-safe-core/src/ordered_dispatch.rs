//! Recover dispatch control flow without treating a predicted array order as
//! the actual result of JavaScript property lookup. The dynamic path retains
//! all selector/case evaluations and the enclosing iteration. The finite path
//! requires a fresh, private dense array and a proved exit before exhaustion.
use crate::{
    array_element, completion, fragment,
    statement_hazards::DeclarationHazard,
    statically_resolved_symbol,
    trivial_loops::LoopBodyControl,
    value_eval::{eval, known_bool, Value},
    Collector,
};
use oxc_ast::ast::{
    BindingPattern, Expression, ForStatement, ForStatementInit, Statement, SwitchStatement,
    VariableDeclarationKind,
};
use oxc_ast_visit::Visit;
use oxc_span::{GetSpan, Span};
use std::{
    collections::{HashMap, HashSet},
    fmt::Write as _,
};

#[derive(Default)]
struct EvalHazard(bool);
impl<'a> Visit<'a> for EvalHazard {
    fn visit_identifier_reference(&mut self, node: &oxc_ast::ast::IdentifierReference<'a>) {
        // Includes parenthesized direct eval, and eval in nested closures.
        self.0 |= node.name == "eval";
    }
}

fn cannot_complete_normally(statement: &Statement<'_>) -> bool {
    match statement {
        Statement::BreakStatement(_)
        | Statement::ContinueStatement(_)
        | Statement::ReturnStatement(_)
        | Statement::ThrowStatement(_) => true,
        Statement::BlockStatement(block) => block.body.last().is_some_and(cannot_complete_normally),
        Statement::IfStatement(branch) => {
            cannot_complete_normally(&branch.consequent)
                && branch
                    .alternate
                    .as_ref()
                    .is_some_and(cannot_complete_normally)
        }
        _ => false,
    }
}

/// The original switch is immediately followed by the loop's terminal break.
/// A break consumed by the switch would therefore exit that same loop next,
/// with the very same completion value. Keeping it in an if arm is equivalent.
/// Continues still target the unchanged enclosing loop.
fn dispatch_switch<'a>(
    body: &'a Statement<'a>,
    collector: &Collector<'_, '_>,
    loop_span: Span,
) -> Option<&'a SwitchStatement<'a>> {
    let Statement::BlockStatement(block) = body else {
        return None;
    };
    let [Statement::SwitchStatement(switch), Statement::BreakStatement(tail)] =
        block.body.as_slice()
    else {
        return None;
    };
    if tail.label.is_some()
        || switch.cases.len() < 2
        || !collector
            .scoping
            .get_bindings(switch.scope_id.get()?)
            .is_empty()
    {
        return None;
    }
    let mut hazard = EvalHazard::default();
    hazard.visit_switch_statement(switch);
    if hazard.0 {
        return None;
    }
    // A shared lexical switch binding cannot be separated into independent
    // if arms. In particular, avoid changing Annex B declaration semantics.
    if switch.cases.iter().any(|case| {
        case.consequent.iter().any(|stmt| {
            matches!(
                stmt,
                Statement::FunctionDeclaration(_) | Statement::ClassDeclaration(_)
            )
        })
    }) {
        return None;
    }
    // No duplicated or skipped fallthrough code. Last case can naturally exit.
    if switch
        .cases
        .iter()
        .take(switch.cases.len() - 1)
        .any(|case| !case.consequent.last().is_some_and(cannot_complete_normally))
    {
        return None;
    }
    if !switch.cases.iter().any(|case| {
        LoopBodyControl::analyze(&case.consequent, loop_span, &collector.active_labels)
            .continues_loop
    }) {
        return None;
    }
    Some(switch)
}

fn statement_text<'s>(source: &'s str, statements: &[Statement<'_>]) -> Option<&'s str> {
    match (statements.first(), statements.last()) {
        (Some(first), Some(last)) => {
            source.get(first.span().start as usize..last.span().end as usize)
        }
        _ => Some(""),
    }
}

#[derive(PartialEq, Eq, Hash)]
enum StrictKey<'a> {
    String(&'a str),
    Number(u64),
    Bool(bool),
    Null,
    Undefined,
}

impl<'a> StrictKey<'a> {
    fn from_value(value: &'a Value) -> Option<Self> {
        Some(match value {
            Value::String(value) => Self::String(value),
            Value::Number(value) if value.is_nan() => return None,
            Value::Number(value) => Self::Number(if *value == 0.0 { 0 } else { value.to_bits() }),
            Value::Bool(value) => Self::Bool(*value),
            Value::Null => Self::Null,
            Value::Undefined => Self::Undefined,
        })
    }
}

impl Collector<'_, '_> {
    /// Structure independent switch arms while keeping the original loop,
    /// initializer, case-label evaluations, property lookup, and updates.
    /// This works even with a proxy, a mutated split method, or an inherited
    /// terminal array index. Nothing relies on predicted selector values.
    pub(super) fn structure_dispatch_switch(
        &self,
        body: &Statement<'_>,
        loop_span: Span,
    ) -> Option<(Span, String)> {
        let switch = dispatch_switch(body, self, loop_span)?;
        let mut serial = 0;
        let name = loop {
            let candidate = format!("__jsvm_selector_{}_{}", switch.span.start, serial);
            if !self.source.contains(&candidate)
                && !self.scoping.symbol_names().any(|name| name == candidate)
                && !self
                    .scoping
                    .root_unresolved_references()
                    .contains_key(candidate.as_str())
            {
                break candidate;
            }
            serial += 1;
        };
        // Comma value suppresses NamedEvaluation for anonymous functions.
        let mut text = format!(
            "{{\nconst {name} = (0, ({}\n));\n",
            fragment(self.source, switch.discriminant.span())
        );
        let mut default = None;
        let mut first = true;
        for case in &switch.cases {
            let Some(test) = &case.test else {
                default = Some(case);
                continue;
            };
            if !first {
                text.push_str(" else ");
            }
            first = false;
            write!(
                text,
                "if ({name} === ({}\n)) {{\n{}\n}}",
                fragment(self.source, test.span()),
                statement_text(self.source, &case.consequent)?
            )
            .ok()?;
        }
        if let Some(case) = default {
            if !first {
                text.push_str(" else ");
            }
            write!(
                text,
                "{{\n{}\n}}",
                statement_text(self.source, &case.consequent)?
            )
            .ok()?;
        }
        text.push_str("\n}");
        Some((switch.span, text))
    }

    /// Full straight-line recovery for a lexical loop-local dense literal
    /// table, when its own entries guarantee an exit. Out-of-bounds reads
    /// are deliberately not considered undefined: prototypes may supply one.
    pub(super) fn bounded_dispatch_replacement(&self, it: &ForStatement<'_>) -> Option<String> {
        if it.update.is_some()
            || it
                .test
                .as_ref()
                .is_some_and(|test| known_bool(test) != Some(true))
        {
            return None;
        }
        let switch = dispatch_switch(&it.body, self, it.span)?;
        let Some(ForStatementInit::VariableDeclaration(init)) = &it.init else {
            return None;
        };
        if init.kind != VariableDeclarationKind::Let || init.declarations.len() != 2 {
            return None;
        }
        let Expression::ComputedMemberExpression(selector) = &switch.discriminant else {
            return None;
        };
        if selector.optional {
            return None;
        }
        let Expression::Identifier(order) = &selector.object else {
            return None;
        };
        let Expression::UpdateExpression(update) = &selector.expression else {
            return None;
        };
        if update.prefix || update.operator.as_str() != "++" {
            return None;
        }
        let oxc_ast::ast::SimpleAssignmentTarget::AssignmentTargetIdentifier(counter) =
            &update.argument
        else {
            return None;
        };
        let order_ref = order.reference_id.get()?;
        let counter_ref = counter.reference_id.get()?;
        let order = statically_resolved_symbol(self.scoping, order_ref)?;
        let counter = statically_resolved_symbol(self.scoping, counter_ref)?;
        if order == counter
            || self.scoping.get_resolved_reference_ids(order) != [order_ref]
            || self.scoping.get_resolved_reference_ids(counter) != [counter_ref]
        {
            return None;
        }
        let mut values = None;
        let mut zero = false;
        for decl in &init.declarations {
            let BindingPattern::BindingIdentifier(id) = &decl.id else {
                return None;
            };
            let symbol = id.symbol_id.get()?;
            let expr = decl.init.as_ref()?;
            if symbol == order {
                let Expression::ArrayExpression(array) = expr else {
                    return None;
                };
                values = Some(
                    array
                        .elements
                        .iter()
                        .map(array_element)
                        .collect::<Option<Vec<_>>>()?,
                );
            } else if symbol == counter {
                zero = matches!(eval(expr), Some(Value::Number(n)) if n == 0.0);
            } else {
                return None;
            }
        }
        if !zero {
            return None;
        }
        let values = values?;
        let mut labels = Vec::with_capacity(switch.cases.len());
        for case in &switch.cases {
            labels.push(match &case.test {
                Some(test) => Some(eval(test)?),
                None => None,
            });
        }
        let default = labels.iter().position(Option::is_none);
        let mut cases = HashMap::with_capacity(labels.len());
        for (index, value) in labels.iter().enumerate() {
            if let Some(key) = value.as_ref().and_then(StrictKey::from_value) {
                cases.entry(key).or_insert(index);
            }
        }
        let mut selected = HashSet::new();
        let mut chunks = Vec::new();
        let mut terminated = false;
        let live = self.completion.needs_value(it.span);
        for value in &values {
            let Some(index) = StrictKey::from_value(value)
                .and_then(|key| cases.get(&key).copied())
                .or(default)
            else {
                // An unmatched *own* dense entry exits the switch and loop.
                if live {
                    chunks.push("void 0;".to_owned());
                }
                terminated = true;
                break;
            };
            if !selected.insert(index) {
                return None;
            } // do not clone effects
            let case = &switch.cases[index];
            let (last, prefix) = case.consequent.split_last()?;
            let (retained, exits) = match last {
                Statement::ContinueStatement(node) if node.label.is_none() => (prefix, false),
                Statement::BreakStatement(node) if node.label.is_none() => (prefix, true),
                Statement::ReturnStatement(_) | Statement::ThrowStatement(_) => {
                    (case.consequent.as_slice(), true)
                }
                _ => return None,
            };
            let control = LoopBodyControl::analyze(retained, it.span, &self.active_labels);
            if control.exits_loop || control.continues_loop {
                return None;
            }
            let content = statement_text(self.source, retained)?;
            // The switch creates a new accumulator initialized to undefined
            // on each iteration. Empty selected arms must reset it as well.
            chunks.push(if live {
                completion::seed_undefined(content)
            } else {
                format!("{{\n{content}\n}}")
            });
            if exits {
                terminated = true;
                break;
            }
        }
        if !terminated {
            return None;
        }
        // Removing a never-selected arm must not remove var/Annex B hoisting.
        for (index, case) in switch.cases.iter().enumerate() {
            if !selected.contains(&index)
                && DeclarationHazard::Discard.present(&case.consequent.iter().collect::<Vec<_>>())
            {
                return None;
            }
        }
        Some(format!("{{\n{}\n}}", chunks.join("\n")))
    }
}

#[cfg(test)]
mod tests {
    use crate::deobfuscate;
    use work_budget::{BudgetExceeded, WorkBudget};

    #[test]
    fn bounded_dispatch_requires_owned_exit_and_private_bindings() -> Result<(), BudgetExceeded> {
        let bounded = "for(let a=[1,'1',true,0],i=0;;){switch(a[i++]){case '1':work('B');continue;case 1:work('A');continue;case true:work('C');continue;case 0:work('D');break;}break;}";
        let result = deobfuscate(bounded, 32, &WorkBudget::unlimited("bounded-dispatch"))?
            .unwrap_or_else(|| unreachable!());
        assert_eq!(result.transforms.get("ordered_switch_unflatten"), Some(&1));
        let positions = ["work('A')", "work('B')", "work('C')", "work('D')"]
            .map(|text| result.source.find(text));
        assert!(positions.iter().all(Option::is_some), "{}", result.source);
        assert!(positions.windows(2).all(|p| p[0] < p[1]));
        assert!(!result.source.contains("switch"), "{}", result.source);
        for input in [
            "for(let a=[1,2],i=0;;){switch(a[i++]){case 1:work();continue;case 2:other();continue;}break;}",
            "for(let a=[1,2],i=0;;){switch(a[i++]){case 1:work(i);continue;case 2:other();break;}break;}",
            "const a=[1,2];const i=0;while(true){switch(a[i++]){case 1:work();continue;case 2:other();break;}break;}",
            "for(var a=[1,2],i=0;;){switch(a[i++]){case 1:work();continue;case 2:other();break;}break;}",
        ] {
            let result = deobfuscate(input, 32, &WorkBudget::unlimited("dynamic-dispatch"))?.unwrap_or_else(|| unreachable!());
            assert_eq!(result.transforms.get("ordered_switch_unflatten"), None, "{}", result.source);
            assert_eq!(result.transforms.get("dispatch_switch_structured"), Some(&1), "{}", result.source);
            assert!(result.source.contains("a[i++]"), "{}", result.source);
        }
        Ok(())
    }

    #[test]
    fn shared_bindings_fallthrough_and_eval_block_dispatch_relocation() -> Result<(), BudgetExceeded>
    {
        for source in [
            "while(true){switch(next()){case 0:let x=1;continue;case 1:work(x);break;}break;}",
            "while(true){switch(next()){case 0:work();case 1:other();continue;}break;}",
            "while(true){switch(next()){case 0:(eval)('work()');continue;case 1:other();break;}break;}",
        ] {
            let result = deobfuscate(source, 32, &WorkBudget::unlimited("dispatch-hazards"))?.unwrap_or_else(|| unreachable!());
            assert!(!result.transforms.contains_key("dispatch_switch_structured"), "{}", result.source);
            assert!(result.source.contains("switch"));
        }
        Ok(())
    }
}
