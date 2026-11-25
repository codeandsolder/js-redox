//! Recover dispatch control flow without treating a predicted array order as
//! the actual result of JavaScript property lookup. The dynamic path retains
//! all selector/case evaluations and the enclosing iteration. The finite path
//! requires a fresh, private dense array and a proved exit before exhaustion.
use crate::{
    completion, fragment,
    numeric::exact_usize,
    reference_is_statically_resolved_read,
    statement_hazards::DeclarationHazard,
    statically_resolved_symbol,
    trivial_loops::LoopBodyControl,
    value_eval::{
        canonical_array_index, eval, eval_with_resolver, inert_literal_value,
        known_bool_with_resolver, strict_primitive_equal, Value,
    },
    Collector,
};
use oxc_ast::ast::{
    BindingPattern, Expression, ForStatement, ForStatementInit, Statement, SwitchStatement,
    VariableDeclarationKind,
};
use oxc_ast_visit::Visit;
use oxc_semantic::{ReferenceId, Scoping};
use oxc_span::{GetSpan, Span};
use oxc_syntax::symbol::SymbolId;
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
    let [.., Statement::SwitchStatement(switch), Statement::BreakStatement(tail)] =
        block.body.as_slice()
    else {
        return None;
    };
    if tail.label.is_some()
        || switch.cases.is_empty()
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

/// Exact primitive facts for a single private dispatch loop activation.
/// A dense literal has own data properties for its indices and length; no
/// other member read is justified, even when standard prototypes seem likely.
struct PrivateDispatchEnvironment<'a> {
    scoping: &'a Scoping,
    order: SymbolId,
    counter: SymbolId,
    values: Vec<Value>,
    index: f64,
}

impl PrivateDispatchEnvironment<'_> {
    fn read_symbol(&self, expr: &Expression<'_>) -> Option<SymbolId> {
        let Expression::Identifier(id) = expr else {
            return None;
        };
        let reference = id.reference_id.get()?;
        let symbol = statically_resolved_symbol(self.scoping, reference)?;
        reference_is_statically_resolved_read(self.scoping, reference, symbol).then_some(symbol)
    }

    fn length(&self) -> Option<Value> {
        Some(Value::Number(f64::from(
            u32::try_from(self.values.len()).ok()?,
        )))
    }

    fn resolve(&self, expr: &Expression<'_>) -> Option<Value> {
        match expr {
            Expression::Identifier(_) if self.read_symbol(expr) == Some(self.counter) => {
                Some(Value::Number(self.index))
            }
            Expression::StaticMemberExpression(member)
                if !member.optional
                    && self.read_symbol(&member.object) == Some(self.order)
                    && member.property.name == "length" =>
            {
                self.length()
            }
            Expression::ComputedMemberExpression(member)
                if !member.optional && self.read_symbol(&member.object) == Some(self.order) =>
            {
                let key = self.value(&member.expression)?;
                if matches!(&key, Value::String(text) if text == "length") {
                    self.length()
                } else {
                    self.values
                        .get(usize::try_from(canonical_array_index(&key)?).ok()?)
                        .cloned()
                }
            }
            _ => None,
        }
    }

    fn value(&self, expr: &Expression<'_>) -> Option<Value> {
        eval_with_resolver(expr, &|expr| self.resolve(expr))
    }

    fn test(&self, expr: &Expression<'_>) -> Option<bool> {
        known_bool_with_resolver(expr, &|expr| self.resolve(expr))
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
        if let [case] = switch.cases.as_slice() {
            if case.test.is_none() {
                let selector = fragment(self.source, switch.discriminant.span());
                let arm = statement_text(self.source, &case.consequent)?;
                return Some((
                    switch.span,
                    format!("{{\nvoid ({selector}\n);\n{{\n{arm}\n}}\n}}"),
                ));
            }
        }

        let mut serial = 0;
        let name = loop {
            let candidate = format!("__jsvm_selector_{}_{serial}", switch.span.start);
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
            let Some(case_label) = &case.test else {
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
                fragment(self.source, case_label.span()),
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

    fn dispatch_references_are_private(
        &self,
        symbol: SymbolId,
        selector: ReferenceId,
        regions: &[Span],
    ) -> bool {
        self.scoping
            .get_resolved_reference_ids(symbol)
            .iter()
            .all(|reference| {
                *reference == selector
                    || (reference_is_statically_resolved_read(self.scoping, *reference, symbol)
                        && self.reference_spans.get(reference).is_some_and(|span| {
                            regions
                                .iter()
                                .any(|region| region.start <= span.start && span.end <= region.end)
                        }))
            })
    }

    /// Prove private binding identities and evaluate the dense literal only
    /// after all references and initializer effects have been accounted for.
    fn private_dispatch_environment(
        &self,
        it: &ForStatement<'_>,
        switch: &SwitchStatement<'_>,
    ) -> Option<PrivateDispatchEnvironment<'_>> {
        let Statement::BlockStatement(body) = &it.body else {
            return None;
        };
        if body.body.len() != 2 {
            return None;
        }
        let Some(ForStatementInit::VariableDeclaration(init)) = &it.init else {
            return None;
        };
        if init.kind != VariableDeclarationKind::Let {
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
        let analyzed_regions = it
            .test
            .iter()
            .map(GetSpan::span)
            .chain(it.update.iter().map(GetSpan::span))
            .chain(
                switch
                    .cases
                    .iter()
                    .filter_map(|case| case.test.as_ref().map(GetSpan::span)),
            )
            .collect::<Vec<_>>();
        if order == counter
            || !self.dispatch_references_are_private(order, order_ref, &analyzed_regions)
            || !self.dispatch_references_are_private(counter, counter_ref, &analyzed_regions)
        {
            return None;
        }
        let mut values = None;
        let mut initial = None;
        for decl in &init.declarations {
            let BindingPattern::BindingIdentifier(id) = &decl.id else {
                return None;
            };
            let symbol = id.symbol_id.get()?;
            if symbol == order {
                let Expression::ArrayExpression(array) = decl.init.as_ref()? else {
                    return None;
                };
                values = Some(
                    array
                        .elements
                        .iter()
                        .map(|element| eval(element.as_expression()?))
                        .collect::<Option<Vec<_>>>()?,
                );
            } else if symbol == counter {
                let Value::Number(value) = eval(decl.init.as_ref()?)? else {
                    return None;
                };
                initial = Some(value);
            } else if !self.scoping.get_resolved_reference_ids(symbol).is_empty()
                || decl
                    .init
                    .as_ref()
                    .is_some_and(|expr| !inert_literal_value(expr) && eval(expr).is_none())
            {
                // An unused, pure additional declarator has no observable
                // initializer or per-iteration binding identity.
                return None;
            }
        }
        Some(PrivateDispatchEnvironment {
            scoping: self.scoping,
            order,
            counter,
            values: values?,
            index: initial?,
        })
    }

    /// Identify the exact statements retained by a selected arm and whether
    /// it exits the original loop. Reject fallthrough and foreign continues.
    fn retained_dispatch_arm<'a>(
        &self,
        switch: &'a SwitchStatement<'a>,
        index: usize,
        loop_span: Span,
    ) -> Option<(&'a [Statement<'a>], bool)> {
        let case = &switch.cases[index];
        match case.consequent.split_last() {
            Some((Statement::ContinueStatement(node), prefix))
                if node.label.as_ref().is_none_or(|label| {
                    self.active_labels
                        .iter()
                        .any(|(span, name)| *span == loop_span && name == label.name.as_str())
                }) =>
            {
                Some((prefix, false))
            }
            Some((Statement::BreakStatement(node), prefix)) if node.label.is_none() => {
                Some((prefix, true))
            }
            Some((last, _))
                if cannot_complete_normally(last) || index + 1 == switch.cases.len() =>
            {
                Some((case.consequent.as_slice(), true))
            }
            None if index + 1 == switch.cases.len() => Some((case.consequent.as_slice(), true)),
            _ => None,
        }
    }

    /// Full straight-line recovery for a lexical loop-local dense literal
    /// table, when its own entries guarantee an exit. Out-of-bounds reads
    /// are deliberately not considered undefined: prototypes may supply one.
    pub(super) fn bounded_dispatch_replacement(&self, it: &ForStatement<'_>) -> Option<String> {
        let switch = dispatch_switch(&it.body, self, it.span)?;
        let mut environment = self.private_dispatch_environment(it, switch)?;
        // Constant labels get an O(1) typed lookup. Otherwise evaluate only
        // the actually examined labels in source order with the postincrement
        // counter value. An unknown or effectful examined label rejects the
        // finite proof instead of assuming it unmatched.
        let static_labels = switch
            .cases
            .iter()
            .map(|case| {
                case.test
                    .as_ref()
                    .map_or(Some(None), |expr| eval(expr).map(Some))
            })
            .collect::<Option<Vec<_>>>();
        let default = switch.cases.iter().position(|case| case.test.is_none());
        let constant_cases = static_labels.as_ref().map(|labels| {
            let mut cases = HashMap::with_capacity(labels.len());
            for (index, value) in labels.iter().enumerate() {
                if let Some(key) = value.as_ref().and_then(StrictKey::from_value) {
                    cases.entry(key).or_insert(index);
                }
            }
            cases
        });
        let mut selected = HashSet::new();
        let mut chunks = Vec::new();
        let live = self.completion.needs_value(it.span);
        let mut needs_break_region = false;
        loop {
            self.budget.checkpoint().ok()?;
            if !it
                .test
                .as_ref()
                .map_or(Some(true), |test| environment.test(test))?
            {
                if live && chunks.is_empty() {
                    chunks.push("void 0;".to_owned());
                }
                break;
            }
            // Only the proven own data slot may be read. Negative, fractional
            // or exhausted indices would require a dynamic property lookup.
            let value = environment.values.get(exact_usize(environment.index)?)?;
            environment.index += 1.0; // dense array indices are exactly representable
            let matched = if let Some(cases) = &constant_cases {
                StrictKey::from_value(value).and_then(|key| cases.get(&key).copied())
            } else {
                let mut matched = None;
                for (index, case) in switch.cases.iter().enumerate() {
                    self.budget.checkpoint().ok()?;
                    if let Some(test) = &case.test {
                        if strict_primitive_equal(value, &environment.value(test)?) {
                            matched = Some(index);
                            break;
                        }
                    }
                }
                matched
            };
            let Some(index) = matched.or(default) else {
                if live {
                    chunks.push("void 0;".to_owned());
                }
                break;
            };
            if !selected.insert(index) {
                return None;
            } // do not clone effects
            let (retained, exits) = self.retained_dispatch_arm(switch, index, it.span)?;
            let control = LoopBodyControl::analyze(retained, it.span, &self.active_labels);
            if control.continues_loop {
                return None;
            }
            needs_break_region |= control.exits_loop;
            let content = statement_text(self.source, retained)?;
            // Each original switch created an accumulator initialized to undefined.
            chunks.push(if live {
                completion::seed_undefined(content)
            } else {
                format!("{{\n{content}\n}}")
            });
            if exits {
                break;
            }
            if it.update.as_ref().is_some_and(|update| {
                !inert_literal_value(update) && environment.value(update).is_none()
            }) {
                return None;
            }
        }
        // Removing a never-selected arm must not remove var/Annex B hoisting.
        for (index, case) in switch.cases.iter().enumerate() {
            if !selected.contains(&index)
                && DeclarationHazard::Discard.present(&case.consequent.iter().collect::<Vec<_>>())
            {
                return None;
            }
        }
        let content = chunks.join("\n");
        Some(if needs_break_region {
            format!("do {{\n{content}\n}} while (false);")
        } else {
            format!("{{\n{content}\n}}")
        })
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
    fn private_value_environment_proves_bounds_reads_and_pure_labels() -> Result<(), BudgetExceeded>
    {
        for source in [
            "for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case 1:work();continue;case 2:other();continue;}break;}",
            "for(let a=[1],i=0;i<a.length;){switch(a[i++]){case 1:work();continue;}break;}",
            "for(let a=[1],i=0;i<a.length;){switch(a[i++]){default:work();continue;}break;}",
            "for(let a=[0,1,2],i=1;i<a['length']&&a[i]!==2;){switch(a[i++]){case 1:work();continue;case 2:other();continue;}break;}",
            "for(let a=[1,3],i=0;i<a.length;a.length){switch(a[i++]){case i:work();continue;case i+1:other();continue;}break;}",
            "for(let a=[1,2],i=-0;1/i<0;){switch(a[i++]){case 1:work();continue;case 2:other();continue;}break;}",
            "for(let a=[1,2],i=-1;i>=0;){switch(a[i++]){case 1:work();continue;case 2:other();continue;}break;}",
            "for(let a=[1,2],i=0;i<1;){switch(a[i++]){case i:work();continue;case sideEffect():other();continue;}break;}",
            "for(let a=[1,2],i=0,unused=void 0;i<a.length;){switch(a[i++]){case 1:if(check())break;work();continue;case 2:other();}break;}",
            "again:for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case 1:work();continue again;case 2:other();continue again;}break;}",
        ] {
            let result = deobfuscate(source, 32, &WorkBudget::unlimited("private-dispatch-values"))?.unwrap_or_else(|| unreachable!());
            assert_eq!(result.transforms.get("ordered_switch_unflatten"), Some(&1), "{source} -> {}",result.source);
            assert!(!result.source.contains("switch"), "{}", result.source);
            assert!(result.analysis_complete);
        }
        for source in [
            "for(let a=[1,2],i=0;i<a.length;effect()){switch(a[i++]){case 1:work();continue;case 2:other();continue;}break;}",
            "for(let a=[1,2],i=0;i<a.length;a[i]){switch(a[i++]){case 1:work();continue;case 2:other();continue;}break;}",
            "for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case effect():other();continue;case 1:work();continue;}break;}",
            "for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case 1:if(check())continue;work();continue;case 2:other();continue;}break;}",
        ] {
            let result = deobfuscate(source, 32, &WorkBudget::unlimited("dynamic-dispatch-values"))?.unwrap_or_else(|| unreachable!());
            assert!(!result.transforms.contains_key("ordered_switch_unflatten"), "{source} -> {}",result.source);
            assert!(result.transforms.contains_key("dispatch_switch_structured"), "{}", result.source);
        }
        Ok(())
    }

    /// Compare the actual `ScriptEvaluation` Completion Record, not only
    /// emitted effects. In particular Empty is distinct from an explicit
    /// undefined completion, and an abrupt path may bypass a trailing arm.
    #[test]
    #[ignore = "requires Node; script completion and exception differential oracle"]
    fn bounded_dispatch_preserves_script_completion_across_exit_shapes(
    ) -> Result<(), Box<dyn std::error::Error>> {
        use std::process::Command;

        fn observe(source: &str) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
            let harness = r"
const vm=require('node:vm');
const events=[];
const context={
  work(label) {events.push(label); return 'value:'+label;},
  tick(label) {events.push('tick:'+label); return undefined;}
};
try {
  const options={};options.timeout=2000;
  const value=vm.runInNewContext(process.argv[1],context,options);
  console.log(JSON.stringify({
    kind:value===undefined?'undefined':typeof value,
    value:value===undefined?null:value,
    events
  }));
} catch(error) {
  console.log(JSON.stringify({kind:'throw',name:error.name,events}));
}
";
            let result = Command::new("node")
                .arg("-e")
                .arg(harness)
                .arg(source)
                .output()?;
            assert!(result.status.success(), "{source}: {result:?}");
            Ok(serde_json::from_slice(&result.stdout)?)
        }

        let cases = [
            "for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case 1:work('A');continue;case 2:work('B');break;}break;}",
            "for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case 1:work('A');continue;case 2:;break;}break;}",
            "for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case 1:work('A');continue;case 2:;continue;}break;}",
            "for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case 1:work('A');continue;case 2:try{work('B');}finally{work('F');}break;}break;}",
            "for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case 1:work('A');continue;case 2:throw new Error('fail');}break;}",
            "for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case 1:work('A');continue;case 2:work('B');continue;}break;}",
            "for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case 1:work('A');continue;case 2:work('B');continue;}break;} 999;",
            "1;for(let a=[2],i=0;i<a.length;){switch(a[i++]){case 1:work('A');continue;case 2:work('B');break;}break;}",
            "1;for(let a=[9],i=0;i<a.length;){switch(a[i++]){case 1:work('A');continue;case 2:work('B');break;}break;}",
            "for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case 1:tick('A');continue;case 2:work('B');break;}break;}",
            "for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case 1:work('A');continue;case 2:work('B');break;}break;} var unused;",
            "try {for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case 1:work('A');continue;case 2:work('B');break;}break;}} finally {tick('finally');}",
            "outer:{for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case 1:work('A');continue;case 2:work('B');break;}break;}}",
        ];
        let mut transformations = 0;
        for source in cases {
            let recovered = deobfuscate(
                source,
                16,
                &WorkBudget::unlimited("completion-dispatch-oracle"),
            )?
            .ok_or_else(|| std::io::Error::other("valid source must recover"))?;
            transformations += recovered
                .transforms
                .get("ordered_switch_unflatten")
                .copied()
                .unwrap_or(0);
            let original = observe(source)?;
            let rewritten = observe(&recovered.source)?;
            assert_eq!(
                original, rewritten,
                "Completion Record mismatch:
ORIGINAL: {source}
REWRITTEN: {}
TRANSFORMS: {:?}",
                recovered.source, recovered.transforms,
            );
        }
        assert!(
            transformations >= 5,
            "expected to exercise bounded dispatch"
        );
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
