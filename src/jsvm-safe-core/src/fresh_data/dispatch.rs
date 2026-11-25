//! Exact normal dispatcher traces derived from the reaching allocation heap.
//! Selection is evaluated in source order, never from a predicted table shape.
use super::{
    flow::{CompletionValue, Flow, Transfer},
    Analyzer, Environment, Fact, Observation, ReachingObservations,
};
use crate::{
    completion, control_flow::statement_has_loop_control, fragment,
    statement_hazards::DeclarationHazard,
};
use oxc_ast::ast::{
    ForStatement, ForStatementInit, Statement, SwitchStatement, VariableDeclarationKind,
};
use oxc_semantic::Scoping;
use oxc_span::GetSpan;
use std::fmt::Write;

#[derive(PartialEq, Eq)]
struct Arm {
    case: usize,
    statements: usize,
}

#[derive(PartialEq, Eq)]
struct Iteration {
    arms: Vec<Arm>,
    continues: bool,
}

#[derive(PartialEq, Eq)]
pub(super) struct DispatchTrace {
    iterations: Vec<Iteration>,
    test_exit: bool,
}

struct Shape<'a, 'ast> {
    body: &'a oxc_ast::ast::BlockStatement<'ast>,
    prefix: &'a [Statement<'ast>],
    switch: &'a SwitchStatement<'ast>,
}

impl<'a, 'ast> Shape<'a, 'ast> {
    fn new(statement: &'a ForStatement<'ast>, scoping: &Scoping) -> Option<Self> {
        let Statement::BlockStatement(body) = &statement.body else {
            return None;
        };
        let [prefix @ .., Statement::SwitchStatement(switch), Statement::BreakStatement(tail)] =
            body.body.as_slice()
        else {
            return None;
        };
        if tail.label.is_some()
            || prefix.iter().any(statement_has_loop_control)
            || !scoping.get_bindings(switch.scope_id.get()?).is_empty()
        {
            return None;
        }
        // Reconstructing a new lexical region must not change Annex B
        // declaration instantiation or the lifetime of explicit resources.
        if DeclarationHazard::Relocate.present(&body.body.iter().collect::<Vec<_>>()) {
            return None;
        }
        let owner = statement.scope_id.get()?;
        if scoping.scope_descendants_from_root().any(|scope| {
            (scope == owner || scoping.scope_is_descendant_of(scope, owner))
                && scoping.scope_flags(scope).contains_direct_eval()
        }) {
            return None;
        }
        Some(Self {
            body,
            prefix,
            switch,
        })
    }
}

pub(super) enum Selection {
    Case(usize),
    NoMatch,
}

impl Analyzer<'_, '_> {
    /// Select case labels in source order, including those following default.
    /// Rewriting a trace removes tests, so that caller additionally requires
    /// inert discriminant and label evaluation.
    pub(super) fn select_cases(
        &mut self,
        switch: &SwitchStatement<'_>,
        discriminant: &Fact,
        inert_required: bool,
        environment: &mut Environment,
    ) -> Option<Selection> {
        let mut default = None;
        for (index, case) in switch.cases.iter().enumerate() {
            let Some(test) = &case.test else {
                default = Some(index);
                continue;
            };
            let label = self.expression(test, environment);
            if inert_required && !label.inert {
                return None;
            }
            let equal =
                self.heap_result(discriminant.strict_equal(&label.fact?, self.budget))??;
            if equal {
                return Some(Selection::Case(index));
            }
        }
        Some(default.map_or(Selection::NoMatch, Selection::Case))
    }

    fn dispatch_iteration(
        &mut self,
        shape: &Shape<'_, '_>,
        environment: &mut Environment,
    ) -> Option<(Iteration, Flow)> {
        let body = self.enter_instance(shape.body.scope_id.get(), environment);
        let result = self.dispatch_body(shape, environment);
        self.leave_instance(body, environment)
            .then_some(result)
            .flatten()
            .filter(|_| self.collect_heap(environment))
    }

    fn dispatch_body(
        &mut self,
        shape: &Shape<'_, '_>,
        environment: &mut Environment,
    ) -> Option<(Iteration, Flow)> {
        let prefix = self.statements(shape.prefix, environment)?;
        if prefix.normal.is_none() || prefix.unproved {
            return None;
        }
        let discriminant = self.expression(&shape.switch.discriminant, environment);
        if !discriminant.inert {
            return None;
        }
        let discriminant = discriminant.fact?;
        let switch = self.enter_instance(shape.switch.scope_id.get(), environment);
        let iteration = self.dispatch_arms(shape, &discriminant, environment);
        let exited = self.leave_instance(switch, environment);
        let (iteration, mut flow) = iteration.filter(|_| exited)?;
        self.heap_result(flow.merge_abrupt(prefix, self.budget))?;
        Some((iteration, flow))
    }

    fn dispatch_arms(
        &mut self,
        shape: &Shape<'_, '_>,
        discriminant: &Fact,
        environment: &mut Environment,
    ) -> Option<(Iteration, Flow)> {
        let mut iteration = Iteration {
            arms: Vec::new(),
            continues: false,
        };
        let mut flow = Flow::normal(CompletionValue::undefined());
        if let Selection::Case(start) =
            self.select_cases(shape.switch, discriminant, true, environment)?
        {
            'cases: for (index, case) in shape.switch.cases.iter().enumerate().skip(start) {
                let mut transfer = None;
                let mut count = 0;
                for (offset, statement) in case.consequent.iter().enumerate() {
                    match statement {
                        Statement::BreakStatement(jump) if jump.label.is_none() => {
                            transfer = Some(false);
                            break;
                        }
                        Statement::ContinueStatement(jump) if jump.label.is_none() => {
                            transfer = Some(true);
                            break;
                        }
                        _ if statement_has_loop_control(statement) => return None,
                        _ => {
                            let next = self.statement(statement, environment)?;
                            if next.unproved
                                || next.normal.is_none()
                                || next.abrupt.keys().any(|kind| {
                                    matches!(kind, Transfer::Break(_) | Transfer::Continue(_))
                                })
                            {
                                return None;
                            }
                            self.sequence_flow(&mut flow, next)?;
                            if !self.collect_heap(environment) {
                                return None;
                            }
                            count = offset + 1;
                        }
                    }
                }
                iteration.arms.push(Arm {
                    case: index,
                    statements: count,
                });
                if let Some(continues) = transfer {
                    iteration.continues = continues;
                    break 'cases;
                }
            }
        }
        Some((iteration, flow))
    }

    pub(super) fn simulate_dispatch(
        &mut self,
        statement: &ForStatement<'_>,
        environment: &mut Environment,
    ) -> Option<Flow> {
        let shape = Shape::new(statement, self.scoping)?;
        self.for_initializer(statement, environment)?;
        self.refresh_iteration_scope(statement, environment)?;
        let mut trace = DispatchTrace {
            iterations: Vec::new(),
            test_exit: false,
        };
        let mut flow = Flow::normal(CompletionValue::undefined());
        loop {
            self.consume_iteration()?;
            self.heap_result(self.budget.consume(u64::from(
                statement.body.span().end - statement.body.span().start,
            )))?;
            if let Some(test) = &statement.test {
                let result = self.expression(test, environment);
                if !result.inert {
                    return None;
                }
                if !result.fact?.truthy() {
                    trace.test_exit = true;
                    break;
                }
            }
            let (iteration, mut iteration_flow) = self.dispatch_iteration(&shape, environment)?;
            flow.normal = iteration_flow.normal.take();
            self.heap_result(flow.merge_abrupt(iteration_flow, self.budget))?;
            if self.loop_failed {
                return None;
            }
            let continues = iteration.continues;
            trace.iterations.push(iteration);
            if !continues {
                break;
            }
            if trace.iterations.len() >= 256 {
                // Bound generated source as well as interpretation time.
                return None;
            }
            self.refresh_iteration_scope(statement, environment)?;
            if let Some(update) = &statement.update {
                self.expression(update, environment);
            }
        }
        self.reads.dispatches.observe(
            (statement.span.start, statement.span.end),
            Observation::Exact(trace),
            PartialEq::eq,
        );
        Some(flow)
    }

    pub(super) fn has_dispatch_shape(&self, statement: &ForStatement<'_>) -> bool {
        Shape::new(statement, self.scoping).is_some()
    }
}

/// A generated name is absent both as literal source and as a decoded
/// identifier. The latter matters for Unicode escapes in source names.
struct Names<'a> {
    source: &'a str,
    scoping: &'a Scoping,
    prefix: String,
    serial: usize,
}

impl<'a> Names<'a> {
    fn new(source: &'a str, scoping: &'a Scoping, start: u32) -> Self {
        let mut salt = 0;
        let prefix = loop {
            let candidate = format!("__jsvm_trace_{start}_{salt}_");
            if !source.contains(&candidate)
                && !scoping
                    .symbol_names()
                    .any(|name| name.starts_with(&candidate))
                && !scoping
                    .root_unresolved_references()
                    .keys()
                    .any(|name| name.starts_with(&candidate))
            {
                break candidate;
            }
            salt += 1;
        };
        Self {
            source,
            scoping,
            prefix,
            serial: 0,
        }
    }

    fn next(&mut self) -> String {
        let name = format!("{}{}", self.prefix, self.serial);
        self.serial += 1;
        name
    }
}

fn append_statements(
    output: &mut String,
    source: &str,
    statements: &[Statement<'_>],
) -> Option<()> {
    if let (Some(first), Some(last)) = (statements.first(), statements.last()) {
        let text = source.get(first.span().start as usize..last.span().end as usize)?;
        // A case boundary was an ASI boundary in the source.
        writeln!(output, "{text}\n;").ok()?;
    }
    Some(())
}

struct IterationBindings {
    copies: Vec<(String, String)>,
}

impl IterationBindings {
    fn new(
        statement: &ForStatement<'_>,
        names: &mut Names<'_>,
        output: &mut String,
    ) -> Option<Self> {
        let mut copies = Vec::new();
        if let Some(ForStatementInit::VariableDeclaration(decl)) = &statement.init {
            if decl.kind == VariableDeclarationKind::Let {
                let mut bindings = names
                    .scoping
                    .get_bindings(statement.scope_id.get()?)
                    .keys()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>();
                bindings.sort_unstable();
                for binding in bindings {
                    let carry = names.next();
                    writeln!(output, "let {carry} = {binding};").ok()?;
                    copies.push((binding, carry));
                }
            }
        }
        Some(Self { copies })
    }

    fn enter(&self, output: &mut String) -> Option<()> {
        output.push_str("{\n");
        for (binding, carry) in &self.copies {
            writeln!(output, "let {binding} = {carry};").ok()?;
        }
        Some(())
    }

    fn leave(&self, output: &mut String, names: &mut Names<'_>, continues: bool) -> Option<()> {
        if continues {
            for (binding, carry) in &self.copies {
                // A declaration's empty Completion retains the preceding
                // switch value, unlike an appended assignment statement.
                writeln!(output, "const {} = ({carry} = {binding});", names.next()).ok()?;
            }
        }
        output.push_str("}\n");
        Some(())
    }
}

impl DispatchTrace {
    pub(super) fn render(
        &self,
        statement: &ForStatement<'_>,
        scoping: &Scoping,
        source: &str,
    ) -> Option<String> {
        let shape = Shape::new(statement, scoping)?;
        let mut names = Names::new(source, scoping, statement.span.start);
        let mut text = String::from("{\n");
        if let Some(initializer) = &statement.init {
            if let ForStatementInit::VariableDeclaration(declaration) = initializer {
                if !matches!(
                    declaration.kind,
                    VariableDeclarationKind::Var
                        | VariableDeclarationKind::Let
                        | VariableDeclarationKind::Const
                ) {
                    return None;
                }
                writeln!(text, "{};", fragment(source, initializer.span())).ok()?;
            } else {
                writeln!(text, "({});", fragment(source, initializer.span())).ok()?;
            }
        }
        text.push_str(&crate::if_ladder_structure::hoisted_var_declarations(
            &statement.body,
        )?);
        let bindings = IterationBindings::new(statement, &mut names, &mut text)?;
        text.push_str("void 0;\n");
        for (index, iteration) in self.iterations.iter().enumerate() {
            bindings.enter(&mut text)?;
            append_update(&mut text, &mut names, statement, index != 0)?;
            text.push_str("{\n");
            append_statements(&mut text, source, shape.prefix)?;
            let mut arm = String::new();
            for slice in &iteration.arms {
                let case = shape.switch.cases.get(slice.case)?;
                append_statements(&mut arm, source, case.consequent.get(..slice.statements)?)?;
            }
            // Each switch has its own Completion accumulator, even when
            // the prefix already produced a nonempty Completion.
            text.push_str(&completion::seed_undefined(&arm));
            text.push_str("\n}\n");
            bindings.leave(&mut text, &mut names, iteration.continues)?;
        }
        if self.test_exit && !self.iterations.is_empty() {
            // ForBodyEvaluation creates the next lexical cells before the
            // final update, even when the following test rejects entry.
            bindings.enter(&mut text)?;
            append_update(&mut text, &mut names, statement, true)?;
            bindings.leave(&mut text, &mut names, false)?;
        }
        text.push_str("}\n");
        Some(text)
    }
}

fn append_update(
    text: &mut String,
    names: &mut Names<'_>,
    statement: &ForStatement<'_>,
    after_first: bool,
) -> Option<()> {
    if after_first {
        if let Some(update) = &statement.update {
            writeln!(
                text,
                "const {} = (0, ({}\n));",
                names.next(),
                fragment(names.source, update.span())
            )
            .ok()?;
        }
    }
    Some(())
}

pub(super) fn render_reaching_dispatch(
    traces: &ReachingObservations<DispatchTrace>,
    statement: &ForStatement<'_>,
    scoping: &Scoping,
    source: &str,
) -> Option<String> {
    traces
        .get(statement.span)?
        .render(statement, scoping, source)
}
