//! Source-local factory results and allocation-site provenance.
use super::super::callables::BindingSite;
use super::*;

pub(super) struct ReturnedCallable {
    pub(super) callable: Callable,
    pub(super) witnesses: Vec<ApiBindingWitness>,
    pub(super) dependencies: BTreeSet<String>,
}

/// Recover functions returning an existing native callable through a
/// confined straight-line value frame. Iterate over nested factory values
/// and immutable aliases, rather than running arbitrary factory bodies.
/// Async returns, closure creation and calls requiring a new environment
/// are not interpreted as existing native callable values.
pub(super) fn resolve_returned_callable<'a>(
    expr: &'a Expression<'a>,
    semantic: &Semantic<'a>,
    wrappers: &WrapperIndex<'a>,
    collector: &FrameContext<'_, '_>,
    budget: &WorkBudget,
) -> Result<Option<ReturnedCallable>> {
    let mut witnesses = Vec::new();
    let Some(factory) = wrappers.factory_call(expr, collector.scoping, budget, &mut witnesses)?
    else {
        return Ok(None);
    };
    resolve_factory_chain(factory, witnesses, semantic, wrappers, collector, budget)
}

fn resolve_factory_chain<'a>(
    mut factory: &'a CallExpression<'a>,
    mut witnesses: Vec<ApiBindingWitness>,
    semantic: &Semantic<'a>,
    wrappers: &WrapperIndex<'a>,
    collector: &FrameContext<'_, '_>,
    budget: &WorkBudget,
) -> Result<Option<ReturnedCallable>> {
    let mut dependencies = BTreeSet::new();
    let mut visited = BTreeSet::new();
    loop {
        budget.consume(1)?;
        if !visited.insert((factory.span.start, factory.span.end)) {
            return Ok(None);
        }
        let Some(wrapper) = wrappers.resolve(
            &factory.callee,
            collector.scoping,
            budget,
            &mut dependencies,
            &mut witnesses,
            None,
        )?
        else {
            return Ok(None);
        };
        if !wrapper.returns_value {
            return Ok(None);
        }
        // Only recognized native bind returns may create a new callable.
        // Ordinary sink calls and arbitrary factory calls are not values.
        let bind = match unparenthesized(wrapper.body) {
            Expression::CallExpression(call) if !call.optional => {
                let Some((object, key)) =
                    member_parts(&call.callee, collector.scoping, collector.constants)
                else {
                    return Ok(None);
                };
                if key != "bind" {
                    return Ok(None);
                }
                Some((call, object))
            }
            _ if wrapper.invocation().is_some() => return Ok(None),
            _ => None,
        };
        let sink = bind.map_or(wrapper.body.span(), |(call, _)| call.span);
        let mut arguments = ValueBuilder::new(
            None,
            collector.scoping,
            collector.constants,
            wrappers.positional_limit,
            budget,
        );
        let args = arguments.call(&factory.arguments)?;
        if arguments.used_iterator {
            dependencies.insert("rest_iterator".into());
        }
        let Some(proof) = wrappers.frame_proof(&wrapper, sink, semantic, collector, budget)? else {
            return Ok(None);
        };
        let Some(mut builder) = instantiate(
            &wrapper,
            &args,
            &proof,
            collector,
            wrappers.positional_limit,
            budget,
        )?
        else {
            return Ok(None);
        };
        let bound = if let Some((call, original_object)) = bind {
            let Some(object) = builder.expression(original_object)?.expression() else {
                return Ok(None);
            };
            let Some(mut target) = collector.callables.resolve(
                object,
                collector.source,
                collector.scoping,
                collector.constants,
            ) else {
                return Ok(None);
            };
            if !std::ptr::eq(object, original_object) {
                target.capture_as_argument();
            }
            let arguments = builder.call(&call.arguments)?;
            let Some(bound) = collector.callables.bind_values(
                target,
                &arguments,
                BindingSite {
                    operation: call.span,
                    allocation: factory.span,
                },
                collector.source,
                collector.scoping,
                collector.constants,
            ) else {
                return Ok(None);
            };
            Some(bound)
        } else {
            None
        };
        if builder.used_iterator {
            dependencies.insert("rest_iterator".into());
        }
        witnesses.push(ApiBindingWitness {
            kind: "wrapper_definition".into(),
            start: wrapper.span.start,
            end: wrapper.span.end,
        });
        append_local_witnesses(&wrapper, &mut witnesses);
        witnesses.push(ApiBindingWitness {
            kind: "wrapper_return".into(),
            start: wrapper.body.span().start,
            end: wrapper.body.span().end,
        });
        witnesses.push(ApiBindingWitness {
            kind: "returned_callable".into(),
            start: factory.span.start,
            end: factory.span.end,
        });
        if let Some(callable) = bound {
            return Ok(Some(ReturnedCallable {
                callable,
                witnesses,
                dependencies,
            }));
        }
        let Some(origin) = wrapper.returned_origin(&mut builder, collector)? else {
            return Ok(None);
        };
        if builder.used_iterator {
            dependencies.insert("rest_iterator".into());
        }
        if let Some(mut callable) = collector.callables.resolve(
            origin,
            collector.source,
            collector.scoping,
            collector.constants,
        ) {
            callable.capture_as_argument();
            return Ok(Some(ReturnedCallable {
                callable,
                witnesses,
                dependencies,
            }));
        }
        let Some(next) =
            wrappers.factory_call(origin, collector.scoping, budget, &mut witnesses)?
        else {
            return Ok(None);
        };
        factory = next;
    }
}

/// Cache factory values in source completion order before analyzing any
/// mutation paths. Calls complete after their nested argument calls, and
/// immutable aliases become available only after their initializer.
pub(in crate::api_surface) fn collect_returned_values<'a>(
    semantic: &Semantic<'a>,
    wrappers: &WrapperIndex<'a>,
    callables: &mut CallableIndex,
    source: &str,
    constants: &ProvenConstantEnvironment,
    budget: &WorkBudget,
) -> Result<()> {
    let scoping = semantic.scoping();
    let mut events = Vec::new();
    for node in semantic.nodes().iter() {
        budget.consume(1)?;
        match node.kind() {
            AstKind::CallExpression(call)
                if !call.optional && wrappers.may_resolve(&call.callee, scoping) =>
            {
                events.push((call.span.end, call.span.start, node.kind()))
            }
            AstKind::VariableDeclarator(decl)
                if decl
                    .id
                    .get_binding_identifier()
                    .and_then(|id| id.symbol_id.get())
                    .is_some_and(|symbol| wrappers.bindings.contains_key(&symbol)) =>
            {
                events.push((decl.span.end, decl.span.start, node.kind()))
            }
            _ => {}
        }
    }
    // At equal end positions a nested call completes before its declaration.
    events.sort_unstable_by_key(|(end, start, _)| (*end, std::cmp::Reverse(*start)));
    for (_, _, kind) in events {
        budget.consume(1)?;
        match kind {
            AstKind::CallExpression(call) => {
                let context = FrameContext {
                    source,
                    scoping,
                    constants,
                    callables,
                };
                // The semantic AST stores call nodes separately from the
                // enclosing Expression enum. Resolve via the direct call
                // entry point, retaining the existing alias-chain path.
                if let Some(returned) =
                    resolve_factory_chain(call, Vec::new(), semantic, wrappers, &context, budget)?
                {
                    let mut callable = returned.callable;
                    callable.mark_returned(&returned.witnesses, returned.dependencies);
                    callables.record_returned_value(call.span, callable);
                }
            }
            AstKind::VariableDeclarator(decl) => {
                if let Some(callable) = decl
                    .init
                    .as_ref()
                    .and_then(|init| callables.resolve(init, source, scoping, constants))
                    .filter(Callable::is_returned)
                {
                    callables.record_returned_alias(decl, scoping, callable);
                }
            }
            _ => {}
        }
    }
    Ok(())
}
