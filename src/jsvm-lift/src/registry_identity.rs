use crate::{
    forwarding_semantics::{
        structurally_proven_registry_forwarding_calls,
        structurally_proven_registry_forwarding_value_calls,
        structurally_proven_registry_read_calls, ProvenRegistryForwardingCall,
        ProvenRegistryForwardingValueCall, ProvenRegistryReadCall,
    },
    receiver_identity::{ProvenOriginContext, ProvenOriginFlow},
};
use oxc_ast::ast::Program;
use oxc_semantic::Scoping;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProvenRegistryObjectOrigin {
    pub allocation_start: u32,
    pub allocation_end: u32,
    pub constructor_start: u32,
    pub constructor_end: u32,
}

impl From<&ProvenOriginContext> for ProvenRegistryObjectOrigin {
    fn from(context: &ProvenOriginContext) -> Self {
        Self {
            allocation_start: context.allocation_start,
            allocation_end: context.allocation_end,
            constructor_start: context.constructor_start,
            constructor_end: context.constructor_end,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenOriginRegistryReadCall {
    pub read: ProvenRegistryReadCall,
    pub origin: ProvenRegistryObjectOrigin,
    pub exact_key: Option<i64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenOriginRegistryHandlerInstall {
    pub install: ProvenRegistryForwardingCall,
    pub origin: ProvenRegistryObjectOrigin,
    pub exact_key: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenOriginRegistryValueInstall {
    pub install: ProvenRegistryForwardingValueCall,
    pub origin: ProvenRegistryObjectOrigin,
    pub exact_key: i64,
}

fn unique_argument_containing(
    argument_spans: &[(u32, u32)],
    start: u32,
    end: u32,
) -> Option<usize> {
    let mut matches = argument_spans
        .iter()
        .enumerate()
        .filter(|(_, (arg_start, arg_end))| *arg_start <= start && end <= *arg_end)
        .map(|(index, _)| index);
    let first = matches.next()?;
    matches.next().is_none().then_some(first)
}

fn joined_origin_and_key(
    flow: &ProvenOriginFlow,
    call_start: u32,
    call_end: u32,
    receiver_start: u32,
    receiver_end: u32,
    key_start: u32,
    key_end: u32,
) -> Option<(ProvenRegistryObjectOrigin, Option<i64>)> {
    let mut calls = flow
        .direct_calls
        .iter()
        .filter(|call| call.call_start == call_start && call.call_end == call_end);
    let call = calls.next()?;
    if calls.next().is_some() {
        return None;
    }

    let receiver_index =
        unique_argument_containing(&call.argument_spans, receiver_start, receiver_end)?;
    if !call.callee.parameter_indices.contains(&receiver_index) {
        return None;
    }
    let key_index = unique_argument_containing(&call.argument_spans, key_start, key_end)?;
    let exact_key = call
        .exact_integer_arguments
        .get(key_index)
        .copied()
        .flatten();
    Some((ProvenRegistryObjectOrigin::from(&call.callee), exact_key))
}

#[must_use]
pub fn proven_origin_registry_read_calls(
    program: &Program<'_>,
    scoping: &Scoping,
    flow: &ProvenOriginFlow,
) -> Vec<ProvenOriginRegistryReadCall> {
    let mut proven = structurally_proven_registry_read_calls(program, scoping)
        .into_iter()
        .filter_map(|read| {
            let (origin, exact_key) = joined_origin_and_key(
                flow,
                read.call_start,
                read.call_end,
                read.receiver_start,
                read.receiver_end,
                read.key_start,
                read.key_end,
            )?;
            Some(ProvenOriginRegistryReadCall {
                read,
                origin,
                exact_key,
            })
        })
        .collect::<Vec<_>>();
    proven.sort_by_key(|proof| (proof.read.call_start, proof.read.call_end, proof.exact_key));
    proven.dedup();
    proven
}

#[must_use]
pub fn proven_origin_registry_value_installs(
    program: &Program<'_>,
    scoping: &Scoping,
    flow: &ProvenOriginFlow,
) -> Vec<ProvenOriginRegistryValueInstall> {
    let mut proven = structurally_proven_registry_forwarding_value_calls(program, scoping)
        .into_iter()
        .filter_map(|install| {
            let (origin, exact_key) = joined_origin_and_key(
                flow,
                install.call_start,
                install.call_end,
                install.receiver_start,
                install.receiver_end,
                install.key_start,
                install.key_end,
            )?;
            Some(ProvenOriginRegistryValueInstall {
                install,
                origin,
                exact_key: exact_key?,
            })
        })
        .collect::<Vec<_>>();
    proven.sort_by_key(|proof| {
        (
            proof.install.call_start,
            proof.install.call_end,
            proof.exact_key,
            proof.install.value_start,
        )
    });
    proven.dedup();
    proven
}

#[must_use]
pub fn proven_origin_registry_handler_installs(
    program: &Program<'_>,
    scoping: &Scoping,
    flow: &ProvenOriginFlow,
) -> Vec<ProvenOriginRegistryHandlerInstall> {
    let mut proven = structurally_proven_registry_forwarding_calls(program, scoping)
        .into_iter()
        .filter_map(|install| {
            let (origin, exact_key) = joined_origin_and_key(
                flow,
                install.call_start,
                install.call_end,
                install.receiver_start,
                install.receiver_end,
                install.key_start,
                install.key_end,
            )?;
            Some(ProvenOriginRegistryHandlerInstall {
                install,
                origin,
                exact_key: exact_key?,
            })
        })
        .collect::<Vec<_>>();
    proven.sort_by_key(|proof| {
        (
            proof.install.call_start,
            proof.install.call_end,
            proof.exact_key,
            proof.install.handler_start,
        )
    });
    proven.dedup();
    proven
}

#[cfg(test)]
mod tests {
    use super::{
        proven_origin_registry_handler_installs, proven_origin_registry_read_calls,
        proven_origin_registry_value_installs,
    };
    use crate::receiver_identity::structurally_proven_origin_flow;
    use oxc_allocator::Allocator;
    use oxc_semantic::SemanticBuilder;
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;

    #[test]
    fn joins_registry_reads_and_installs_by_exact_origin_and_key() {
        let source = r#"
            const C = function() {
                install(this, 7, function handler() {});
                run(this);
            };
            function install(state, key, value) { state.T[key] = value; }
            function read(state, key) { let value; value = state.T[key]; return value; }
            function run(state) { return read(state, 7); }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let scoping = semantic.semantic.scoping();
        let flow = structurally_proven_origin_flow(&parsed.program, scoping);
        let installs = proven_origin_registry_handler_installs(&parsed.program, scoping, &flow);
        let reads = proven_origin_registry_read_calls(&parsed.program, scoping, &flow);
        assert_eq!(installs.len(), 1);
        assert_eq!(reads.len(), 1);
        assert_eq!(installs[0].exact_key, 7);
        assert_eq!(reads[0].exact_key, Some(7));
        assert_eq!(installs[0].origin, reads[0].origin);
        assert_eq!(
            installs[0].install.registry_path,
            reads[0].read.registry_path
        );
    }

    #[test]
    fn joins_non_function_registry_values_by_exact_origin_and_key() {
        let source = r#"
            const C = function() {
                install(this, 7, "payload");
            };
            function write(state, key, value) { state.T[key] = value; }
            function install(state, key, value) { write(state, key, value); }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let scoping = semantic.semantic.scoping();
        let flow = structurally_proven_origin_flow(&parsed.program, scoping);
        let values = proven_origin_registry_value_installs(&parsed.program, scoping, &flow);
        let handlers = proven_origin_registry_handler_installs(&parsed.program, scoping, &flow);
        assert_eq!(values.len(), 1);
        let root = values
            .iter()
            .find(|proof| {
                &source[proof.install.value_start as usize..proof.install.value_end as usize]
                    == "\"payload\""
            })
            .expect("outer literal value");
        assert_eq!(root.exact_key, 7);
        assert_eq!(root.install.registry_path, vec!["T"]);
        assert!(handlers.is_empty());
    }

    #[test]
    fn keeps_origin_for_dynamic_registry_read_key() {
        let source = r#"
            const C = function(key) {
                install(this, 7, function handler() {});
                run(this, key);
            };
            function install(state, key, value) { state.T[key] = value; }
            function read(state, key) { let value; value = state.T[key]; return value; }
            function run(state, key) { return read(state, key); }
            new C(window.dynamicKey);
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let scoping = semantic.semantic.scoping();
        let flow = structurally_proven_origin_flow(&parsed.program, scoping);
        let reads = proven_origin_registry_read_calls(&parsed.program, scoping, &flow);
        assert_eq!(reads.len(), 1);
        assert_eq!(reads[0].exact_key, None);
        assert_eq!(reads[0].read.registry_path, vec!["T"]);
    }

    #[test]
    fn does_not_join_same_registry_shape_on_different_object() {
        let source = r#"
            const C = function(other) {
                install(this, 7, function handler() {});
                run(other);
            };
            function install(state, key, value) { state.T[key] = value; }
            function read(state, key) { let value; value = state.T[key]; return value; }
            function run(state) { return read(state, 7); }
            new C({T: []});
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let scoping = semantic.semantic.scoping();
        let flow = structurally_proven_origin_flow(&parsed.program, scoping);
        let installs = proven_origin_registry_handler_installs(&parsed.program, scoping, &flow);
        let reads = proven_origin_registry_read_calls(&parsed.program, scoping, &flow);
        assert_eq!(installs.len(), 1);
        assert!(reads.is_empty());
    }
}
