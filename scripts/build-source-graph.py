#!/usr/bin/env python3
import argparse
import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path
from urllib.parse import urljoin


def external_id(url: str) -> str:
    return 'external:' + hashlib.sha256(url.encode()).hexdigest()[:20]


def specifier_id(specifier: str) -> str:
    return 'specifier:' + hashlib.sha256(specifier.encode()).hexdigest()[:20]


def main():
    ap = argparse.ArgumentParser(description='Build a provenance/source reference graph for a recovered browser capture')
    ap.add_argument('project', type=Path)
    args = ap.parse_args()
    project = args.project.resolve()

    manifest = json.loads((project / 'har-manifest.json').read_text())
    source_index_path = project / 'analysis/source-index.json'
    sourcemaps_path = project / 'analysis/sourcemaps.json'
    jsvm_path = project / 'analysis/jsvm/index.json'
    jsrefs_path = project / 'analysis/js-references.json'
    deobfuscation_path = project / 'analysis/deobfuscation.json'
    bundles_path = project / 'analysis/bundles.json'
    import_maps_path = project / 'analysis/import-maps.json'
    wasm_path = project / 'analysis/wasm/index.json'
    runtime_path = project / 'analysis/runtime-scripts.json'

    source_index = json.loads(source_index_path.read_text()) if source_index_path.exists() else {'units': []}
    sourcemaps = json.loads(sourcemaps_path.read_text()) if sourcemaps_path.exists() else {'source_maps': []}
    jsvm = json.loads(jsvm_path.read_text()) if jsvm_path.exists() else {'code_units': [], 'dynamic_code_units': []}
    jsrefs = json.loads(jsrefs_path.read_text()) if jsrefs_path.exists() else {'code_units': []}
    deobfuscation = (
        json.loads(deobfuscation_path.read_text())
        if deobfuscation_path.exists()
        else {'units': []}
    )
    bundles = (
        json.loads(bundles_path.read_text())
        if bundles_path.exists()
        else {'bundles': [], 'modules': []}
    )
    wasm = json.loads(wasm_path.read_text()) if wasm_path.exists() else {'modules': []}
    runtime = (
        json.loads(runtime_path.read_text())
        if runtime_path.exists()
        else {'sources': [], 'alpine_families': [], 'gtm_families': []}
    )
    import_maps = (
        json.loads(import_maps_path.read_text())
        if import_maps_path.exists()
        else {'maps': [], 'documents': {}, 'summary': {}}
    )

    source_by_resource = defaultdict(list)
    for unit in source_index.get('units', []):
        rid = unit.get('resource_id')
        if rid is not None:
            source_by_resource[int(rid)].append(unit)

    nodes = {}
    edges = []
    edge_seen = set()

    def add_node(node_id, **fields):
        if node_id not in nodes:
            nodes[node_id] = {'id': node_id, **fields}
        else:
            for key, value in fields.items():
                if value is not None and key not in nodes[node_id]:
                    nodes[node_id][key] = value
        return node_id

    def add_edge(src, dst, kind, **fields):
        frozen = (src, dst, kind, json.dumps(fields, sort_keys=True, separators=(',', ':')))
        if frozen in edge_seen:
            return
        edge_seen.add(frozen)
        edges.append({'from': src, 'to': dst, 'kind': kind, **fields})

    url_to_resources = defaultdict(list)
    resource_nodes_by_sha = defaultdict(list)
    for r in manifest.get('resources', []):
        rid = int(r['id'])
        node_id = f'resource:{rid}'
        units = source_by_resource.get(rid, [])
        add_node(
            node_id,
            type='resource',
            resource_id=rid,
            url=r.get('url'),
            kind=r.get('kind'),
            status=r.get('status'),
            body_present=r.get('body_present'),
            raw_path=r.get('output_path'),
            source_paths=[u.get('source_path') for u in units if u.get('source_path')],
            sha256=r.get('sha256'),
        )
        if r.get('url'):
            url_to_resources[r['url']].append(node_id)
        if r.get('sha256'):
            resource_nodes_by_sha[r['sha256']].append(node_id)

    external_nodes = {}

    def targets_for(url):
        captured = url_to_resources.get(url)
        if captured:
            return list(captured)
        node_id = external_nodes.get(url)
        if node_id is None:
            node_id = external_id(url)
            external_nodes[url] = node_id
            add_node(node_id, type='external_url', url=url, captured=False)
        return [node_id]

    # HAR-extracted HTML/script/source-map references.
    for r in manifest.get('resources', []):
        src = f"resource:{int(r['id'])}"
        for ref in r.get('references', []):
            url = ref.get('resolved_url')
            if not url:
                continue
            kind = ref.get('kind') or 'reference'
            for dst in targets_for(url):
                add_edge(src, dst, kind, raw=ref.get('raw'), resolved_url=url)

        # Redirects are first-class navigation edges even when no body exists.
        location = None
        for h in r.get('response_headers', []):
            if str(h.get('name', '')).lower() == 'location':
                location = h.get('value')
                break
        if location and r.get('url'):
            resolved = urljoin(r['url'], location)
            for dst in targets_for(resolved):
                add_edge(src, dst, 'redirect', raw=location, resolved_url=resolved)

    # Inline scripts are generated source nodes owned by their HTML resource.
    inline_node_by_raw = {}
    inline_nodes_by_sha = defaultdict(list)
    for item in manifest.get('inline_scripts', []):
        if not item.get('output_path'):
            continue
        parent = int(item['parent_resource_id'])
        ordinal = int(item['ordinal'])
        node_id = f'inline:{parent}:{ordinal}'
        add_node(
            node_id,
            type='inline_script',
            parent_resource_id=parent,
            ordinal=ordinal,
            script_type=item.get('script_type'),
            source_path=item.get('output_path'),
            bytes=item.get('body_bytes'),
            sha256=item.get('sha256'),
        )
        add_edge(f'resource:{parent}', node_id, 'inline_script', ordinal=ordinal)
        if item.get('output_path'):
            inline_node_by_raw[item['output_path']] = node_id
        if item.get('sha256'):
            inline_nodes_by_sha[item['sha256']].append(node_id)

    # Debugger-observed runtime scripts are provenance, not independent network
    # resources. Preserve exact runtime identities while linking network/inline
    # executions back to captured source and generated Alpine expressions back
    # to the DOM directives that caused the browser to compile them.
    family_counts = {
        row.get('shape'): row.get('source_count', 0)
        for row in runtime.get('alpine_families', [])
        if row.get('shape')
    }
    gtm_family_counts = {
        row.get('shape'): row.get('source_count', 0)
        for row in runtime.get('gtm_families', [])
        if row.get('shape')
    }
    for source in runtime.get('sources', []):
        digest = source.get('sha256')
        if not digest:
            continue
        runtime_node = f"runtime:{digest[:20]}"
        classification = source.get('classification')
        alpine = source.get('alpine') or {}
        gtm = source.get('gtm') or {}
        generated = source.get('generated') or {}
        add_node(
            runtime_node,
            type='runtime_script',
            classification=classification,
            sha256=digest,
            bytes=source.get('size'),
            capture_path=source.get('path'),
            event_count=source.get('event_count'),
            script_ids=source.get('script_ids', []),
            cdp_sessions=source.get('cdp_sessions', []),
            execution_context_ids=source.get('execution_context_ids', []),
            script_instances=source.get('script_instances', []),
            urls=source.get('urls', []),
            instrumentation_kind=source.get('instrumentation_kind'),
            generated_root_sha256s=generated.get('root_sha256s', []),
            generated_root_urls=generated.get('root_urls', []),
            generation_max_depth=generated.get('max_depth'),
            application_source=classification != 'capture_instrumentation',
        )

        for origin in generated.get('origins', []):
            chain = origin.get('chain') or []
            if not chain:
                continue
            parent = chain[0]
            edge_fields = {
                'cdp_session': origin.get('cdp_session') or parent.get('cdp_session') or 'main',
                'child_script_id': origin.get('child_script_id'),
                'parent_script_id': parent.get('script_id'),
                'function_name': parent.get('function_name'),
                'line_number': parent.get('line_number'),
                'column_number': parent.get('column_number'),
                'generation_depth': len(chain),
            }
            parent_sha = parent.get('sha256')
            if parent_sha:
                add_edge(
                    f"runtime:{parent_sha[:20]}",
                    runtime_node,
                    'runtime_generated_code',
                    **edge_fields,
                )
            elif parent.get('url'):
                for parent_node in targets_for(parent['url']):
                    add_edge(
                        parent_node,
                        runtime_node,
                        'runtime_generated_code',
                        **edge_fields,
                    )

        if classification in {'network_response', 'network_observed'}:
            parents = list(resource_nodes_by_sha.get(digest, []))
            if not parents:
                for url in source.get('urls', []):
                    parents.extend(url_to_resources.get(url, []))
            for parent in dict.fromkeys(parents):
                add_edge(parent, runtime_node, 'runtime_execution')
        elif classification == 'inline_script':
            for parent in inline_nodes_by_sha.get(digest, []):
                add_edge(parent, runtime_node, 'runtime_execution')
        elif classification == 'document_inline_script':
            for origin in source.get('document_inline_origins', []):
                document_key = json.dumps(
                    [origin.get('cdp_session'), origin.get('url'), origin.get('frame_id')],
                    separators=(',', ':'),
                )
                document_digest = hashlib.sha256(document_key.encode()).hexdigest()[:20]
                document_node = f'runtime-document:{document_digest}'
                add_node(
                    document_node,
                    type='runtime_document',
                    cdp_session=origin.get('cdp_session'),
                    url=origin.get('url'),
                    frame_id=origin.get('frame_id'),
                )
                add_edge(
                    document_node,
                    runtime_node,
                    'runtime_document_inline',
                    script_id=origin.get('script_id'),
                    start_line=origin.get('start_line'),
                    start_column=origin.get('start_column'),
                    end_line=origin.get('end_line'),
                    end_column=origin.get('end_column'),
                )
        elif classification == 'alpine_expression':
            shape = alpine.get('shape')
            if shape:
                family_digest = hashlib.sha256(shape.encode()).hexdigest()[:20]
                family_node = f'runtime-family:{family_digest}'
                add_node(
                    family_node,
                    type='runtime_expression_family',
                    framework='alpine',
                    shape=shape,
                    source_count=family_counts.get(shape),
                )
                add_edge(runtime_node, family_node, 'runtime_expression_family')

            for match in alpine.get('dom_matches', []):
                snapshot_key = json.dumps(
                    [match.get('source'), match.get('path')],
                    separators=(',', ':'),
                )
                snapshot_digest = hashlib.sha256(snapshot_key.encode()).hexdigest()[:20]
                snapshot_node = f'dom-snapshot:{snapshot_digest}'
                add_node(
                    snapshot_node,
                    type='dom_snapshot',
                    source=match.get('source'),
                    path=match.get('path'),
                )
                directive_key = json.dumps(
                    [
                        match.get('source'),
                        match.get('path'),
                        match.get('tag_ordinal'),
                        match.get('tag'),
                        match.get('attribute'),
                    ],
                    separators=(',', ':'),
                )
                directive_digest = hashlib.sha256(directive_key.encode()).hexdigest()[:20]
                directive_node = f'dom-directive:{directive_digest}'
                add_node(
                    directive_node,
                    type='dom_directive',
                    source=match.get('source'),
                    path=match.get('path'),
                    tag_ordinal=match.get('tag_ordinal'),
                    tag=match.get('tag'),
                    attribute=match.get('attribute'),
                )
                add_edge(snapshot_node, directive_node, 'dom_directive')
                add_edge(
                    directive_node,
                    runtime_node,
                    'runtime_alpine_compile',
                    mapping_kind=alpine.get('dom_mapping_kind'),
                    expression=alpine.get('expression'),
                    compiled_expression=alpine.get('compiled_expression'),
                    shape=shape,
                )
        elif classification == 'gtm_custom_javascript':
            shape = gtm.get('shape')
            if shape:
                family_digest = hashlib.sha256(
                    ('google_tag_manager\0' + shape).encode()
                ).hexdigest()[:20]
                family_node = f'runtime-family:{family_digest}'
                add_node(
                    family_node,
                    type='runtime_expression_family',
                    framework='google_tag_manager',
                    shape=shape,
                    source_count=gtm_family_counts.get(shape),
                )
                add_edge(runtime_node, family_node, 'runtime_expression_family')

    # Safe static deobfuscation is a provenance-preserving source transform.
    deob_nodes = {}
    for unit in deobfuscation.get('units', []):
        if unit.get('exit'):
            continue
        ordinal = int(unit.get('ordinal', 0))
        rid = unit.get('resource_id')
        node_id = f'deobfuscated:{ordinal}'
        deob_nodes[ordinal] = node_id
        add_node(
            node_id,
            type='deobfuscated_source',
            resource_id=rid,
            input_path=unit.get('input_path'),
            source_path=unit.get('output_path'),
            readable_source_path=unit.get('readable_output_path'),
            readable_formatted=bool(unit.get('readable_formatted')),
            input_sha256=unit.get('input_sha256'),
            output_sha256=unit.get('output_sha256'),
            changed=bool(unit.get('changed')),
            iterations=unit.get('iterations'),
            transforms=unit.get('transforms', {}),
            arithmetic_state_proofs=unit.get('arithmetic_state_proofs', []),
            string_recovery_report_path=unit.get('string_recovery_report_path'),
            string_recovery_changed=bool(unit.get('string_recovery_changed')),
            string_recovery_replacements=unit.get('string_recovery_replacements', 0),
            pre_deob_sha256=unit.get('pre_deob_sha256'),
            safe_static_only=True,
            presentation_formatted=bool(unit.get('presentation_formatted', False)),
            runtime_semantics_preserved_by_design=bool(
                unit.get('runtime_semantics_preserved_by_design', True)
            ),
        )
        parent = inline_node_by_raw.get(unit.get('raw_path'))
        if parent is None and rid is not None:
            parent = f'resource:{int(rid)}'
        if parent:
            add_edge(
                parent,
                node_id,
                'safe_deobfuscation',
                changed=bool(unit.get('changed')),
                transforms=unit.get('transforms', {}),
                string_recovery_replacements=unit.get('string_recovery_replacements', 0),
            )

    # Statically explicit Webpack/Next module tables become navigable project modules.
    bundle_nodes = {}
    for bundle in bundles.get('bundles', []):
        bundle_id = int(bundle['bundle_id'])
        node_id = f'bundle:{bundle_id}'
        bundle_nodes[bundle_id] = node_id
        add_node(
            node_id,
            type='bundle_payload',
            bundle_id=bundle_id,
            resource_id=bundle.get('resource_id'),
            kind=bundle.get('kind'),
            chunk_ids=bundle.get('chunk_ids', []),
            parent_path=bundle.get('parent_path'),
            start=bundle.get('start'),
            end=bundle.get('end'),
            module_count=bundle.get('module_count'),
        )
        parent_ordinal = bundle.get('parent_ordinal')
        if parent_ordinal is not None and int(parent_ordinal) in deob_nodes:
            add_edge(
                deob_nodes[int(parent_ordinal)],
                node_id,
                'bundle_payload',
                chunk_ids=bundle.get('chunk_ids', []),
            )

    bundle_rows_by_id = {
        int(bundle['bundle_id']): bundle for bundle in bundles.get('bundles', [])
    }
    bundle_module_nodes = {}
    module_nodes_by_id = defaultdict(list)
    module_rows = {}
    for module in bundles.get('modules', []):
        bundle_id = int(module['bundle_id'])
        ordinal = int(module.get('module_ordinal', 0))
        node_id = f'bundle-module:{bundle_id}:{ordinal}'
        bundle_module_nodes[(bundle_id, str(module.get('module_id')))] = node_id
        module_nodes_by_id[str(module.get('module_id'))].append(node_id)
        module_rows[node_id] = module
        add_node(
            node_id,
            type='bundle_module',
            bundle_id=bundle_id,
            module_ordinal=ordinal,
            module_id=module.get('module_id'),
            resource_id=module.get('resource_id'),
            parent_path=module.get('parent_path'),
            chunk_ids=module.get('chunk_ids', []),
            source_path=module.get('source_path'),
            formatted=bool(module.get('formatted')),
            sha256=module.get('sha256'),
            value_kind=module.get('value_kind'),
            dependencies=module.get('dependencies', []),
            dependency_map=module.get('dependency_map', {}),
            export_names=module.get('export_names', []),
            commonjs_export=bool(module.get('commonjs_export')),
        )
        parent = bundle_nodes.get(bundle_id)
        if parent:
            add_edge(
                parent,
                node_id,
                'bundle_module',
                module_id=module.get('module_id'),
            )

    def nested_private_bundle_candidate(candidate_node, source_module):
        candidate_module = module_rows[candidate_node]
        candidate_bundle = bundle_rows_by_id[int(candidate_module['bundle_id'])]
        if candidate_bundle.get('kind') != 'webpack_module_table':
            return False
        if candidate_bundle.get('parent_path') != source_module.get('parent_path'):
            return False
        source_start = source_module.get('value_start')
        source_end = source_module.get('value_end')
        bundle_start = candidate_bundle.get('start')
        bundle_end = candidate_bundle.get('end')
        if None in (source_start, source_end, bundle_start, bundle_end):
            return False
        return (
            int(source_start) <= int(bundle_start)
            and int(bundle_end) <= int(source_end)
        )

    for source_node, module in module_rows.items():
        bundle_id = int(module['bundle_id'])
        for dependency in module.get('dependencies', []):
            dependency = str(dependency)
            target = bundle_module_nodes.get((bundle_id, dependency))
            cross_bundle = False
            excluded_nested = []
            candidates = []
            if target is None:
                all_candidates = list(module_nodes_by_id.get(dependency, []))
                excluded_nested = [
                    candidate
                    for candidate in all_candidates
                    if nested_private_bundle_candidate(candidate, module)
                ]
                candidates = [
                    candidate
                    for candidate in all_candidates
                    if candidate not in excluded_nested
                ]
                if len(candidates) == 1:
                    target = candidates[0]
                    cross_bundle = True
            if target is not None:
                add_edge(
                    source_node,
                    target,
                    'bundle_module_dependency',
                    module_id=dependency,
                    cross_bundle=cross_bundle,
                    excluded_nested_module_tables=len(excluded_nested),
                )
                continue

            ref_key = f"{bundle_id}:{dependency}"
            ref_id = 'bundle-module-ref:' + hashlib.sha256(ref_key.encode()).hexdigest()[:20]
            add_node(
                ref_id,
                type='bundle_module_reference',
                module_id=dependency,
                source_bundle_id=bundle_id,
                candidate_nodes=candidates,
                excluded_nested_module_table_nodes=excluded_nested,
                ambiguous=bool(candidates),
            )
            add_edge(
                source_node,
                ref_id,
                'bundle_module_dependency_unresolved',
                module_id=dependency,
                candidate_count=len(candidates),
                excluded_nested_module_table_count=len(excluded_nested),
            )

    # Source maps link generated JS -> map resource -> recovered original source.
    for sm in sourcemaps.get('source_maps', []):
        rid = sm.get('resource_id')
        if rid is None:
            continue
        src = f'resource:{int(rid)}'
        map_rid = sm.get('map_resource_id')
        map_node = None
        if map_rid is not None:
            map_node = f'resource:{int(map_rid)}'
            add_edge(src, map_node, 'source_map', map_url=sm.get('map_url'))
        elif sm.get('map_url'):
            targets = targets_for(sm['map_url'])
            map_node = targets[0]
            for dst in targets:
                add_edge(src, dst, 'source_map', map_url=sm.get('map_url'))

        for rec in sm.get('recovered', []):
            if rec.get('status') != 'recovered':
                continue
            ordinal = int(rec.get('ordinal', 0))
            node_id = f'sourcemap-source:{int(rid)}:{ordinal}'
            add_node(
                node_id,
                type='sourcemap_source',
                parent_resource_id=int(rid),
                ordinal=ordinal,
                logical_source=rec.get('logical_source'),
                source_path=rec.get('source_path'),
                bytes=rec.get('bytes'),
            )
            add_edge(map_node or src, node_id, 'source_map_source', ordinal=ordinal)

        composition = sm.get('composition') or {}
        composed_map_path = composition.get('composed_map_path')
        composed_node = None
        if composed_map_path:
            composed_node = f'sourcemap-composed:{int(rid)}'
            add_node(
                composed_node,
                type='composed_source_map',
                parent_resource_id=int(rid),
                source_path=composed_map_path,
                composed_links=composition.get('composed_links', 0),
                composed_sources=composition.get('composed_sources', 0),
            )
            add_edge(map_node or src, composed_node, 'source_map_composed')

        for link_index, link in enumerate(composition.get('links', [])):
            chain_node = f'sourcemap-chain:{int(rid)}:{link_index}'
            add_node(
                chain_node,
                type='sourcemap_chain_link',
                parent_resource_id=int(rid),
                depth=link.get('depth'),
                source_ordinal=link.get('source_ordinal'),
                logical_source=link.get('logical_source'),
                raw_reference=link.get('raw_reference'),
                map_url=link.get('map_url'),
                map_resource_id=link.get('map_resource_id'),
                map_origin=link.get('map_origin'),
                status=link.get('status'),
            )
            add_edge(map_node or src, chain_node, 'source_map_chain')
            nested_map_rid = link.get('map_resource_id')
            if nested_map_rid is not None:
                add_edge(chain_node, f'resource:{int(nested_map_rid)}', 'source_map_chain_resource')
            elif link.get('map_url'):
                for dst in targets_for(link['map_url']):
                    add_edge(chain_node, dst, 'source_map_chain_resource')

        for rec in sm.get('composed_recovered', []):
            if rec.get('status') != 'recovered':
                continue
            ordinal = int(rec.get('ordinal', 0))
            node_id = f'sourcemap-final:{int(rid)}:{ordinal}'
            add_node(
                node_id,
                type='sourcemap_composed_source',
                parent_resource_id=int(rid),
                ordinal=ordinal,
                logical_source=rec.get('logical_source'),
                source_path=rec.get('source_path'),
                bytes=rec.get('bytes'),
            )
            add_edge(composed_node or map_node or src, node_id, 'source_map_composed_source', ordinal=ordinal)

    # Static Function(...) recovery is a generated-code provenance edge.
    generated_analysis_parent = {}
    for dyn in jsvm.get('dynamic_code_units', []):
        scan = int(dyn['parent_scan_id'])
        ordinal = int(dyn['ordinal'])
        node_id = f'dynamic:{scan}:{ordinal}'
        add_node(
            node_id,
            type='generated_dynamic_code',
            parent_scan_id=scan,
            ordinal=ordinal,
            depth=dyn.get('depth'),
            generated_kind=dyn.get('kind'),
            outer_start=dyn.get('outer_start'),
            outer_end=dyn.get('outer_end'),
            body_bytes=dyn.get('body_bytes'),
            raw_dump=dyn.get('raw_dump'),
            source_path=dyn.get('source_path'),
            analysis_path=dyn.get('analysis_path'),
            analysis_stage=dyn.get('analysis_stage'),
            recovery_report=dyn.get('recovery_report'),
            formatted=dyn.get('formatted'),
            child_scan_id=dyn.get('child_scan_id'),
        )

        analysis_parent = node_id
        analysis_path = dyn.get('analysis_path')
        if analysis_path and analysis_path != dyn.get('raw_dump'):
            recovery_node = f'generated-recovery:{scan}:{ordinal}'
            add_node(
                recovery_node,
                type='generated_recovered_source',
                parent_scan_id=scan,
                ordinal=ordinal,
                recovery_stage=dyn.get('analysis_stage'),
                source_path=analysis_path,
                readable_source_path=dyn.get('source_path'),
                recovery_report=dyn.get('recovery_report'),
            )
            add_edge(
                node_id,
                recovery_node,
                'generated_safe_recovery',
                recovery_stage=dyn.get('analysis_stage'),
            )
            analysis_parent = recovery_node

        child_scan_id = dyn.get('child_scan_id')
        if child_scan_id is not None:
            generated_analysis_parent[int(child_scan_id)] = analysis_parent

    scan_to_parent = {}
    for unit in jsvm.get('code_units', []):
        if unit.get('scan_id') is None:
            continue
        scan_id = int(unit['scan_id'])
        if unit.get('origin') == 'generated_dynamic_code':
            parent = generated_analysis_parent.get(scan_id)
            if parent is None:
                parent_scan = unit.get('parent_scan_id')
                ordinal = unit.get('parent_dynamic_ordinal')
                if parent_scan is None or ordinal is None:
                    continue
                parent = f"dynamic:{int(parent_scan)}:{int(ordinal)}"
        else:
            deob_ordinal = unit.get('deobfuscation_ordinal')
            if deob_ordinal is not None and int(deob_ordinal) in deob_nodes:
                parent = deob_nodes[int(deob_ordinal)]
            elif unit.get('resource_id') is not None:
                parent = f"resource:{int(unit['resource_id'])}"
            else:
                continue
        scan_to_parent[scan_id] = parent

    for dyn in jsvm.get('dynamic_code_units', []):
        scan = int(dyn['parent_scan_id'])
        ordinal = int(dyn['ordinal'])
        node_id = f'dynamic:{scan}:{ordinal}'
        parent = scan_to_parent.get(scan)
        if parent:
            add_edge(
                parent,
                node_id,
                'generated_code',
                outer_start=dyn.get('outer_start'),
                outer_end=dyn.get('outer_end'),
                depth=dyn.get('depth'),
            )

    for unit in jsvm.get('devirtualized_units', []):
        scan = int(unit['parent_scan_id'])
        ordinal = int(unit['vm_ordinal'])
        vm_kind = unit.get('vm_kind') or 'unknown'
        node_id = f'devirtualized:{scan}:{vm_kind}:{ordinal}'
        add_node(
            node_id,
            type='devirtualized_vm',
            parent_scan_id=scan,
            vm_ordinal=ordinal,
            vm_kind=vm_kind,
            parent_function_id=unit.get('parent_function_id'),
            function_name=unit.get('function_name'),
            function_start=unit.get('function_start'),
            function_end=unit.get('function_end'),
            switch_start=unit.get('switch_start'),
            switch_end=unit.get('switch_end'),
            selector_style=unit.get('selector_style'),
            handler_table=unit.get('handler_table'),
            architecture=unit.get('architecture'),
            handler_count=unit.get('handler_count'),
            source_path=unit.get('source_path'),
            pseudocode_path=unit.get('pseudocode_path'),
            ir_path=unit.get('ir_path'),
        )
        parent = scan_to_parent.get(scan)
        if parent:
            add_edge(
                parent,
                node_id,
                'devirtualized_vm',
                vm_kind=vm_kind,
                function_start=unit.get('function_start'),
                function_end=unit.get('function_end'),
                switch_start=unit.get('switch_start'),
                switch_end=unit.get('switch_end'),
                handler_table=unit.get('handler_table'),
            )

    # Import-map definitions are captured provenance too, not just resolver state.
    for record in import_maps.get('maps', []):
        src = inline_node_by_raw.get(record.get('raw_path'))
        if not src:
            continue
        document_resource_id = record.get('document_resource_id')
        for specifier, resolved in record.get('imports', {}).items():
            if resolved is None:
                continue
            for dst in targets_for(resolved):
                add_edge(
                    src,
                    dst,
                    'import_map_entry',
                    specifier=specifier,
                    resolved_url=resolved,
                    document_resource_id=document_resource_id,
                    scope=None,
                )
        for scope, entries in record.get('scopes', {}).items():
            for specifier, resolved in entries.items():
                if resolved is None:
                    continue
                for dst in targets_for(resolved):
                    add_edge(
                        src,
                        dst,
                        'import_map_entry',
                        specifier=specifier,
                        resolved_url=resolved,
                        document_resource_id=document_resource_id,
                        scope=scope,
                    )

    # AST-backed JavaScript module / worker references.
    specifier_nodes = {}
    for unit in jsrefs.get('code_units', []):
        rid = unit.get('resource_id')
        if rid is None:
            continue
        src = inline_node_by_raw.get(unit.get('raw_path')) or f"resource:{int(rid)}"
        for ref in unit.get('references', []):
            resolved = ref.get('resolved_url')
            candidates = []
            if resolved:
                contexts = ref.get('resolution_candidates') or [{}]
                for context in contexts:
                    candidates.append(
                        {
                            'resolved_url': resolved,
                            'document_resource_id': context.get('document_resource_id'),
                            'resolution': ref.get('resolution'),
                            'import_map_key': ref.get('import_map_key'),
                            'scope': ref.get('scope'),
                        }
                    )
            else:
                for context in ref.get('resolution_candidates', []):
                    if context.get('resolved_url'):
                        candidates.append(context)

            if candidates:
                for candidate in candidates:
                    candidate_url = candidate.get('resolved_url')
                    for dst in targets_for(candidate_url):
                        add_edge(
                            src,
                            dst,
                            f"js_{ref.get('kind') or 'reference'}",
                            specifier=ref.get('specifier'),
                            glob=ref.get('glob'),
                            glob_match_url=candidate.get('glob_match_url'),
                            resolved_url=candidate_url,
                            resolution=candidate.get('resolution'),
                            import_map_key=candidate.get('import_map_key'),
                            scope=candidate.get('scope'),
                            document_resource_id=candidate.get('document_resource_id'),
                            start=ref.get('start'),
                            end=ref.get('end'),
                        )
                continue

            specifier = ref.get('specifier') or ''
            node_id = specifier_nodes.get(specifier)
            if node_id is None:
                node_id = specifier_id(specifier)
                specifier_nodes[specifier] = node_id
                add_node(
                    node_id,
                    type='module_specifier',
                    specifier=specifier,
                    bare=bool(ref.get('bare_specifier')),
                    captured=False,
                )
            add_edge(
                src,
                node_id,
                f"js_{ref.get('kind') or 'reference'}",
                specifier=specifier,
                glob=ref.get('glob'),
                resolved_url=None,
                resolution=ref.get('resolution'),
                import_map_key=ref.get('import_map_key'),
                scope=ref.get('scope'),
                start=ref.get('start'),
                end=ref.get('end'),
            )

    # Captured or statically recovered WebAssembly modules are first-class
    # derived-source nodes with exact provenance back to the carrier resource.
    for module in wasm.get('modules', []):
        digest = module['sha256']
        node_id = f"wasm:{digest[:20]}"
        add_node(
            node_id,
            type='wasm_module',
            sha256=digest,
            bytes=module.get('byte_len'),
            binary_path=module.get('binary_path'),
            extracted=bool(module.get('extracted')),
            status=module.get('status'),
            report_path=module.get('report_path'),
            readable_wat_path=module.get('wat_path'),
            deep_analysis_path=module.get('deep_path'),
        )
        for origin in module.get('origins', []):
            kind = origin.get('type')
            parent = None
            if kind in {'resource', 'resource_inline_base64'} and origin.get('resource_id') is not None:
                parent = f"resource:{int(origin['resource_id'])}"
            elif kind == 'inline_script_base64':
                parent = f"inline:{int(origin['parent_resource_id'])}:{int(origin['ordinal'])}"
            if parent:
                add_edge(
                    parent,
                    node_id,
                    'wasm_resource' if kind == 'resource' else 'wasm_inline_base64',
                    encoding=origin.get('encoding'),
                    start=origin.get('byte_start'),
                    end=origin.get('byte_end'),
                )

    edge_counts = Counter(edge['kind'] for edge in edges)
    node_counts = Counter(node['type'] for node in nodes.values())
    graph = {
        'schema': 'har-source-graph/v0',
        'project': str(project),
        'capture_salvaged': bool(manifest.get('salvaged')),
        'nodes': sorted(nodes.values(), key=lambda n: n['id']),
        'edges': sorted(edges, key=lambda e: (e['from'], e['kind'], e['to'])),
        'summary': {
            'nodes': len(nodes),
            'edges': len(edges),
            'node_types': dict(sorted(node_counts.items())),
            'edge_kinds': dict(sorted(edge_counts.items())),
            'external_urls': sum(n['type'] == 'external_url' for n in nodes.values()),
        },
    }
    out = project / 'analysis/source-graph.json'
    out.write_text(json.dumps(graph, indent=2) + '\n')
    print(json.dumps(graph['summary'], sort_keys=True))
    print(f'wrote {out}')


if __name__ == '__main__':
    main()
