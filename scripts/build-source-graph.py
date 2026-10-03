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

    for module in bundles.get('modules', []):
        bundle_id = int(module['bundle_id'])
        ordinal = int(module.get('module_ordinal', 0))
        node_id = f'bundle-module:{bundle_id}:{ordinal}'
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
        )
        parent = bundle_nodes.get(bundle_id)
        if parent:
            add_edge(
                parent,
                node_id,
                'bundle_module',
                module_id=module.get('module_id'),
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

    # Static Function(...) recovery is a generated-code provenance edge.
    scan_to_parent = {}
    for unit in jsvm.get('code_units', []):
        if unit.get('scan_id') is None:
            continue
        if unit.get('origin') == 'generated_dynamic_code':
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
        scan_to_parent[int(unit['scan_id'])] = parent
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
            formatted=dyn.get('formatted'),
            child_scan_id=dyn.get('child_scan_id'),
        )
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

    # AST-backed JavaScript module / worker references.
    specifier_nodes = {}
    for unit in jsrefs.get('code_units', []):
        rid = unit.get('resource_id')
        if rid is None:
            continue
        src = inline_node_by_raw.get(unit.get('raw_path')) or f"resource:{int(rid)}"
        for ref in unit.get('references', []):
            resolved = ref.get('resolved_url')
            if resolved:
                targets = targets_for(resolved)
            else:
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
                targets = [node_id]
            for dst in targets:
                add_edge(
                    src,
                    dst,
                    f"js_{ref.get('kind') or 'reference'}",
                    specifier=ref.get('specifier'),
                    resolved_url=resolved,
                    start=ref.get('start'),
                    end=ref.get('end'),
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
