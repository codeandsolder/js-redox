#!/usr/bin/env python3
import json
import os
import subprocess
import tempfile
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURE_ROOT = Path(os.environ.get("JSVM_FIXTURE_ROOT", ROOT))
SCANNER = ROOT / ".cargo-target-nodebug/debug/jsvm-lift"
LIFTER = ROOT / ".cargo-target-nodebug/debug/switch-ir"


def fixture(relative: str) -> Path:
    local = ROOT / relative
    if local.is_file():
        return local
    external = FIXTURE_ROOT / relative
    if external.is_file():
        return external
    raise FileNotFoundError(
        f"missing regression fixture {relative}; set JSVM_FIXTURE_ROOT to a workspace containing it"
    )


VIDFAST = fixture("corpus/real/vidfast-next-365-71c2a8238d040bc9.js")
NEGATIVES = [
    fixture("corpus/hard_negatives/portalfluently-sfp-murmurhash.js"),
    fixture("corpus/hard_negatives/yandex-tmgrdfrend-generator-state.js"),
    fixture("corpus/hard_negatives/bing-parser-switch.js"),
]


def run_json(source: Path, work: Path):
    scan = work / f"{source.stem}.scan.json"
    ir = work / f"{source.stem}.switch-ir.json"
    with scan.open("w") as f:
        cp = subprocess.run(
            [str(SCANNER), "--json", str(source)],
            cwd=ROOT,
            text=True,
            stdout=f,
            stderr=subprocess.PIPE,
            timeout=180,
        )
    if cp.returncode:
        raise RuntimeError(f"scanner failed for {source}: {cp.stderr}")
    cp = subprocess.run(
        [str(LIFTER), str(source), str(scan), "--output", str(ir)],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=180,
    )
    if cp.returncode:
        raise RuntimeError(f"switch-ir failed for {source}:\n{cp.stdout}\n{cp.stderr}")
    return json.loads(ir.read_text()), cp.stdout


def overlaps(vms):
    sets = [{h["semantic_hash"] for h in vm["handlers"]} for vm in vms]
    values = []
    for i in range(len(sets)):
        for j in range(i + 1, len(sets)):
            values.append(len(sets[i] & sets[j]))
    return values


def main():
    if not SCANNER.is_file() or not LIFTER.is_file():
        raise SystemExit("build jsvm-lift and switch-ir first")

    with tempfile.TemporaryDirectory(prefix="jsvm-switch-ir-") as td:
        work = Path(td)
        doc, stdout = run_json(VIDFAST, work)
        vms = doc["vms"]
        assert doc["schema"] == "jsvm-switch-ir/v0"
        assert len(vms) >= 16, len(vms)

        by_style = {}
        for vm in vms:
            by_style.setdefault(vm["selector_style"], []).append(vm)

        indexed = by_style.get("indexed", [])
        call = by_style.get("call", [])
        assert len(indexed) >= 8, len(indexed)
        assert len(call) >= 8, len(call)

        for vm in indexed:
            roles = vm["role_bindings"]
            for role in ("stack", "sp", "ip", "opcode_map", "raw_opcode"):
                assert role in roles, (vm["parent_function_id"], role, roles)
        for vm in call:
            roles = vm["role_bindings"]
            helpers = vm["helper_bindings"]
            for role in (
                "stack",
                "control_stack",
                "ip",
                "bytecode",
                "decode_key",
                "env",
                "env_fallback",
            ):
                assert role in roles, (vm["parent_function_id"], role, roles)
            for helper in (
                "read_byte",
                "read_u16",
                "read_string",
                "stack_push",
                "stack_pop",
                "env_lookup",
            ):
                assert helpers.get(helper), (vm["parent_function_id"], helper, helpers)

        assert sum(len(vm["handlers"]) for vm in vms) == 536

        expected_indexed_labels = Counter(
            {
                "slot_load": 3,
                "property_get": 2,
                "property_set": 2,
                "slot_store": 2,
                "jump_if_truthy": 1,
                "jump_if_falsy": 1,
                "jump": 1,
                "pop": 1,
                "dup": 1,
                "nop": 1,
                "push_null": 1,
                "push_undefined": 1,
                "increment": 1,
                "decrement": 1,
                "to_number": 1,
                "add": 1,
                "sub": 1,
                "mul": 1,
                "div": 1,
                "mod": 1,
                "lt": 1,
                "lte": 1,
                "gt": 1,
                "gte": 1,
                "strict_eq": 1,
                "strict_neq": 1,
                "loose_eq": 1,
                "loose_neq": 1,
            }
        )
        expected_call_labels = Counter(
            {
                "property_get": 4,
                "property_set": 2,
                "call": 2,
                "operator_dispatch": 2,
                "method_call": 2,
                "throw": 2,
                "pop": 1,
                "env_load_soft": 1,
                "construct": 1,
                "jump": 1,
                "control_pop": 1,
                "return": 1,
                "push_literal": 1,
                "return_peek": 1,
                "dup": 1,
                "global_load_checked": 1,
                "control_push": 1,
                "closure_create": 1,
                "env_call": 1,
                "env_load": 1,
                "jump_if_falsy": 1,
                "collect_args": 1,
                "jump_if_truthy": 1,
                "yield": 1,
                "env_store": 1,
                "object_from_pairs": 1,
            }
        )
        for vm in indexed:
            labels = Counter(handler["semantic_label"] for handler in vm["handlers"])
            assert labels == expected_indexed_labels, (vm["parent_function_id"], labels)
        for vm in call:
            labels = Counter(handler["semantic_label"] for handler in vm["handlers"])
            assert labels == expected_call_labels, (vm["parent_function_id"], labels)

        coarse_by_label = {}
        for vm in vms:
            for handler in vm["handlers"]:
                label = handler["semantic_label"]
                assert not label.endswith("unknown"), (vm["parent_function_id"], handler)
                old_hash = coarse_by_label.setdefault(label, handler["coarse_semantic_hash"])
                assert old_hash == handler["coarse_semantic_hash"], (label, old_hash, handler)

        # Semantic labels intentionally ignore randomized opcode numbering and
        # decoded/static property spelling. Each independently renamed copy of a
        # family should expose the same operation inventory.
        for style, group in (("indexed", indexed), ("call", call)):
            inventories = [
                Counter(h["semantic_label"] for h in vm["handlers"])
                for vm in group
            ]
            assert all(inv == inventories[0] for inv in inventories[1:]), (
                style,
                inventories,
            )
            assert not any(
                label.endswith("unknown") for label in inventories[0]
            ), (style, inventories[0])
            print(f"{style} semantic inventory:", dict(inventories[0]))

        indexed_overlap = overlaps(indexed)
        call_overlap = overlaps(call)
        assert min(indexed_overlap) >= 23, indexed_overlap
        assert min(call_overlap) >= 22, call_overlap
        print(stdout.rstrip())
        print(
            "indexed semantic-hash overlap:",
            f"min={min(indexed_overlap)} median={sorted(indexed_overlap)[len(indexed_overlap)//2]} max={max(indexed_overlap)}",
        )
        print(
            "call semantic-hash overlap:",
            f"min={min(call_overlap)} median={sorted(call_overlap)[len(call_overlap)//2]} max={max(call_overlap)}",
        )

        kinds = Counter(
            effect["ir"]["kind"]
            for vm in vms
            for handler in vm["handlers"]
            for effect in handler["effects"]
        )
        raw_count = kinds["raw_js"] + kinds["raw_expression"]
        assert raw_count == 0, kinds
        assert sum(kinds.values()) == 1432, sum(kinds.values())
        print("IR kinds:", dict(kinds.most_common()))

        for negative in NEGATIVES:
            neg_doc, _ = run_json(negative, work)
            assert not neg_doc["vms"], (negative, len(neg_doc["vms"]))

        print(
            "PASS: Vidfast direct-switch IR roles recovered across "
            f"{len(vms)} interpreters; all {len(NEGATIVES)} hard negatives emit zero VMs"
        )


if __name__ == "__main__":
    main()
