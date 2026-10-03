#!/usr/bin/env python3
import argparse
import json
import re
from pathlib import Path


def safe_name(value):
    value = re.sub(r"[^A-Za-z0-9._-]+", "-", value or "anon").strip("-")
    return value[:80] or "anon"


PSEUDO = {
    "nop": "no operation",
    "pop": "discard(pop())",
    "dup": "push(peek())",
    "push_null": "push(null)",
    "push_undefined": "push(undefined)",
    "increment": "push(to_numeric(pop()) + 1)",
    "decrement": "push(to_numeric(pop()) - 1)",
    "to_number": "push(to_numeric(pop()))",
    "add": "rhs = pop(); lhs = pop(); push(lhs + rhs)",
    "sub": "rhs = pop(); lhs = pop(); push(lhs - rhs)",
    "mul": "rhs = pop(); lhs = pop(); push(lhs * rhs)",
    "div": "rhs = pop(); lhs = pop(); push(lhs / rhs)",
    "mod": "rhs = pop(); lhs = pop(); push(lhs % rhs)",
    "lt": "rhs = pop(); lhs = pop(); push(lhs < rhs)",
    "lte": "rhs = pop(); lhs = pop(); push(lhs <= rhs)",
    "gt": "rhs = pop(); lhs = pop(); push(lhs > rhs)",
    "gte": "rhs = pop(); lhs = pop(); push(lhs >= rhs)",
    "strict_eq": "rhs = pop(); lhs = pop(); push(lhs === rhs)",
    "strict_neq": "rhs = pop(); lhs = pop(); push(lhs !== rhs)",
    "loose_eq": "rhs = pop(); lhs = pop(); push(lhs == rhs)",
    "loose_neq": "rhs = pop(); lhs = pop(); push(lhs != rhs)",
    "property_get": "key = pop(); object = pop(); push(object[key])",
    "property_set": "value = pop(); key/object = pop operands; object[key] = value; push(value)",
    "slot_load": "push(vm_slot[operand])",
    "slot_store": "vm_slot[operand] = pop()",
    "jump": "ip = branch_target",
    "jump_if_truthy": "if (pop()) ip = branch_target; else advance()",
    "jump_if_falsy": "if (!pop()) ip = branch_target; else advance()",
    "conditional_jump": "branch on pop() and update ip",
    "env_load": "push(resolve_lexical(read_string()))",
    "env_load_soft": "push(env[name] ?? fallback_env[name] ?? undefined)",
    "global_load_checked": "require named global; push(global[name])",
    "env_store": "assign nearest lexical owner of name",
    "env_call": "fn = resolve_lexical(name); push(fn(...args))",
    "call": "fn = pop(); push(fn(...args))",
    "method_call": "receiver = pop(); method = receiver[name]; push(method.call(receiver, ...args))",
    "construct": "ctor = pop(); push(Reflect.construct(ctor, args))",
    "operator_dispatch": "operator = operator_table[read_byte()]; push(operator(...operands))",
    "collect_args": "push(pop_n(read_u16()))",
    "spread_concat": "push([...lhs, ...rhs])",
    "object_from_pairs": "pairs = pop_n(2 * read_u16()); push(object_from_pairs(pairs))",
    "push_literal": "decode literal from bytecode and push it",
    "closure_create": "capture lexical environment; push nested VM-backed function",
    "control_push": "push exception/control frame",
    "control_pop": "pop exception/control frame",
    "yield": "value = yield pop(); push(value)",
    "return": "return stack empty ? undefined : pop()",
    "return_peek": "return stack empty ? undefined : peek()",
    "throw": "throw pop()",
    "push_value": "push(value)",
}


def pseudo_for(label):
    return PSEUDO.get(label, f"semantic operation: {label}")


def control_for(label):
    if label == "jump":
        return "jump"
    if label in {"jump_if_truthy", "jump_if_falsy", "conditional_jump"}:
        return "conditional_branch"
    if label in {"return", "return_peek"}:
        return "return"
    if label == "throw":
        return "throw"
    if label == "yield":
        return "yield"
    return "fallthrough"


def render_pseudocode(vm, provenance):
    lines = [
        "Generated semantic pseudocode for a captured JavaScript VM.",
        "This is analyst-oriented approximate semantics, NOT an executable replacement.",
        "",
        f"resource: {provenance.get('url')}",
        f"function: {vm.get('function_name') or '<anonymous>'} ({vm.get('parent_function_id')})",
        f"selector style: {vm.get('selector_style')}  selector: {vm.get('selector')}",
        f"function span: {vm.get('function_start')}..{vm.get('function_end')}",
        f"switch span: {vm.get('switch_start')}..{vm.get('switch_end')}",
        "",
        "roles:",
    ]
    for role, original in sorted(vm.get("role_bindings", {}).items()):
        lines.append(f"  {role:16} <- {original}")
    if vm.get("helper_bindings"):
        lines.append("helpers:")
        for role, original in sorted(vm["helper_bindings"].items()):
            lines.append(f"  {role:16} <- {original}")
    lines.append("")

    def opcode_key(handler):
        opcode = handler.get("opcode")
        return (opcode is None, opcode if opcode is not None else 1 << 60)

    for handler in sorted(vm.get("handlers", []), key=opcode_key):
        opcode = handler.get("opcode")
        key = "default" if opcode is None else str(opcode)
        label = handler.get("semantic_label", "unknown")
        lines.extend(
            [
                f"opcode {key:>7}  {label}  [{control_for(label)}]",
                f"  pseudo: {pseudo_for(label)}",
                f"  exact semantic hash:  {handler.get('semantic_hash')}",
                f"  coarse semantic hash: {handler.get('coarse_semantic_hash')}",
            ]
        )
        normalized = [effect.get("normalized", "") for effect in handler.get("effects", [])]
        original = [effect.get("source", "") for effect in handler.get("effects", [])]
        if normalized:
            lines.append("  normalized:")
            lines.extend(f"    {line}" for line in normalized)
        if original != normalized and original:
            lines.append("  original:")
            lines.extend(f"    {line}" for line in original)
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def render_table_pseudocode(vm, provenance):
    lines = [
        "Generated semantic pseudocode for a captured function-table JavaScript VM.",
        "This is analyst-oriented approximate semantics, NOT an executable replacement.",
        "",
        f"resource: {provenance.get('url')}",
        f"handler table: {vm.get('handler_table')}",
        f"dispatcher: {vm.get('dispatcher_function_id')}",
        f"architecture: {vm.get('architecture')}",
        f"handlers: {len(vm.get('handlers', []))}",
        "",
        "roles:",
    ]
    for role, original in sorted(vm.get("role_bindings", {}).items()):
        lines.append(f"  {role:20} <- {original}")
    if vm.get("method_bindings"):
        lines.append("methods:")
        for original, role in sorted(vm["method_bindings"].items()):
            lines.append(f"  {role:20} <- {original}")
    lines.append("")

    def handler_key(handler):
        raw = str(handler.get("key", ""))
        try:
            return (0, int(raw))
        except ValueError:
            return (1, raw)

    for handler in sorted(vm.get("handlers", []), key=handler_key):
        lines.extend(
            [
                f"handler {handler.get('key')}  semantic={handler.get('semantic_hash')}",
                f"  op kinds: {', '.join(handler.get('op_kinds', []))}",
            ]
        )
        for statement in handler.get("statements", []):
            ir = statement.get("ir", {})
            kind = ir.get("kind", "unknown")
            normalized = statement.get("normalized") or statement.get("source") or ""
            lines.append(f"  [{kind}] {normalized}")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def main():
    ap = argparse.ArgumentParser(
        description="Materialize supported JavaScript VM semantic IR as readable analyst modules"
    )
    ap.add_argument("project", type=Path)
    args = ap.parse_args()
    project = args.project.resolve()
    index_path = project / "analysis/jsvm/index.json"
    if not index_path.exists():
        print("no VM analysis index; 0 devirtualized units")
        return

    index = json.loads(index_path.read_text())
    all_units = []
    switch_count = 0
    table_count = 0

    for row in index.get("code_units", []):
        row.pop("devirtualized_units", None)
        units = []
        scan_id = int(row["scan_id"])

        switch_ir = row.get("switch_ir")
        if switch_ir:
            ir = json.loads((project / switch_ir).read_text())
            for ordinal, vm in enumerate(ir.get("vms", []), 1):
                stem = safe_name(vm.get("function_name") or vm.get("parent_function_id"))
                base = (
                    Path("src/_devirtualized")
                    / f"{scan_id:04}"
                    / f"switch-vm-{ordinal:02}-{stem}"
                )
                rel = base.with_suffix(".js")
                pseudo_rel = base.with_suffix(".pseudo.txt")
                out = project / rel
                pseudo_out = project / pseudo_rel
                out.parent.mkdir(parents=True, exist_ok=True)

                provenance = {
                    "resource_id": row.get("resource_id"),
                    "url": row.get("url"),
                    "captured_raw_path": row.get("raw_path"),
                    "analysis_path": row.get("path"),
                    "analysis_origin": row.get("analysis_origin"),
                    "scan_report": row.get("report"),
                    "switch_ir": switch_ir,
                    "parent_function_id": vm.get("parent_function_id"),
                    "function_start": vm.get("function_start"),
                    "function_end": vm.get("function_end"),
                    "switch_start": vm.get("switch_start"),
                    "switch_end": vm.get("switch_end"),
                }
                handlers = []
                for handler in vm.get("handlers", []):
                    label = handler.get("semantic_label", "unknown")
                    handlers.append(
                        {
                            "opcode": handler.get("opcode"),
                            "label": label,
                            "control": control_for(label),
                            "pseudocode": pseudo_for(label),
                            "semantic_hash": handler.get("semantic_hash"),
                            "coarse_semantic_hash": handler.get("coarse_semantic_hash"),
                            "normalized": [
                                effect.get("normalized", "")
                                for effect in handler.get("effects", [])
                            ],
                            "original": [
                                effect.get("source", "")
                                for effect in handler.get("effects", [])
                            ],
                        }
                    )

                payload = {
                    "schema": "jsvm-readable-switch-module/v1",
                    "provenance": provenance,
                    "function_name": vm.get("function_name"),
                    "selector": vm.get("selector"),
                    "selector_style": vm.get("selector_style"),
                    "role_bindings": vm.get("role_bindings", {}),
                    "helper_bindings": vm.get("helper_bindings", {}),
                    "opcode_map": {
                        str(handler.get("opcode")): handler.get("semantic_label")
                        for handler in vm.get("handlers", [])
                        if handler.get("opcode") is not None
                    },
                    "handlers": handlers,
                }
                out.write_text(
                    "// Generated semantic view of a captured JavaScript VM.\n"
                    "// Provenance-preserving analyst output; not an executable replacement.\n"
                    f"// Human-first listing: {pseudo_rel.name}\n"
                    + "export default "
                    + json.dumps(payload, indent=2, ensure_ascii=False)
                    + ";\n"
                )
                pseudo_out.write_text(render_pseudocode(vm, provenance))

                item = {
                    "vm_kind": "direct_switch",
                    "parent_scan_id": scan_id,
                    "resource_id": row.get("resource_id"),
                    "vm_ordinal": ordinal,
                    "parent_function_id": vm.get("parent_function_id"),
                    "function_name": vm.get("function_name"),
                    "function_start": vm.get("function_start"),
                    "function_end": vm.get("function_end"),
                    "switch_start": vm.get("switch_start"),
                    "switch_end": vm.get("switch_end"),
                    "selector_style": vm.get("selector_style"),
                    "handler_count": len(vm.get("handlers", [])),
                    "source_path": str(rel),
                    "pseudocode_path": str(pseudo_rel),
                    "ir_path": switch_ir,
                }
                units.append(item)
                all_units.append(item)
                switch_count += 1

        table_ir = row.get("table_ir")
        if table_ir:
            ir = json.loads((project / table_ir).read_text())
            for ordinal, vm in enumerate(ir.get("vms", []), 1):
                stem = safe_name(vm.get("handler_table") or vm.get("dispatcher_function_id"))
                base = (
                    Path("src/_devirtualized")
                    / f"{scan_id:04}"
                    / f"table-vm-{ordinal:02}-{stem}"
                )
                rel = base.with_suffix(".js")
                pseudo_rel = base.with_suffix(".pseudo.txt")
                out = project / rel
                pseudo_out = project / pseudo_rel
                out.parent.mkdir(parents=True, exist_ok=True)

                provenance = {
                    "resource_id": row.get("resource_id"),
                    "url": row.get("url"),
                    "captured_raw_path": row.get("raw_path"),
                    "analysis_path": row.get("path"),
                    "analysis_origin": row.get("analysis_origin"),
                    "scan_report": row.get("report"),
                    "table_ir": table_ir,
                    "parent_scan_id": scan_id,
                }
                payload = {
                    "schema": "jsvm-readable-table-module/v1",
                    "provenance": provenance,
                    "dispatcher_function_id": vm.get("dispatcher_function_id"),
                    "handler_table": vm.get("handler_table"),
                    "handler_count": vm.get("handler_count"),
                    "architecture": vm.get("architecture"),
                    "producer_method": vm.get("producer_method"),
                    "linked_transducer": vm.get("linked_transducer"),
                    "role_bindings": vm.get("role_bindings", {}),
                    "method_bindings": vm.get("method_bindings", {}),
                    "handlers": vm.get("handlers", []),
                }
                out.write_text(
                    "// Generated semantic view of a captured function-table JavaScript VM.\n"
                    "// Provenance-preserving analyst output; not an executable replacement.\n"
                    f"// Human-first listing: {pseudo_rel.name}\n"
                    + "export default "
                    + json.dumps(payload, indent=2, ensure_ascii=False)
                    + ";\n"
                )
                pseudo_out.write_text(render_table_pseudocode(vm, provenance))

                item = {
                    "vm_kind": "function_table",
                    "parent_scan_id": scan_id,
                    "resource_id": row.get("resource_id"),
                    "vm_ordinal": ordinal,
                    "parent_function_id": vm.get("dispatcher_function_id"),
                    "function_name": None,
                    "handler_table": vm.get("handler_table"),
                    "architecture": vm.get("architecture"),
                    "handler_count": len(vm.get("handlers", [])),
                    "source_path": str(rel),
                    "pseudocode_path": str(pseudo_rel),
                    "ir_path": table_ir,
                }
                units.append(item)
                all_units.append(item)
                table_count += 1

        row["devirtualized_units"] = units

    index["devirtualized_units"] = all_units
    index_path.write_text(json.dumps(index, indent=2) + "\n")
    print(
        f"materialized {len(all_units)} VM module(s): "
        f"{switch_count} direct-switch + {table_count} function-table; "
        "human pseudocode under src/_devirtualized/"
    )


if __name__ == "__main__":
    main()
