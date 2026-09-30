#!/usr/bin/env python3
import argparse
import json
import re
from pathlib import Path


def iter_reports(path: Path):
    text = path.read_text()
    decoder = json.JSONDecoder()
    pos = 0
    n = len(text)
    while pos < n:
        while pos < n and text[pos].isspace():
            pos += 1
        if pos >= n:
            break
        try:
            obj, end = decoder.raw_decode(text, pos)
        except json.JSONDecodeError as exc:
            print(
                f"[warning] trailing/incomplete JSON ignored at offset {pos}: {exc}",
                file=__import__("sys").stderr,
            )
            break
        yield obj
        pos = end


def parse_int_aliases(source: str) -> set[str]:
    # Only promote helpers we can prove are direct aliases of the built-in.
    return set(re.findall(
        r"(?:^|[,;])\s*([A-Za-z_$][\w$]*)\s*=\s*parseInt\b",
        source,
    ))


def resolve_parse_int(expr: str | None, aliases: set[str]) -> int | None:
    if not expr:
        return None
    m = re.fullmatch(
        r'\s*([A-Za-z_$][\w$]*)\(\s*(["\'])([0-9A-Za-z+-]+)\2\s*,\s*(\d+)\s*\)\s*',
        expr,
    )
    if not m or m.group(1) not in aliases:
        return None
    try:
        return int(m.group(3), int(m.group(4)))
    except (ValueError, OverflowError):
        return None


def fmt_field(value, expr, aliases):
    if value is not None:
        return str(value)
    resolved = resolve_parse_int(expr, aliases)
    if resolved is not None:
        return f"{resolved}{{{expr}}}"
    if expr:
        return "{" + expr + "}"
    return "{?}"


def resolved_field(value, expr, aliases):
    if value is not None:
        return int(value)
    return resolve_parse_int(expr, aliases)


def selector_domain(masks):
    masks = sorted(set(int(x) for x in masks))
    if not masks or any(m <= 0 or (m & (m - 1)) for m in masks):
        return None
    combined = 0
    for m in masks:
        combined |= m
    # Only claim a dense 0..N domain when the masks cover every bit up to N.
    if combined + 1 != 1 << len(masks):
        return None
    return set(range(combined + 1))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("jsonl")
    ap.add_argument("--instructions", type=int, default=20)
    ap.add_argument("--max-decoders", type=int, default=None)
    ap.add_argument("--builder-start", type=int, default=None)
    ap.add_argument("--all", action="store_true", help="include unlinked decoder candidates")
    args = ap.parse_args()

    for report in iter_reports(Path(args.jsonl)):
        builders_by_start = {b["start"]: b for b in report.get("push_builders", [])}
        source_path = Path(report["file"])
        try:
            source = source_path.read_text()
        except FileNotFoundError:
            source = ""
        aliases = parse_int_aliases(source)
        shown = 0
        report_observed = set()
        report_selector_domain = set()
        print(f"\n== {source_path.name} ==")
        if aliases:
            print("parseInt aliases:", ", ".join(sorted(aliases)))

        for dec in report.get("decoder_candidates", []):
            linked = dec.get("builder_var") is not None and dec.get("builder_start") is not None
            if not linked and not args.all:
                continue
            if args.builder_start is not None and dec.get("builder_start") != args.builder_start:
                continue
            if args.max_decoders is not None and shown >= args.max_decoders:
                break

            builder = builders_by_start.get(dec.get("builder_start")) if linked else None
            width = int(dec["width"])
            canonical_width = None
            width_score = None
            candidate_top_scoring = False
            if builder:
                hints = builder.get("width_hints", [])
                if hints:
                    top = max(hints, key=lambda h: h["score"])
                    top_score = top["score"]
                    tied = [h for h in hints if h["score"] == top_score]
                    canonical_width = min(h["width"] for h in tied)
                    for h in hints:
                        if h["width"] == width:
                            width_score = h["score"]
                            candidate_top_scoring = h["score"] == top_score
                            break

            confidence = 0
            reasons = []
            if linked:
                confidence += 3
                reasons.append("builder-linked")
            if builder and builder.get("arguments", 0) % width == 0:
                confidence += 1
                reasons.append("length-aligned")
            if candidate_top_scoring:
                confidence += 3
                reasons.append("decoder-width-is-top-scoring-period")
            offsets = sorted(dec.get("operand_offsets", []))
            if offsets and offsets[0] == 0 and len(offsets) >= 2:
                confidence += 1
                reasons.append("multiple-fetch-offsets")

            print(
                f"decoder {dec['function_id']} object={dec['object']} "
                f"builder={dec.get('builder_var') or '?'} width={width} ip={dec['ip']} "
                f"base={dec.get('base') or '<inline>'} offsets={offsets} "
                f"confidence={confidence}/8"
            )
            print(
                f"  builder_min_top_period={canonical_width} linked_decoder_width={width} candidate_width_score={width_score} "
                f"reasons={','.join(reasons)}"
            )
            print(f"  evidence: {dec.get('preview','')[:220]}")
            masks = dec.get("selector_masks", [])
            domain = selector_domain(masks)
            if dec.get("selector_var") or masks:
                print(
                    f"  selector: var={dec.get('selector_var')} masks={masks} "
                    f"domain={sorted(domain) if domain is not None else '?'}"
                )
                if domain is not None:
                    report_selector_domain.update(domain)

            if not builder:
                shown += 1
                continue

            values = builder.get("values", [])
            unknowns = {u["index"]: u["preview"] for u in builder.get("unknowns", [])}
            instruction_count = len(values) // width if width else 0
            opcodes = set()
            unknown_opcode_slots = 0
            for insn in range(instruction_count):
                idx = insn * width
                value = resolved_field(values[idx], unknowns.get(idx), aliases)
                if value is None:
                    unknown_opcode_slots += 1
                else:
                    opcodes.add(value)
            report_observed.update(opcodes)
            print(
                f"  stream: args={len(values)} instructions={instruction_count} "
                f"known={sum(v is not None for v in values)}/{len(values)}"
            )
            print(
                f"  opcodes: observed={sorted(opcodes)} "
                f"unknown_slots={unknown_opcode_slots}"
            )
            if domain is not None:
                print(
                    f"  selector-vs-stream: unobserved={sorted(domain-opcodes)} "
                    f"out_of_domain={sorted(opcodes-domain)}"
                )

            limit = min(instruction_count, args.instructions)
            for insn in range(limit):
                pc = insn * width
                fields = []
                for off in range(width):
                    idx = pc + off
                    fields.append(fmt_field(values[idx], unknowns.get(idx), aliases))
                print(f"    {insn:04d} pc={pc:04d}: " + " | ".join(fields))

            shown += 1

        if shown == 0:
            print("(no linked decoder candidates)")
        elif report_observed:
            print(
                f"report opcode union: observed={sorted(report_observed)}"
            )
            if report_selector_domain:
                print(
                    f"report selector union: domain={sorted(report_selector_domain)} "
                    f"unobserved={sorted(report_selector_domain-report_observed)}"
                )


if __name__ == "__main__":
    main()
