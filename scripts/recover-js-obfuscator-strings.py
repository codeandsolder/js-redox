#!/usr/bin/env python3
"""Conservatively recover common javascript-obfuscator string-array decoders.

Static only: recognizes a self-redefining string-table provider, the generated
Base64 or RC4 decoder, and (when present) the generated push/shift checksum
rotation. It never executes target JavaScript.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
from dataclasses import dataclass
from pathlib import Path

IDENT = r"[A-Za-z_$][A-Za-z0-9_$]*"
NUM = r"(?:0[xX][0-9A-Fa-f]+|\d+)"
LOWER_B64 = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+/="


def match_balanced(text: str, start: int, opener: str, closer: str) -> int | None:
    assert text[start] == opener
    depth = 0
    quote = None
    esc = False
    i = start
    while i < len(text):
        ch = text[i]
        if quote:
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == quote:
                quote = None
            i += 1
            continue
        if ch in "'\"`":
            quote = ch
        elif ch == opener:
            depth += 1
        elif ch == closer:
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return None


def decode_js_string(text: str, start: int) -> tuple[str, int] | None:
    quote = text[start]
    if quote not in "'\"":
        return None
    out: list[str] = []
    i = start + 1
    while i < len(text):
        ch = text[i]
        if ch == quote:
            return "".join(out), i + 1
        if ch != "\\":
            out.append(ch)
            i += 1
            continue
        i += 1
        if i >= len(text):
            return None
        esc = text[i]
        i += 1
        simple = {"n": "\n", "r": "\r", "t": "\t", "b": "\b", "f": "\f", "v": "\v", "0": "\0"}
        if esc in "\\'\"/":
            out.append(esc)
        elif esc in simple:
            out.append(simple[esc])
        elif esc == "x" and i + 2 <= len(text):
            try:
                out.append(chr(int(text[i:i+2], 16)))
            except ValueError:
                return None
            i += 2
        elif esc == "u":
            if i < len(text) and text[i] == "{":
                j = text.find("}", i + 1)
                if j < 0:
                    return None
                try:
                    out.append(chr(int(text[i+1:j], 16)))
                except ValueError:
                    return None
                i = j + 1
            elif i + 4 <= len(text):
                try:
                    out.append(chr(int(text[i:i+4], 16)))
                except ValueError:
                    return None
                i += 4
            else:
                return None
        elif esc in "\n\r":
            if esc == "\r" and i < len(text) and text[i] == "\n":
                i += 1
        else:
            # JS identity escape in non-strict strings.
            out.append(esc)
    return None


def parse_string_array(text: str, start: int) -> tuple[list[str], int] | None:
    end = match_balanced(text, start, "[", "]")
    if end is None:
        return None
    vals: list[str] = []
    i = start + 1
    while i < end - 1:
        while i < end - 1 and (text[i].isspace() or text[i] == ","):
            i += 1
        if i >= end - 1:
            break
        got = decode_js_string(text, i)
        if got is None:
            return None
        val, i = got
        vals.append(val)
        while i < end - 1 and text[i].isspace():
            i += 1
        if i < end - 1 and text[i] not in ",]":
            return None
    return vals, end


@dataclass
class Provider:
    name: str
    values: list[str]
    function_start: int
    function_end: int


@dataclass
class Decoder:
    name: str
    provider: Provider
    offset: int
    mode: str
    index_param: str
    key_param: str | None
    rotation: int = 0


def function_body(source: str, match: re.Match[str]) -> tuple[str, int] | None:
    brace = source.find("{", match.end() - 1)
    if brace < 0:
        return None
    end = match_balanced(source, brace, "{", "}")
    if end is None:
        return None
    return source[brace + 1:end - 1], end


def discover_providers(source: str) -> list[Provider]:
    out = []
    for m in re.finditer(rf"\bfunction\s+({IDENT})\s*\(\s*\)\s*\{{", source):
        name = m.group(1)
        got = function_body(source, m)
        if not got:
            continue
        body, end = got
        vm = re.search(rf"\b(?:var|let|const)\s+({IDENT})\s*=\s*\[", body)
        if not vm:
            continue
        arr_name = vm.group(1)
        arr_abs = source.find("[", m.start() + vm.start())
        parsed = parse_string_array(source, arr_abs)
        if not parsed:
            continue
        vals, _ = parsed
        if not vals:
            continue
        if not re.search(rf"\b{re.escape(name)}\s*=\s*function\s*\(\s*\)\s*\{{\s*return\s+{re.escape(arr_name)}\s*;?\s*\}}", body):
            continue
        if not re.search(rf"\breturn\s+{re.escape(name)}\s*\(\s*\)\s*;?", body):
            continue
        out.append(Provider(name, vals, m.start(), end))
    return out


def discover_decoders(source: str, providers: list[Provider]) -> list[Decoder]:
    out = []
    for provider in providers:
        for m in re.finditer(rf"\bfunction\s+({IDENT})\s*\(([^)]*)\)\s*\{{", source):
            name = m.group(1)
            got = function_body(source, m)
            if not got:
                continue
            body, _ = got
            if not re.search(rf"=\s*{re.escape(provider.name)}\s*\(\s*\)", body):
                continue
            redef = re.search(rf"\b{re.escape(name)}\s*=\s*function\s*\(([^)]*)\)\s*\{{", body)
            if not redef:
                continue
            params = [p.strip() for p in redef.group(1).split(",") if p.strip()]
            if not params or not re.fullmatch(IDENT, params[0]):
                continue
            index_param = params[0]
            key_param = params[1] if len(params) > 1 and re.fullmatch(IDENT, params[1]) else None
            om = re.search(rf"\b{re.escape(index_param)}\s*=\s*{re.escape(index_param)}\s*-\s*({NUM})\s*;", body)
            if not om:
                continue
            offset = int(om.group(1), 0)
            if LOWER_B64 not in body or "decodeURIComponent" not in body:
                continue
            # javascript-obfuscator RC4 helper has a 256-byte KSA/PRGA and consumes key param.
            rc4_shape = key_param is not None and "0x100" in body and body.count("charCodeAt") >= 2
            mode = "rc4" if rc4_shape else "base64"
            out.append(Decoder(name, provider, offset, mode, index_param, key_param))
    # Prefer the most featureful decoder if a provider has multiple wrappers.
    uniq = {}
    for d in out:
        key = (d.name, d.provider.name)
        if key not in uniq or (d.mode == "rc4" and uniq[key].mode != "rc4"):
            uniq[key] = d
    return list(uniq.values())


def b64_lower_decode(value: str) -> str:
    out = bytearray()
    q = 0
    acc = 0
    for ch in value:
        c = LOWER_B64.find(ch)
        if c < 0:
            continue
        old_q = q
        acc = acc * 64 + c if q % 4 else c
        q += 1
        if old_q % 4:
            out.append(255 & (acc >> ((-2 * q) & 6)))
    return bytes(out).decode("utf-8")


def rc4_js(value: str, key: str) -> str:
    data = b64_lower_decode(value)
    s = list(range(256))
    j = 0
    key_units = [ord(c) for c in key]
    if not key_units:
        raise ValueError("empty RC4 key")
    for i in range(256):
        j = (j + s[i] + key_units[i % len(key_units)]) % 256
        s[i], s[j] = s[j], s[i]
    i = j = 0
    out = []
    for ch in data:
        i = (i + 1) % 256
        j = (j + s[i]) % 256
        s[i], s[j] = s[j], s[i]
        out.append(chr(ord(ch) ^ s[(s[i] + s[j]) % 256]))
    return "".join(out)


def decode_at(dec: Decoder, raw: int, key: str | None) -> str:
    idx = raw - dec.offset
    vals = dec.provider.values
    if not (0 <= idx < len(vals)):
        raise IndexError(idx)
    encoded = vals[idx]
    if dec.mode == "base64":
        return b64_lower_decode(encoded)
    if key is None:
        raise ValueError("RC4 decoder requires literal key")
    return rc4_js(encoded, key)


def js_parse_int(s: str) -> int:
    m = re.match(r"^[\s]*([+-]?)(0[xX][0-9A-Fa-f]+|\d+)", s)
    if not m:
        raise ValueError(f"parseInt({s!r})")
    sign = -1 if m.group(1) == "-" else 1
    token = m.group(2)
    return sign * int(token, 16 if token.lower().startswith("0x") else 10)


def literal_string(token: str) -> str:
    got = decode_js_string(token, 0)
    if not got or got[1] != len(token):
        raise ValueError(token)
    return got[0]


def decoder_call_pattern(name: str) -> re.Pattern[str]:
    return re.compile(rf"\b{re.escape(name)}\s*\(\s*({NUM})(?:\s*,\s*('(?:\\.|[^'\\])*'|\"(?:\\.|[^\"\\])*\"))?\s*\)")


def try_rotation(source: str, dec: Decoder) -> int | None:
    # Find the generated rotator invocation (...)(provider, TARGET).
    suffix_re = re.compile(rf"\}}\s*\)?\s*\(\s*{re.escape(dec.provider.name)}\s*,\s*({NUM})\s*\)\s*\)?")
    for sm in suffix_re.finditer(source):
        start = source.rfind("(function", max(0, sm.start() - 12000), sm.start())
        if start < 0:
            continue
        seg = source[start:sm.end()]
        if "shift" not in seg or "push" not in seg or "parseInt" not in seg:
            continue
        am = re.search(rf"\b(?:var|let|const)\s+({IDENT})\s*=\s*{re.escape(dec.name)}\b", seg)
        if not am:
            continue
        alias = am.group(1)
        # Generated form: try { var checksum = EXPR; if (checksum === targetParam) ... }
        em = re.search(r"\btry\s*\{\s*var\s+([A-Za-z_$][\w$]*)\s*=\s*(.*?);\s*if\s*\(\s*\1\s*===", seg, re.S)
        if not em:
            continue
        expr = em.group(2)
        target = int(sm.group(1), 0)
        call_re = decoder_call_pattern(alias)
        original = list(dec.provider.values)
        for rot in range(len(original)):
            dec.provider.values = original[rot:] + original[:rot]
            failed = False
            def repl(cm: re.Match[str]) -> str:
                nonlocal failed
                try:
                    raw = int(cm.group(1), 0)
                    key = literal_string(cm.group(2)) if cm.group(2) else None
                    return str(js_parse_int(decode_at(dec, raw, key)))
                except Exception:
                    failed = True
                    return "0"
            reduced = re.sub(rf"parseInt\s*\(\s*{call_re.pattern}\s*\)", repl, expr)
            if failed:
                continue
            if not re.fullmatch(r"[0-9A-Fa-fxX+\-*/().\s]+", reduced):
                continue
            try:
                value = eval(reduced, {"__builtins__": {}}, {})
            except Exception:
                continue
            if isinstance(value, (int, float)) and math.isfinite(value) and abs(value - target) < 1e-9:
                dec.provider.values = original
                return rot
        dec.provider.values = original
    return None


def safe_aliases(source: str, decoder_name: str) -> list[str]:
    names = [decoder_name]
    for m in re.finditer(rf"\b(?:var|let|const)\s+({IDENT})\s*=\s*{re.escape(decoder_name)}\b", source):
        alias = m.group(1)
        decls = len(re.findall(rf"\b(?:var|let|const)\s+{re.escape(alias)}\b", source))
        writes = len(re.findall(rf"(?<![A-Za-z0-9_$]){re.escape(alias)}\s*=", source))
        if decls == 1 and writes == 1:
            names.append(alias)
    return names


def recover(source: str) -> tuple[str, dict]:
    if LOWER_B64 not in source:
        return source, {
            "schema": "js-static-string-recovery/v1",
            "safe_static_only": True,
            "changed": False,
            "input_sha256": hashlib.sha256(source.encode()).hexdigest(),
            "output_sha256": hashlib.sha256(source.encode()).hexdigest(),
            "decoders": [],
            "replacements": 0,
        }
    providers = discover_providers(source)
    decoders = discover_decoders(source, providers)
    replacements: list[tuple[int, int, str, str]] = []
    rows = []
    for dec in decoders:
        rotator_re = re.compile(
            rf"\}}\s*\)?\s*\(\s*{re.escape(dec.provider.name)}\s*,\s*{NUM}\s*\)\s*\)?"
        )
        has_rotator = any(
            "shift" in source[max(0, m.start() - 12000):m.end()]
            and "push" in source[max(0, m.start() - 12000):m.end()]
            for m in rotator_re.finditer(source)
        )
        rot = try_rotation(source, dec)
        if has_rotator and rot is None:
            rows.append({
                "decoder": dec.name,
                "provider": dec.provider.name,
                "mode": dec.mode,
                "offset": dec.offset,
                "rotation": None,
                "table_entries": len(dec.provider.values),
                "aliases": [],
                "replacements": 0,
                "status": "rotation-unproven",
            })
            continue
        if rot is not None:
            dec.rotation = rot
            dec.provider.values[:] = dec.provider.values[rot:] + dec.provider.values[:rot]
        aliases = safe_aliases(source, dec.name)
        seen_spans = set()
        for alias in aliases:
            cre = decoder_call_pattern(alias)
            for m in cre.finditer(source):
                span = (m.start(), m.end())
                if span in seen_spans:
                    continue
                try:
                    raw = int(m.group(1), 0)
                    key = literal_string(m.group(2)) if m.group(2) else None
                    text = decode_at(dec, raw, key)
                except Exception:
                    continue
                replacements.append((m.start(), m.end(), json.dumps(text, ensure_ascii=False), dec.name))
                seen_spans.add(span)
        rows.append({
            "decoder": dec.name,
            "provider": dec.provider.name,
            "mode": dec.mode,
            "offset": dec.offset,
            "rotation": dec.rotation,
            "table_entries": len(dec.provider.values),
            "aliases": aliases,
            "replacements": len(seen_spans),
        })
    # Never allow overlap; generated decoder calls are simple and should be disjoint.
    replacements.sort(key=lambda r: (r[0], r[1]))
    filtered = []
    end = -1
    for r in replacements:
        if r[0] < end:
            continue
        filtered.append(r)
        end = r[1]
    out = source
    for start, stop, text, _ in reversed(filtered):
        out = out[:start] + text + out[stop:]
    return out, {
        "schema": "js-static-string-recovery/v1",
        "safe_static_only": True,
        "changed": bool(filtered),
        "input_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "output_sha256": hashlib.sha256(out.encode()).hexdigest(),
        "decoders": rows,
        "replacements": len(filtered),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("input", type=Path)
    ap.add_argument("output", type=Path)
    ap.add_argument("--report", type=Path)
    args = ap.parse_args()
    source = args.input.read_text()
    out, report = recover(source)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(out)
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
