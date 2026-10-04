#!/usr/bin/env python3
"""Conservatively recover proven static string-table decoders.

Static only: recognizes common javascript-obfuscator Base64/RC4 tables and a
strict rotated-Base91 scaffold used by the generated VM corpus. Base91 recovery
is limited to ASCII-safe outputs and never executes target JavaScript.
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
class Base91Decoder:
    name: str
    table_name: str
    values: list[str]
    rotation: int
    alphabet: str
    transform: str


def parse_simple_literal(token: str):
    token = token.strip()
    if not token:
        raise ValueError("empty literal")
    if token[0] in "'\"":
        got = decode_js_string(token, 0)
        if got is None or got[1] != len(token):
            raise ValueError(token)
        return got[0]
    if token == "null":
        return None
    if re.fullmatch(r"void\s+" + NUM, token):
        return None
    if re.fullmatch(r"!\s*0[xX]?0*", token):
        return True
    if re.fullmatch(r"!\s*(?:0[xX]0*1|1)", token):
        return False
    if re.fullmatch(NUM, token):
        return int(token, 0)
    raise ValueError(token)


def parse_simple_array(text: str, start: int) -> tuple[list[object], int] | None:
    end = match_balanced(text, start, "[", "]")
    if end is None:
        return None
    vals = []
    item_start = start + 1
    quote = None
    esc = False
    depth = 0
    for i in range(start + 1, end):
        ch = text[i]
        if quote:
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == quote:
                quote = None
            continue
        if ch in "'\"":
            quote = ch
        elif ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == "," and depth == 0:
            token = text[item_start:i].strip()
            if token:
                try:
                    vals.append(parse_simple_literal(token))
                except ValueError:
                    return None
            item_start = i + 1
    token = text[item_start:end - 1].strip()
    if token:
        try:
            vals.append(parse_simple_literal(token))
        except ValueError:
            return None
    return vals, end


def discover_simple_arrays(source: str) -> dict[str, list[object]]:
    arrays = {}
    for m in re.finditer(rf"\b(?:var|let|const)\s+({IDENT})\s*=\s*\[", source):
        start = source.find("[", m.start(), m.end() + 1)
        if start < 0:
            continue
        parsed = parse_simple_array(source, start)
        if parsed is None:
            continue
        values, _ = parsed
        arrays[m.group(1)] = values
    return arrays



def enclosing_function_scope(
    spans: list[tuple[int, int, str]], pos: int
) -> tuple[int, int] | None:
    containers = [(start, end) for start, end, _ in spans if start < pos < end]
    return min(containers, key=lambda span: span[1] - span[0]) if containers else None


def named_functions(source: str, name: str):
    out = []
    for m in re.finditer(rf"\bfunction\s+{re.escape(name)}\s*\(([^)]*)\)\s*\{{", source):
        got = function_body(source, m)
        if not got:
            continue
        body, end = got
        params = [p.strip().lstrip("...").strip() for p in m.group(1).split(",") if p.strip()]
        out.append((body, m.start(), end, params))
    return out

def named_function(source: str, name: str) -> tuple[str, int, int, list[str]] | None:
    m = re.search(rf"\bfunction\s+{re.escape(name)}\s*\(([^)]*)\)\s*\{{", source)
    if not m:
        return None
    got = function_body(source, m)
    if not got:
        return None
    body, end = got
    params = [p.strip().lstrip("...").strip() for p in m.group(1).split(",") if p.strip()]
    return body, m.start(), end, params


def string_literals(text: str):
    i = 0
    while i < len(text):
        if text[i] not in "'\"":
            i += 1
            continue
        got = decode_js_string(text, i)
        if got is None:
            i += 1
            continue
        value, end = got
        yield value
        i = end


def substitute_simple_array_literals(
    text: str, simple_arrays: dict[str, list[object]]
) -> str:
    pattern = re.compile(rf"\b({IDENT})\s*\[\s*({NUM})\s*\]")

    def repl(match: re.Match[str]) -> str:
        values = simple_arrays.get(match.group(1))
        if values is None:
            return match.group(0)
        index = int(match.group(2), 0)
        if not 0 <= index < len(values):
            return match.group(0)
        value = values[index]
        if isinstance(value, bool):
            return "true" if value else "false"
        if isinstance(value, int):
            return str(value)
        if isinstance(value, str):
            return json.dumps(value)
        if value is None:
            return "void 0"
        return match.group(0)

    return pattern.sub(repl, text)


def looks_like_base91_decoder(
    body: str, alphabet: str, simple_arrays: dict[str, list[object]]
) -> bool:
    if len(alphabet) != 91 or len(set(alphabet)) != 91:
        return False
    resolved = substitute_simple_array_literals(body, simple_arrays)
    compact = re.sub(r"\s+", "", resolved)
    required_fragments = (
        ".indexOf(",
        ".push(",
        "*91",
        "&8191",
        ">88?13:14",
        "&255",
        ">>=8",
        "-=8",
        "=-1",
        ">-1",
    )
    return all(fragment in compact for fragment in required_fragments)


def decode_base91(value: str, alphabet: str) -> str:
    out = bytearray()
    acc = 0
    bits = 0
    pending = -1
    for ch in value:
        index = alphabet.find(ch)
        if index < 0:
            continue
        if pending < 0:
            pending = index
            continue
        pending += index * 91
        acc |= pending << bits
        bits += 13 if (pending & 8191) > 88 else 14
        while bits > 7:
            out.append(acc & 255)
            acc >>= 8
            bits -= 8
        pending = -1
    if pending > -1:
        out.append((acc | pending << bits) & 255)
    if not out.isascii():
        raise ValueError("decoded Base91 bytes are not ASCII-safe")
    return out.decode("ascii")


def discover_rotated_base91_decoders(
    source: str, simple_arrays: dict[str, list[object]]
) -> list[Base91Decoder]:
    out = []
    spans = function_spans(source)
    assignment = re.compile(rf"\b({IDENT})\s*=\s*({IDENT})\s*\(\s*\[")
    for m in assignment.finditer(source):
        table_name, rotator = m.group(1), m.group(2)
        table_scope = enclosing_function_scope(spans, m.start())
        array_start = source.find("[", m.start(), m.end())
        parsed = parse_string_array(source, array_start)
        if parsed is None:
            continue
        values, array_end = parsed
        suffix = re.match(rf"\s*,\s*({NUM})\s*\)", source[array_end:])
        if not suffix or not values:
            continue
        rotation = int(suffix.group(1), 0) % len(values)

        rotator_fn = next(
            (
                found
                for found in named_functions(source, rotator)
                if enclosing_function_scope(spans, found[1]) == table_scope
            ),
            None,
        )
        if not rotator_fn or len(rotator_fn[3]) < 2:
            continue
        rotator_body, _, _, rotator_params = rotator_fn
        array_param, count_param = rotator_params[:2]
        push_shift = re.search(
            rf"\b{re.escape(array_param)}\s*\.\s*push\s*\(\s*"
            rf"{re.escape(array_param)}\s*\.\s*shift\s*\(\s*\)\s*\)",
            rotator_body,
        )
        loop_uses_count = re.search(
            rf"\bfor\s*\([^;]*;[^;]*<\s*{re.escape(count_param)}\b", rotator_body
        )
        returned = re.search(rf"\breturn\s+{re.escape(array_param)}\s*;?", rotator_body)
        if not (push_shift and loop_uses_count and returned):
            continue

        for dm in re.finditer(rf"\bfunction\s+({IDENT})\s*\(([^)]*)\)\s*\{{", source):
            if dm.start() >= m.start():
                continue
            if enclosing_function_scope(spans, dm.start()) != table_scope:
                continue
            decoder_name = dm.group(1)
            got = function_body(source, dm)
            if not got:
                continue
            decoder_body, _ = got
            # The compact wrapper must directly feed an indexed entry from the
            # rotated table into a named transform and cache/return the result.
            transform_match = re.search(
                rf"\b({IDENT})\s*\(\s*{re.escape(table_name)}\s*\[", decoder_body
            )
            if (
                not transform_match
                or "typeof" not in decoder_body
                or "return" not in decoder_body
                or len(decoder_body) > 4096
            ):
                continue
            transform = transform_match.group(1)
            transform_fn = next(
                (
                    found
                    for found in named_functions(source, transform)
                    if enclosing_function_scope(spans, found[1]) == table_scope
                ),
                None,
            )
            if not transform_fn or transform_fn[1] >= dm.start():
                continue
            transform_body = transform_fn[0]
            alphabets = [s for s in string_literals(transform_body) if len(s) == 91]
            alphabet = next(
                (
                    candidate
                    for candidate in alphabets
                    if looks_like_base91_decoder(transform_body, candidate, simple_arrays)
                ),
                None,
            )
            if alphabet is None:
                continue
            rotated = values[rotation:] + values[:rotation]
            out.append(
                Base91Decoder(
                    name=decoder_name,
                    table_name=table_name,
                    values=rotated,
                    rotation=rotation,
                    alphabet=alphabet,
                    transform=transform,
                )
            )
    unique = {}
    for decoder in out:
        unique[(decoder.name, decoder.table_name)] = decoder
    return list(unique.values())


def function_spans(source: str):
    spans = []
    for m in re.finditer(rf"\bfunction(?:\s+{IDENT})?\s*\(([^)]*)\)\s*\{{", source):
        got = function_body(source, m)
        if not got:
            continue
        _, end = got
        spans.append((m.start(), end, m.group(1)))
    return spans


def shadowed_scopes(source: str, name: str, primary_start: int) -> list[tuple[int, int]]:
    spans = function_spans(source)
    shadows = []
    declaration_positions = [
        m.start()
        for m in re.finditer(rf"\bfunction\s+{re.escape(name)}\s*\(", source)
        if m.start() != primary_start
    ]
    declaration_positions.extend(
        m.start()
        for m in re.finditer(rf"\b(?:var|let|const)\s+{re.escape(name)}\b", source)
    )
    for start, end, params in spans:
        param_names = [p.strip().lstrip("...").strip() for p in params.split(",") if p.strip()]
        if name in param_names:
            shadows.append((start, end))
    for pos in declaration_positions:
        containers = [(start, end) for start, end, _ in spans if start < pos < end]
        if containers:
            shadows.append(min(containers, key=lambda span: span[1] - span[0]))
    shadows.sort()
    merged = []
    for start, end in shadows:
        if merged and start <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], end))
        else:
            merged.append((start, end))
    return merged


def in_spans(pos: int, spans: list[tuple[int, int]]) -> bool:
    return any(start <= pos < end for start, end in spans)


def base91_call_replacements(
    source: str,
    decoder: Base91Decoder,
    simple_arrays: dict[str, list[object]],
) -> list[tuple[int, int, str, str]]:
    primary = named_function(source, decoder.name)
    if not primary:
        return []
    excluded = shadowed_scopes(source, decoder.name, primary[1])
    replacements = []
    seen = set()

    direct = re.compile(rf"\b{re.escape(decoder.name)}\s*\(\s*({NUM})\s*\)")
    for m in direct.finditer(source):
        if in_spans(m.start(), excluded):
            continue
        index = int(m.group(1), 0)
        if not 0 <= index < len(decoder.values):
            continue
        try:
            text = decode_base91(decoder.values[index], decoder.alphabet)
        except ValueError:
            continue
        span = (m.start(), m.end())
        seen.add(span)
        replacements.append((*span, json.dumps(text, ensure_ascii=False), decoder.name))

    indirect = re.compile(
        rf"\b{re.escape(decoder.name)}\s*\(\s*({IDENT})\s*\[\s*({NUM})\s*\]\s*\)"
    )
    for m in indirect.finditer(source):
        if in_spans(m.start(), excluded):
            continue
        values = simple_arrays.get(m.group(1))
        if values is None:
            continue
        slot = int(m.group(2), 0)
        if not 0 <= slot < len(values) or not isinstance(values[slot], int):
            continue
        index = values[slot]
        if not 0 <= index < len(decoder.values):
            continue
        span = (m.start(), m.end())
        if span in seen:
            continue
        try:
            text = decode_base91(decoder.values[index], decoder.alphabet)
        except ValueError:
            continue
        replacements.append((*span, json.dumps(text, ensure_ascii=False), decoder.name))
    return replacements


STRING_TOKEN = r"(?:'(?:\\.|[^'\\])*'|\"(?:\\.|[^\"\\])*\")"
STRING_CONCAT_RE = re.compile(rf"({STRING_TOKEN})\s*\+\s*({STRING_TOKEN})")


def fold_literal_string_concats(source: str) -> tuple[str, int]:
    folds = 0
    while True:
        replacements = []
        for m in STRING_CONCAT_RE.finditer(source):
            try:
                left = literal_string(m.group(1))
                right = literal_string(m.group(2))
            except ValueError:
                continue
            replacements.append((m.start(), m.end(), json.dumps(left + right, ensure_ascii=False)))
        if not replacements:
            break
        out = source
        for start, end, text in reversed(replacements):
            out = out[:start] + text + out[end:]
        source = out
        folds += len(replacements)
    return source, folds


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
    providers = discover_providers(source) if LOWER_B64 in source else []
    decoders = discover_decoders(source, providers)
    simple_arrays = discover_simple_arrays(source)
    base91_decoders = discover_rotated_base91_decoders(source, simple_arrays)
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

    for dec in base91_decoders:
        recovered = base91_call_replacements(source, dec, simple_arrays)
        replacements.extend(recovered)
        rows.append({
            "decoder": dec.name,
            "provider": dec.table_name,
            "mode": "rotated_base91",
            "offset": 0,
            "rotation": dec.rotation,
            "table_entries": len(dec.values),
            "aliases": [dec.name],
            "transform": dec.transform,
            "alphabet_sha256": hashlib.sha256(dec.alphabet.encode()).hexdigest(),
            "replacements": len(recovered),
            "status": "proven",
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
    concat_folds = 0
    if base91_decoders and filtered:
        out, concat_folds = fold_literal_string_concats(out)
    return out, {
        "schema": "js-static-string-recovery/v2",
        "safe_static_only": True,
        "changed": bool(filtered or concat_folds),
        "input_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "output_sha256": hashlib.sha256(out.encode()).hexdigest(),
        "decoders": rows,
        "replacements": len(filtered) + concat_folds,
        "decoder_call_replacements": len(filtered),
        "literal_concat_folds": concat_folds,
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
