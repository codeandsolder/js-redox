#!/usr/bin/env python3
"""Finish static string recovery after Rust's proof-gated decoder stage.

Classic javascript-obfuscator Base64/RC4 table and rotation recovery is owned by
`static-string-recover` in Rust. This temporary Python layer owns only the
remaining rotated-Base91/table/concat recovery and never executes target code.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path

IDENT = r"[A-Za-z_$][A-Za-z0-9_$]*"
NUM = r"(?:0[xX][0-9A-Fa-f]+|\d+)"
ROOT = Path(__file__).resolve().parents[1]
DEFAULT_DECODER_RECOVERER = ROOT / ".cargo-target-nodebug/debug/static-string-recover"


def match_balanced(text: str, start: int, opener: str, closer: str) -> int | None:
    if not 0 <= start < len(text) or text[start] != opener:
        return None
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


def function_body(source: str, match: re.Match[str]) -> tuple[str, int] | None:
    brace = source.find("{", match.end() - 1)
    if brace < 0:
        return None
    end = match_balanced(source, brace, "{", "}")
    if end is None:
        return None
    return source[brace + 1:end - 1], end


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


def literal_string(token: str) -> str:
    got = decode_js_string(token, 0)
    if not got or got[1] != len(token):
        raise ValueError(token)
    return got[0]


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
    declaration_start: int
    scope_start: int
    scope_end: int


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
    duplicates = set()
    for m in re.finditer(rf"\b(?:var|let|const)\s+({IDENT})\s*=\s*\[", source):
        name = m.group(1)
        start = source.find("[", m.start(), m.end() + 1)
        if start < 0:
            continue
        parsed = parse_simple_array(source, start)
        if parsed is None:
            continue
        values, _ = parsed
        if name in arrays:
            duplicates.add(name)
        else:
            arrays[name] = values
    for name in duplicates:
        arrays.pop(name, None)
    return arrays



def enclosing_function_scope(
    spans: list[tuple[int, int, str]], pos: int
) -> tuple[int, int] | None:
    containers = [(start, end) for start, end, _ in spans if start < pos < end]
    return min(containers, key=lambda span: span[1] - span[0]) if containers else None


def scope_bounds(scope: tuple[int, int] | None, source_len: int) -> tuple[int, int]:
    return scope if scope is not None else (0, source_len)


def scope_strictly_contains(
    outer: tuple[int, int] | None,
    inner: tuple[int, int] | None,
    source_len: int,
) -> bool:
    outer_start, outer_end = scope_bounds(outer, source_len)
    if inner is None:
        return False
    return outer_start < inner[0] and inner[1] < outer_end


def scope_parent(
    spans: list[tuple[int, int, str]],
    scope: tuple[int, int],
) -> tuple[int, int] | None:
    parents = [
        (start, end)
        for start, end, _ in spans
        if start < scope[0] and end > scope[1]
    ]
    return min(parents, key=lambda span: span[1] - span[0]) if parents else None


def scope_params(
    spans: list[tuple[int, int, str]], scope: tuple[int, int] | None
) -> list[str]:
    if scope is None:
        return []
    for start, end, params in spans:
        if (start, end) == scope:
            return [
                p.strip().lstrip("...").strip()
                for p in params.split(",")
                if p.strip()
            ]
    return []


def scope_directly_declares(
    source: str,
    spans: list[tuple[int, int, str]],
    scope: tuple[int, int] | None,
    name: str,
) -> bool:
    if name in scope_params(spans, scope):
        return True
    patterns = (
        rf"\bfunction\s+{re.escape(name)}\s*\(",
        rf"\b(?:var|let|const)\s+{re.escape(name)}\b",
    )
    for pattern in patterns:
        for match in re.finditer(pattern, source):
            if enclosing_function_scope(spans, match.start()) == scope:
                return True
    return False


def scope_chain_shadows(
    source: str,
    spans: list[tuple[int, int, str]],
    inner: tuple[int, int],
    outer: tuple[int, int] | None,
    name: str,
) -> bool:
    scope: tuple[int, int] | None = inner
    while scope != outer:
        if scope_directly_declares(source, spans, scope, name):
            return True
        if scope is None:
            return True
        scope = scope_parent(spans, scope)
    return False


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


BASE91_SIGNATURE = (
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


def base91_signature_matches(text: str) -> bool:
    compact = re.sub(r"\s+", "", text)
    return all(fragment in compact for fragment in BASE91_SIGNATURE)


def substitute_affine_array_state(
    text: str,
    array_name: str,
    state_name: str,
    base: int,
    values: list[object],
) -> str:
    pattern = re.compile(
        rf"\b{re.escape(array_name)}\s*\[\s*{re.escape(state_name)}"
        rf"\s*(?:([+-])\s*({NUM}))?\s*\]"
    )

    def repl(match: re.Match[str]) -> str:
        offset = 0
        if match.group(2):
            offset = int(match.group(2), 0)
            if match.group(1) == "-":
                offset = -offset
        index = base + offset
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


AFFINE_REF_TEXT = (
    rf"{IDENT}\s*\[\s*{IDENT}"
    rf"\s*(?:[+-]\s*{NUM})?\s*\]"
)
AFFINE_REF_RE = re.compile(
    rf"\b({IDENT})\s*\[\s*({IDENT})"
    rf"\s*(?:([+-])\s*({NUM}))?\s*\]"
)


def parse_affine_ref(text: str):
    match = AFFINE_REF_RE.fullmatch(text.strip())
    if not match:
        return None
    offset = 0
    if match.group(4):
        offset = int(match.group(4), 0)
        if match.group(3) == "-":
            offset = -offset
    return match.group(1), match.group(2), offset


def semantic_affine_base91_signature_matches(
    window: str, simple_arrays: dict[str, list[object]]
) -> bool:
    """Resolve flattened Base91 constants from their exact semantic positions."""
    normalized = re.sub(r"\+\s*-\s*(?=(?:0[xX][0-9A-Fa-f]+|\d+))", "-", window)
    normalized = re.sub(r"-\s*-\s*(?=(?:0[xX][0-9A-Fa-f]+|\d+))", "+", normalized)
    partial = substitute_simple_array_literals(normalized, simple_arrays)
    constraints: dict[tuple[str, str], set[int]] = {}

    def constrain(ref_text: str, expected: int) -> bool:
        parsed = parse_affine_ref(ref_text)
        if parsed is None:
            return False
        array_name, state_name, offset = parsed
        values = simple_arrays.get(array_name)
        if values is None:
            return False
        candidates = {
            index - offset
            for index, value in enumerate(values)
            if value == expected
        }
        if not candidates:
            return False
        key = (array_name, state_name)
        if key in constraints:
            candidates &= constraints[key]
        if not candidates:
            return False
        constraints[key] = candidates
        return True

    conditional = re.search(
        rf"&\s*({AFFINE_REF_TEXT})\s*\)\s*>\s*88\s*"
        rf"\?\s*({AFFINE_REF_TEXT})\s*:\s*14",
        partial,
    )
    if conditional:
        if not constrain(conditional.group(1), 8191):
            return False
        if not constrain(conditional.group(2), 13):
            return False

    for match in re.finditer(
        rf"\.push\s*\([^()]*&\s*({AFFINE_REF_TEXT})\s*\)",
        partial,
    ):
        if not constrain(match.group(1), 255):
            return False

    for match in re.finditer(rf">>=\s*({AFFINE_REF_TEXT})", partial):
        if not constrain(match.group(1), 8):
            return False

    for match in re.finditer(
        rf"while\s*\([^)]*>\s*({AFFINE_REF_TEXT})\s*\)",
        partial,
    ):
        if not constrain(match.group(1), 7):
            return False

    if not constraints or any(len(candidates) != 1 for candidates in constraints.values()):
        return False

    resolved = normalized
    for (array_name, state_name), candidates in constraints.items():
        base = next(iter(candidates))
        resolved = substitute_affine_array_state(
            resolved,
            array_name,
            state_name,
            base,
            simple_arrays[array_name],
        )
    resolved = substitute_simple_array_literals(resolved, simple_arrays)
    return base91_signature_matches(resolved)


def affine_base91_signature_matches(
    body: str, simple_arrays: dict[str, list[object]]
) -> bool:
    # A flattened decoder may replace Base91 constants with ARRAY[state+offset]
    # lookups. Prove a local core only if one and only one state value makes the
    # complete exact Base91 signature hold.
    for index_match in re.finditer(r"\.indexOf\s*\(", body):
        start = max(0, index_match.start() - 900)
        end = min(len(body), index_match.start() + 1800)
        window = body[start:end]
        if semantic_affine_base91_signature_matches(window, simple_arrays):
            return True

        for array_name, values in simple_arrays.items():
            affine = re.compile(
                rf"\b{re.escape(array_name)}\s*\[\s*({IDENT})"
                rf"\s*(?:([+-])\s*({NUM}))?\s*\]"
            )
            by_state: dict[str, list[int]] = {}
            for match in affine.finditer(window):
                offset = 0
                if match.group(3):
                    offset = int(match.group(3), 0)
                    if match.group(2) == "-":
                        offset = -offset
                by_state.setdefault(match.group(1), []).append(offset)

            for state_name, offsets in by_state.items():
                if len(offsets) < 4:
                    continue
                # Every lookup participating in this local core must stay in
                # bounds under the same state value.
                low = max(-offset for offset in offsets)
                high = min(len(values) - 1 - offset for offset in offsets)
                if low > high or high - low > len(values) * 2:
                    continue

                matches = []
                for base in range(low, high + 1):
                    resolved = substitute_affine_array_state(
                        window, array_name, state_name, base, values
                    )
                    resolved = substitute_simple_array_literals(
                        resolved, simple_arrays
                    )
                    if base91_signature_matches(resolved):
                        matches.append(base)
                        if len(matches) > 1:
                            break
                if len(matches) == 1:
                    return True
    return False


def looks_like_base91_decoder(
    body: str, alphabet: str, simple_arrays: dict[str, list[object]]
) -> bool:
    if len(alphabet) != 91 or len(set(alphabet)) != 91:
        return False
    resolved = substitute_simple_array_literals(body, simple_arrays)
    if base91_signature_matches(resolved):
        return True
    return affine_base91_signature_matches(body, simple_arrays)


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

        rotated = values[rotation:] + values[:rotation]
        for dm in re.finditer(rf"\bfunction\s+({IDENT})\s*\(([^)]*)\)\s*\{{", source):
            decoder_scope = enclosing_function_scope(spans, dm.start())
            same_scope = decoder_scope == table_scope
            nested_scope = (
                decoder_scope is not None
                and scope_strictly_contains(table_scope, decoder_scope, len(source))
            )
            if same_scope:
                # The root helper scaffold is hoisted before the table is built.
                # A same-scope decoder appearing after initialization may instead
                # be an unrelated class/method-local function our lightweight
                # function-scope index cannot see.
                if dm.start() >= m.start():
                    continue
            elif nested_scope:
                # Nested handler helpers may be declared later in source order,
                # but only after the shared table has been initialized and only
                # while the binding resolves lexically to that proven table.
                if decoder_scope[0] <= array_end:
                    continue
                if scope_chain_shadows(
                    source, spans, decoder_scope, table_scope, table_name
                ):
                    continue
            else:
                continue

            decoder_name = dm.group(1)
            got = function_body(source, dm)
            if not got:
                continue
            decoder_body, _ = got
            # The compact wrapper must directly feed an indexed entry from the
            # proven rotated table into a named transform and cache/return it.
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
                    if enclosing_function_scope(spans, found[1]) == decoder_scope
                    and found[1] < dm.start()
                ),
                None,
            )
            if not transform_fn:
                continue
            transform_body = transform_fn[0]
            transform_scope = (transform_fn[1], transform_fn[2])

            # Proof constants are lexical bindings, not file-global names.
            # Drop any literal-array name shadowed by the transform's own
            # parameters/locals or by an intervening decoder scope.
            proof_arrays = {}
            for array_name, array_values in simple_arrays.items():
                if scope_directly_declares(
                    source, spans, transform_scope, array_name
                ):
                    continue
                if decoder_scope is not None and scope_chain_shadows(
                    source, spans, decoder_scope, table_scope, array_name
                ):
                    continue
                proof_arrays[array_name] = array_values

            alphabets = [s for s in string_literals(transform_body) if len(s) == 91]
            alphabet = next(
                (
                    candidate
                    for candidate in alphabets
                    if looks_like_base91_decoder(
                        transform_body, candidate, proof_arrays
                    )
                ),
                None,
            )
            if alphabet is None:
                continue
            scope_start, scope_end = scope_bounds(decoder_scope, len(source))
            out.append(
                Base91Decoder(
                    name=decoder_name,
                    table_name=table_name,
                    values=rotated,
                    rotation=rotation,
                    alphabet=alphabet,
                    transform=transform,
                    declaration_start=dm.start(),
                    scope_start=scope_start,
                    scope_end=scope_end,
                )
            )
    unique = {}
    for decoder in out:
        unique[
            (
                decoder.declaration_start,
                decoder.name,
                decoder.table_name,
                decoder.scope_start,
                decoder.scope_end,
            )
        ] = decoder
    return list(unique.values())


def function_spans(source: str):
    spans = []

    def add_span(match: re.Match[str], params: str) -> None:
        brace = source.find("{", match.end() - 1)
        if brace < 0:
            return
        end = match_balanced(source, brace, "{", "}")
        if end is not None:
            spans.append((match.start(), end, params))

    for m in re.finditer(rf"\bfunction(?:\s+{IDENT})?\s*\(([^)]*)\)\s*\{{", source):
        add_span(m, m.group(1))

    # Constructors are lexical function scopes for nested helper declarations.
    for m in re.finditer(r"\bconstructor\s*\(([^)]*)\)\s*\{", source):
        add_span(m, m.group(1))

    # Recovered class/object methods are often emitted with literal computed
    # names, e.g. ["run"]() { ... } or async ["runAsync"]() { ... }. This
    # syntax is unambiguous with ordinary calls/control statements and gives
    # nested decoder helpers their correct lexical visibility.
    quoted_method = re.compile(
        r"(?:\basync\s+)?\[\s*"
        r"(?:'(?:\\.|[^'\\])*'|\"(?:\\.|[^\"\\])*\")"
        r"\s*\]\s*\(([^)]*)\)\s*\{"
    )
    for m in quoted_method.finditer(source):
        add_span(m, m.group(1))

    # Generated block arrows usually have flat parameters. Complex/default or
    # destructured arrow parameters are deliberately left unmodeled.
    arrow = re.compile(rf"(?:\(([^()]*?)\)|({IDENT}))\s*=>\s*\{{")
    for m in arrow.finditer(source):
        params = m.group(1) if m.group(1) is not None else m.group(2)
        add_span(m, params or "")

    spans.sort(key=lambda span: (span[0], span[1]))
    return spans


def shadowed_scopes(
    source: str,
    name: str,
    primary_start: int,
    scope_start: int,
    scope_end: int,
) -> list[tuple[int, int]]:
    """Return only lexical descendants that shadow this specific decoder."""
    spans = function_spans(source)
    primary_scope = (scope_start, scope_end)
    shadows = []

    def proper_descendant(scope: tuple[int, int]) -> bool:
        return (
            scope != primary_scope
            and scope_start <= scope[0]
            and scope[1] <= scope_end
        )

    # A parameter shadows through exactly its own function-like scope.
    for start, end, params in spans:
        scope = (start, end)
        if not proper_descendant(scope):
            continue
        param_names = [
            p.strip().lstrip("...").strip()
            for p in params.split(",")
            if p.strip()
        ]
        if name in param_names:
            shadows.append(scope)

    declaration_positions = [
        m.start()
        for m in re.finditer(rf"\bfunction\s+{re.escape(name)}\s*\(", source)
        if m.start() != primary_start
        and scope_start <= m.start() < scope_end
    ]
    declaration_positions.extend(
        m.start()
        for m in re.finditer(
            rf"\b(?:var|let|const)\s+{re.escape(name)}\b", source
        )
        if scope_start <= m.start() < scope_end
    )

    for pos in declaration_positions:
        scope = enclosing_function_scope(spans, pos)
        decl_scope = scope_bounds(scope, len(source))
        if decl_scope == primary_scope:
            # Another declaration in the same lexical scope makes name
            # resolution ambiguous. Fail this decoder closed.
            return [primary_scope]
        if proper_descendant(decl_scope):
            shadows.append(decl_scope)

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
    excluded = shadowed_scopes(
        source,
        decoder.name,
        decoder.declaration_start,
        decoder.scope_start,
        decoder.scope_end,
    )
    replacements = []
    seen = set()

    direct = re.compile(rf"\b{re.escape(decoder.name)}\s*\(\s*({NUM})\s*\)")
    for m in direct.finditer(source, decoder.scope_start, decoder.scope_end):
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
    for m in indirect.finditer(source, decoder.scope_start, decoder.scope_end):
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


def immutable_literal_string_arrays(
    source: str, simple_arrays: dict[str, list[object]]
) -> dict[str, list[object]]:
    """Return const literal arrays proven read-only by conservative text use."""
    out = {}
    for name, values in simple_arrays.items():
        decls = list(
            re.finditer(
                rf"\bconst\s+({re.escape(name)})\s*=\s*\[",
                source,
            )
        )
        if len(decls) != 1:
            continue
        declaration_name_start = decls[0].start(1)
        safe = True
        for match in re.finditer(rf"\b{re.escape(name)}\b", source):
            if match.start() == declaration_name_start:
                continue
            cursor = match.end()
            while cursor < len(source) and source[cursor].isspace():
                cursor += 1
            # Bare references can escape/alias the array. Only bracketed reads
            # are allowed; the index itself may be dynamic.
            if cursor >= len(source) or source[cursor] != "[":
                safe = False
                break
            read_end = match_balanced(source, cursor, "[", "]")
            if read_end is None:
                safe = False
                break
            suffix = source[read_end:read_end + 32].lstrip()
            if (
                suffix.startswith("++")
                or suffix.startswith("--")
                or suffix.startswith("(")
                or suffix.startswith("?.(")
                or re.match(
                    r"(?:\?\.|\.)\s*(?:call|apply|bind)\s*\(",
                    suffix,
                )
                or (
                    suffix.startswith("=")
                    and not suffix.startswith(("==", "=>"))
                )
                or re.match(
                    r"(?:\*\*=|>>>=|<<=|>>=|&&=|\|\|=|\?\?=|[+\-*/%&|^]=)",
                    suffix,
                )
            ):
                safe = False
                break
            prefix = source[max(0, match.start() - 12):match.start()].rstrip()
            if prefix.endswith(("++", "--")) or re.search(r"\bdelete\s*$", prefix):
                safe = False
                break
        if safe:
            out[name] = values
    return out


def replace_immutable_string_table_reads(
    source: str, arrays: dict[str, list[object]]
) -> tuple[str, int]:
    replacements = []
    for name, values in arrays.items():
        pattern = re.compile(rf"\b{re.escape(name)}\s*\[\s*({NUM})\s*\]")
        for match in pattern.finditer(source):
            index = int(match.group(1), 0)
            if not 0 <= index < len(values):
                continue
            value = values[index]
            if not isinstance(value, str):
                continue
            replacements.append(
                (match.start(), match.end(), json.dumps(value, ensure_ascii=False))
            )
    out = source
    for start, end, text in reversed(replacements):
        out = out[:start] + text + out[end:]
    return out, len(replacements)


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


def filter_nonoverlapping_replacements(
    replacements: list[tuple[int, int, str, str]],
) -> list[tuple[int, int, str, str]]:
    replacements.sort(key=lambda row: (row[0], row[1]))
    filtered = []
    end = -1
    for row in replacements:
        if row[0] < end:
            continue
        filtered.append(row)
        end = row[1]
    return filtered


def apply_text_replacements(
    source: str, replacements: list[tuple[int, int, str, str]]
) -> str:
    out = source
    for start, stop, text, _ in reversed(replacements):
        out = out[:start] + text + out[stop:]
    return out


def recover_base91_pass(
    source: str, iteration: int
) -> tuple[str, list[dict], dict[str, int]]:
    # Every Base91 decoder accepted below must expose its exact 91-character,
    # 91-unique-symbol alphabet as a quoted string literal. Ordinary large app
    # bundles almost never do. Gate the expensive global array/scope discovery
    # on that necessary condition so non-Base91 inputs stay linear-time.
    if not any(len(value) == 91 and len(set(value)) == 91 for value in string_literals(source)):
        return source, [], {
            "preflight_skipped": True,
            "decoder_calls": 0,
            "immutable_string_table_replacements": 0,
            "literal_concat_folds": 0,
        }

    simple_arrays = discover_simple_arrays(source)
    immutable_string_arrays = immutable_literal_string_arrays(source, simple_arrays)
    decoders = discover_rotated_base91_decoders(source, simple_arrays)
    replacements: list[tuple[int, int, str, str]] = []
    rows = []
    for dec in decoders:
        recovered = base91_call_replacements(source, dec, simple_arrays)
        replacements.extend(recovered)
        if recovered or iteration == 1:
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
                "declaration_start": dec.declaration_start,
                "scope_start": dec.scope_start,
                "scope_end": dec.scope_end,
                "replacements": len(recovered),
                "iteration": iteration,
                "status": "proven",
            })

    filtered = filter_nonoverlapping_replacements(replacements)
    out = apply_text_replacements(source, filtered)
    immutable_table_reads = 0
    concat_folds = 0
    if decoders and filtered:
        out, immutable_table_reads = replace_immutable_string_table_reads(
            out, immutable_string_arrays
        )
        out, concat_folds = fold_literal_string_concats(out)
    return out, rows, {
        "preflight_skipped": False,
        "decoder_calls": len(filtered),
        "immutable_string_table_replacements": immutable_table_reads,
        "literal_concat_folds": concat_folds,
    }


def recover_base91(
    source: str, original: bytes, classic_report: dict
) -> tuple[str, dict]:
    rows = []
    decoder_call_replacements = int(
        classic_report.get("transforms", {}).get("string_array_decode", 0)
    )
    immutable_table_reads = 0
    concat_folds = 0
    base91_iterations = []
    out = source

    for iteration in range(1, 5):
        recovered_out, iteration_rows, stats = recover_base91_pass(out, iteration)
        rows.extend(iteration_rows)
        base91_iterations.append({
            "iteration": iteration,
            **stats,
        })
        decoder_call_replacements += stats["decoder_calls"]
        immutable_table_reads += stats["immutable_string_table_replacements"]
        concat_folds += stats["literal_concat_folds"]
        if recovered_out == out:
            break
        out = recovered_out

    total_replacements = (
        decoder_call_replacements + immutable_table_reads + concat_folds
    )
    return out, {
        "schema": "js-static-string-recovery/v4",
        "safe_static_only": True,
        "changed": out.encode("utf-8") != original,
        "input_sha256": hashlib.sha256(original).hexdigest(),
        "output_sha256": hashlib.sha256(out.encode("utf-8")).hexdigest(),
        "classic_decoder_recovery": classic_report,
        "decoders": rows,
        "replacements": total_replacements,
        "decoder_call_replacements": decoder_call_replacements,
        "immutable_string_table_replacements": immutable_table_reads,
        "literal_concat_folds": concat_folds,
        "base91_iterations": base91_iterations,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("input", type=Path)
    ap.add_argument("output", type=Path)
    ap.add_argument("--report", type=Path)
    ap.add_argument("--decoder-recoverer", type=Path, default=DEFAULT_DECODER_RECOVERER)
    args = ap.parse_args()
    raw = args.input.read_bytes()
    raw_sha = hashlib.sha256(raw).hexdigest()

    decoder_recoverer = args.decoder_recoverer
    fallback = ROOT / "target/debug/static-string-recover"
    if decoder_recoverer == DEFAULT_DECODER_RECOVERER and not decoder_recoverer.is_file() and fallback.is_file():
        decoder_recoverer = fallback

    with tempfile.TemporaryDirectory(prefix="js-redox-string-recovery-") as td:
        td = Path(td)
        classic_out = td / "classic.js"
        classic_report_path = td / "classic.json"
        cp = subprocess.run(
            [
                str(decoder_recoverer),
                str(args.input),
                str(classic_out),
                "--report",
                str(classic_report_path),
            ],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if cp.returncode:
            raise SystemExit(
                f"Rust static decoder recovery failed ({cp.returncode}): "
                f"{cp.stdout}{cp.stderr}"
            )
        classic_report = json.loads(classic_report_path.read_text())
        classic_bytes = classic_out.read_bytes()
        classic_sha = hashlib.sha256(classic_bytes).hexdigest()
        if (
            classic_report.get("schema") != "js-static-decoder-recovery/v1"
            or not classic_report.get("safe_static_only")
            or classic_report.get("input_sha256") != raw_sha
            or classic_report.get("output_sha256") != classic_sha
        ):
            raise SystemExit("Rust static decoder recovery provenance validation failed")
        source = classic_bytes.decode("utf-8")
        out, report = recover_base91(source, raw, classic_report)

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(out.encode("utf-8"))
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
