#!/usr/bin/env python3

import re

JAVASCRIPT_SCRIPT_TYPES = {
    "",
    "module",
    "text/javascript",
    "application/javascript",
    "application/ecmascript",
    "text/ecmascript",
    "application/x-ecmascript",
    "application/x-javascript",
    "text/javascript1.0",
    "text/javascript1.1",
    "text/javascript1.2",
    "text/javascript1.3",
    "text/javascript1.4",
    "text/javascript1.5",
    "text/jscript",
    "text/livescript",
    "text/x-ecmascript",
    "text/x-javascript",
}


def normalize_script_type(value: object) -> str:
    script_type = str(value or "text/javascript").strip().lower()
    if ";" in script_type:
        script_type = script_type.split(";", 1)[0].strip()
    script_type = script_type or "text/javascript"

    # Cloudflare Rocket Loader temporarily rewrites executable script types to
    # "<hex-token>-<original-type>" while it controls execution order. Browser
    # captures can therefore contain values such as
    # "80bb470769a376240e5e4e06-text/javascript" even though the payload is
    # ordinary JavaScript. Only peel the prefix when the suffix is already a
    # known executable type so arbitrary custom MIME types remain data.
    match = re.fullmatch(r"([0-9a-f]{16,})-(.+)", script_type)
    if match and match.group(2) in JAVASCRIPT_SCRIPT_TYPES:
        return match.group(2)
    return script_type


def inline_script_kind(value: object) -> str:
    script_type = normalize_script_type(value)
    if script_type in JAVASCRIPT_SCRIPT_TYPES:
        return "javascript"
    if (
        script_type in {"importmap", "speculationrules"}
        or "json" in script_type
    ):
        return "json"
    return "text"


def inline_script_extension(value: object) -> str:
    kind = inline_script_kind(value)
    return {"javascript": "js", "json": "json", "text": "txt"}[kind]


def is_executable_script(value: object) -> bool:
    return inline_script_kind(value) == "javascript"
