#!/usr/bin/env python3

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
    return script_type or "text/javascript"


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
