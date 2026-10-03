#!/usr/bin/env python3
import argparse
import hashlib
import html
import json
import mimetypes
import re
import shutil
from pathlib import Path
from urllib.parse import quote, unquote, urljoin, urlsplit

SAVED_ORIGIN = "https://saved-page.invalid/"
SAVED_FROM_RE = re.compile(r"saved\s+from\s+url=\(\d+\)(.*?)\s*-->", re.IGNORECASE | re.DOTALL)
SOURCE_REF_RE = re.compile(r"(?:\/\/[#@]|\/\*[#@])\s*(sourceMappingURL|sourceURL)\s*=\s*([^\s*]+)")
CHARSET_RE = re.compile(r"(?:charset\s*=\s*[\"']?)([A-Za-z0-9._:-]+)", re.IGNORECASE)


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_url(rel: Path) -> str:
    return urljoin(SAVED_ORIGIN, quote(rel.as_posix(), safe="/:@-._~!$&'()*+,;="))


def kind_for(path: Path, mime: str | None = None) -> str:
    suffix = path.suffix.lower()
    base = (mime or "").split(";", 1)[0].lower()
    if suffix in {".js", ".mjs", ".cjs", ".jsx"} or "javascript" in base or "ecmascript" in base:
        return "javascript"
    if suffix in {".html", ".htm", ".xhtml"} or "html" in base:
        return "html"
    if suffix == ".css" or base == "text/css":
        return "css"
    if suffix in {".json", ".map"} or "json" in base:
        return "json"
    if suffix in {".txt", ".md", ".xml"} or base.startswith("text/"):
        return "text"
    if base.startswith("image/") or suffix in {".png", ".jpg", ".jpeg", ".gif", ".webp", ".ico", ".avif", ".svg"}:
        return "image"
    if base.startswith("font/") or suffix in {".woff", ".woff2", ".ttf", ".otf", ".eot"}:
        return "font"
    if base.startswith("audio/") or base.startswith("video/"):
        return "media"
    return "binary"


def guess_mime(path: Path) -> str:
    mime, _ = mimetypes.guess_type(path.name)
    if path.suffix.lower() == ".map":
        return "application/json"
    return mime or "application/octet-stream"


def read_text_lossless(path: Path) -> str | None:
    data = path.read_bytes()
    encodings = []
    if data.startswith(b"\xef\xbb\xbf"):
        encodings.append("utf-8-sig")
    elif data.startswith((b"\xff\xfe", b"\xfe\xff")):
        encodings.append("utf-16")

    head = data[:8192].decode("ascii", errors="ignore")
    match = CHARSET_RE.search(head)
    if match:
        encodings.append(match.group(1))
    encodings.extend(["utf-8", "windows-1252"])

    seen = set()
    for encoding in encodings:
        key = encoding.lower()
        if key in seen:
            continue
        seen.add(key)
        try:
            return data.decode(encoding)
        except (UnicodeDecodeError, LookupError):
            continue
    return None


def find_tag_end(text: str, start: int) -> int | None:
    quote_char = None
    i = start
    while i < len(text):
        ch = text[i]
        if quote_char:
            if ch == quote_char:
                quote_char = None
        elif ch in {"'", '"'}:
            quote_char = ch
        elif ch == ">":
            return i
        i += 1
    return None


def parse_attrs(tag: str) -> dict[str, str]:
    attrs: dict[str, str] = {}
    m = re.match(r"\s*<\s*[A-Za-z0-9:_-]+", tag)
    i = m.end() if m else 0
    n = len(tag)
    while i < n:
        while i < n and (tag[i].isspace() or tag[i] == "/"):
            i += 1
        if i >= n or tag[i] == ">":
            break
        start = i
        while i < n and not tag[i].isspace() and tag[i] not in "=>/":
            i += 1
        if i == start:
            i += 1
            continue
        key = tag[start:i].lower()
        while i < n and tag[i].isspace():
            i += 1
        value = ""
        if i < n and tag[i] == "=":
            i += 1
            while i < n and tag[i].isspace():
                i += 1
            if i < n and tag[i] in {"'", '"'}:
                q = tag[i]
                i += 1
                start = i
                while i < n and tag[i] != q:
                    i += 1
                value = tag[start:i]
                if i < n:
                    i += 1
            else:
                start = i
                while i < n and not tag[i].isspace() and tag[i] not in ">/":
                    i += 1
                value = tag[start:i]
        attrs[key] = html.unescape(value)
    return attrs


def extract_script_tags(text: str) -> list[dict]:
    lower = text.lower()
    out = []
    pos = 0
    while True:
        start = lower.find("<script", pos)
        if start < 0:
            break
        open_end = find_tag_end(text, start + 7)
        if open_end is None:
            break
        attrs = parse_attrs(text[start:open_end + 1])
        body_start = open_end + 1
        close_start = lower.find("</script", body_start)
        if close_start < 0:
            break
        close_end = lower.find(">", close_start)
        if close_end < 0:
            close_end = close_start + len("</script>")
        out.append({
            "attrs": attrs,
            "body": text[body_start:close_start],
            "start": start,
            "end": min(close_end + 1, len(text)),
        })
        pos = min(close_end + 1, len(text))
    return out


def clean_ref(raw: str) -> str | None:
    raw = html.unescape(raw.strip())
    if not raw or raw.startswith("#"):
        return None
    scheme = urlsplit(raw).scheme.lower()
    if scheme in {"data", "blob", "javascript", "mailto", "tel", "about"}:
        return None
    return raw.replace("\\", "/")


def ref(base: str, kind: str, raw: str) -> dict | None:
    cleaned = clean_ref(raw)
    if cleaned is None:
        return None
    return {"kind": kind, "raw": cleaned, "resolved_url": urljoin(base, cleaned)}


def html_references(text: str, base: str) -> list[dict]:
    refs = []
    for match in re.finditer(r"(?is)<(script|link|img|iframe|source|video|audio|object|embed)\b", text):
        end = find_tag_end(text, match.end())
        if end is None:
            continue
        tag_name = match.group(1).lower()
        attrs = parse_attrs(text[match.start():end + 1])
        candidates = []
        if tag_name == "script" and attrs.get("src"):
            candidates.append(("script_src", attrs["src"]))
        elif tag_name == "link" and attrs.get("href"):
            rel = attrs.get("rel", "").lower()
            as_kind = attrs.get("as", "").lower()
            if "stylesheet" in rel:
                kind = "stylesheet"
            elif "modulepreload" in rel or ("preload" in rel and as_kind == "script"):
                kind = "script_preload"
            else:
                kind = "link_href"
            candidates.append((kind, attrs["href"]))
        else:
            for attr_name in ("src", "data"):
                if attrs.get(attr_name):
                    candidates.append((f"{tag_name}_{attr_name}", attrs[attr_name]))
        if attrs.get("srcset"):
            for item in attrs["srcset"].split(","):
                url = item.strip().split()[0] if item.strip() else ""
                if url:
                    candidates.append((f"{tag_name}_srcset", url))
        for kind, raw in candidates:
            row = ref(base, kind, raw)
            if row:
                refs.append(row)
    return refs


def source_references(text: str, base: str) -> list[dict]:
    refs = []
    for kind, raw in SOURCE_REF_RE.findall(text):
        raw = raw.strip("'\";")
        row = ref(base, "source_map" if kind == "sourceMappingURL" else "source_url", raw)
        if row:
            refs.append(row)
    return refs


def infer_original_url(text: str) -> str | None:
    m = SAVED_FROM_RE.search(text)
    if not m:
        return None
    candidate = html.unescape(m.group(1).strip())
    return candidate if urlsplit(candidate).scheme in {"http", "https"} else None


def discover_assets_dir(page: Path, page_text: str) -> Path | None:
    candidates = [
        page.with_name(page.stem + "_files"),
        page.with_name(page.stem + ".files"),
        page.with_name(page.name + "_files"),
    ]

    # Browsers/locales do not all use the same companion-directory suffix.
    # Local references in the saved HTML are better evidence than guessing names.
    base = canonical_url(Path(page.name))
    for reference in html_references(page_text, base):
        raw = reference.get("raw") or ""
        parsed = urlsplit(raw)
        if parsed.scheme or parsed.netloc or raw.startswith("/"):
            continue
        parts = Path(unquote(parsed.path)).parts
        if not parts or parts[0] in {".", ".."}:
            continue
        candidates.append(page.parent / parts[0])

    seen = set()
    for candidate in candidates:
        candidate = candidate.resolve()
        if candidate in seen:
            continue
        seen.add(candidate)
        if candidate.is_dir():
            return candidate
    return None


def copy_file(src: Path, dest: Path) -> bytes:
    data = src.read_bytes()
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(data)
    return data


def main():
    ap = argparse.ArgumentParser(
        description="Normalize a browser Save Page / Webpage, Complete capture into the source-recovery project manifest"
    )
    ap.add_argument("html", type=Path)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--assets-dir", type=Path)
    ap.add_argument("--overwrite", action="store_true")
    args = ap.parse_args()

    page = args.html.resolve()
    output = args.output.resolve()
    if not page.is_file():
        raise SystemExit(f"saved page HTML does not exist: {page}")
    if output.exists():
        if not args.overwrite:
            raise SystemExit(f"output already exists: {output} (use --overwrite)")
        shutil.rmtree(output)
    output.mkdir(parents=True)

    page_text = read_text_lossless(page)
    if page_text is None:
        raise SystemExit("saved page HTML is not decodable as UTF-8")

    assets = args.assets_dir.resolve() if args.assets_dir else discover_assets_dir(page, page_text)
    if args.assets_dir and not assets.is_dir():
        raise SystemExit(f"assets directory does not exist: {assets}")

    files: list[tuple[Path, Path]] = [(page, Path("saved-page") / page.name)]
    if assets:
        for src in sorted(p for p in assets.rglob("*") if p.is_file()):
            files.append((src, Path("saved-page") / assets.name / src.relative_to(assets)))

    resources = []
    counts: dict[str, int] = {}
    rel_to_id: dict[Path, int] = {}
    for rid, (src, capture_rel) in enumerate(files):
        out_rel = Path("resources") / capture_rel
        data = copy_file(src, output / out_rel)
        mime = guess_mime(src)
        kind = kind_for(src, mime)
        base_url = canonical_url(capture_rel)
        refs = []
        text = read_text_lossless(src) if kind in {"javascript", "html", "css", "json", "text"} else None
        if kind in {"javascript", "css"} and text is not None:
            refs.extend(source_references(text, base_url))
        resources.append({
            "id": rid,
            "pageref": "saved-page",
            "started_date_time": "",
            "time_ms": 0.0,
            "method": "SAVED",
            "url": base_url,
            "status": 200,
            "status_text": "Saved locally",
            "mime_type": mime,
            "declared_size": len(data),
            "encoding": None,
            "body_present": True,
            "body_bytes": len(data),
            "sha256": sha256_hex(data),
            "kind": kind,
            "output_path": out_rel.as_posix(),
            "reused_body": False,
            "request_headers": [],
            "response_headers": [],
            "references": refs,
            "saved_source_path": str(src),
        })
        rel_to_id[capture_rel] = rid
        counts[kind] = counts.get(kind, 0) + 1

    page_rel = Path("saved-page") / page.name
    page_id = rel_to_id[page_rel]
    page_url = resources[page_id]["url"]
    page_refs = html_references(page_text, page_url)
    resources[page_id]["references"].extend(page_refs)

    # Saved-page filenames are not reliable type metadata. HTML relationships are.
    by_url = {resource["url"]: resource for resource in resources}
    for reference in page_refs:
        target = by_url.get(reference.get("resolved_url"))
        if not target:
            continue
        if reference["kind"] in {"script_src", "script_preload"}:
            target["kind"] = "javascript"
            target["mime_type"] = "application/javascript"
        elif reference["kind"] == "stylesheet":
            target["kind"] = "css"
            target["mime_type"] = "text/css"

    # Re-run sourceURL/sourceMappingURL discovery after relationship-based type promotion.
    for resource in resources:
        if resource["kind"] not in {"javascript", "css"}:
            continue
        source_path = Path(resource["saved_source_path"])
        text = read_text_lossless(source_path)
        if text is None:
            continue
        known = {
            (item.get("kind"), item.get("raw"), item.get("resolved_url"))
            for item in resource.get("references", [])
        }
        for item in source_references(text, resource["url"]):
            key = (item.get("kind"), item.get("raw"), item.get("resolved_url"))
            if key not in known:
                resource["references"].append(item)
                known.add(key)

    inline_scripts = []
    inline_seen: dict[str, str] = {}
    for ordinal, script in enumerate(extract_script_tags(page_text), 1):
        attrs = script["attrs"]
        ty = (attrs.get("type") or "text/javascript").strip().lower()
        src = clean_ref(attrs.get("src", "")) if "src" in attrs else None
        if src:
            inline_scripts.append({
                "parent_resource_id": page_id,
                "ordinal": ordinal,
                "script_type": ty,
                "src": src,
                "resolved_src": urljoin(page_url, src),
                "output_path": None,
                "body_bytes": 0,
                "sha256": None,
            })
            continue
        body = script["body"]
        if not body.strip():
            continue
        body_bytes = body.encode("utf-8")
        ext = "json" if "json" in ty else "js"
        digest = sha256_hex(body_bytes)
        desired = Path("resources") / page_rel.parent / (page_rel.name + ".inline") / f"script-{ordinal:03}.{ext}"
        out_rel = desired
        existing = inline_seen.get(out_rel.as_posix())
        if existing and existing != digest:
            out_rel = desired.with_name(f"{desired.stem}-{digest[:10]}{desired.suffix}")
        if out_rel.as_posix() not in inline_seen:
            dest = output / out_rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(body_bytes)
            inline_seen[out_rel.as_posix()] = digest
        inline_scripts.append({
            "parent_resource_id": page_id,
            "ordinal": ordinal,
            "script_type": ty,
            "src": None,
            "resolved_src": None,
            "output_path": out_rel.as_posix(),
            "body_bytes": len(body_bytes),
            "sha256": digest,
        })

    counts["resources_total"] = len(resources)
    counts["pages"] = 1
    counts["inline_scripts"] = sum(bool(s.get("output_path")) for s in inline_scripts)
    original_url = infer_original_url(page_text)
    manifest = {
        "schema": "saved-page-project/v0",
        "source_kind": "saved_page_complete" if assets else "saved_page_html",
        "source": str(page),
        "source_har": None,
        "original_page_url": original_url,
        "assets_dir": str(assets) if assets else None,
        "har_version": "",
        "salvaged": False,
        "parse_error": None,
        "pages": [{
            "id": "saved-page",
            "title": page.stem,
            "started_date_time": "",
            "original_url": original_url,
        }],
        "resources": resources,
        "inline_scripts": inline_scripts,
        "counts": counts,
    }

    rendered = json.dumps(manifest, indent=2) + "\n"
    (output / "har-manifest.json").write_text(rendered)
    (output / "capture-manifest.json").write_text(rendered)
    (output / ".vscode").mkdir(exist_ok=True)
    (output / ".vscode/settings.json").write_text(
        '{\n  "editor.maxTokenizationLineLength": 200000\n}\n'
    )
    print(
        f"saved-page capture: {len(resources)} resources, "
        f"{len(inline_scripts)} script records -> {output}"
    )
    if original_url:
        print(f"original page URL: {original_url}")
    if assets:
        print(f"complete-page assets: {assets}")


if __name__ == "__main__":
    main()
