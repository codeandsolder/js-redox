#!/usr/bin/env python3
"""Use free inference as a discovery oracle over deterministic zero-residual JavaScript."""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import sqlite3
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CORPUS = ROOT / "work/scum-corpus-20261007"
DEFAULT_DB = DEFAULT_CORPUS / "preclass/corpus.sqlite"
DEFAULT_CANDIDATES = DEFAULT_CORPUS / "preclass/candidates"
DEFAULT_DEOB = ROOT / ".cargo-target-nodebug/debug/deobfuscate-safe"
DEFAULT_STDIO = Path("/home/jan/projects/inference-redox/target/debug/inference-redox-stdio")
REVIEW_CONTRACT = "js-zero-llm-review/v2"
ALLOWED_CATEGORIES = frozenset({
    "hidden_string_decoder",
    "encoded_semantic_payload",
    "control_flow_flattening",
    "protection_virtual_machine",
    "runtime_code_generation",
    "operator_or_call_proxy",
    "opaque_arithmetic_or_predicate",
    "anti_analysis_scaffolding",
    "hidden_wasm_semantics",
    "reflective_property_indirection",
    "concealed_environment_probe",
    "residual_alias_or_wrapper",
    "other_readability_reduction",
})
SYSTEM = """You are an adversarial JavaScript deobfuscation reviewer helping improve js-redox.

The supplied program has already passed through our conservative deobfuscation pipeline, and our current deterministic residual scanner reports zero actionable residuals. That only means our current detectors found nothing they know how to classify.

Your job is to find structures that appear to have been introduced primarily to reduce human readability or to obscure otherwise straightforward program semantics. Focus on concrete structure in the source. Do not guess from company names, site names, library names, or protector brands.

Everything is mechanically recoverable in principle; do not treat "recoverability" as a useful distinction. A useful finding is instead: "this code contains an extra structure that plausibly exists mainly to make the underlying semantics harder for a human to see, and here is the simpler semantics it seems to conceal."

Use ONLY these exact category labels:
- hidden_string_decoder
- encoded_semantic_payload
- control_flow_flattening
- protection_virtual_machine
- runtime_code_generation
- operator_or_call_proxy
- opaque_arithmetic_or_predicate
- anti_analysis_scaffolding
- hidden_wasm_semantics
- reflective_property_indirection
- concealed_environment_probe
- residual_alias_or_wrapper
- other_readability_reduction

Category definitions and decision rules:

hidden_string_decoder
Flag indirect recovery of strings or property names through tables, integer/affine indices, table rotation, custom alphabets, base64/XOR/RC4-like decoding, stable decoder aliases, or wrappers around those mechanisms. Strong evidence is a table plus repeated decoder-style access whose outputs replace direct literals/property names. Do NOT flag localization/config tables, webpack module tables, enum maps, parser tables, or ordinary application lookup tables.

encoded_semantic_payload
Flag encoded, packed, compressed, encrypted, escaped, or byte-array material when it is decoded into semantically important program material such as executable source, hidden configuration, bytecode, dispatch tables, another decoder, or WebAssembly. Do NOT flag ordinary assets, hashes, certificates, protocol payloads, fonts/images, or data merely because it is encoded.

control_flow_flattening
Flag an artificial dispatcher/state variable/order table/loop+switch/if-ladder whose apparent purpose is replacing straightforward local control flow. The important distinction is whether the state represents real domain state. Do NOT flag genuine parsers, protocol state machines, workflow/UI/game state, reducers, interpreters, or other real stateful algorithms.

protection_virtual_machine
Flag an opaque instruction stream plus a generic interpreter/register/stack/opcode engine when the apparent purpose is concealing ordinary program logic. Do NOT flag real language runtimes, emulators, template engines, regex engines, product scripting VMs, or expression evaluators merely for being interpreters.

runtime_code_generation
Flag important semantics that are assembled as source/bytecode/module data and then executed or compiled at runtime: Function/eval-like construction, generated modules, script/blob URLs, reconstructed executable source, etc. Follow data flow into the execution boundary. Do NOT flag ordinary templates, editors, query construction, JSON parsing, or normal dynamic import selection.

operator_or_call_proxy
Flag helper functions or tables that mechanically replace direct operators, calls, constructors, or property access and whose main effect appears to be hiding simple syntax. Examples: wrappers equivalent to a+b, a===b, f(x), new C(x), obj[k]. Do NOT flag legitimate adapters, callbacks, event emitters, DI, framework hooks, memoizers, decorators, or compatibility layers.

opaque_arithmetic_or_predicate
Flag deliberately inflated arithmetic/boolean expressions, algebraically cancelling terms, hidden constants, or predicates that are provably invariant and appear to exist to obscure simpler values/control flow. Do NOT flag cryptography, hashes, compression, codecs, DSP, binary protocols, PRNGs, bitsets, or performance-oriented integer tricks.

anti_analysis_scaffolding
Flag structures whose apparent purpose is making source inspection or modification harder: debugger traps, devtools timing checks, source-format sensitivity, function-to-string integrity checks, regexes over serialized function bodies, console sabotage, source-text checksums, anti-hook/instrumentation checks, or deliberate failure after source modification. Do NOT flag ordinary assertions, feature detection, performance measurement, CSP handling, or downloaded-resource integrity checks.

hidden_wasm_semantics
Assume ordinary captured/recovered WebAssembly is separately decompiled by the pipeline. Flag only when Wasm semantics are themselves hidden by an extra readability-reduction layer: encoded/reconstructed module bytes, protection VMs implemented in Wasm, opaque JS/Wasm glue deliberately concealing behavior, or similar. Ordinary Wasm use, wasm-bindgen/Emscripten glue, codecs, games, ML/crypto kernels, and normal .wasm fetching are not matches.

reflective_property_indirection
Flag pervasive Reflect/Proxy/descriptor/dynamic-property machinery that appears primarily to replace direct language operations with indirection. Do NOT flag legitimate reactive frameworks, membranes, RPC proxies, sandboxes, instrumentation, observability, or compatibility layers.

concealed_environment_probe
Browser/environment/fingerprint/challenge logic is NOT suspicious by itself. Use this label only when the actual probing semantics are hidden behind another readability-reduction structure such as decoded property names, flattened dispatch, opaque arithmetic, generated calls, or proxy wrappers.

residual_alias_or_wrapper
Flag stable aliases, forwarding wrappers, one-shot initialization wrappers/IIFEs, stale decoder bootstrap scaffolding, or other layers that remain only to hide a simpler stable binding/expression. Do NOT flag ordinary module scoping, closures, lazy initialization, or lifecycle wrappers.

other_readability_reduction
Use only for a concrete repeated structure whose apparent purpose is reducing readability but does not fit another label. Never use this as a generic "weird code" bucket.

False-positive discipline:
- Minification is not obfuscation.
- Generated code is not automatically obfuscation.
- Numeric webpack/module IDs are not decoder calls.
- Computed indexing is ubiquitous.
- Large tables can be ordinary domain data.
- Bitwise-heavy code can be a real algorithm.
- A switch loop can be a real state machine.
- WebAssembly is not suspicious by itself.
- Fingerprinting, anti-bot, advertising, analytics, DRM, security logic, and challenge code are behavioral categories, not proof of readability reduction.
- Framework internals are often indirect by design.
- Complex code may genuinely implement a complex algorithm.

For each apparent match, explicitly state the strongest ordinary/benign structural explanation and lower confidence unless the source gives evidence against it.

Return ONLY one JSON object with exactly these top-level keys:
{
  "verdict": "suspicious" | "clean" | "uncertain",
  "confidence": 0.0,
  "matches": [
    {
      "category": "one_exact_label_from_above",
      "confidence": 0.0,
      "evidence": ["short concrete observations from the source"],
      "simpler_semantics": "the more direct/readable semantics this structure appears to conceal",
      "benign_alternative": "strongest plausible ordinary explanation, or empty string",
      "detector_idea": "brief structural idea for a deterministic detector or transform"
    }
  ],
  "checked_clean": ["exact category labels considered and rejected"],
  "note": "brief overall assessment and any limitation caused by missing/truncated context"
}

If verdict is clean, matches must be empty. If verdict is uncertain, explain what additional local evidence would distinguish deliberate readability reduction from ordinary code. Do not invent new category names."""


def utc_now() -> str:
    return dt.datetime.now(dt.UTC).isoformat(timespec="microseconds")


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def ensure_schema(db: sqlite3.Connection) -> None:
    db.executescript("""
        CREATE TABLE IF NOT EXISTS body_llm_review (
          sha256 TEXT NOT NULL,
          review_contract TEXT NOT NULL,
          deterministic_pipeline_id TEXT NOT NULL,
          reviewed_at TEXT NOT NULL,
          transformed_sha256 TEXT NOT NULL,
          model TEXT,
          provider TEXT,
          verdict TEXT NOT NULL,
          confidence REAL NOT NULL,
          categories_json TEXT NOT NULL,
          note TEXT NOT NULL,
          response_json TEXT NOT NULL,
          PRIMARY KEY (sha256, review_contract, deterministic_pipeline_id, transformed_sha256, model, provider)
        );
        CREATE INDEX IF NOT EXISTS llm_review_verdict_idx
          ON body_llm_review(review_contract, verdict, confidence);
    """)


def decode_json_object(text: str) -> dict:
    text = text.strip()
    if text.startswith("```"):
        lines = text.splitlines()
        if lines and lines[0].startswith("```"):
            lines = lines[1:]
        if lines and lines[-1].strip() == "```":
            lines = lines[:-1]
        text = "\n".join(lines).strip()
    try:
        value = json.loads(text)
    except json.JSONDecodeError:
        start = text.find("{")
        end = text.rfind("}")
        if start < 0 or end <= start:
            raise
        value = json.loads(text[start:end + 1])
    if not isinstance(value, dict):
        raise ValueError("LLM review is not a JSON object")
    return value


def validate_review(value: dict) -> tuple[str, float, list[str], str]:
    verdict = str(value.get("verdict") or "").lower()
    if verdict not in {"suspicious", "clean", "uncertain"}:
        raise ValueError(f"invalid verdict: {verdict!r}")
    confidence = float(value.get("confidence"))
    if not 0.0 <= confidence <= 1.0:
        raise ValueError(f"invalid confidence: {confidence}")
    matches = value.get("matches")
    if not isinstance(matches, list):
        raise ValueError("matches must be a list")
    categories: list[str] = []
    for index, match in enumerate(matches):
        if not isinstance(match, dict):
            raise ValueError(f"matches[{index}] must be an object")
        category = match.get("category")
        if category not in ALLOWED_CATEGORIES:
            raise ValueError(f"matches[{index}] has unknown category: {category!r}")
        categories.append(category)
        match_confidence = float(match.get("confidence"))
        if not 0.0 <= match_confidence <= 1.0:
            raise ValueError(f"matches[{index}] has invalid confidence: {match_confidence}")
        evidence = match.get("evidence")
        if not isinstance(evidence, list) or not all(isinstance(item, str) for item in evidence):
            raise ValueError(f"matches[{index}].evidence must be a list of strings")
    if verdict == "clean" and matches:
        raise ValueError("clean verdict must not contain matches")
    if verdict == "suspicious" and not matches:
        raise ValueError("suspicious verdict must contain at least one match")
    checked_clean = value.get("checked_clean")
    if not isinstance(checked_clean, list) or not all(item in ALLOWED_CATEGORIES for item in checked_clean):
        raise ValueError("checked_clean must contain only exact canonical category labels")
    note = str(value.get("note") or "")[:4000]
    return verdict, confidence, sorted(set(categories)), note


class StdioClient:
    def __init__(self, binary: Path, env_file: Path):
        self.proc = subprocess.Popen(
            [str(binary), "--env-file", str(env_file)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )
        self.serial = 0

    def close(self) -> None:
        if self.proc.stdin:
            self.proc.stdin.close()
        try:
            self.proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            self.proc.terminate()
            self.proc.wait(timeout=5)

    def call(self, payload: dict) -> dict:
        self.serial += 1
        request_id = f"js-review-{self.serial}"
        payload = {"id": request_id, **payload}
        if not self.proc.stdin or not self.proc.stdout:
            raise RuntimeError("inference-redox stdio unavailable")
        self.proc.stdin.write(json.dumps(payload, separators=(",", ":")) + "\n")
        self.proc.stdin.flush()
        line = self.proc.stdout.readline()
        if not line:
            stderr = self.proc.stderr.read() if self.proc.stderr else ""
            raise RuntimeError(f"inference-redox exited early: {stderr[-4000:]}")
        response = json.loads(line)
        if response.get("id") != request_id:
            raise RuntimeError(f"unexpected response id: {response.get('id')!r}")
        if not response.get("ok"):
            raise RuntimeError(str(response.get("error") or "inference error"))
        return response["result"]


def request_template(prompt: str, expected_output_tokens: int) -> dict:
    return {
        "system_prompt": SYSTEM,
        "prompt": prompt,
        "expected_output_tokens": expected_output_tokens,
        "max_output_tokens": expected_output_tokens,
        "temperature": 0.0,
        "include_reasoning": False,
        "agentic": False,
        "requirements": {
            "allowed_route_classes": ["free"],
            "response_schema": None,
            "reasoning": "none",
            "reasoning_max_tokens": None,
            "require_verified_reasoning": False,
            "required_parameters": [],
            "minimum_uptime_30m": None,
        },
    }


def review_source(client: StdioClient, source: str, expected_output_tokens: int) -> tuple[dict, dict]:
    prompt = "Review this JavaScript for residual structures introduced to reduce readability or conceal straightforward semantics.\n\n```javascript\n" + source + "\n```"
    template = request_template(prompt, expected_output_tokens)
    plan = client.call(
        {
            "op": "select_pool_quota",
            "suitability": {},
            "request_template": template,
            "selection": {
                "unknown_suitability": "allow",
                "discovery_limit": 24,
                "quota_unknown_policy": "allow",
            },
            "fastest_response_cheap": 1.5,
        }
    )
    candidates = plan.get("candidates") or []
    if not candidates:
        raise RuntimeError("no free inference candidate available")
    selected = next(
        (
            candidate
            for candidate in candidates
            if float((candidate.get("route") or {}).get("expected_cost_usd") or 0.0) <= 0.0
        ),
        None,
    )
    if selected is None:
        raise RuntimeError("no zero-cost free inference candidate available")
    execution = client.call(
        {
            "op": "infer_selected_quota",
            "request_template": template,
            "selected_candidate": selected,
            "selected_execution": {
                "quota_unknown_policy": "allow",
                "max_cost_usd": 0.0,
            },
        }
    )
    response = execution.get("response") if isinstance(execution, dict) and "response" in execution else execution
    if not isinstance(response, dict):
        raise RuntimeError("unexpected inference response")
    review = decode_json_object(str(response.get("content") or ""))
    return review, {"selected": selected, "response": response}


def latest_pipeline(db: sqlite3.Connection, digest: str) -> str:
    row = db.execute(
        "SELECT pipeline_id FROM body_analysis_latest WHERE sha256=? AND analysis_contract='safe-deob+sus/v1'",
        (digest,),
    ).fetchone()
    if row is None:
        raise RuntimeError(f"no deterministic latest result for {digest}")
    return str(row[0])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--database", type=Path, default=DEFAULT_DB)
    parser.add_argument("--candidate-dir", type=Path, default=DEFAULT_CANDIDATES)
    parser.add_argument("--candidate", default="llm-review-zero")
    parser.add_argument("--deobfuscate-safe", type=Path, default=DEFAULT_DEOB)
    parser.add_argument("--inference-stdio", type=Path, default=DEFAULT_STDIO)
    parser.add_argument("--env-file", type=Path, required=True)
    parser.add_argument("--limit", type=int, default=0)
    parser.add_argument("--max-source-chars", type=int, default=80_000)
    parser.add_argument("--expected-output-tokens", type=int, default=4096)
    parser.add_argument("--nice", type=int, default=10)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    if args.nice:
        os.nice(args.nice)
    paths = [Path(line) for line in (args.candidate_dir / f"{args.candidate}.txt").read_text().splitlines() if line.strip()]
    if args.limit:
        paths = paths[:args.limit]
    if args.dry_run:
        print(json.dumps({"review_contract": REVIEW_CONTRACT, "candidate": args.candidate, "count": len(paths), "free_only": True}, indent=2))
        return
    for required in (args.deobfuscate_safe, args.inference_stdio, args.env_file):
        if not required.is_file():
            raise SystemExit(f"missing required file: {required}")

    db = sqlite3.connect(args.database)
    ensure_schema(db)
    client = StdioClient(args.inference_stdio, args.env_file)
    counts = {"suspicious": 0, "clean": 0, "uncertain": 0, "errors": 0, "skipped": 0}
    try:
        for index, path in enumerate(paths, 1):
            digest = sha256(path)
            pipeline = latest_pipeline(db, digest)
            with tempfile.TemporaryDirectory(prefix="js-redox-llm-review-") as tmp:
                out = Path(tmp) / f"{digest}.js"
                report = Path(tmp) / "deob.json"
                cp = subprocess.run(
                    [str(args.deobfuscate_safe), str(path), str(out), "--report", str(report)],
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                )
                if cp.returncode or not out.is_file():
                    counts["errors"] += 1
                    print(json.dumps({"sha256": digest, "status": "deob_error", "error": (cp.stderr or cp.stdout)[-1000:]}), flush=True)
                    continue
                transformed_sha = sha256(out)
                existing = db.execute(
                    "SELECT 1 FROM body_llm_review WHERE sha256=? AND review_contract=? AND deterministic_pipeline_id=? AND transformed_sha256=? LIMIT 1",
                    (digest, REVIEW_CONTRACT, pipeline, transformed_sha),
                ).fetchone()
                if existing:
                    counts["skipped"] += 1
                    continue
                text = out.read_text(encoding="utf-8", errors="replace")
                if len(text) > args.max_source_chars:
                    half = args.max_source_chars // 2
                    text = text[:half] + "\n/* ... middle omitted for review budget ... */\n" + text[-half:]
                try:
                    review, evidence = review_source(client, text, args.expected_output_tokens)
                    verdict, confidence, categories, note = validate_review(review)
                    selected = evidence["selected"]
                    response = evidence["response"]
                    route = selected.get("route") or {}
                    endpoint = route.get("endpoint") or {}
                    model = response.get("model") or selected.get("canonical_id") or endpoint.get("model")
                    provider = response.get("provider") or endpoint.get("provider") or endpoint.get("source")
                    with db:
                        db.execute(
                            "INSERT OR REPLACE INTO body_llm_review VALUES (?,?,?,?,?,?,?,?,?,?,?,?)",
                            (
                                digest, REVIEW_CONTRACT, pipeline, utc_now(), transformed_sha,
                                model or "", provider or "", verdict, confidence,
                                json.dumps(categories, separators=(",", ":")), note,
                                json.dumps(review, sort_keys=True, separators=(",", ":")),
                            ),
                        )
                    counts[verdict] += 1
                    print(json.dumps({"done": index, "total": len(paths), "sha256": digest, "verdict": verdict, "confidence": confidence, "model": model, "provider": provider}), flush=True)
                except Exception as exc:
                    counts["errors"] += 1
                    print(json.dumps({"done": index, "total": len(paths), "sha256": digest, "status": "error", "error": repr(exc)}), flush=True)
    finally:
        client.close()
        db.close()
    print(json.dumps({"schema": "js-redox-llm-review-summary/v1", "review_contract": REVIEW_CONTRACT, "counts": counts}, indent=2))


if __name__ == "__main__":
    main()
