#!/usr/bin/env python3
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MATERIALIZER = ROOT / "scripts/materialize-safe-deobfuscation.py"
DEOBFUSCATOR = Path(
    os.environ.get(
        "JS_REDOX_DEOBFUSCATOR",
        ROOT / ".cargo-target-nodebug/debug/deobfuscate-safe",
    )
)
TEMP_ROOT = ROOT / "work/test-tmp"


def run(*argv: object) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(arg) for arg in argv],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=60,
    )


def main() -> None:
    if not DEOBFUSCATOR.is_file():
        raise SystemExit(f"missing binary: {DEOBFUSCATOR}")
    TEMP_ROOT.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="source-mode-pipeline-", dir=TEMP_ROOT) as td:
        temp = Path(td)
        project = temp / "project"
        analysis = project / "analysis"
        source_dir = project / "src"
        analysis.mkdir(parents=True)
        source_dir.mkdir(parents=True)

        # Byte-identical source can have different semantics based on its
        # logical filename. Top-level return is CommonJS-valid but ESM-invalid.
        source = b"return 1;\n"
        for suffix in ("mjs", "cjs"):
            (source_dir / f"same.{suffix}").write_bytes(source)

        (analysis / "source-index.json").write_text(
            json.dumps(
                {
                    "schema": "capture-source-index/v1",
                    "units": [
                        {
                            "kind": "javascript",
                            "raw_path": "src/same.mjs",
                            "source_path": "src/same.mjs",
                        },
                        {
                            "kind": "javascript",
                            "raw_path": "src/same.cjs",
                            "source_path": "src/same.cjs",
                        },
                    ],
                    "summary": {},
                }
            )
            + "\n"
        )

        recoverer = temp / "recover.py"
        recoverer.write_text(
            "\n".join(
                [
                    "import hashlib, json, sys",
                    "from pathlib import Path",
                    "src, dst = Path(sys.argv[1]), Path(sys.argv[2])",
                    'report = Path(sys.argv[sys.argv.index("--report") + 1])',
                    "source = src.read_bytes()",
                    'recovered = source + b"// recovered\\n"',
                    "dst.parent.mkdir(parents=True, exist_ok=True)",
                    "dst.write_bytes(recovered)",
                    "input_digest = hashlib.sha256(source).hexdigest()",
                    "output_digest = hashlib.sha256(recovered).hexdigest()",
                    "report.parent.mkdir(parents=True, exist_ok=True)",
                    "report.write_text(json.dumps({",
                    '    "safe_static_only": True,',
                    '    "input_sha256": input_digest,',
                    '    "output_sha256": output_digest,',
                    '    "changed": True,',
                    '    "replacements": 1,',
                    '    "decoders": [],',
                    '}) + "\\n")',
                    "",
                ]
            )
        )

        completed = run(
            sys.executable,
            MATERIALIZER,
            project,
            "--deobfuscator",
            DEOBFUSCATOR,
            "--string-recoverer",
            recoverer,
            "--formatter",
            "/bin/cp",
            "--jobs",
            "2",
        )
        if completed.returncode:
            raise RuntimeError(
                "source-mode materializer regression failed:\n"
                + completed.stdout
                + completed.stderr
            )

        artifact = json.loads((analysis / "deobfuscation.json").read_text())
        units = {Path(unit["raw_path"]).suffix: unit for unit in artifact["units"]}
        module = units[".mjs"]
        commonjs = units[".cjs"]
        assert artifact["mode_sensitive_deduplication"] is True, artifact
        assert artifact["summary"]["unique_raw_inputs"] == 2, artifact["summary"]
        assert artifact["summary"]["unique_pre_deob_inputs"] == 2, artifact["summary"]
        assert module["source_mode"] == "module", module
        assert commonjs["source_mode"] == "commonjs", commonjs
        assert module["exit"] != 0, module
        assert commonjs["exit"] == 0, commonjs
        assert commonjs["safe_static_only"] is True, commonjs

        string_artifact = json.loads((analysis / "string-recovery.json").read_text())
        string_units = string_artifact["units"]
        string_modes = {unit["source_mode"] for unit in string_units}
        assert string_modes == {"module", "commonjs"}, string_artifact
        assert all(unit["exit"] == 0 for unit in string_units), string_units
        assert all("fallback" not in unit for unit in string_units), string_units
        assert all(unit["changed"] is True for unit in string_units), string_units
        assert all(
            unit["input_sha256"] != unit["output_sha256"] for unit in string_units
        ), string_units
        assert string_artifact["summary"]["unique_input_bodies"] == 2, string_artifact
        assert string_artifact["summary"]["failed_units"] == 0, string_artifact
        assert module["pre_deob_sha256"] != module["input_sha256"], module
        assert commonjs["pre_deob_sha256"] != commonjs["input_sha256"], commonjs

        print("source-mode pipeline: identical bytes kept distinct as module/commonjs")


if __name__ == "__main__":
    main()
