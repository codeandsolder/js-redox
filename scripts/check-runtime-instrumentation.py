#!/usr/bin/env python3
import runpy
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
instrumentation_kind = runpy.run_path(
    str(ROOT / "scripts/analyze-runtime-scripts.py"),
    run_name="runtime_analysis_instrumentation_test",
)["instrumentation_kind"]


def main() -> None:
    scroll_probe = """() => ({
      y: scrollY,
      height: document.documentElement.scrollHeight,
    })"""
    assert instrumentation_kind(scroll_probe) == "recorder-scroll"

    # Ordinary application bundles can contain the same tokens. The live corpus
    # exposed multi-MiB false positives, so content signatures alone are not
    # sufficient without bounding the known tiny recorder probe shape.
    page_bundle = (
        "const app = '" + ("x" * 5000) + "';\n"
        "const h = document.documentElement.scrollHeight;\n"
        "console.log(scrollY, h);\n"
    )
    assert instrumentation_kind(page_bundle) is None

    assert instrumentation_kind(
        "((utilityScript, ...args) => utilityScript.evaluate(...args))"
    ) == "playwright-utility"

    print("PASS: runtime instrumentation classifier rejects large page-code false positives")


if __name__ == "__main__":
    main()
