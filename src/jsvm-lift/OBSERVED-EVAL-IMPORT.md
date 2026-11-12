# Optional source-tree runtime eval evidence

The native Rust source-tree command supports optional execution-observed
JavaScript sources. The ordinary static path does not change; no Node or ZIPP
process is required to import a previously exported witness.

For optional observed-eval inputs, source-tree constructs its complete output
in a temporary sibling directory and publishes it only after every witness
and AST link has been validated. Rejected or incomplete captures leave no
partial output or staging files. The requested destination must not exist,
so an existing analyst result is never silently overwritten. On Linux,
Android and Apple platforms, the final publication uses the operating
system's exclusive no-replace rename, so a concurrently created empty
output directory is also protected. Static-only source-tree retains its
previous output behavior.

## CLI

Repeat one group of three paths for each independent capture:

~~~bash
deobfuscate-safe source-tree handlers/ readable/ \
  --context-source original.pretty.js \
  --observed-eval exported-runtime/ original-outer.js normalized-inner.js

deobfuscate-safe source-tree handlers/ readable/ \
  --context-source original.pretty.js \
  --observed-eval first-export/ outer-1.js inner-1.js \
  --observed-eval second-export/ outer-2.js inner-2.js
~~~

EXPORTED_RUNTIME is the v2 export from the js-redox Knitsail experiment,
containing a manifest.json and content-addressed raw/ and readable/ files.
The outer and inner JavaScript files must match the complete SHA-256 digests
in the manifest; private payloads remain outside Git.

The importer checks the loader's indirect-eval source site and the inner
executable direct-eval AST with the OXC semantic resolver, including the
argument AST and semantic identifier binding roles. Lexical frames cover
both ordinary function expressions/declarations and arrow functions,
including nested arrow callbacks. Function and arrow frames have distinct
kinds: matching argument names and parameter lists alone cannot conflate
the two source forms. Each observed source
must match its exact SHA-256, UTF-16 code-unit length, event counts and
content-addressed path. Old single-layer v1 manifests are deliberately
rejected.

The output gains a runtime-observed/ tree with entry metadata, exact raw
source, optional formatted JavaScript, and AST-linked navigation sidecars.
Matching lexical structure does NOT establish whole-function equivalence,
and observed execution does NOT prove universal reachability.

If a static source cannot be parsed, or no lexical site matches, those
conditions are recorded. The observed code remains accessible; this is
not silently reported as a verified universal static transformation.
The original static JS files and reconstruction.json remain byte-identical.

Source capture and the full experimental reproduction are documented in
https://github.com/codeandsolder/js-redox/pull/179

## Verified archived Knitsail integration (2026-11-12)

With Node v26.13.1 and the matching system simdjson library restored on Acer,
the saved 2026-09-27 HTML challenge produced the original v2 witness again:
51 direct eval executions, 40 unique source strings, 25 standalone formatted,
15 exact raw-only, and an 851-character challenge result.

The native source-tree command was run twice against a **focused subset of
three actual static Knitsail source views**: once without the optional input,
once with the v2 witness. The observed output included all 40 strings and
three AST lexical-site matches. The three generated static JavaScript files
and the static reconstruction.json were byte-identical between runs. All 154
relative links in the 46 runtime evidence/sidecar Markdown pages resolved.
The complete original manifest, including evidenceKind and environment,
was preserved **byte-for-byte**.

The importer also rejects symlinked intermediate source directories and
requires all listed event occurrences to account for the manifest's event
count. Focused Rust unit tests cover both cases, and a CLI parser regression
covers multiple independent 3-path option groups.

This does not authorize promoting observed code into unconditional static
deobfuscation: every generated fragment is tied to a specific captured
execution and the matched original AST site, not a proof of all reachable paths.

## General direct-eval source-site matching (2026-11-12)

The v2 inner executable evalSite.expression is checked against the full, exact
UTF-16-addressed source callsite and its OXC executable direct-eval node.
It is not limited to the historical Knitsail expression eval(D).

For arbitrary expression arguments, OXC Codegen produces a normalized AST
representation. Argument arity and spread are retained separately, so a
sequence expression is not conflated with multiple call arguments.
Every referenced identifier carries an OXC semantic binding role: formal
parameter with frame depth and position, import, local declaration kind,
or unresolved/global. Shadowed, optional, or indirect eval are not promoted
to direct-eval evidence. These remain structural provenance matches, not
proofs of equivalent variable values or whole-function behavior.

ES-module files (.mjs and .mts) use module parsing; .js supports script or
ESM parsing, and corresponding .cjs/.jsx/TypeScript extensions use their
source-type parsers. UTF-16 source offsets are checked after non-BMP Unicode,
and offsets inside surrogate pairs are refused.

Focused regressions cover compound arguments, lexical shadowing,
multi-argument versus sequence expression, spread, module imports,
source-site UTF-16 indexing, and a full v2 import with an ESM callsite.
