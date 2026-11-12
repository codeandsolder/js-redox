# Optional source-tree runtime eval evidence

The native Rust source-tree command supports optional execution-observed
JavaScript sources. The ordinary static path does not change; no Node or ZIPP
process is required to import a previously exported witness.

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
argument's nearest lexical formal-parameter binding. Each observed source
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
