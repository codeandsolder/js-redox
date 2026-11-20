# Temporary upstream backport

This directory contains the published MIT-licensed `oxc_semantic` 0.158.0 source (release tag `crates_v0.158.0`, commit `74e5e665ab8227c3d43abf3ce0e4383830e80c12`), plus the semantic fix from [oxc-project/oxc#28542](https://github.com/oxc-project/oxc/pull/28542), specifically the release-compatible revision `3836b2a24`. The newer upstream PR revision depends on catch-binding changes introduced after 0.158.0.

Only `src/binder.rs`, `src/builder.rs`, `src/checker/javascript.rs`, and `src/checker/mod.rs` differ from the published source. The other Oxc crates continue to use crates.io, preserving identical AST, allocator and symbol types across the graph.

Remove this directory and the root `[patch.crates-io]` entry once the upstream fix ships in a release used by js-redox. Keep the downstream regression test.
