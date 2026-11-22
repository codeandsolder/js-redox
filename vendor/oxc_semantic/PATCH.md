# Temporary upstream backport

Published MIT-licensed oxc_semantic 0.159.0, crate VCS commit d9483516f84068f867e0a3949ac0ec53ef82aa63, with oxc-project/oxc#28542 applied. The binder and checker patches come from upstream PR head d0faa805ed560a27149ce796bf36404515680079 and retain the release's catch-variable changes. The builder uses the identical additions from the preceding release-compatible revision 3836b2a24 because the newer PR's surrounding builder context depends on later upstream changes. All hunks apply with exact context (fuzz=0).

Only src/binder.rs, src/builder.rs, src/checker/javascript.rs and src/checker/mod.rs differ from the published source. Other Oxc crates use crates.io, preserving one type universe. Remove the path override and vendor directory when the fix ships, retaining the downstream regression.
