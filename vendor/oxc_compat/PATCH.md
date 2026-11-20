# Temporary upstream backport

Published MIT-licensed `oxc_compat` 0.158.0 (release tag `crates_v0.158.0`, commit `74e5e665ab8227c3d43abf3ce0e4383830e80c12`) with [oxc-project/oxc#29927](https://github.com/oxc-project/oxc/pull/29927) applied from commit `c94a30db0469926e98f68182f66021d26ef3fb51`. Only `src/babel_targets.rs` differs from the released source. Unsupported Babel target map entries must fail explicitly instead of silently disappearing.

Remove this directory and its root `[patch.crates-io]` entry when the upstream fix ships in the used Oxc release. Retain the downstream regression; if upstream implements a previously unsupported form, adjust the regression to assert the effective target rather than always expecting an error. Review both Oxc patches on every grouped Oxc dependency upgrade.
