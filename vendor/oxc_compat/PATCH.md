# Temporary upstream backport

Published MIT-licensed oxc_compat 0.159.0, crate VCS commit d9483516f84068f867e0a3949ac0ec53ef82aa63, with oxc-project/oxc#29927 from c94a30db0469926e98f68182f66021d26ef3fb51 applied with exact context (fuzz=0). Only src/babel_targets.rs differs from the published source.

Remove the path override and vendor directory when the fix ships. Retain the downstream regression; if upstream implements a previously unsupported form, test the effective target rather than requiring an error.
