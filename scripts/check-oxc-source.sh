#!/usr/bin/env bash
set -euo pipefail

# oxc_index and oxc_sourcemap are separate upstream repositories.
cargo metadata --locked --format-version 1 | jq -e '
  [.packages[] | select(.name == "oxc" or (.name | startswith("oxc_"))) |
    select(.name != "oxc_index" and .name != "oxc_sourcemap")] as $crates |
  ($crates | length > 0) and
  ($crates | all(.source != null and (.source | test("^git\\+https://github\\.com/codeandsolder/oxc\\.git\\?rev=[0-9a-f]{40}#[0-9a-f]{40}$")))) and
  ($crates | map(.source) | unique | length == 1) and
  ($crates | map(.name) | length == (unique | length))
'
