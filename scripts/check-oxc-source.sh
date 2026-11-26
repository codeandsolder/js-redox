#!/usr/bin/env bash
set -euo pipefail

# oxc_index and oxc_sourcemap are separate upstream repositories.
# Shared patch queues must remain selected, including after lockfile maintenance.
cargo metadata --locked --format-version 1 | jq -e '
  [.packages[] | select(.name == "oxc" or (.name | startswith("oxc_"))) |
    select(.name != "oxc_index" and .name != "oxc_sourcemap")] as $crates |
  ($crates | length > 0) and
  ($crates | all(.source != null and (.source | test("^git\\+https://github\\.com/codeandsolder/oxc\\.git\\?rev=[0-9a-f]{40}#[0-9a-f]{40}$")))) and
  ($crates | map(.source) | unique | length == 1) and
  ($crates | map(.name) | length == (unique | length)) and
  (.packages as $packages |
    {"js-redox-deps": ["compact_str", "oxc_sourcemap", "petgraph", "phf_macros"],
     "compression-backend": ["compression-codecs", "oxc-browserslist"]} |
    to_entries | all(. as $family |
      ($family.value | all(. as $name |
        [$packages[] | select(.name == $name)] as $matches |
        ($matches | length == 1) and
        ($matches[0].source // "" | startswith("git+https://github.com/codeandsolder/cargo-patches.git?branch=generated/" + $family.key + "#"))))))
'
