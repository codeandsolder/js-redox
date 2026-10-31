#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
project="$root/src/jsvm-lift"
publish_root="$root/.cargo-target-nodebug"
toolchain="$(cd "$root" && rustup show active-toolchain | awk '{print $1}')"
cargo_bin="$(RUSTUP_TOOLCHAIN="$toolchain" rustup which cargo)"
rustc_bin="$(RUSTUP_TOOLCHAIN="$toolchain" rustup which rustc)"

export RUSTC="$rustc_bin"
export RUSTUP_TOOLCHAIN="$toolchain"
export CARGO_PROFILE_DEV_DEBUG=0
export CARGO_PROFILE_DEV_INCREMENTAL=false

if [[ "${JSVM_LOCAL_BUILD:-0}" == "1" ]]; then
  echo "JSVM_LOCAL_BUILD=1 is disabled for this project; use the sccache-dist build path." >&2
  exit 2
fi

jobs="$("$root/scripts/cargo-dist-jobs.sh")"
mode="sccache-dist"

profile=debug
for arg in "$@"; do
  [[ "$arg" == "--release" ]] && profile=release
done

echo "building JS VM tools with $jobs Cargo jobs ($mode)"
echo "publish root: $publish_root"
echo "cargo: $("$cargo_bin" --version)"
echo "rustc: $("$rustc_bin" --version)"
echo "RUSTC_WRAPPER=${RUSTC_WRAPPER:-<unset>}"

cd "$project"
"$cargo_bin" build -j "$jobs" "$@"

composer_args=()
if [[ "$profile" == "release" ]]; then
  composer_args+=(--release)
fi
"$cargo_bin" build -j "$jobs" -p sourcemap-compose "${composer_args[@]}"
"$cargo_bin" build -j "$jobs" -p wasm-redox --bin wasm-redox --bin fresh-eval "${composer_args[@]}"

# Site-wrapper target is a disposable compile cache; durable executables are published below.
shim_target_root="/var/cache/sentinelx/cargo-target"
if [[ -r /etc/sentinelx/build-scratch.conf ]]; then
  # shellcheck disable=SC1091
  . /etc/sentinelx/build-scratch.conf
  shim_target_root="${SENTINELX_CARGO_TARGET_ROOT:-$shim_target_root}"
fi
workspace="$(pwd -P)"
hash="$(printf '%s' "$workspace" | sha256sum | cut -c1-16)"
name="$(basename "$workspace" | tr -c 'A-Za-z0-9._-' '_')"
actual="$shim_target_root/${name}-$hash/$profile"
# Cargo workspaces place durable artifacts in the workspace target directory,
# not necessarily under this member crate. Ask Cargo instead of duplicating
# that layout rule here.
cargo_target="$("$cargo_bin" metadata --no-deps --format-version 1 \
  | rg -o '"target_directory":"[^"]+' \
  | cut -d '"' -f 4)"
if [[ -z "$cargo_target" ]]; then
  echo "failed to discover Cargo target_directory" >&2
  exit 2
fi
mirror="$cargo_target/$profile"
canonical="$publish_root/$profile"
mkdir -p "$canonical"

# SentinelX Cargo mirrors final link artifacts to the workspace target/ before
# deleting its disposable scratch target. Prefer that durable mirror after Cargo
# returns, while retaining the scratch path as a fallback for older wrappers.
bins=(
  jsvm-lift reduce signature roles normalize disasm ir table-signature table-ir
  switch-ir deobfuscate-safe har-project js-format js-refs bundle-unpack
  source-materialize bundle-materialize vm-materialize
  sourcemap-compose sus-scan wasm-redox fresh-eval wasm-import-semantics
  source-directives api-surface static-string-recover static-byte-artifacts
)
published=0
for bin in "${bins[@]}"; do
  source_bin=""
  if [[ -f "$mirror/$bin" ]]; then
    source_bin="$mirror/$bin"
  elif [[ -f "$actual/$bin" ]]; then
    source_bin="$actual/$bin"
  fi
  if [[ -z "$source_bin" ]]; then
    echo "missing built executable: $bin" >&2
    exit 2
  fi
  install -m 0755 "$source_bin" "$canonical/$bin"
  published=$((published + 1))
done

echo "artifact mirror: $mirror"
echo "scratch target: $actual"
echo "published $published executable(s) to $canonical"
if [[ -e "$canonical/jsvm-lift" ]]; then
  stat -c 'canonical scanner: %y %s %n' "$canonical/jsvm-lift"
fi
