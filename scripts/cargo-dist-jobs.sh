#!/usr/bin/env bash
set -euo pipefail

if [[ -n "${CARGO_BUILD_JOBS:-}" ]]; then
  printf '%s\n' "$CARGO_BUILD_JOBS"
  exit 0
fi

if command -v sccache >/dev/null 2>&1 && command -v uv >/dev/null 2>&1; then
  status=$(sccache --dist-status 2>/dev/null || true)
  read -r cpus busy < <(
    printf '%s' "$status" | uv run python -c '
import json, sys
try:
    d=json.load(sys.stdin)["SchedulerStatus"][1]
    print(int(d["num_cpus"]), int(d.get("in_progress", 0)))
except Exception:
    pass
' 2>/dev/null || true
  )

  if [[ "${cpus:-}" =~ ^[0-9]+$ ]] && (( cpus > 0 )); then
    # Normal cap: use at most two thirds of the remote farm.
    cap=$(( cpus * 2 / 3 ))
    (( cap < 1 )) && cap=1

    # Also respect current shared-farm occupancy. Keep at least two slots
    # unclaimed for unrelated work and scheduler jitter.
    reserve=2
    free=$(( cpus - ${busy:-0} - reserve ))
    (( free < 1 )) && free=1

    jobs=$cap
    (( free < jobs )) && jobs=$free
    printf '%s\n' "$jobs"
    exit 0
  fi
fi

nproc 2>/dev/null || printf '1\n'
