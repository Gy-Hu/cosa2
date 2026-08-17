#!/usr/bin/env bash
set -euo pipefail

root=${CEGP_PONO_ROOT:-/hpc/home/connect.cchen099/gy-env/pono}
manifest=${CEGP_MANIFEST:-${root}/experiments/cegp_bandit/liveness_2025.txt}
strategy=${CEGP_STRATEGY:?CEGP_STRATEGY must name a refinement strategy}
timeout_seconds=${CEGP_TIMEOUT:-1000}
commit=${CEGP_COMMIT:-$(git --git-dir="$root/.git" --work-tree="$root" rev-parse --short=12 HEAD)}
result_root=${CEGP_RESULT_ROOT:-/hpc/home/connect.cchen099/gy-env/pono-cegp-bandit-results}

index=$((LSB_JOBINDEX - 1))
benchmark=$(sed -n "$((index + 1))p" "$manifest")
if [[ -z "$benchmark" ]]; then
  echo "No benchmark for LSF index ${LSB_JOBINDEX}" >&2
  exit 2
fi

output_dir=${result_root}/${commit}/${strategy}
mkdir -p "$output_dir"
cd "$root"

exec python3 experiments/cegp_bandit/run_case.py \
  --strategy "$strategy" \
  --benchmark "$benchmark" \
  --timeout "$timeout_seconds" \
  --output "$output_dir/case-${index}.json"
