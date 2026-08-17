#!/usr/bin/env bash
set -euo pipefail

strategy=${1:?usage: submit_lsf.sh STRATEGY [MAX_PARALLEL]}
max_parallel=${2:-12}
case "$strategy" in
  baseline|full_reduce|consec_core|full_add|ucb|fallback32|ucb_fallback32) ;;
  *) echo "Unknown strategy: $strategy" >&2; exit 2 ;;
esac

root=${CEGP_PONO_ROOT:-/hpc/home/connect.cchen099/gy-env/pono}
manifest=${CEGP_MANIFEST:-${root}/experiments/cegp_bandit/liveness_2025.txt}
result_root=${CEGP_RESULT_ROOT:-/hpc/home/connect.cchen099/gy-env/pono-cegp-bandit-results}
timeout_seconds=${CEGP_TIMEOUT:-1000}
commit=$(git --git-dir="$root/.git" --work-tree="$root" rev-parse --short=12 HEAD)
count=$(grep -cve '^[[:space:]]*$' "$manifest")
log_dir=${result_root}/${commit}/${strategy}/lsf
mkdir -p "$log_dir"

export CEGP_PONO_ROOT="$root"
export CEGP_MANIFEST="$manifest"
export CEGP_RESULT_ROOT="$result_root"
export CEGP_TIMEOUT="$timeout_seconds"
export CEGP_STRATEGY="$strategy"
export CEGP_COMMIT="$commit"

bsub \
  -q bmcpu \
  -n 1 \
  -R "rusage[mem=16384]" \
  -W 00:20 \
  -J "cegp_${strategy}[1-${count}]%${max_parallel}" \
  -oo "${log_dir}/%I.%J.out" \
  -eo "${log_dir}/%I.%J.err" \
  "$root/experiments/cegp_bandit/lsf_array.sh"
