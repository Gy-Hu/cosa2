#!/usr/bin/env bash
set -euo pipefail

strategy=${1:?usage: submit_lsf.sh STRATEGY [MAX_PARALLEL] [START] [END]}
max_parallel=${2:-12}
case "$strategy" in
  baseline|full_reduce|consec_core|full_add|ucb|fallback32|ucb_fallback32|\
    warmup10|ucb_fallback32_warmup10|bzla_itp|bzla_itp_fallback32|\
    bzla_itp_ucb_fallback32|no_pseudo|no_pseudo_fallback32|\
    no_pseudo_ucb_fallback32|no_pseudo_packet_lean_core|\
    no_pseudo_packet_array_local|no_pseudo_packet_cex_diverse|\
    no_pseudo_packet_recovery|no_pseudo_mab_ic3ia_refinement) ;;
  *) echo "Unknown strategy: $strategy" >&2; exit 2 ;;
esac

root=${CEGP_PONO_ROOT:-/hpc/home/connect.cchen099/gy-env/pono}
manifest=${CEGP_MANIFEST:-${root}/experiments/cegp_bandit/liveness_2025.txt}
result_root=${CEGP_RESULT_ROOT:-/hpc/home/connect.cchen099/gy-env/pono-cegp-bandit-results}
timeout_seconds=${CEGP_TIMEOUT:-1000}
wall_time=${CEGP_WALL_TIME:-00:20}
commit=${CEGP_COMMIT:-$(git --git-dir="$root/.git" --work-tree="$root" rev-parse --short=12 HEAD)}
count=$(grep -cve '^[[:space:]]*$' "$manifest")
start=${3:-1}
end=${4:-$count}
if ((start < 1 || end < start || end > count)); then
  echo "Invalid manifest range ${start}-${end}; expected 1-${count}" >&2
  exit 2
fi
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
  -W "$wall_time" \
  -J "cegp_${strategy}_${start}_${end}[${start}-${end}]%${max_parallel}" \
  -oo "${log_dir}/%I.%J.out" \
  -eo "${log_dir}/%I.%J.err" \
  "$root/experiments/cegp_bandit/lsf_array.sh"
