#!/usr/bin/env bash
set -euo pipefail

strategy=${1:?usage: run_one_strategy_full_track_lsf.sh STRATEGY FIRST_JOB}
current_job=${2:?usage: run_one_strategy_full_track_lsf.sh STRATEGY FIRST_JOB}

root=${CEGP_PONO_ROOT:-/hpc/home/connect.cchen099/gy-env/pono}
manifest=${CEGP_MANIFEST:-/hpc/home/connect.cchen099/gy-env/pono-cegp-bandit-manifests/all-array-310.txt}
timeout_seconds=${CEGP_TIMEOUT:-1000}
max_parallel=${CEGP_MAX_PARALLEL:-64}
remaining_ranges=${CEGP_REMAINING_RANGES:-"65:128 129:192 193:256 257:310"}

wait_for_job_array()
{
  local job_id=$1
  while bjobs -a -o "stat" "$job_id" 2>/dev/null \
    | tail -n +2 \
    | grep -Eq '^[[:space:]]*(PEND|RUN|PSUSP|USUSP|SSUSP|WAIT)'; do
    sleep 30
  done
}

submit_range()
{
  local start=$1
  local end=$2
  local output
  output=$(
    CEGP_PONO_ROOT="$root" \
    CEGP_MANIFEST="$manifest" \
    CEGP_TIMEOUT="$timeout_seconds" \
      "$root/experiments/cegp_bandit/submit_lsf.sh" \
        "$strategy" "$max_parallel" "$start" "$end" 2>&1
  )
  printf '%s\n' "$output" >&2
  local job_id
  job_id=$(printf '%s\n' "$output" \
    | sed -n 's/.*Job <\([0-9][0-9]*\)>.*/\1/p' \
    | tail -n 1)
  if [[ -z "$job_id" ]]; then
    echo "Failed to parse LSF job id for ${strategy} ${start}-${end}" >&2
    exit 2
  fi
  printf '%s\n' "$job_id"
}

wait_for_job_array "$current_job"

for range in $remaining_ranges; do
  start=${range%%:*}
  end=${range##*:}
  current_job=$(submit_range "$start" "$end")
  echo "range=${start}-${end} strategy=${strategy} job=${current_job}"
  wait_for_job_array "$current_job"
done

echo "all 310 cases completed for ${strategy}"
