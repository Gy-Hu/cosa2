#!/usr/bin/env bash
set -euo pipefail

strategy=${1:?usage: run_one_strategy_full_track_lsf.sh STRATEGY FIRST_JOB}
current_job=${2:?usage: run_one_strategy_full_track_lsf.sh STRATEGY FIRST_JOB}

root=${CEGP_PONO_ROOT:-/hpc/home/connect.cchen099/gy-env/pono}
manifest=${CEGP_MANIFEST:-/hpc/home/connect.cchen099/gy-env/pono-cegp-bandit-manifests/all-array-310.txt}
timeout_seconds=${CEGP_TIMEOUT:-1000}
wall_time=${CEGP_WALL_TIME:-00:20}
max_parallel=${CEGP_MAX_PARALLEL:-64}
submit_threshold=${CEGP_SUBMIT_THRESHOLD:-$max_parallel}
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
    CEGP_WALL_TIME="$wall_time" \
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

job_ids=("$current_job")
ranges=($remaining_ranges)
next_range=0

active_elements()
{
  local total=0
  local job_id count
  for job_id in "${job_ids[@]}"; do
    count=$(bjobs -a -o "stat" "$job_id" 2>/dev/null \
      | tail -n +2 \
      | grep -Ec '^[[:space:]]*(PEND|RUN|PSUSP|USUSP|SSUSP|WAIT)' || true)
    total=$((total + count))
  done
  printf '%s\n' "$total"
}

while true; do
  active=$(active_elements)
  if ((next_range < ${#ranges[@]} && active <= submit_threshold)); then
    range=${ranges[$next_range]}
    start=${range%%:*}
    end=${range##*:}
    current_job=$(submit_range "$start" "$end")
    job_ids+=("$current_job")
    next_range=$((next_range + 1))
    echo "range=${start}-${end} strategy=${strategy} job=${current_job} active_before=${active}"
    continue
  fi
  if ((next_range == ${#ranges[@]} && active == 0)); then
    break
  fi
  echo "pipeline strategy=${strategy} active=${active} submitted_ranges=${next_range}/${#ranges[@]}"
  sleep 30
done

echo "all 310 cases completed for ${strategy}"
