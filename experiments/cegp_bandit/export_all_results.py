#!/usr/bin/env python3
"""Export raw CEGP experiments plus reviewable CSV/Markdown summaries."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import shutil
import tarfile
from collections import Counter
from pathlib import Path


FULL_RESULT_COMMIT = "29de180e1f45"
BASELINE = "baseline"
FINAL = "no_pseudo_ucb_fallback32"

SELECT_RE = re.compile(
    r"(?P<kind>CEGP-BANDIT|IC3IA-FALLBACK-BANDIT) select(?P<body>[^\n]*)"
)
UPDATE_RE = re.compile(
    r"(?P<kind>CEGP-BANDIT|IC3IA-FALLBACK-BANDIT) update[^\n]*"
    r"reward=(?P<reward>[-+0-9.eE]+)"
)
ARM_RE = re.compile(r"\barm=(\d+)")
LIMIT_RE = re.compile(r"\blimit=(\d+)")


def is_solved(record: dict) -> bool:
    return not record["timed_out"] and record["result"] in {"sat", "unsat"}


def par2(record: dict) -> float:
    return (
        float(record["wall_seconds"])
        if is_solved(record)
        else 2.0 * float(record["timeout_seconds"])
    )


def load_records(directory: Path) -> list[dict]:
    return [
        json.loads(path.read_text(encoding="utf-8"))
        for path in sorted(directory.glob("case-*.json"))
    ]


def index_records(directory: Path) -> dict[str, dict]:
    records = load_records(directory)
    indexed = {record["benchmark"]: record for record in records}
    if len(indexed) != len(records):
        raise ValueError(f"duplicate benchmark records in {directory}")
    return indexed


def write_csv(path: Path, rows: list[dict], fieldnames: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=fieldnames, lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)


def parse_mab(record: dict) -> dict:
    text = record.get("stderr_tail", "")
    selects = list(SELECT_RE.finditer(text))
    updates = list(UPDATE_RE.finditer(text))
    outer_selects = [m for m in selects if m.group("kind") == "CEGP-BANDIT"]
    fallback_selects = [
        m for m in selects if m.group("kind") == "IC3IA-FALLBACK-BANDIT"
    ]
    outer_updates = [
        m for m in updates if m.group("kind") == "CEGP-BANDIT"
    ]
    fallback_updates = [
        m for m in updates if m.group("kind") == "IC3IA-FALLBACK-BANDIT"
    ]
    rewards = [float(m.group("reward")) for m in updates]
    return {
        "outer_selects": len(outer_selects),
        "outer_updates": len(outer_updates),
        "fallback_selects": len(fallback_selects),
        "fallback_updates": len(fallback_updates),
        "fallback_arms": ";".join(
            match.group(1)
            for m in fallback_selects
            if (match := ARM_RE.search(m.group("body")))
        ),
        "fallback_limits": ";".join(
            match.group(1)
            for m in fallback_selects
            if (match := LIMIT_RE.search(m.group("body")))
        ),
        "reward_sum": sum(rewards),
        "nonzero_reward_updates": sum(reward != 0.0 for reward in rewards),
        "mab_lines": " | ".join(
            line for line in text.splitlines() if "BANDIT" in line
        ),
    }


def metrics(records: list[dict]) -> dict:
    total = sum(par2(record) for record in records)
    return {
        "completed_cases": len(records),
        "solved": sum(is_solved(record) for record in records),
        "sat": sum(record["result"] == "sat" for record in records),
        "unsat": sum(record["result"] == "unsat" for record in records),
        "timeouts": sum(record["timed_out"] for record in records),
        "unknown": sum(record["result"] == "unknown" for record in records),
        "missing": sum(record["result"] == "missing" for record in records),
        "par2_total": total,
        "par2_mean": total / len(records) if records else "",
    }


def copy_raw_json(result_root: Path, output: Path) -> int:
    destination = output / "raw_json"
    count = 0
    for source in sorted(result_root.glob("*/*/case-*.json")):
        relative = source.relative_to(result_root)
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
        count += 1
    return count


def create_raw_archive(
    result_root: Path, log_root: Path, manifest: Path, output: Path
) -> tuple[Path, int]:
    archive = output / "raw_experiment_artifacts.tar.gz"
    with tarfile.open(archive, "w:gz") as tar:
        tar.add(result_root, arcname="pono-cegp-bandit-results")
        if log_root.exists():
            tar.add(log_root, arcname="pono-cegp-bandit-logs")
        tar.add(manifest, arcname=f"manifests/{manifest.name}")
    return archive, archive.stat().st_size


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--result-root", type=Path, required=True)
    parser.add_argument("--log-root", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    if args.output.exists():
        shutil.rmtree(args.output)
    args.output.mkdir(parents=True)

    manifest = [
        line.strip()
        for line in args.manifest.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    if len(manifest) != 310 or len(set(manifest)) != 310:
        raise ValueError("expected a 310-entry unique manifest")

    full_root = args.result_root / FULL_RESULT_COMMIT
    baseline = index_records(full_root / BASELINE)
    final = index_records(full_root / FINAL)
    if set(baseline) != set(manifest) or set(final) != set(manifest):
        raise ValueError("full result sets do not match the manifest")

    per_case_rows = []
    mab_rows = []
    gained = []
    lost = []
    conflicts = []
    for index, benchmark in enumerate(manifest):
        base = baseline[benchmark]
        candidate = final[benchmark]
        base_solved = is_solved(base)
        final_solved = is_solved(candidate)
        if final_solved and not base_solved:
            gained.append(benchmark)
        if base_solved and not final_solved:
            lost.append(benchmark)
        if base_solved and final_solved and base["result"] != candidate["result"]:
            conflicts.append(benchmark)
        winner = "tie"
        if par2(candidate) < par2(base):
            winner = "final"
        elif par2(base) < par2(candidate):
            winner = "baseline"
        per_case_rows.append(
            {
                "index": index,
                "year": benchmark.split("/array/", 1)[1].split("/", 1)[0],
                "benchmark": benchmark,
                "baseline_result": base["result"],
                "baseline_solved": base_solved,
                "baseline_wall_seconds": base["wall_seconds"],
                "baseline_par2": par2(base),
                "final_result": candidate["result"],
                "final_solved": final_solved,
                "final_wall_seconds": candidate["wall_seconds"],
                "final_par2": par2(candidate),
                "winner": winner,
                "par2_improvement": par2(base) - par2(candidate),
            }
        )
        mab = parse_mab(candidate)
        mab_rows.append({"index": index, "benchmark": benchmark, **mab})

    write_csv(
        args.output / "full_310_per_case.csv",
        per_case_rows,
        list(per_case_rows[0]),
    )
    write_csv(
        args.output / "mab_events_per_case.csv", mab_rows, list(mab_rows[0])
    )

    run_rows = []
    for commit_dir in sorted(path for path in args.result_root.iterdir() if path.is_dir()):
        for strategy_dir in sorted(path for path in commit_dir.iterdir() if path.is_dir()):
            records = load_records(strategy_dir)
            if not records:
                continue
            mab_cases = sum(
                "BANDIT" in record.get("stderr_tail", "") for record in records
            )
            run_rows.append(
                {
                    "result_commit": commit_dir.name,
                    "strategy": strategy_dir.name,
                    **metrics(records),
                    "mab_triggered_cases": mab_cases,
                }
            )
    write_csv(args.output / "run_summary.csv", run_rows, list(run_rows[0]))

    raw_json_count = copy_raw_json(args.result_root, args.output)
    archive, archive_size = create_raw_archive(
        args.result_root, args.log_root, args.manifest, args.output
    )
    archive_sha = sha256(archive)
    (args.output / "SHA256SUMS").write_text(
        f"{archive_sha}  {archive.name}\n", encoding="utf-8"
    )

    base_metrics = metrics(list(baseline.values()))
    final_metrics = metrics(list(final.values()))
    outer_cases = sum(row["outer_selects"] > 0 for row in mab_rows)
    fallback_cases = sum(row["fallback_selects"] > 0 for row in mab_rows)
    any_cases = sum(
        row["outer_selects"] + row["fallback_selects"] > 0 for row in mab_rows
    )
    total_selects = sum(
        row["outer_selects"] + row["fallback_selects"] for row in mab_rows
    )
    total_updates = sum(
        row["outer_updates"] + row["fallback_updates"] for row in mab_rows
    )
    arm_counts = Counter(
        arm
        for row in mab_rows
        for arm in row["fallback_arms"].split(";")
        if arm
    )

    readme = f"""# Exported CEGP/IC3IA experiments

This directory contains all structured experiment results and a compressed
archive of the complete LSF/diagnostic artifacts.

Commit-like directory names and the `result_commit` CSV column use the original
cluster experiment IDs. Their GitHub-sanitized commit equivalents are listed
in `../PUBLISH_COMMIT_MAP.md`.

## Full 310-case result

| Configuration | Solved | PAR-2 total | PAR-2 mean |
| --- | ---: | ---: | ---: |
| IC3IA+CEGP baseline | {base_metrics['solved']}/310 | {base_metrics['par2_total']:.2f} | {base_metrics['par2_mean']:.2f} |
| Final CPU-only UCB | **{final_metrics['solved']}/310** | **{final_metrics['par2_total']:.2f}** | **{final_metrics['par2_mean']:.2f}** |

- Solved delta: **+{final_metrics['solved'] - base_metrics['solved']}**
- Total PAR-2 improvement: **{base_metrics['par2_total'] - final_metrics['par2_total']:.2f}**
- Lost baseline-solved cases: **{len(lost)}**
- SAT/UNSAT conflicts: **{len(conflicts)}**

Newly solved cases:

{chr(10).join(f'- `{benchmark}`' for benchmark in gained)}

## MAB trigger frequency

MAB activity is sparse on this benchmark set:

| Measurement | Value |
| --- | ---: |
| Cases with any MAB selection | {any_cases}/310 ({100.0 * any_cases / 310:.2f}%) |
| Cases with outer CEGP arm selection | {outer_cases}/310 ({100.0 * outer_cases / 310:.2f}%) |
| Cases with IC3IA fallback arm selection | {fallback_cases}/310 ({100.0 * fallback_cases / 310:.2f}%) |
| Total MAB selections | {total_selects} |
| Total MAB updates | {total_updates} |
| Fallback arm-0 selections | {arm_counts.get('0', 0)} |
| Fallback arm-1 selections | {arm_counts.get('1', 0)} |
| Fallback arm-2 selections | {arm_counts.get('2', 0)} |

Most instances never reach either learning decision point. The performance
comparison is therefore between complete configurations; it is not evidence
that MAB alone explains the full gain.

## Files

- `full_310_per_case.csv`: all 310 baseline/final outcomes and solve times.
- `mab_events_per_case.csv`: per-case MAB selections, arms, limits, and rewards.
- `run_summary.csv`: every recorded commit/strategy experiment, including
  partial or cancelled ablations.
- `raw_json/`: all {raw_json_count} structured case JSON files.
- `{archive.name}`: all raw result directories, LSF logs, diagnostic logs, and
  the validated manifest ({archive_size} bytes).
- `SHA256SUMS`: archive integrity hash.
"""
    (args.output / "README.md").write_text(readme, encoding="utf-8")

    print(
        json.dumps(
            {
                "raw_json": raw_json_count,
                "archive_bytes": archive_size,
                "archive_sha256": archive_sha,
                "mab_cases": any_cases,
                "mab_selects": total_selects,
                "mab_updates": total_updates,
                "gained": len(gained),
                "lost": len(lost),
                "conflicts": len(conflicts),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
