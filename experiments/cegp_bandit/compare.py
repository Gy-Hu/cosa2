#!/usr/bin/env python3
"""Compare strategies by solved count, PAR-2, and fixed-arm oracle gap."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def load_strategy(path: Path) -> dict[str, dict]:
    records = {}
    for result_path in sorted(path.glob("case-*.json")):
        record = json.loads(result_path.read_text(encoding="utf-8"))
        records[record["benchmark"]] = record
    return records


def par2(record: dict) -> float:
    if record["solved"]:
        return float(record["wall_seconds"])
    return 2.0 * float(record["timeout_seconds"])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "commit_dir",
        type=Path,
        help="directory containing baseline/, full_add/, consec_core/, ...",
    )
    parser.add_argument("--baseline", default="baseline")
    args = parser.parse_args()

    strategies = {
        path.name: load_strategy(path)
        for path in sorted(args.commit_dir.iterdir())
        if path.is_dir() and list(path.glob("case-*.json"))
    }
    if args.baseline not in strategies:
        parser.error(f"missing baseline results: {args.commit_dir / args.baseline}")

    common = set.intersection(*(set(records) for records in strategies.values()))
    if not common:
        parser.error("strategies have no completed benchmarks in common")

    baseline_records = strategies[args.baseline]
    baseline_total = sum(par2(baseline_records[name]) for name in common)
    baseline_solved = sum(baseline_records[name]["solved"] for name in common)

    summary = {}
    for strategy, records in strategies.items():
        total = sum(par2(records[name]) for name in common)
        solved = sum(records[name]["solved"] for name in common)
        summary[strategy] = {
            "completed_cases": len(records),
            "common_cases": len(common),
            "solved": solved,
            "solved_delta_vs_baseline": solved - baseline_solved,
            "par2_total": total,
            "par2_mean": total / len(common),
            "par2_improvement_vs_baseline": baseline_total - total,
        }

    fixed_names = [
        name
        for name in ("baseline", "consec_core", "full_add")
        if name in strategies
    ]
    oracle_total = 0.0
    oracle_solved = 0
    oracle_winners = {}
    for benchmark in sorted(common):
        choices = [
            (par2(strategies[name][benchmark]), name)
            for name in fixed_names
        ]
        best_score, best_name = min(choices)
        oracle_total += best_score
        oracle_solved += int(any(
            strategies[name][benchmark]["solved"] for name in fixed_names
        ))
        oracle_winners[benchmark] = best_name

    output = {
        "commit_dir": str(args.commit_dir),
        "common_cases": len(common),
        "strategies": summary,
        "fixed_arm_oracle": {
            "arms": fixed_names,
            "solved": oracle_solved,
            "par2_total": oracle_total,
            "par2_mean": oracle_total / len(common),
            "winners": oracle_winners,
        },
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
