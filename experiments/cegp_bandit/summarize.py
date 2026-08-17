#!/usr/bin/env python3
"""Summarize CEGP experiment JSON files and compute PAR-2."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def is_solved(record: dict) -> bool:
    return not record["timed_out"] and record["result"] in {"sat", "unsat"}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("result_dir", type=Path)
    args = parser.parse_args()

    records = []
    for path in sorted(args.result_dir.glob("case-*.json")):
        records.append(json.loads(path.read_text(encoding="utf-8")))
    if not records:
        parser.error(f"no case-*.json files found in {args.result_dir}")

    rows = []
    total_par2 = 0.0
    solved = 0
    for record in records:
        penalty = 2.0 * float(record["timeout_seconds"])
        record_solved = is_solved(record)
        score = float(record["wall_seconds"]) if record_solved else penalty
        total_par2 += score
        solved += int(record_solved)
        rows.append(
            {
                "benchmark": record["benchmark"],
                "result": record["result"],
                "solved": record_solved,
                "wall_seconds": record["wall_seconds"],
                "par2": score,
            }
        )

    summary = {
        "strategy": records[0]["strategy"],
        "cases": len(records),
        "solved": solved,
        "sat": sum(record["result"] == "sat" for record in records),
        "unsat": sum(record["result"] == "unsat" for record in records),
        "timeouts": sum(record["timed_out"] for record in records),
        "par2_total": total_par2,
        "par2_mean": total_par2 / len(records),
        "rows": rows,
    }
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
