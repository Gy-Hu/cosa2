#!/usr/bin/env python3
"""Run one CEGP/IC3IA benchmark and emit a structured JSON record."""

from __future__ import annotations

import argparse
import json
import os
import resource
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path


STRATEGY_FLAGS = {
    "baseline": [],
    "full_reduce": [],
    "consec_core": ["--no-cegp-nonconsec-axiom-red"],
    "full_add": [
        "--no-cegp-nonconsec-axiom-red",
        "--no-cegp-consec-axiom-red",
    ],
    "ucb": ["--cegp-bandit"],
}


def parse_result(stdout: str) -> str:
    for line in stdout.splitlines():
        value = line.strip().lower()
        if value in {"sat", "unsat", "unknown"}:
            return value
    return "missing"


def tail(text: str, lines: int = 80) -> str:
    return "\n".join(text.splitlines()[-lines:])


def atomic_write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w", encoding="utf-8", dir=path.parent, delete=False
    ) as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")
        temporary = Path(handle.name)
    temporary.replace(path)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--strategy", choices=sorted(STRATEGY_FLAGS), required=True)
    parser.add_argument("--benchmark", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=1000.0)
    parser.add_argument("--pono", default="./build/pono")
    parser.add_argument("--smt-solver", default="cvc5")
    parser.add_argument("--smt-interpolator", default="cvc5")
    parser.add_argument("--verbosity", type=int, default=0)
    args = parser.parse_args()

    benchmark = Path(args.benchmark)
    pono = Path(args.pono)
    if not benchmark.is_file():
        parser.error(f"benchmark does not exist: {benchmark}")
    if not pono.is_file():
        parser.error(f"Pono executable does not exist: {pono}")

    command = [
        str(pono),
        "--engine",
        "ic3ia",
        "--bound",
        "2147483646",
        "--pseudo-init-prop",
        "--ceg-prophecy-arrays",
        "--smt-solver",
        args.smt_solver,
        "--smt-interpolator",
        args.smt_interpolator,
        "--verbosity",
        str(args.verbosity),
        *STRATEGY_FLAGS[args.strategy],
        str(benchmark),
    ]

    started_at = datetime.now(timezone.utc)
    started = time.monotonic()
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    timed_out = False
    try:
        completed = subprocess.run(
            command,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=args.timeout,
            check=False,
            env=os.environ.copy(),
        )
        returncode = completed.returncode
        stdout = completed.stdout
        stderr = completed.stderr
    except subprocess.TimeoutExpired as error:
        timed_out = True
        returncode = 124
        stdout = error.stdout or ""
        stderr = error.stderr or ""
        if isinstance(stdout, bytes):
            stdout = stdout.decode(errors="replace")
        if isinstance(stderr, bytes):
            stderr = stderr.decode(errors="replace")
    finished = time.monotonic()
    after = resource.getrusage(resource.RUSAGE_CHILDREN)

    result = parse_result(stdout)
    solved = not timed_out and returncode == 0 and result in {"sat", "unsat"}
    payload = {
        "schema_version": 1,
        "strategy": args.strategy,
        "smt_solver": args.smt_solver,
        "smt_interpolator": args.smt_interpolator,
        "benchmark": str(benchmark),
        "command": command,
        "timeout_seconds": args.timeout,
        "started_at_utc": started_at.isoformat(),
        "finished_at_utc": datetime.now(timezone.utc).isoformat(),
        "wall_seconds": finished - started,
        "cpu_user_seconds": after.ru_utime - before.ru_utime,
        "cpu_system_seconds": after.ru_stime - before.ru_stime,
        "max_rss_kib": after.ru_maxrss,
        "hostname": os.uname().nodename,
        "lsf_job_id": os.environ.get("LSB_JOBID"),
        "lsf_job_index": os.environ.get("LSB_JOBINDEX"),
        "returncode": returncode,
        "timed_out": timed_out,
        "result": result,
        "solved": solved,
        "stdout_tail": tail(stdout),
        "stderr_tail": tail(stderr),
    }
    atomic_write_json(args.output, payload)
    print(json.dumps({key: payload[key] for key in (
        "strategy", "benchmark", "result", "solved", "wall_seconds"
    )}, sort_keys=True))
    return 0 if solved else returncode or 2


if __name__ == "__main__":
    sys.exit(main())
