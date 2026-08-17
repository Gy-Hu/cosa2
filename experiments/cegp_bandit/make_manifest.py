#!/usr/bin/env python3
"""Build a deterministic manifest from a BTOR2 benchmark directory."""

from __future__ import annotations

import argparse
from pathlib import Path


def count_bad_properties(path: Path) -> int:
    count = 0
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        fields = line.split()
        if len(fields) >= 2 and fields[1] == "bad":
            count += 1
    return count


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--benchmark-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--expect-count", type=int)
    parser.add_argument(
        "--require-one-bad",
        action="store_true",
        help="fail unless every BTOR2 file contains exactly one bad property",
    )
    args = parser.parse_args()

    paths = sorted(args.benchmark_root.rglob("*.btor2"))
    if args.expect_count is not None and len(paths) != args.expect_count:
        parser.error(f"expected {args.expect_count} files, found {len(paths)}")
    if args.require_one_bad:
        invalid = [(path, count_bad_properties(path)) for path in paths]
        invalid = [(path, count) for path, count in invalid if count != 1]
        if invalid:
            details = ", ".join(f"{path} ({count})" for path, count in invalid)
            parser.error(f"files without exactly one bad property: {details}")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        "".join(f"{path.as_posix()}\n" for path in paths), encoding="utf-8"
    )
    print(f"wrote {len(paths)} benchmarks to {args.output}")


if __name__ == "__main__":
    main()
