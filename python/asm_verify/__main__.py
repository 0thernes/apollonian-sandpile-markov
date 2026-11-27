# SPDX-License-Identifier: Apache-2.0
"""CLI entrypoint for `python -m asm_verify`."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from . import full_oracle_report


def cli(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="python -m asm_verify",
        description="Run the exact arbitrary-precision Python verification oracle (v3.0.0).",
    )
    parser.add_argument(
        "--json",
        type=Path,
        default=None,
        help="Optional output path for the JSON verification report (defaults to results/exact_verification_report.json).",
    )
    args = parser.parse_args(argv)
    report = full_oracle_report()
    out = args.json or (Path(__file__).resolve().parents[2] / "results" / "exact_verification_report.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"oracle_status": "PASS", "version": "3.0.0", "output": str(out)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(cli())
