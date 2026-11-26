# SPDX-License-Identifier: Apache-2.0
"""Targeted mutation-testing harness for python/asm_verify/__init__.py (target: 100% kill rate)."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "python" / "asm_verify" / "__init__.py"

MUTANTS = [
    ("M01_jacobi_flip_mod8", "if n % 8 in (3, 5):", "if n % 8 in (3, 7):"),
    ("M02_jacobi_flip_qr", "if a % 4 == 3 and n % 4 == 3:", "if a % 4 == 1 and n % 4 == 3:"),
    ("M03_descartes_coeff", "return s * s - 2 * sum(v * v for v in q)", "return s * s - 3 * sum(v * v for v in q)"),
    ("M04_refl_factor", "arr[idx] = 2 * (sum(q) - q[idx]) - q[idx]", "arr[idx] = 3 * (sum(q) - q[idx]) - q[idx]"),
    ("M05_oct_delta", "delta = 4 * (f1 + f2 + f3) - 2 * s", "delta = 4 * (f1 + f2 + f3) - 2 * s + 1"),
    ("M06_sandpile_deg_a2", 'deg = 4 if lattice == "Z2" else 6', 'deg = 4 if lattice == "Z2" else 7'),
    ("M07_markov_mod32", "if m % 32 != 2:", "if m % 32 != 0:"),
    ("M08_cluster_p2", "p2 = p1 * p1 + v", "p2 = p1 * p1 + 2 * v"),
]


def main() -> int:
    orig = TARGET.read_text(encoding="utf-8")
    killed = 0
    results = []
    for name, old, new in MUTANTS:
        assert old in orig, f"Mutation anchor missing: {name}"
        mutated = orig.replace(old, new, 1)
        with tempfile.TemporaryDirectory() as td:
            td_path = Path(td)
            pkg = td_path / "python" / "asm_verify"
            pkg.mkdir(parents=True)
            (pkg / "__init__.py").write_text(mutated, encoding="utf-8")
            tests_copy = td_path / "tests"
            tests_copy.mkdir()
            (tests_copy / "test_all.py").write_text(
                (ROOT / "tests" / "test_all.py").read_text(encoding="utf-8"),
                encoding="utf-8",
            )
            try:
                proc = subprocess.run(
                    [sys.executable, "-m", "pytest", "-q", "-x", str(tests_copy / "test_all.py")],
                    capture_output=True,
                    text=True,
                    timeout=20,
                )
                is_killed = proc.returncode != 0
            except subprocess.TimeoutExpired:
                is_killed = True
            if is_killed:
                killed += 1
            results.append({"mutant": name, "killed": is_killed})
    rate = 100.0 * killed / len(MUTANTS)
    out = {"killed": killed, "total": len(MUTANTS), "kill_rate_pct": rate, "details": results}
    print(json.dumps(out, indent=2))
    return 0 if killed == len(MUTANTS) else 1


if __name__ == "__main__":
    raise SystemExit(main())
