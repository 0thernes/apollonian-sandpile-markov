#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Verify results/lean_axioms.txt obeys a strict axiom allowlist and matches README.md verbatim."""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    axioms_file = ROOT / "results" / "lean_axioms.txt"
    readme_file = ROOT / "README.md"
    if not axioms_file.exists():
        print(f"ERROR: missing {axioms_file}", file=sys.stderr)
        return 1
    if not readme_file.exists():
        print(f"ERROR: missing {readme_file}", file=sys.stderr)
        return 1

    axioms_text = axioms_file.read_text(encoding="utf-8").strip().replace("\r\n", "\n")
    readme_text = readme_file.read_text(encoding="utf-8").replace("\r\n", "\n")

    # Strict allowlist parsing of every `'decl' depends on axioms: [...]` block (may wrap across lines)
    decl_pat = re.compile(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]", flags=re.DOTALL)
    matches = decl_pat.findall(axioms_text)
    if len(matches) < 19:
        print(
            f"ERROR: expected >= 19 audited declarations in {axioms_file}, parsed {len(matches)}",
            file=sys.stderr,
        )
        return 1

    for decl, raw_axioms in matches:
        used = {tok.strip() for tok in raw_axioms.split(",") if tok.strip()}
        unpermitted = used - ALLOWED_AXIOMS
        if unpermitted:
            print(
                f"ERROR: declaration {decl!r} uses unpermitted axioms {sorted(unpermitted)}",
                file=sys.stderr,
            )
            return 1

    if axioms_text not in readme_text:
        print("ERROR: README.md does not contain verbatim results/lean_axioms.txt block!", file=sys.stderr)
        return 1

    print(
        f"OK: {len(matches)} audited declarations strictly within {sorted(ALLOWED_AXIOMS)} "
        f"and reproduced verbatim in README.md ({len(axioms_text.splitlines())} lines)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
