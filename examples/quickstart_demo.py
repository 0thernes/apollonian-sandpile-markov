# SPDX-License-Identifier: Apache-2.0
"""Quickstart demonstration of all three mathematical pillars (runs in < 1 second)."""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "python"))
import asm_verify as av


def main() -> None:
    print("=== Pillar I: Apollonian & Generalized Octahedral Reciprocity ===")
    a2 = av.audit_apollonian_packing((-7, 17, 12, 20), 300)
    au = av.audit_apollonian_packing((-4, 8, 9, 9), 300)
    print(f"  Obstructed (-7,17,12,20): quads={a2['quads_visited']}, squares={a2['squares']}, mod24={a2['mod24']}")
    print(f"  Unobstructed (-4,8,9,9):  quads={au['quads_visited']}, squares={au['squares'][:5]}..., mod24={au['mod24']}")
    oct_o = av.audit_octahedral_packing((-6, 10, 17, 40, 24, 17), 500)
    print(f"  Octahedral (-6,10,17,40,24,17): sextuples={oct_o['sextuples_visited']}, 2^k*m^2 hits={oct_o['pow2_squares']}")

    print("\n=== Pillar II: Z^2 vs Triangular A_2 Abelian Sandpile Identity ===")
    print(f"  Z^2 3x3 Dhar identity: {av.dhar_identity('Z2', 3)}")
    print(f"  A_2 3x3 Dhar identity: {av.dhar_identity('A2', 3)}")

    print("\n=== Pillar III: Markov Mod-32 Theorem & 5-Step Cluster Laurent ===")
    mk = av.audit_markov_tree(10_000)
    print(f"  Markov <= 10^4: triples={mk['triples_count']}, unique={mk['uniqueness_holds']}, even_mod32={mk['all_even_mod32_eq2']}, even_mod64={mk['even_mod64_residues']}")
    print(f"  5-step cluster specialization at (1,1,1): {av.markov_cluster_5step(1, 1, 1)}")


if __name__ == "__main__":
    main()
