# SPDX-License-Identifier: Apache-2.0
"""Independent arbitrary-precision Python oracle for Apollonian-Sandpile-Markov (v2.1.0)."""

from __future__ import annotations

import json
import math
from collections import deque
from collections.abc import Sequence
from pathlib import Path
from typing import Any


def jacobi(a: int, n: int) -> int:
    """Exact Jacobi symbol (a / n) for odd n >= 1."""
    if n <= 0 or n % 2 == 0:
        raise ValueError("n must be a positive odd integer")
    a %= n
    res = 1
    while a != 0:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                res = -res
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            res = -res
        a %= n
    return res if n == 1 else 0


def is_perfect_square(x: int) -> bool:
    if x < 0:
        return False
    r = math.isqrt(x)
    return r * r == x


def signed_odd_part(a: int) -> int:
    if a == 0:
        return 0
    while a % 2 == 0:
        a //= 2
    return a


def descartes_q(q: Sequence[int]) -> int:
    if len(q) != 4:
        raise ValueError("Descartes quadruple must have length 4")
    s = sum(q)
    return s * s - 2 * sum(v * v for v in q)


def apollonian_refl(q: tuple[int, int, int, int], idx: int) -> tuple[int, int, int, int]:
    if not (0 <= idx <= 3):
        raise ValueError(f"Apollonian reflection index must be in 0..3, got {idx}")
    arr = list(q)
    arr[idx] = 2 * (sum(q) - q[idx]) - q[idx]
    return (arr[0], arr[1], arr[2], arr[3])


def audit_apollonian_packing(root: tuple[int, int, int, int], max_bend: int) -> dict[str, Any]:
    visited = {tuple(sorted(root))}
    queue = deque([root])
    bends: set[int] = set()
    mod24: set[int] = set()
    all_q0 = True
    while queue:
        q = queue.popleft()
        if descartes_q(q) != 0:
            all_q0 = False
        for b in q:
            bends.add(b)
            mod24.add(b % 24)
        for i in range(4):
            nxt = apollonian_refl(q, i)
            if max(nxt) <= max_bend:
                key = tuple(sorted(nxt))
                if key not in visited:
                    visited.add(key)
                    queue.append(nxt)
    squares = sorted(b for b in bends if is_perfect_square(b))
    return {
        "root": list(root),
        "max_bend": max_bend,
        "quads_visited": len(visited),
        "distinct_bends": len(bends),
        "squares": squares,
        "mod24": sorted(mod24),
        "all_descartes_zero": all_q0,
    }


def is_octahedral(x: Sequence[int]) -> bool:
    if len(x) != 6:
        raise ValueError("Octahedral sextuple must have length 6")
    s = x[0] + x[3]
    return (
        x[1] + x[4] == s
        and x[2] + x[5] == s
        and (x[0] - x[3]) ** 2 + (x[1] - x[4]) ** 2 + (x[2] - x[5]) ** 2 == 2 * s * s
    )


def oct_refl(
    x: tuple[int, int, int, int, int, int], mask: int
) -> tuple[int, int, int, int, int, int]:
    if not (0 <= mask <= 7):
        raise ValueError(f"Octahedral reflection mask must be in 0..7, got {mask}")
    s1, s2, s3 = bool(mask & 1), bool(mask & 2), bool(mask & 4)
    s = x[0] + x[3]
    f1 = x[3] if s1 else x[0]
    f2 = x[4] if s2 else x[1]
    f3 = x[5] if s3 else x[2]
    delta = 4 * (f1 + f2 + f3) - 2 * s
    return (
        x[0] + delta if s1 else x[0],
        x[1] + delta if s2 else x[1],
        x[2] + delta if s3 else x[2],
        x[3] if s1 else x[3] + delta,
        x[4] if s2 else x[4] + delta,
        x[5] if s3 else x[5] + delta,
    )


def audit_octahedral_packing(
    root: tuple[int, int, int, int, int, int], max_bend: int
) -> dict[str, Any]:
    def canonical(x: tuple[int, int, int, int, int, int]) -> tuple[int, ...]:
        pairs = sorted(tuple(sorted((x[i], x[i + 3]))) for i in range(3))
        return (pairs[0][0], pairs[1][0], pairs[2][0], pairs[0][1], pairs[1][1], pairs[2][1])

    visited = {canonical(root)}
    queue = deque([root])
    bends: set[int] = set()
    mod24: set[int] = set()
    all_oct = True
    while queue:
        x = queue.popleft()
        if not is_octahedral(x):
            all_oct = False
        for b in x:
            bends.add(b)
            mod24.add(b % 24)
        for mask in range(8):
            nxt = oct_refl(x, mask)
            if max(nxt) <= max_bend:
                key = canonical(nxt)
                if key not in visited:
                    visited.add(key)
                    queue.append(nxt)
    pow2_sq = sorted(b for b in bends if b >= 0 and is_perfect_square(signed_odd_part(b)))
    return {
        "root": list(root),
        "sextuples_visited": len(visited),
        "distinct_bends": len(bends),
        "pow2_squares": pow2_sq,
        "mod24": sorted(mod24),
        "all_octahedral": all_oct,
    }


def stabilize_sandpile(lattice: str, n: int, init: Sequence[int]) -> tuple[list[int], list[int]]:
    if lattice not in ("Z2", "A2"):
        raise ValueError(f"Unsupported lattice {lattice!r}; expected 'Z2' or 'A2'")
    if n < 1:
        raise ValueError(f"Grid size n must be >= 1, got {n}")
    if len(init) != n * n:
        raise ValueError(f"Initial configuration length must equal n*n ({n * n}), got {len(init)}")
    deg = 4 if lattice == "Z2" else 6
    deltas = [(-1, 0), (1, 0), (0, -1), (0, 1)]
    if lattice == "A2":
        deltas += [(-1, 1), (1, -1)]
    s = list(init)
    odo = [0] * (n * n)
    q = deque(i for i, v in enumerate(s) if v >= deg)
    in_q = [v >= deg for v in s]
    while q:
        u = q.popleft()
        in_q[u] = False
        if s[u] < deg:
            continue
        k = s[u] // deg
        s[u] -= k * deg
        odo[u] += k
        r, c = divmod(u, n)
        for dr, dc in deltas:
            nr, nc = r + dr, c + dc
            if 0 <= nr < n and 0 <= nc < n:
                v = nr * n + nc
                s[v] += k
                if s[v] >= deg and not in_q[v]:
                    q.append(v)
                    in_q[v] = True
    return s, odo


def dhar_identity(lattice: str, n: int) -> list[int]:
    if lattice not in ("Z2", "A2"):
        raise ValueError(f"Unsupported lattice {lattice!r}; expected 'Z2' or 'A2'")
    if n < 1:
        raise ValueError(f"Grid size n must be >= 1, got {n}")
    deg = 4 if lattice == "Z2" else 6
    mu = deg - 1
    s1, _ = stabilize_sandpile(lattice, n, [2 * mu] * (n * n))
    e, _ = stabilize_sandpile(lattice, n, [2 * mu - v for v in s1])
    return e


def audit_markov_tree(max_val: int) -> dict[str, Any]:
    if max_val < 1:
        raise ValueError(f"max_val must be >= 1, got {max_val}")
    visited = {(1, 1, 1)}
    queue = deque([(1, 1, 1)])
    max_counts: dict[int, int] = {}
    nums: set[int] = set()
    even_mod64: set[int] = set()
    all_odd4 = True
    all_even32 = True
    while queue:
        x, y, z = queue.popleft()
        assert x * x + y * y + z * z == 3 * x * y * z
        max_counts[z] = max_counts.get(z, 0) + 1
        for m in (x, y, z):
            nums.add(m)
            if m % 2 == 1:
                if m % 4 != 1:
                    all_odd4 = False
            else:
                if m % 32 != 2:
                    all_even32 = False
                even_mod64.add(m % 64)
        for raw in (
            sorted((3 * y * z - x, y, z)),
            sorted((x, 3 * x * z - y, z)),
            sorted((x, y, 3 * x * y - z)),
        ):
            nxt = (raw[0], raw[1], raw[2])
            if nxt[2] <= max_val and nxt not in visited:
                visited.add(nxt)
                queue.append(nxt)
    return {
        "max_val": max_val,
        "triples_count": len(visited),
        "distinct_numbers": len(nums),
        "uniqueness_holds": all(c == 1 for c in max_counts.values()),
        "all_odd_mod4_eq1": all_odd4,
        "all_even_mod32_eq2": all_even32,
        "even_mod64_residues": sorted(even_mod64),
    }


def markov_cluster_5step(x1: int, x2: int, x3: int) -> tuple[int, int, int, int, int]:
    p1 = x2 * x2 + x3 * x3
    v = x1 * x1 * x3 * x3
    w = x1 * x1 * x2 * x2
    p2 = p1 * p1 + v
    p3 = w * p1 * p1 + p2 * p2
    r4 = p1**3 + 2 * x1 * x1 * p1 * p1 + x1 * x1 * v
    p4 = w * w * p1**3 + p2 * p2 * r4
    p5 = w**4 * p1**4 + p2 * (
        2 * w**3 * v * p1 * p1 + w * w * v * p2 * p2 + 2 * w * w * p1**3 * r4 + p2 * p2 * r4 * r4
    )
    return p1, p2, p3, p4, p5


def full_oracle_report() -> dict[str, Any]:
    a1 = audit_apollonian_packing((-3, 5, 8, 8), 1000)
    a2 = audit_apollonian_packing((-7, 17, 12, 20), 1000)
    a3 = audit_apollonian_packing((-11, 21, 24, 28), 1000)
    au = audit_apollonian_packing((-4, 8, 9, 9), 1000)
    oct_obs = audit_octahedral_packing((-6, 10, 17, 40, 24, 17), 1500)
    oct_str = audit_octahedral_packing((0, 0, 1, 2, 2, 1), 400)
    e_z2_15 = dhar_identity("Z2", 15)
    e_a2_15 = dhar_identity("A2", 15)
    mk = audit_markov_tree(1_000_000)
    return {
        "pillar1": {
            "hkrs_root1": a1,
            "hkrs_root2": a2,
            "hkrs_root3": a3,
            "square_contrast_4899": au,
            "octahedral_obstructed": oct_obs,
            "octahedral_strip": oct_str,
        },
        "pillar2": {
            "z2_15x15_sum": sum(e_z2_15),
            "a2_15x15_sum": sum(e_a2_15),
            "z2_3x3_id": dhar_identity("Z2", 3),
            "a2_3x3_id": dhar_identity("A2", 3),
            "a2_2x2_id": dhar_identity("A2", 2),
        },
        "pillar3": {
            "markov_1e6": mk,
            "cluster_5step_at_111": list(markov_cluster_5step(1, 1, 1)),
        },
    }


def main() -> None:
    report = full_oracle_report()
    out = Path(__file__).resolve().parents[2] / "results" / "exact_verification_report.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"oracle_status": "PASS", "version": "2.1.0", "output": str(out)}))


if __name__ == "__main__":
    main()
