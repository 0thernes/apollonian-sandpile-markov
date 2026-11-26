# SPDX-License-Identifier: Apache-2.0
"""Comprehensive pytest + Hypothesis + Rust/C11/Python differential test suite."""

from __future__ import annotations

import json
import math
import shutil
import subprocess
import sys
from pathlib import Path

import pytest
from hypothesis import given, settings, strategies as st

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "python"))

import asm_verify as av  # noqa: E402


# --- 1. Property-based tests (Hypothesis) ---

@given(
    m=st.integers(min_value=1, max_value=2000).map(lambda k: 2 * k + 1),
    n=st.integers(min_value=1, max_value=2000).map(lambda k: 2 * k + 1),
)
@settings(max_examples=200)
def test_hypothesis_gauss_quadratic_reciprocity(m: int, n: int) -> None:
    if math.gcd(m, n) == 1:
        expected = -1 if (m % 4 == 3 and n % 4 == 3) else 1
        assert av.jacobi(m, n) * av.jacobi(n, m) == expected
    else:
        assert av.jacobi(m, n) == 0
    assert av.jacobi(-1, n) == (1 if n % 4 == 1 else -1)
    assert av.jacobi(2, n) == (1 if n % 8 in (1, 7) else -1)


@given(
    a=st.integers(min_value=-500, max_value=500),
    b=st.integers(min_value=-500, max_value=500),
    c=st.integers(min_value=-500, max_value=500),
    d=st.integers(min_value=-500, max_value=500),
    idx=st.integers(min_value=0, max_value=3),
)
@settings(max_examples=200)
def test_hypothesis_descartes_involution_and_invariance(
    a: int, b: int, c: int, d: int, idx: int
) -> None:
    q = (a, b, c, d)
    q1 = av.apollonian_refl(q, idx)
    assert av.apollonian_refl(q1, idx) == q
    assert av.descartes_q(q1) == av.descartes_q(q)


@given(
    x1=st.integers(min_value=1, max_value=10),
    x2=st.integers(min_value=1, max_value=10),
    x3=st.integers(min_value=1, max_value=10),
)
@settings(max_examples=120)
def test_hypothesis_markov_5step_cluster_laurent(x1: int, x2: int, x3: int) -> None:
    p1, p2, p3, p4, p5 = av.markov_cluster_5step(x1, x2, x3)
    assert p1 > 0 and p2 > 0 and p3 > 0 and p4 > 0 and p5 > 0
    assert p1 * p4 == (x1**4) * (x2**2) * (x3**2) * p2 * p2 + p3 * p3
    assert p2 * p5 == (x1**6) * (x2**4) * (x3**2) * p3 * p3 + p4 * p4


@given(
    lattice=st.sampled_from(["Z2", "A2"]),
    chips=st.lists(st.integers(min_value=0, max_value=10), min_size=9, max_size=9),
)
@settings(max_examples=80)
def test_hypothesis_sandpile_abelian_confluence(lattice: str, chips: list[int]) -> None:
    # Stabilize directly vs adding half then remaining half — Abelian property
    s_direct, odo_direct = av.stabilize_sandpile(lattice, 3, chips)
    half1 = [v // 2 for v in chips]
    half2 = [v - v // 2 for v in chips]
    s_mid, odo1 = av.stabilize_sandpile(lattice, 3, half1)
    s_split, odo2 = av.stabilize_sandpile(lattice, 3, [a + b for a, b in zip(s_mid, half2)])
    assert s_direct == s_split
    assert odo_direct == [a + b for a, b in zip(odo1, odo2)]


# --- 2. Golden & Metamorphic tests ---

def test_pillar1_apollonian_and_octahedral_obstructions() -> None:
    for root in [(-3, 5, 8, 8), (-7, 17, 12, 20), (-11, 21, 24, 28)]:
        res = av.audit_apollonian_packing(root, 600)
        assert res["all_descartes_zero"] is True
        assert res["squares"] == []
    a2 = av.audit_apollonian_packing((-7, 17, 12, 20), 600)
    au = av.audit_apollonian_packing((-4, 8, 9, 9), 600)
    assert a2["mod24"] == au["mod24"]
    assert 9 in au["squares"]

    oct_obs = av.audit_octahedral_packing((-6, 10, 17, 40, 24, 17), 1200)
    oct_str = av.audit_octahedral_packing((0, 0, 1, 2, 2, 1), 300)
    assert oct_obs["all_octahedral"] is True
    assert oct_obs["pow2_squares"] == []
    assert oct_obs["mod24"] == oct_str["mod24"]
    assert 1 in oct_str["pow2_squares"] and 2 in oct_str["pow2_squares"]


def test_pillar2_z2_vs_a2_sandpile_identities() -> None:
    e_z2_3 = av.dhar_identity("Z2", 3)
    assert e_z2_3 == [2, 1, 2, 1, 0, 1, 2, 1, 2]
    e_a2_3 = av.dhar_identity("A2", 3)
    assert e_a2_3 == [4, 2, 3, 2, 0, 2, 3, 2, 4]
    # Check idempotence and symmetry
    ee, _ = av.stabilize_sandpile("A2", 3, [v + v for v in e_a2_3])
    assert ee == e_a2_3
    # Verify A2 even-Laplacian witnesses on a 7x7 window
    for x in range(-3, 4):
        for y in range(-3, 4):
            def u4(ix: int, iy: int) -> int:
                return (ix * (ix - 1)) // 2 + (iy * (iy - 1)) // 2

            lap = (
                u4(x + 1, y) + u4(x - 1, y) + u4(x, y + 1) + u4(x, y - 1)
                + u4(x + 1, y - 1) + u4(x - 1, y + 1) - 6 * u4(x, y)
            )
            assert lap == 4


def test_pillar3_markov_mod32_and_cluster() -> None:
    mk = av.audit_markov_tree(100_000)
    assert mk["uniqueness_holds"] is True
    assert mk["all_odd_mod4_eq1"] is True
    assert mk["all_even_mod32_eq2"] is True
    assert mk["even_mod64_residues"] == [2, 34]
    assert av.markov_cluster_5step(1, 1, 1) == (2, 5, 29, 433, 37_666)


# --- 3. Negative / boundary tests ---

def test_negative_inputs_rejected() -> None:
    with pytest.raises(ValueError):
        av.jacobi(3, 0)
    with pytest.raises(ValueError):
        av.jacobi(3, 4)
    with pytest.raises(ValueError):
        av.jacobi(3, -5)
    assert av.is_perfect_square(-4) is False
    assert av.is_perfect_square(0) is True
    assert av.is_perfect_square(15) is False


# --- 4. Differential Rust <-> Python <-> C11 cross-verification ---

def test_differential_rust_python_consistency() -> None:
    rust_json = ROOT / "results" / "rust_summary.json"
    if not rust_json.exists():
        pytest.skip("rust_summary.json not generated yet")
    rs = json.loads(rust_json.read_text(encoding="utf-8"))
    py = av.full_oracle_report()

    # Exact bit-for-bit agreement across all 3 pillars!
    assert rs["pillar1"]["hkrs_root1"]["quads"] == py["pillar1"]["hkrs_root1"]["quads_visited"]
    assert rs["pillar1"]["hkrs_root2"]["quads"] == py["pillar1"]["hkrs_root2"]["quads_visited"]
    assert rs["pillar1"]["hkrs_root3"]["quads"] == py["pillar1"]["hkrs_root3"]["quads_visited"]
    assert rs["pillar1"]["unobstructed_4899"]["quads"] == py["pillar1"]["unobstructed_4899"]["quads_visited"]
    assert rs["pillar1"]["octahedral_obstructed"]["sextuples"] == py["pillar1"]["octahedral_obstructed"]["sextuples_visited"]
    assert rs["pillar1"]["octahedral_obstructed"]["mod24"] == py["pillar1"]["octahedral_obstructed"]["mod24"]
    assert rs["pillar2"]["z2_15x15"]["sum_chips"] == py["pillar2"]["z2_15x15_sum"]
    assert rs["pillar2"]["a2_15x15"]["sum_chips"] == py["pillar2"]["a2_15x15_sum"]
    assert rs["pillar3"]["cluster_5step_at_111"] == py["pillar3"]["cluster_5step_at_111"]
    assert rs["pillar3"]["even_mod64_residues"] == py["pillar3"]["markov_1e6"]["even_mod64_residues"]


def test_c11_independent_binary_if_built() -> None:
    for name in ("asm_verify.exe", "asm_verify"):
        cand = ROOT / "native" / name
        if cand.exists():
            proc = subprocess.run([str(cand)], capture_output=True, text=True, check=True)
            data = json.loads(proc.stdout)
            assert data["c11_status"] == "PASS"
            return
    if shutil.which("gcc") is None:
        pytest.skip("C11 binary not built in this environment")
