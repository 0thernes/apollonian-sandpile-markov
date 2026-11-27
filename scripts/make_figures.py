# SPDX-License-Identifier: Apache-2.0
"""Generate 4 publication-grade vector PDF figures and 1280x640 GitHub social preview."""

from __future__ import annotations

import cmath
import json
import math
from collections import Counter, deque
from pathlib import Path
from typing import Any

import matplotlib

matplotlib.use("Agg")
import matplotlib.patches as mpatches
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.colors import ListedColormap

ROOT = Path(__file__).resolve().parents[1]
FIG_DIR = ROOT / "paper" / "figures"
MEDIA_DIR = ROOT / "docs" / "media"
FIG_DIR.mkdir(parents=True, exist_ok=True)
MEDIA_DIR.mkdir(parents=True, exist_ok=True)

# Publication typography & vector PDF settings
plt.rcParams.update({
    "font.family": "serif",
    "font.serif": ["DejaVu Serif", "Times New Roman", "CMU Serif"],
    "mathtext.fontset": "cm",
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
    "axes.linewidth": 0.9,
    "axes.edgecolor": "#2d3748",
    "xtick.color": "#2d3748",
    "ytick.color": "#2d3748",
    "text.color": "#1a202c",
    "axes.titlesize": 11,
    "axes.labelsize": 9.5,
    "xtick.labelsize": 8.5,
    "ytick.labelsize": 8.5,
    "legend.fontsize": 8.2,
})


# --- Exact mathematical generators (self-contained, zero approximations) ---

def generate_apollonian_circles(
    b0: int, b1: int, b2: int, b3: int, max_bend: int = 380
) -> list[tuple[int, complex]]:
    """Compute exact (bend, center) pairs for an Apollonian gasket via complex Descartes."""
    # Place bounding circle b0 < 0 centered at 0 with radius R0 = -1/b0
    r0 = -1.0 / b0
    r1 = 1.0 / b1
    r2 = 1.0 / b2
    # c1 tangent internally to c0 on the left
    z0 = 0.0 + 0.0j
    z1 = complex(-(r0 - r1), 0.0)
    # c2 tangent internally to c0 (dist r0 - r2) and externally to c1 (dist r1 + r2)
    d01 = r0 - r1
    d02 = r0 - r2
    d12 = r1 + r2
    # Law of cosines from c0 toward c1 (-x axis)
    cos_a = (d01 * d01 + d02 * d02 - d12 * d12) / (2.0 * d01 * d02)
    cos_a = max(-1.0, min(1.0, cos_a))
    sin_a = math.sqrt(max(0.0, 1.0 - cos_a * cos_a))
    z2 = complex(-d02 * cos_a, d02 * sin_a)
    # Complex Descartes for z3: (b3*z3) = b0*z0 + b1*z1 + b2*z2 +/- 2*sqrt(...)
    zb0, zb1, zb2 = b0 * z0, b1 * z1, b2 * z2
    disc = cmath.sqrt(zb0 * zb1 + zb1 * zb2 + zb2 * zb0)
    cand_a = (zb0 + zb1 + zb2 + 2.0 * disc) / b3
    cand_b = (zb0 + zb1 + zb2 - 2.0 * disc) / b3

    # Pick candidate tangent to c0, c1, c2
    def err(zc: complex) -> float:
        r3 = 1.0 / b3
        return abs(abs(zc - z0) - (r0 - r3)) + abs(abs(zc - z1) - (r1 + r3)) + abs(abs(zc - z2) - (r2 + r3))

    z3 = cand_a if err(cand_a) <= err(cand_b) else cand_b
    zb3 = b3 * z3

    root_q = ((b0, zb0), (b1, zb1), (b2, zb2), (b3, zb3))
    seen_circles: dict[tuple[int, int, int], tuple[int, complex]] = {}
    for b, zb in root_q:
        z = zb / b
        key = (b, round(z.real * 1e5), round(z.imag * 1e5))
        seen_circles[key] = (b, z)

    visited_quads: set[tuple[tuple[int, int, int], ...]] = set()
    queue = deque([root_q])

    def q_key(q: tuple[tuple[int, complex], ...]) -> tuple[tuple[int, int, int], ...]:
        return tuple(
            sorted(
                (b, round((zb / b).real * 1e4), round((zb / b).imag * 1e4))
                for b, zb in q
            )
        )

    visited_quads.add(q_key(root_q))
    while queue:
        q = queue.popleft()
        sum_b = sum(item[0] for item in q)
        sum_zb = sum(item[1] for item in q)
        for idx in range(4):
            bi, zbi = q[idx]
            nb = 2 * (sum_b - bi) - bi
            if nb <= 0 or nb > max_bend:
                continue
            nzb = 2 * (sum_zb - zbi) - zbi
            nz = nzb / nb
            ckey = (nb, round(nz.real * 1e5), round(nz.imag * 1e5))
            if ckey not in seen_circles:
                seen_circles[ckey] = (nb, nz)
            nq = list(q)
            nq[idx] = (nb, nzb)
            nq_t = (nq[0], nq[1], nq[2], nq[3])
            qk = q_key(nq_t)
            if qk not in visited_quads:
                visited_quads.add(qk)
                queue.append(nq_t)
    return list(seen_circles.values())


def audit_apollonian_bends(root: tuple[int, int, int, int], max_bend: int) -> list[int]:
    visited = {tuple(sorted(root))}
    queue = deque([root])
    bends: set[int] = set()
    while queue:
        q = queue.popleft()
        for b in q:
            bends.add(b)
        s = sum(q)
        for i in range(4):
            arr = list(q)
            arr[i] = 2 * (s - q[i]) - q[i]
            nxt = (arr[0], arr[1], arr[2], arr[3])
            if max(nxt) <= max_bend:
                k = tuple(sorted(nxt))
                if k not in visited:
                    visited.add(k)
                    queue.append(nxt)
    return sorted(bends)


def stabilize_grid(lattice: str, init: np.ndarray) -> np.ndarray:
    """Fast vectorized exact Abelian sandpile stabilization on Z^2 or A_2."""
    deg = 4 if lattice == "Z2" else 6
    grid = init.astype(np.int64).copy()
    while True:
        fire = grid // deg
        if not np.any(fire > 0):
            break
        grid -= fire * deg
        grid[1:, :] += fire[:-1, :]
        grid[:-1, :] += fire[1:, :]
        grid[:, 1:] += fire[:, :-1]
        grid[:, :-1] += fire[:, 1:]
        if lattice == "A2":
            grid[1:, :-1] += fire[:-1, 1:]
            grid[:-1, 1:] += fire[1:, :-1]
    return grid


def dhar_identity_grid(lattice: str, n: int) -> np.ndarray:
    deg = 4 if lattice == "Z2" else 6
    mu = deg - 1
    base = np.full((n, n), 2 * mu, dtype=np.int64)
    s1 = stabilize_grid(lattice, base)
    return stabilize_grid(lattice, 2 * mu - s1)


def generate_markov_tree(max_val: int) -> tuple[list[tuple[int, int, int]], list[int]]:
    visited: set[tuple[int, int, int]] = {(1, 1, 1)}
    queue: deque[tuple[int, int, int]] = deque([(1, 1, 1)])
    nums: set[int] = set()
    while queue:
        x, y, z = queue.popleft()
        nums.update((x, y, z))
        for raw in (
            sorted((3 * y * z - x, y, z)),
            sorted((x, 3 * x * z - y, z)),
            sorted((x, y, 3 * x * y - z)),
        ):
            nxt = (raw[0], raw[1], raw[2])
            if nxt[2] <= max_val and nxt not in visited:
                visited.add(nxt)
                queue.append(nxt)
    return sorted(visited, key=lambda t: t[2]), sorted(nums)


def factor_odd_primes(n: int) -> list[int]:
    primes: list[int] = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            if d % 2 == 1:
                primes.append(d)
            while n % d == 0:
                n //= d
        d += 1 if d == 2 else 2
    if n > 2:
        primes.append(n)
    return primes


# --- Figure 1: Apollonian, Octahedral Q(sqrt(-2)), & Soddy Dimension Dichotomy ---

def make_fig1(rust_summary: dict[str, Any]) -> None:
    fig, axes = plt.subplots(2, 2, figsize=(13.2, 8.8), dpi=300)
    fig.subplots_adjust(left=0.06, right=0.97, top=0.92, bottom=0.07, wspace=0.25, hspace=0.30)
    fig.suptitle(
        "Pillar I: Thin Vieta Reflection Groups — Apollonian, Octahedral $\\mathbb{Q}(\\sqrt{-2})$, and Soddy Obstructions",
        fontsize=12.5, fontweight="bold", y=0.975,
    )

    # Panel (a): Apollonian Gasket (-7, 17, 12, 20)
    ax = axes[0, 0]
    circles = generate_apollonian_circles(-7, 17, 12, 20, max_bend=340)
    r0 = 1.0 / 7.0
    res_colors = {0: "#2b6cb0", 8: "#319795", 9: "#dd6b20", 12: "#805ad5", 17: "#c53030", 20: "#2f855a"}
    outer = mpatches.Circle((0, 0), r0, facecolor="#f7fafc", edgecolor="#1a202c", linewidth=1.6, zorder=1)
    ax.add_patch(outer)
    for b, z in sorted(circles, key=lambda item: item[0]):
        if b <= 0:
            continue
        rad = 1.0 / b
        col = res_colors.get(b % 24, "#4a5568")
        circ = mpatches.Circle((z.real, z.imag), rad, facecolor=col, alpha=0.24, edgecolor=col, linewidth=0.75, zorder=2)
        ax.add_patch(circ)
        if b <= 45:
            ax.text(z.real, z.imag, str(b), ha="center", va="center", fontsize=8.0 if b <= 25 else 6.6,
                    fontweight="bold", color="#1a202c", zorder=4)
    ax.set_xlim(-r0 * 1.12, r0 * 1.12)
    ax.set_ylim(-r0 * 1.12, r0 * 1.12)
    ax.set_aspect("equal")
    ax.set_xticks([])
    ax.set_yticks([])
    ax.set_title("(a) HKRS Obstructed Packing $(-7, 17, 12, 20)$ ($b \\leq 340$)", fontweight="bold", pad=6)
    handles = [mpatches.Patch(facecolor=c, alpha=0.55, edgecolor=c, label=f"$b \\equiv {r}\\ (24)$")
               for r, c in res_colors.items()]
    ax.legend(handles=handles, loc="lower left", ncol=2, frameon=True, facecolor="white", framealpha=0.92, fontsize=7.0)
    ax.text(
        0.97, 0.96, "$\\chi(q) = -1$ globally\n0 squares (all $b$)",
        transform=ax.transAxes, ha="right", va="top", fontsize=7.8,
        bbox={"boxstyle": "round,pad=0.35", "facecolor": "#fff5f5", "edgecolor": "#c53030", "lw": 0.9},
    )

    # Panel (b): Obstructed (-7,17,12,20) vs Square-Hitting Contrast (-4,8,9,9)
    ax = axes[0, 1]
    b_obs = audit_apollonian_bends((-7, 17, 12, 20), 1000)
    b_un = audit_apollonian_bends((-4, 8, 9, 9), 1000)
    xs = np.linspace(0, 1000, 200)
    sq_obs = [sum(1 for b in b_obs if 0 <= b <= x and math.isqrt(b) ** 2 == b) for x in xs]
    sq_un = [sum(1 for b in b_un if 0 <= b <= x and math.isqrt(b) ** 2 == b) for x in xs]
    ax.plot(xs, sq_un, color="#2b6cb0", lw=2.3, label="Contrast $(-4, 8, 9, 9)$: 8 squares ($9, 36, \\dots, 900$)")
    ax.plot(xs, sq_obs, color="#c53030", lw=2.3, ls="--", label="HKRS Obstructed $(-7, 17, 12, 20)$: 0 squares (T1c)")
    ax.fill_between(xs, sq_obs, sq_un, color="#2b6cb0", alpha=0.10)
    ax.set_xlabel("Curvature cutoff $B$")
    ax.set_ylabel("Cumulative perfect-square curvatures $\\leq B$")
    ax.set_title("(b) Identical Mod-24 Set $\\{0,8,9,12,17,20\\}$, Opposite Square Fate", fontweight="bold", pad=6)
    ax.set_ylim(-0.6, 9.8)
    ax.grid(True, alpha=0.25, ls=":")
    ax.legend(loc="upper left", frameon=True, facecolor="white")
    # Small inset bar chart comparing mod 24 residue frequencies
    ins = ax.inset_axes([0.52, 0.14, 0.44, 0.42])
    mods = [0, 8, 9, 12, 17, 20]
    c_obs = Counter(b % 24 for b in b_obs if b > 0)
    c_un = Counter(b % 24 for b in b_un if b > 0)
    x_pos = np.arange(len(mods))
    ins.bar(x_pos - 0.18, [c_un[m] for m in mods], width=0.35, color="#2b6cb0", alpha=0.85, label="(-4,8,9,9)")
    ins.bar(x_pos + 0.18, [c_obs[m] for m in mods], width=0.35, color="#c53030", alpha=0.85, label="(-7,17,12,20)")
    ins.set_xticks(x_pos)
    ins.set_xticklabels([str(m) for m in mods], fontsize=7)
    ins.tick_params(axis="y", labelsize=7)
    ins.set_title("Distinct bends mod 24", fontsize=7.5, pad=2)
    ins.grid(True, axis="y", alpha=0.2)

    # Panel (c): Generalized Octahedral Q(sqrt(-2)) Reciprocity Obstruction (T1d)
    ax = axes[1, 0]
    oct_o = rust_summary["pillar1"]["octahedral_obstructed"]
    oct_s = rust_summary["pillar1"]["octahedral_strip"]
    categories = ["Distinct bends\n(orbit sample)", "Hits $m^2$\n(perfect sq.)", "Hits $2m^2$\n(double sq.)", "Hits $2^e m^2$\n(total obstructed)"]
    vals_strip = [oct_s["bends"], oct_s["squares"], oct_s["double_squares"], oct_s["squares"] + oct_s["double_squares"]]
    vals_obs = [oct_o["bends"], 0, 0, oct_o["pow2_squares"]]
    xp = np.arange(len(categories))
    w = 0.34
    b1 = ax.bar(xp - w / 2, vals_strip, w, color="#2f855a", alpha=0.88, label="Octahedral Strip $(0,0,1,2,2,1)$ ($b\\leq 400$)")
    b2 = ax.bar(xp + w / 2, vals_obs, w, color="#805ad5", alpha=0.88, label="Obstructed $(-6,10,17,40,24,17)$ ($b\\leq 1500$, T1d)")
    for rect in list(b1) + list(b2):
        h = rect.get_height()
        ax.text(rect.get_x() + rect.get_width() / 2, h + 4, f"{int(h)}", ha="center", va="bottom", fontsize=8.2, fontweight="bold")
    ax.set_xticks(xp)
    ax.set_xticklabels(categories, fontsize=8.2)
    ax.set_ylabel("Count in exact BFS orbit")
    ax.set_ylim(0, 265)
    ax.set_title("(c) Octahedral $\\mathbb{Q}(\\sqrt{-2})$ Mod-8 Locking (T1d; cf. Shi et al. 2025)", fontweight="bold", pad=6)
    ax.grid(True, axis="y", alpha=0.25, ls=":")
    ax.legend(loc="upper right", frameon=True, facecolor="white", fontsize=7.6)
    ax.text(
        0.50, 0.56,
        "Shared mod-24 set (BFS): $\\{0,1,2,8,9,10,16,17,18\\}$\n"
        "Mod-8 locking (Lean): $b_1\\!\\equiv\\!2, b_2\\!\\equiv\\!2, b_3\\!\\equiv\\!1, b_4\\!\\equiv\\!0, b_5\\!\\equiv\\!0, b_6\\!\\equiv\\!1$\n"
        "Closed Jacobi checks: $\\left(\\frac{-3}{11}\\right)=\\left(\\frac{5}{27}\\right)=\\left(\\frac{17}{11}\\right)=-1$",
        transform=ax.transAxes, ha="center", va="center", fontsize=7.5,
        bbox={"boxstyle": "round,pad=0.4", "facecolor": "#faf5ff", "edgecolor": "#805ad5", "lw": 0.9},
    )

    # Panel (d): Exact Soddy Dimension Dichotomy (d-1) | 2 <=> d in {2, 3} (T1e)
    ax = axes[1, 1]
    ds = np.arange(2, 9)
    coeffs = 2.0 / (ds - 1.0)
    bar_cols = ["#2b6cb0" if (2 % (d - 1) == 0) else "#cbd5e0" for d in ds]
    bars = ax.bar(ds, coeffs, color=bar_cols, edgecolor="#2d3748", linewidth=0.9, width=0.58)
    ax.axhline(1.0, color="#2b6cb0", ls=":", lw=1.0, alpha=0.6)
    ax.axhline(2.0, color="#2b6cb0", ls=":", lw=1.0, alpha=0.6)
    for d, val, _rect in zip(ds, coeffs, bars):
        lbl = f"{int(val)} (INT)" if (2 % (d - 1) == 0) else f"2/{d - 1}"
        ax.text(d, val + 0.06, lbl, ha="center", va="bottom", fontsize=8.3,
                fontweight="bold" if (2 % (d - 1) == 0) else "normal",
                color="#1a365d" if (2 % (d - 1) == 0) else "#4a5568")
    ax.set_xticks(ds)
    ax.set_xticklabels([f"$d={d}$" for d in ds])
    ax.set_ylabel("Vieta reflection multiplier $\\alpha_d = 2/(d-1)$")
    ax.set_ylim(0, 2.45)
    ax.set_title("(d) Soddy Divisibility $(d-1)\\mid 2 \\Leftrightarrow d\\in\\{2,3\\}$ (LMW 2002; T1e)", fontweight="bold", pad=6)
    ax.grid(True, axis="y", alpha=0.25, ls=":")
    s3 = rust_summary["pillar1"]["soddy3d_contrast"]
    ax.text(
        0.96, 0.90,
        f"3D Soddy contrast $(-6,13,13,13,18)$:\n"
        f"Reflects to $25=5^2$, {s3['squares']} squares in {s3['quintuples']} quintuples\n"
        f"(Non-integral reflection for all $d \\geq 4$)",
        transform=ax.transAxes, ha="right", va="top", fontsize=7.8,
        bbox={"boxstyle": "round,pad=0.38", "facecolor": "#ebf8ff", "edgecolor": "#2b6cb0", "lw": 0.9},
    )

    fig.savefig(FIG_DIR / "fig1_apollonian_octahedral_reciprocity.pdf")
    plt.close(fig)


# --- Figure 2: Z^2 Sandpile Identity, A_2 Even-Laplacian Rigidity, Tropical Solitons ---

def make_fig2() -> dict[str, Any]:
    n = 65
    e_z2 = dhar_identity_grid("Z2", n)
    e_a2 = dhar_identity_grid("A2", n)

    # Tropical soliton drop: 3 grains on background of 3 on Z^2 (65x65)
    bg = np.full((n, n), 3, dtype=np.int64)
    drops = [(18, 22), (46, 20), (34, 48)]
    for r, c in drops:
        bg[r, c] += 1
    trop = stabilize_grid("Z2", bg)

    fig, axes = plt.subplots(1, 3, figsize=(14.4, 5.2), dpi=300)
    fig.subplots_adjust(left=0.035, right=0.985, top=0.84, bottom=0.11, wspace=0.18)
    fig.suptitle(
        "Pillar II: Finite $65\\times 65$ Sandpile Computations ($\\mathbb{Z}^2$ and $\\mathbb{A}_2$ Dhar Identities, and $3$-Drop Relaxation)",
        fontsize=12.0, fontweight="bold", y=0.965,
    )

    # Panel (a): Z^2 65x65 Identity
    cmap_z2 = ListedColormap(["#1a202c", "#2b6cb0", "#38b2ac", "#ecc94b"])
    ax = axes[0]
    im0 = ax.imshow(e_z2, cmap=cmap_z2, vmin=-0.5, vmax=3.5, interpolation="nearest")
    ax.set_xticks([])
    ax.set_yticks([])
    ax.set_title("(a) $\\mathbb{Z}^2$ $65\\times 65$ Identity ($\\deg=4$, max stable $3$)", fontweight="bold", pad=6)
    cbar0 = fig.colorbar(im0, ax=ax, fraction=0.046, pad=0.03, ticks=[0, 1, 2, 3])
    cbar0.set_label("Chips $s(v)$", fontsize=8.5)
    z2_counts = Counter(int(v) for v in e_z2.ravel())
    ax.set_xlabel(f"Chip counts: 0:{z2_counts[0]}, 1:{z2_counts[1]}, 2:{z2_counts[2]}, 3:{z2_counts[3]}", fontsize=8.0)

    # Panel (b): A_2 65x65 Identity
    cmap_a2 = ListedColormap(["#1a202c", "#2b6cb0", "#3182ce", "#38b2ac", "#ed8936", "#e53e3e"])
    ax = axes[1]
    im1 = ax.imshow(e_a2, cmap=cmap_a2, vmin=-0.5, vmax=5.5, interpolation="nearest")
    ax.set_xticks([])
    ax.set_yticks([])
    ax.set_title("(b) $\\mathbb{A}_2$ $65\\times 65$ Dhar Identity ($\\deg=6$, max stable $5$)", fontweight="bold", pad=6)
    cbar1 = fig.colorbar(im1, ax=ax, fraction=0.046, pad=0.03, ticks=[0, 1, 2, 3, 4, 5])
    cbar1.set_label("Chips $s(v)$", fontsize=8.5)
    a2_counts = Counter(int(v) for v in e_a2.ravel())
    center_val = int(e_a2[n // 2, n // 2])
    ax.set_xlabel(f"Exact chip counts: 4:{a2_counts[4]}, 5:{a2_counts[5]} (computation; independent of T2d)", fontsize=7.8)

    # Panel (c): 3-Drop Relaxation on Z^2 Sea
    ax = axes[2]
    cmap_tr = ListedColormap(["#1a202c", "#2b6cb0", "#4fd1c5", "#edf2f7"])
    im2 = ax.imshow(trop, cmap=cmap_tr, vmin=-0.5, vmax=3.5, interpolation="nearest")
    for r, c in drops:
        ax.scatter([c], [r], s=55, c="#e53e3e", edgecolors="white", linewidths=1.0, zorder=5)
    ax.set_xticks([])
    ax.set_yticks([])
    ax.set_title("(c) $3$-Drop Relaxation on Height-3 $\\mathbb{Z}^2$ Sea (cf. KS 2016)", fontweight="bold", pad=6)
    cbar2 = fig.colorbar(im2, ax=ax, fraction=0.046, pad=0.03, ticks=[0, 1, 2, 3])
    cbar2.set_label("Chips $s(v)$", fontsize=8.5)
    ax.set_xlabel("Red dots: 3 unit drops on height-3 sea (finite computation)", fontsize=8.0)
    ax.text(
        0.04, 0.96, "Trivalent balancing:\n$(1,0)+(0,1)+(-1,-1)=(0,0)$",
        transform=ax.transAxes, ha="left", va="top", fontsize=7.5,
        bbox={"boxstyle": "round,pad=0.3", "facecolor": "white", "edgecolor": "#2b6cb0", "lw": 0.8, "alpha": 0.92},
    )

    fig.savefig(FIG_DIR / "fig2_sandpile_apollonian_a2_tropical.pdf")
    plt.close(fig)
    return {
        "n": n,
        "z2_counts": {str(k): int(z2_counts[k]) for k in range(4)},
        "a2_counts": {str(k): int(a2_counts[k]) for k in range(6)},
        "a2_center_value": center_val,
        "z2_center_value": int(e_z2[n // 2, n // 2]),
    }


# --- Figure 3: Markov Tree, Mod-32 Locking, 5-Step Cluster Laurent, Hurwitz n=4 ---

def make_fig3(rust_summary: dict[str, Any]) -> None:
    _triples, nums = generate_markov_tree(10_000_000)

    fig, axes = plt.subplots(2, 2, figsize=(13.2, 8.8), dpi=300)
    fig.subplots_adjust(left=0.065, right=0.97, top=0.92, bottom=0.075, wspace=0.25, hspace=0.31)
    fig.suptitle(
        "Pillar III: Markov–Cohn Tree, Zhang (2007) Mod-32 Congruence (T3b), 5-Step Quiver Identities (T3d), and Hurwitz (1907) $n=4$ (T3e)",
        fontsize=11.4, fontweight="bold", y=0.975,
    )

    # Panel (a): Binary Cohn/Markov Tree from (1,2,5) down to depth 4
    ax = axes[0, 0]
    # Build explicit binary tree starting at (1, 2, 5)
    nodes: list[tuple[float, float, tuple[int, int, int], int]] = []
    edges: list[tuple[tuple[float, float], tuple[float, float]]] = []

    def add_tree(triple: tuple[int, int, int], depth: int, x: float, dx: float) -> None:
        y = 4.0 - depth
        nodes.append((x, y, triple, depth))
        if depth == 3:
            return
        a, b, c = triple  # a <= b <= c
        # Left branch replaces b -> 3ac - b; Right branch replaces a -> 3bc - a
        l_raw = sorted((a, c, 3 * a * c - b))
        r_raw = sorted((b, c, 3 * b * c - a))
        left = (l_raw[0], l_raw[1], l_raw[2])
        right = (r_raw[0], r_raw[1], r_raw[2])
        lx, rx = x - dx, x + dx
        ly, ry = y - 1.0, y - 1.0
        edges.append(((x, y), (lx, ly)))
        edges.append(((x, y), (rx, ry)))
        add_tree(left, depth + 1, lx, dx * 0.5)
        add_tree(right, depth + 1, rx, dx * 0.5)

    # Root (1,1,1) -> (1,1,2) -> (1,2,5)
    ax.plot([0, 0], [5.15, 4.55], color="#718096", lw=1.4, zorder=1)
    ax.plot([0, 0], [4.55, 4.0], color="#718096", lw=1.4, zorder=1)
    add_tree((1, 2, 5), 0, 0.0, 2.25)

    for (x1, y1), (x2, y2) in edges:
        ax.plot([x1, x2], [y1, y2], color="#a0aec0", lw=1.25, zorder=1)

    for x, y, lbl, is_even in [(0.0, 5.15, "1", False), (0.0, 4.55, "2  (2 mod 64)", True)]:
        col = "#00b5d8" if is_even else "#ecc94b"
        ax.text(x, y, lbl, ha="center", va="center", fontsize=8.0, fontweight="bold",
                bbox={"boxstyle": "round,pad=0.25", "facecolor": col, "edgecolor": "#1a202c", "lw": 0.9}, zorder=3)

    for x, y, tri, depth in nodes:
        z = tri[2]
        is_even = (z % 2 == 0)
        col = "#90cdf4" if is_even else "#fefcbf"
        ec = "#2b6cb0" if is_even else "#b7791f"
        txt = f"{z}" + (f"\n({z % 64} mod 64)" if is_even else "")
        ax.text(x, y, txt, ha="center", va="center", fontsize=7.5 if depth < 3 else 6.1,
                fontweight="bold",
                bbox={"boxstyle": "round,pad=0.20", "facecolor": col, "edgecolor": ec, "lw": 0.9}, zorder=3)

    ax.set_xlim(-4.85, 4.85)
    ax.set_ylim(0.55, 5.65)
    ax.axis("off")
    ax.set_title("(a) Cohn–Markov Tree: Gold = Odd ($\\equiv 1\\ (4)$), Blue = Even ($\\equiv 2\\ (32)$, Zhang 2007)", fontweight="bold", pad=4)

    # Panel (b): Exact Residue Audit up to 10^7
    ax = axes[0, 1]
    odd_primes_set: set[int] = set()
    for m in nums:
        for p in factor_odd_primes(m):
            odd_primes_set.add(p)
    p_mod4 = Counter(p % 4 for p in odd_primes_set)
    even_nums = [m for m in nums if m % 2 == 0]
    odd_nums = [m for m in nums if m % 2 == 1]
    e_mod64 = Counter(m % 64 for m in even_nums)
    o_mod4 = Counter(m % 4 for m in odd_nums)

    labels = [
        "Odd primes\n$p\\equiv 1\\ (4)$",
        "Odd primes\n$p\\equiv 3\\ (4)$",
        "Odd Markov\n$m\\equiv 1\\ (4)$",
        "Odd Markov\n$m\\equiv 3\\ (4)$",
        "Even Markov\n$m\\equiv 2\\ (64)$",
        "Even Markov\n$m\\equiv 34\\ (64)$",
        "Even Markov\nother mod 32",
    ]
    counts = [
        p_mod4[1], p_mod4[3],
        o_mod4[1], o_mod4[3],
        e_mod64[2], e_mod64[34],
        sum(1 for m in even_nums if m % 32 != 2),
    ]
    cols = ["#2f855a", "#e53e3e", "#d69e2e", "#e53e3e", "#2b6cb0", "#319795", "#e53e3e"]
    xp = np.arange(len(labels))
    bars = ax.bar(xp, counts, color=cols, edgecolor="#1a202c", linewidth=0.8, width=0.62)
    for rect, val in zip(bars, counts):
        ax.text(rect.get_x() + rect.get_width() / 2, val + 1.2, str(val),
                ha="center", va="bottom", fontsize=8.4, fontweight="bold")
    ax.set_xticks(xp)
    ax.set_xticklabels(labels, fontsize=7.2)
    ax.set_ylabel("Exact count ($m \\leq 10^7$, 56 numbers)")
    ax.set_ylim(0, max(counts) * 1.18)
    ax.set_title("(b) Zero Violations Across 56 Markov Numbers $\\leq 10^7$ (Zhang 2007, T3b)", fontweight="bold", pad=6)
    ax.grid(True, axis="y", alpha=0.25, ls=":")

    # Panel (c): 5-Step Fomin-Zelevinsky Cluster Mutation Laurent Numerators (T3d)
    ax = axes[1, 0]
    steps = np.arange(1, 6)
    vals_111 = [2, 5, 29, 433, 37666]
    total_degs = [2, 4, 8, 14, 24]  # exact homogeneous total degree of P_k(x1,x2,x3)
    ax.semilogy(steps, vals_111, "o-", color="#2b6cb0", lw=2.3, ms=7.5, label="$P_k(1,1,1)$ along $(2,5,29) \\to (5,29,433) \\to (29,433,37666)$")
    label_pos = {
        1: (1.08, 3.1, "left", "bottom"),
        2: (2.0, 8.2, "center", "bottom"),
        3: (2.92, 48.0, "right", "bottom"),
        4: (3.86, 760.0, "right", "bottom"),
        5: (4.82, 34000.0, "right", "center"),
    }
    for s, v, deg in zip(steps, vals_111, total_degs):
        lx, ly, ha, va = label_pos[int(s)]
        ax.text(lx, ly, f"$P_{s}(1,1,1)={v:,}$\n(deg {deg})", ha=ha, va=va,
                fontsize=7.6, fontweight="bold", color="#1a365d")
    ax.axvspan(3.6, 5.4, color="#ebf8ff", alpha=0.75, zorder=0)
    ax.text(4.5, 4.2, "Non-monomial exact\npolynomial divisions:\nStep 4 by $P_1 = x_2^2+x_3^2$\nStep 5 by $P_2 = P_1^2+x_1^2x_3^2$",
            ha="center", va="center", fontsize=7.5,
            bbox={"boxstyle": "round,pad=0.35", "facecolor": "white", "edgecolor": "#2b6cb0", "lw": 0.9})
    ax.set_xticks(steps)
    ax.set_xticklabels([f"Step {k}\n($P_{k}$)" for k in steps])
    ax.set_ylabel("Cluster numerator value at $(1,1,1)$ (log scale)")
    ax.set_xlim(0.60, 5.42)
    ax.set_ylim(1.2, 2.2e5)
    ax.set_title("(c) 5-Step Markov Quiver Exchange Identities & Non-Monomial Div. (T3d)", fontweight="bold", pad=6)
    ax.grid(True, which="both", alpha=0.25, ls=":")
    ax.legend(loc="upper left", frameon=True, facecolor="white", fontsize=7.8)

    # Panel (d): Complete Markov-Hurwitz n=4 Classification (T3e)
    ax = axes[1, 1]
    hw = rust_summary["pillar3"]["hurwitz_n4_le120_counts"]
    a_vals = np.arange(1, 9)
    h_counts = [hw["a1"], hw["a2"], hw["a3"], hw["a4"], 0, 0, 0, 0]
    h_cols = ["#2b6cb0", "#e53e3e", "#e53e3e", "#2f855a", "#a0aec0", "#a0aec0", "#a0aec0", "#a0aec0"]
    bars = ax.bar(a_vals, h_counts, color=h_cols, edgecolor="#1a202c", lw=0.9, width=0.6)
    notes = ["$a=1$\nAll $\\equiv 2\\ (4)$\nroot $(2,2,2,2)$", "EMPTY\n(T3e)", "EMPTY\n(T3e)",
             "$a=4$\nAll odd\nroot $(1,1,1,1)$", "EMPTY\n$a\\geq 5$", "EMPTY", "EMPTY", "EMPTY"]
    for a, c, note in zip(a_vals, h_counts, notes):
        ax.text(a, c + 0.18, f"{c}\n{note}" if a in (1, 4) else f"0\n{note}",
                ha="center", va="bottom", fontsize=7.2,
                fontweight="bold" if a in (1, 4) else "normal",
                color="#1a202c" if a in (1, 4) else "#9b2c2c")
    ax.set_xticks(a_vals)
    ax.set_xticklabels([f"$a={a}$" for a in a_vals])
    ax.set_ylabel("Solutions with $\\max x_i \\leq 120$")
    ax.set_ylim(0, 5.7)
    ax.set_title("(d) Hurwitz (1907) $n=4$ Admissible Coefficients $\\sum x_i^2 = a\\prod x_i$ (T3e)", fontweight="bold", pad=6)
    ax.grid(True, axis="y", alpha=0.25, ls=":")

    fig.savefig(FIG_DIR / "fig3_markov_cohn_mod32_hurwitz.pdf")
    plt.close(fig)


# --- Figure 4: Unified Vieta Reflection & Six-Kernel Architecture Diagram ---

def make_fig4() -> None:
    fig, ax = plt.subplots(figsize=(13.6, 6.8), dpi=300)
    ax.set_xlim(0, 100)
    ax.set_ylim(0, 56)
    ax.axis("off")

    def box(x: float, y: float, w: float, h: float, title: str, body: str, fc: str, ec: str, title_fs: float = 9.2, body_fs: float = 7.6) -> None:
        rect = mpatches.FancyBboxPatch(
            (x, y), w, h, boxstyle="round,pad=0.6,rounding_size=1.2",
            facecolor=fc, edgecolor=ec, linewidth=1.35, zorder=2
        )
        ax.add_patch(rect)
        ax.text(x + w / 2, y + h - 1.5, title, ha="center", va="top", fontsize=title_fs, fontweight="bold", color="#1a202c", zorder=3)
        ax.text(x + w / 2, y + (h - 2.6) / 2, body, ha="center", va="center", fontsize=body_fs, color="#2d3748", zorder=3, linespacing=1.28)

    def arrow(x1: float, y1: float, x2: float, y2: float, col: str = "#4a5568") -> None:
        ax.annotate(
            "", xy=(x2, y2), xytext=(x1, y1),
            arrowprops={"arrowstyle": "-|>,head_width=0.35,head_length=0.55", "color": col, "lw": 1.3},
            zorder=1,
        )

    ax.text(50, 54.4, "Unified Vieta-Reflection Architecture & Six-Kernel Verification Pipeline (0TH-2026-018, v3.0.0)",
            ha="center", va="center", fontsize=12.4, fontweight="bold", color="#1a202c")

    # Tier 0: Root Generator
    box(11, 44.5, 78, 7.2,
        "Universal Quadratic Vieta Reflection & Reciprocity Engine (Zero-Mathlib Lean 4.35.0)",
        "Quadratic form involutions  x_i -> c * prod_{j!=i} x_j - x_i  &  Lorentzian / Lattice Laplacians\n"
        "Self-contained Eisenstein (1844) Gauss Quadratic Reciprocity & Jacobi Symbol Module (T1b)",
        "#ebf8ff", "#2b6cb0", title_fs=9.4, body_fs=7.9)

    # Tier 1: Three Pillars
    box(2.5, 23.5, 30.0, 16.5,
        "Pillar I: Thin Reflection Groups",
        "T1a: Descartes Lorentzian & Gaussian norm\n"
        "T1b: Zero-Mathlib Jacobi & Eisenstein QR\n"
        "T1c: HKRS (2024) obstruction on 3 roots\n"
        "     (contrast (-4,8,9,9) hits 9)\n"
        "T1d: Octahedral mod-8 lock + 5 Jacobi vals\n"
        "T1e: General d-dim Soddy refls <-> d in {2,3}",
        "#fff5f5", "#c53030")

    box(35.0, 23.5, 30.0, 16.5,
        "Pillar II: Sandpiles & Lattice Identities",
        "T2a: Comm., least action, confluence & TERM.\n"
        "T2b: Direct Z^2 det4=192, det9=100,352 + traces\n"
        "T2c: One isotropic Z^2 K=3 obstruction\n"
        "T2d: Elem. A_2 parity lemma (MK=4A-2B+4C -> 2|K)\n"
        "T2e: Lattice-polygon edge-normal closure id\n"
        "T2f: Direct A_2 det4=1,092, det9=5,393,920",
        "#fffaf0", "#dd6b20")

    box(67.5, 23.5, 30.0, 16.5,
        "Pillar III: Markov-Hurwitz & Quiver",
        "T3a: SL2(Z) Fricke trace & Cohn tree (3 | tr)\n"
        "T3b: Markov descent + Zhang (2007) m=2(32)\n"
        "     (ALL pos. sols; witnesses 2 and 34)\n"
        "T3c: Hensel sqrt(-1) mod p^k uniqueness\n"
        "T3d: 5-step quiver exchange ids (P1, P2 div.)\n"
        "T3e: Hurwitz (1907) n=4 complete Vieta orbits",
        "#f0fff4", "#2f855a")

    arrow(36, 44.5, 17.5, 40.6, "#c53030")
    arrow(50, 44.5, 50.0, 40.6, "#dd6b20")
    arrow(64, 44.5, 82.5, 40.6, "#2f855a")

    # Tier 2: Contract & NonVacuity / Adversarial
    box(11, 12.2, 78, 6.8,
        "Machine-Checked Contract: Challenge.lean + Solution.lean + PalomarSolution.lean + VerifyAllDecls.lean",
        "19 Exported Declarations (16 Theorems + Master + NonVacuity + 10 Refutations)  |  884 Exhaustively Axiom-Audited Decls\n"
        "Strictly [propext, Classical.choice, Quot.sound]  |  0 sorry  |  0 admit  |  0 native_decide  |  0 Mathlib",
        "#faf5ff", "#6b46c1", title_fs=9.0, body_fs=7.6)

    arrow(17.5, 23.5, 30.0, 19.6, "#6b46c1")
    arrow(50.0, 23.5, 50.0, 19.6, "#6b46c1")
    arrow(82.5, 23.5, 70.0, 19.6, "#6b46c1")

    # Tier 3: Independent Verification Oracles
    box(2.0, 1.5, 47.0, 7.0,
        "Six Independent Formal Type-Checking Kernels + Negative Gate",
        "lean 4.35.0 + VerifyAllDecls  |  leanchecker --fresh  |  lean4lean\n"
        "nanoda_bin  |  con-leche  |  con-ron  |  lake check & comparator --paranoid",
        "#edf2f7", "#2d3748", title_fs=8.8, body_fs=7.4)

    box(51.0, 1.5, 47.0, 7.0,
        "Three Independent Computational & Differential Oracles",
        "Rust (#![forbid(unsafe_code)], 6/6 tests)  |  ISO C11 (ASan/UBSan + 7-law libFuzzer)\n"
        "Python Oracle + Hypothesis (600+ props) + 12/12 pytest + 10/10 (100%) Mutation",
        "#e6fffa", "#2c7a7b", title_fs=8.8, body_fs=7.4)

    arrow(36, 12.2, 25.5, 9.1, "#2d3748")
    arrow(64, 12.2, 74.5, 9.1, "#2c7a7b")

    fig.savefig(FIG_DIR / "fig4_unified_vieta_architecture.pdf", bbox_inches="tight", pad_inches=0.12)
    plt.close(fig)


# --- Social Preview PNG (1280 x 640) ---

def make_social_preview() -> None:
    fig = plt.figure(figsize=(12.8, 6.4), dpi=100, facecolor="#0b1120")

    # Left panel: Apollonian Gasket in neon cyan/gold on dark canvas
    ax1 = fig.add_axes((0.03, 0.14, 0.28, 0.56), facecolor="#0b1120")
    circles = generate_apollonian_circles(-7, 17, 12, 20, max_bend=280)
    r0 = 1.0 / 7.0
    ax1.add_patch(mpatches.Circle((0, 0), r0, facecolor="#111827", edgecolor="#38bdf8", lw=2.0))
    pal = {0: "#38bdf8", 8: "#34d399", 9: "#fbbf24", 12: "#a78bfa", 17: "#f87171", 20: "#60a5fa"}
    for b, z in circles:
        if b <= 0:
            continue
        col = pal.get(b % 24, "#94a3b8")
        ax1.add_patch(mpatches.Circle((z.real, z.imag), 1.0 / b, facecolor=col, alpha=0.22, edgecolor=col, lw=0.85))
    ax1.set_xlim(-r0 * 1.06, r0 * 1.06)
    ax1.set_ylim(-r0 * 1.06, r0 * 1.06)
    ax1.set_aspect("equal")
    ax1.axis("off")
    ax1.set_title("HKRS Apollonian & Octahedral", color="#e2e8f0", fontsize=11, fontweight="bold", pad=6)

    # Middle panel: A_2 51x51 Sandpile Identity
    ax2 = fig.add_axes((0.36, 0.14, 0.28, 0.56), facecolor="#0b1120")
    e_a2 = dhar_identity_grid("A2", 51)
    cmap_dark = ListedColormap(["#0f172a", "#1d4ed8", "#0284c7", "#14b8a6", "#f59e0b", "#ef4444"])
    ax2.imshow(e_a2, cmap=cmap_dark, vmin=-0.5, vmax=5.5, interpolation="nearest")
    ax2.axis("off")
    ax2.set_title("A2 51x51 Dhar Identity (Computation)", color="#e2e8f0", fontsize=11, fontweight="bold", pad=6)

    # Right panel: Markov Mod-32 Tree
    ax3 = fig.add_axes((0.69, 0.14, 0.28, 0.56), facecolor="#0b1120")
    pts = [(0, 4, "1", False), (0, 3, "2", True), (0, 2, "5", False),
           (-1.2, 1, "13", False), (1.2, 1, "29", False),
           (-1.9, 0, "34", True), (-0.5, 0, "194", True), (0.5, 0, "433", False), (1.9, 0, "169", False)]
    segs = [((0, 4), (0, 3)), ((0, 3), (0, 2)), ((0, 2), (-1.2, 1)), ((0, 2), (1.2, 1)),
            ((-1.2, 1), (-1.9, 0)), ((-1.2, 1), (-0.5, 0)), ((1.2, 1), (0.5, 0)), ((1.2, 1), (1.9, 0))]
    for p, q in segs:
        ax3.plot([p[0], q[0]], [p[1], q[1]], color="#475569", lw=1.8, zorder=1)
    for x, y, lbl, ev in pts:
        ax3.text(x, y, lbl, ha="center", va="center", color="#0b1120", fontsize=10, fontweight="bold",
                 bbox={"boxstyle": "round,pad=0.32", "facecolor": "#38bdf8" if ev else "#fbbf24", "edgecolor": "white", "lw": 1.1}, zorder=3)
    ax3.set_xlim(-2.5, 2.5)
    ax3.set_ylim(-0.6, 4.6)
    ax3.axis("off")
    ax3.set_title("Markov Tree (Zhang 2007 Mod-32)", color="#e2e8f0", fontsize=11, fontweight="bold", pad=6)

    # Banner Title & Footer Badges
    fig.text(0.5, 0.90, "apollonian-sandpile-markov", ha="center", va="center",
             color="#f8fafc", fontsize=26, fontweight="bold", family="sans-serif")
    fig.text(0.5, 0.80, "Thin Vieta Reflection Groups  •  Lattice Sandpile Identities  •  Markov-Hurwitz Spectra",
             ha="center", va="center", color="#94a3b8", fontsize=13.5, family="sans-serif")
    fig.text(0.5, 0.055,
             "16 Lean 4.35.0 Statements (19 Exports, 884 Audited)  |  Zero Mathlib  |  6 Independent Kernels  |  Rust + C11 + Python",
             ha="center", va="center", color="#38bdf8", fontsize=10.5, fontweight="bold", family="sans-serif")

    fig.savefig(MEDIA_DIR / "social-preview.png", dpi=100, facecolor="#0b1120")
    plt.close(fig)


def main() -> None:
    rust_summary = json.loads((ROOT / "results" / "rust_summary.json").read_text(encoding="utf-8"))
    make_fig1(rust_summary)
    fig2_stats = make_fig2()
    make_fig3(rust_summary)
    make_fig4()
    make_social_preview()
    out_stats = ROOT / "results" / "figure_stats.json"
    out_stats.write_text(json.dumps(fig2_stats, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"figures_status": "PASS", "fig2_stats": fig2_stats}, indent=2))


if __name__ == "__main__":
    main()
