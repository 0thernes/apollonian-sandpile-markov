<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Changelog

All notable changes to `apollonian-sandpile-markov` (`0TH-2026-018`) are documented in this file following [Keep a Changelog](https://keepachangelog.com/en/1.1.0/) and [Semantic Versioning](https://semver.org/).

## [Unreleased] - 2026-11-26

### Changed (documentation only; no Lean, paper, data or PDF changes)
- Corrected claim wording in `README.md`, `CLAIMS.md`, `LIMITATIONS.md`, `CITATION.cff`, `lean/formalization.yaml` and `docs/*.md` to match the 2026-11-26 statement audit ([audit log](https://github.com/0thernes/0thernes-research-archive/blob/main/docs/reviews/2026-11-26-statement-audit.md)).
- `T3b` is now credited as a formalization of Ying Zhang's theorem (Acta Arith. 128 (2007), arXiv:math/0612620); `T1c` as a formalization of Haag–Kertzer–Rickards–Stange (2024) for three packings; `T3e` as the classical Hurwitz (1907) classification; arXiv:2510.21702 is cited for octahedral obstructions (`T1d`).
- `(-4,8,9,9)` is no longer called unobstructed; `T2d` is described as an elementary parity lemma with its full hypothesis; `T2a`, `T2b`, `T2e`, `T3d` and `T3e` descriptions narrowed to what Lean states. The "Original Results" line of the 1.0.0 entry below is superseded by these descriptions.
- Kernel-replay coverage and the 16 comparator `by sorry` stubs in `lean/PalomarChallenge.lean` are now stated explicitly.
- `ERRATA.md`: added the "2026-11-26 statement audit" section listing errors in the frozen paper and known issues in the formal code.

## [1.0.0] - 2026-11-26

### Added
- **Zero-Mathlib Lean 4.35.0 Formalization (`lean/`):** 15 machine-checked headline theorems (`T1a`–`T3e`), `Challenge.lean`, `Solution.lean`, `PalomarChallenge.lean`, `PalomarSolution.lean`, `NonVacuity.lean`, `Adversarial.lean`, `VerifyAxioms.lean`, `comparator.json`, and `formalization.yaml` — 18 declarations audited strictly within `[propext, Classical.choice, Quot.sound]`.
- **Original Results:** Triangular Lattice $\mathbb{A}_2$ Even-Laplacian Rigidity Theorem (`T2d`, universally obstructing `K=5`), Exact Mod-32 Theorem for even Markov numbers (`T3b`, sharp mod 64), and zero-GCD-exception parabolic Dehn-twist CRT formalization of HKRS (2024) (`T1c`).
- **Multi-Language Oracles:** Zero-dependency Rust crate (`rust/`), ISO C11 verifier + 100k fuzzer (`native/`), and Python exact oracle + Hypothesis + differential + 8/8 (100%) mutation test harness (`python/`, `tests/`, `scripts/mutate.py`).
- **AMS-LaTeX White Paper & Figures (`paper/`, `dist/`):** 13-page zero-warning AMS-LaTeX preprint with 4 visually inspected vector PDF figures, 20 Crossref/arXiv-verified references, frozen PDF, and clean-room deterministic `mtime=0` arXiv tarball.
- **Interactive Web Observatory & Proof Blueprint (`studio/`, `blueprint/`, `docs/`):** Zero-dependency 4-mode interactive browser lab and filterable Lean Proof Blueprint deployed to GitHub Pages.
- **Governance & Provenance:** Build Standard v1.2.0 (90/90 `repo.yaml`), Playbook v1.3 compliance, 3-cycle `HARDENING_LOG.md`, 6-kernel CI with SLSA attestations, and `MANIFEST.sha256`.
