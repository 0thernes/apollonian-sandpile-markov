<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Changelog

All notable changes to `apollonian-sandpile-markov` (`0TH-2026-018`) are documented in this file following [Keep a Changelog](https://keepachangelog.com/en/1.1.0/) and [Semantic Versioning](https://semver.org/).

## [2.0.0] - 2026-11-26

### Added & Resolved — Full Statement-Audit Remediation (13 Paper + 9 Code Items), Direct 9×9 Lean Determinants (`T2b`/`T2f`), Coverage-Guided `libFuzzer`, Dual Timestamps & 10/10 Mutation
- **Resolved ALL 9 Formal-Code Audit Items (`lean/`):**
  - Added a self-contained zero-Mathlib general `n × n` Laplace determinant `detMat` with verified elementary row-operation soundness in `SandpileTropical.lean`, proving `detMat 9 (gridLap 3) = 100,352` directly inside `T2b` AND `detMat 9 (a2GridLap 3) = 5,393,920` directly inside new theorem **`T2f`** (`t2f_a2_grid_orders_and_dhar_identity`, alongside Klein-4 block similarity and legal `A_2` Dhar traces).
  - Expanded `T1e` to export `soddy3Q` preservation for all five 3D Soddy reflections `soddy3Refl1`–`soddy3Refl5`; expanded `T3a` to export explicit `3 ∣ A.tr ∧ 3 ∣ B.tr ∧ 3 ∣ (A*B).tr`; renamed `rootUnobstructed` → `rootSquareContrast` and `adv1_unobstructed_hits_square` → `adv1_square_contrast_hits_square`; added explicit constructive witnesses for the `T2d` hypothesis bundle and `IsStabilizingOdometer` in `NonVacuity.lean`; fixed `lean/lake-manifest.json` package name (`"ApollonianSandpileMarkov"`); and updated `lean/formalization.yaml` (`19` audited declarations, `17` intentional comparator stubs in `PalomarChallenge.lean`).
- **Resolved ALL 13 Paper, Figure, Web & Bibliography Audit Items:**
  - Rewrote `paper/main.tex`, regenerated all 4 vector PDF figures (`fig1`–`fig4`) and `docs/media/social-preview.png` (visually inspected), and updated `studio/index.html`, `blueprint/index.html`, `docs/index.html`, `README.md`, `CLAIMS.md`, `LIMITATIONS.md`, `ERRATA.md`, `VERIFICATION.md`, `CITATION.cff`, `docs/statement-fidelity.md`, and `docs/literature-log.md`.
  - Credited `T3b` to Ying Zhang (`zhang2007`, *Acta Arith.* 128 (2007) 295–301, `arXiv:math/0612620`), cited Shi et al. (`shi2025`, `arXiv:2510.21702`) for octahedral reciprocity obstructions, credited `T3e` to Hurwitz (`hurwitz1907`), added 2017 reprint note on `baragar1993` (`23/23` live verified via Crossref/arXiv), fixed Cohn root matrix typo (`B_0 = [[1,2],[2,5]]`), removed `"Fibonacci-odd branch"`, removed unsupported causal claim linking `T2d` to height-5 sandpile plateaus, and narrowed `T1c`/`T1d`/`T1e`/`T2a`/`T2b`/`T2d`/`T2e`/`T2f`/`T3d`/`T3e` wording to match exact Lean propositions.
- **Hardened Engineering & Provenance:**
  - Added coverage-guided `libFuzzer` target (`native/fuzz_libfuzzer.c`), expanded C11 fuzzer to 7 laws (`100,000` iterations), expanded `scripts/mutate.py` to `10/10` (`100%`) semantic mutation kill rate, added live negative Lean kernel rejection gate in CI, added dual DigiCert RFC 3161 (`.tsr`) + 3-calendar Bitcoin OpenTimestamps (`.ots`), strict CSP + WCAG 2.2 AA across `studio/`, `blueprint/`, and `docs/`, and Build Standard v1.2.0 documentation (`docs/architecture.md`, `docs/configuration.md`, `docs/operations.md`, `docs/faq.md`, `docs/glossary.md`, `UPGRADING.md`, `docs/reviews/2026-11-26-10-pass-red-team-review.md`).

## [1.0.0] - 2026-11-26

### Added
- **Zero-Mathlib Lean 4.35.0 Formalization (`lean/`):** 15 machine-checked headline theorems (`T1a`–`T3e`), `Challenge.lean`, `Solution.lean`, `PalomarChallenge.lean`, `PalomarSolution.lean`, `NonVacuity.lean`, `Adversarial.lean`, `VerifyAxioms.lean`, `comparator.json`, and `formalization.yaml` — 18 declarations audited strictly within `[propext, Classical.choice, Quot.sound]`.
- **Original Results:** Triangular Lattice $\mathbb{A}_2$ Even-Laplacian Rigidity Theorem (`T2d`, universally obstructing `K=5`), Exact Mod-32 Theorem for even Markov numbers (`T3b`, sharp mod 64), and zero-GCD-exception parabolic Dehn-twist CRT formalization of HKRS (2024) (`T1c`).
- **Multi-Language Oracles:** Zero-dependency Rust crate (`rust/`), ISO C11 verifier + 100k fuzzer (`native/`), and Python exact oracle + Hypothesis + differential + 8/8 (100%) mutation test harness (`python/`, `tests/`, `scripts/mutate.py`).
- **AMS-LaTeX White Paper & Figures (`paper/`, `dist/`):** 13-page zero-warning AMS-LaTeX preprint with 4 visually inspected vector PDF figures, 20 Crossref/arXiv-verified references, frozen PDF, and clean-room deterministic `mtime=0` arXiv tarball.
- **Interactive Web Observatory & Proof Blueprint (`studio/`, `blueprint/`, `docs/`):** Zero-dependency 4-mode interactive browser lab and filterable Lean Proof Blueprint deployed to GitHub Pages.
- **Governance & Provenance:** Build Standard v1.2.0 (90/90 `repo.yaml`), Playbook v1.3 compliance, 3-cycle `HARDENING_LOG.md`, 6-kernel CI with SLSA attestations, and `MANIFEST.sha256`.
