<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Changelog

All notable changes to `apollonian-sandpile-markov` (`0TH-2026-018`) are documented in this file following [Keep a Changelog](https://keepachangelog.com/en/1.1.0/) and [Semantic Versioning](https://semver.org/).

## [3.0.0] - 2026-11-27

### Added & Upgraded — Four Major Formal-Proof Gap Closures + Deep Adversarial Hardening (`ADR 0003`)
- **Lean 4.35.0 Formal Upgrades (Breaking Strengthening of `T1e`, `T2a`, `T3b`, `T3e` in `Challenge.lean` / `PalomarChallenge.lean`; 884 Exhaustively Axiom-Audited Declarations):**
  - **`T1e` (`ApollonianReciprocity.lean`):** Formalized the full **Lagarias–Mallows–Wilks (2002) general `d`-dimensional Soddy–Gosset integrality dichotomy** (`soddyQ d`, `soddyRefl d α k`, universal involution, exact change factorization, preservation iff `(d - 1) * α = 2`, hence existence iff `d = 2 ∨ d = 3`).
  - **`T2a` (`SandpileTropical.lean`):** Formalized `IsDissipative`, inductive `ReachesSink` / `HasReachableSink`, a constructive strictly superharmonic potential `potentialVal R D (dist i)`, explicit stabilizing odometers, uniform trace-length bounds, and **universal finite termination and existence of a legal stabilizing trace** on every sinked dissipative sandpile graph.
  - **`T3b` (`MarkovHurwitzCluster.lean`):** Formalized **Markov's classical descent theorem (1879/1880)** proving *every* positive integer solution `(x, y, z)` of `x^2 + y^2 + z^2 = 3xyz` lies in `InMarkovTree x y z`, lifting pairwise coprimality, odd-prime `p ≡ 1 (mod 4)`, and Ying Zhang's mod-32 theorem to all positive integer Markov solutions.
  - **`T3e` (`MarkovHurwitzCluster.lean`):** Defined `InHurwitz4Orbit` and proved **Hurwitz's (1907) complete `n = 4` Vieta-orbit bi-implications** (`IsHurwitz4 1 ↔ InHurwitz4Orbit 1 2 2 2 2` and `IsHurwitz4 4 ↔ InHurwitz4Orbit 4 1 1 1 1`).
  - **`NonVacuity.lean` & `Adversarial.lean`:** Added witnesses for `soddyQ 3`, sinked-dissipative multi-hop `gridGraph 3`, and `InHurwitz4Orbit`; strengthened `adv2_4d_soddy_not_integral` to refute 4D `soddyRefl`; and added 10th refutation `adv10_t2a_sink_reachability_necessary` proving `HasReachableSink` is strictly necessary even for dissipative graphs (`sinklessGraph2`).
  - Removed dead `have` bindings and informal scratch comments in `ApollonianReciprocity.lean` and `MarkovHurwitzCluster.lean`, and cleaned stale `Matrix-Tree` section comments in `SandpileTropical.lean` and `rust/src/lib.rs`.
- **Interactive Observatory, Tooling, Hygiene & Documentation Fixes:**
  - **`studio/index.html`:** Fixed Mode 2 circle palette collision (`C4-01`: non-square mod-24 circles no longer reuse gold `#fbbf24`, which is now reserved exclusively for perfect squares); fixed `C4-02` unconditional HKRS message on non-HKRS presets; eliminated all inline `style=` attributes, added `type="button"` to all 11 buttons, added WCAG roving-`tabindex` Arrow/Home/End keyboard navigation, honored `prefers-reduced-motion: reduce`, and aligned Mode 1 3-drop caption wording.
  - **`.gitleaks.toml`, `ERRATA.md`, `scripts/make_figures.py`, `scripts/audit_repo.py`:** Fixed copy-pasted title and `SHA256SUMS` allowlist in `.gitleaks.toml`; fixed Build Standard 10-class taxonomy and historical audit heading in `ERRATA.md`; removed unused `n` parameter in `stabilize_grid` and typed `make_fig1(rust_summary: dict[str, Any])`; expanded `audit_repo.py` to enforce zero inline `style=`, zero `.innerHTML`, and explicit `type="button"` across all three HTML portals; added `docs/adr/0003-v3-termination-descent-and-general-soddy.md`; regenerated figures, zero-warning AMS-LaTeX PDF, deterministic arXiv tarball, dual timestamps, and SHA-256 manifests.

## [2.1.0] - 2026-11-26

### Added & Hardened — 3-Cycle Adversarial Audit (`28` Findings Resolved Across Lean, Rust, C11, Python, Paper, Web, CI & Docs)
- **Lean 4.35.0 Formal Hardening (`lean/`):**
  - Added `lean/VerifyAllDecls.lean`, a Lean 4 metaprogram running `Lean.collectAxioms` exhaustively across all **818 declarations** under `ApollonianSandpileMarkov.*` (strictly within `[propext, Classical.choice, Quot.sound]`, zero forbidden axioms).
  - Expanded `NonVacuity.lean` with constructive witnesses for `rootHKRS2`, `rootHKRS3`, `lapZ2 uZ2_lap3a ≤ 3`, and `cohnA0.det = 1 ∧ cohnB0.det = 1`.
  - Expanded `Adversarial.lean` from 6 to **9 machine-checked refutations** (`adv7_t2d_mean_equation_necessary`, `adv8_t2a_legal_trace_necessary`, `adv9_octahedral_strip_hits_square_and_double_square`).
- **Oracles, Fuzzing & Tests (`rust/`, `native/`, `python/`, `tests/`):**
  - Added `python/asm_verify/__main__.py` (`python -m asm_verify --json ...`), strict `ValueError` validation across all Python oracle entrypoints, renamed the final legacy JSON key `"unobstructed_4899"` → `"square_contrast_4899"`, and expanded `tests/test_all.py` to `12/12` passing tests (`10/10` mutants killed).
  - Made Rust `exact_det_bareiss` total for `n = 0` with square-matrix assertion, guarded `smallest_prime_factor`, and expanded Rust tests from `3/3` to `6/6` (including `#[should_panic]` negative tests).
  - Expanded `native/fuzz_libfuzzer.c` from 3 to **all 7 algebraic laws**.
- **Audit Gates, Citations, Paper, Web & CI:**
  - Fixed `scripts/audit_repo.py` to validate `repo.yaml` unconditionally against committed `repo-standard.schema.json`, added Palomar + Lean forbidden-token (`axiom`, `implemented_by`, `@[extern`), markdown relative-link, HTML CSP/a11y/zero-`innerHTML`, blueprint declaration-existence, and SWHID checks.
  - Hardened `scripts/check_citations.py` to inspect BOTH `update-to` AND `updated-by` (plus `relation.is-retracted-by`) in Crossref and verify title/author surname overlap across all 23 live Crossref/arXiv entries.
  - Hardened `scripts/check_readme_axioms.py` to strict allowlist parsing of every `depends on axioms: [...]` block.
  - Switched `paper/main.tex` bibliography to `plainurl` (visible clickable DOIs in the PDF), aligned `pdftitle`, cited SWHID in `CITATION.cff`, `.zenodo.json`, `CITATION.bib`, and §5.4.
  - Added `.skip-link`, `#main-content`, `:focus-visible`, `aria-pressed`, and safe DOM creation (eliminating `.innerHTML` and inline styles) across `docs/index.html` and `blueprint/index.html`; upgraded CI to `actions/checkout@v5`, `actions/setup-python@v6`, `VerifyAllDecls.lean`, `openssl ts -reply` RFC 3161 check, and strict Python secret scan; added `docs/adr/0002-direct-detmat-and-statement-audit-remediation.md`; fixed broken relative link in `SUPPORT.md`, dead `oracle.py` path in `README.md`, and stale pre-audit wording in `docs/glossary.md`, `docs/architecture.md`, `docs/threat-model.md`, and `docs/benchmarks.md`.

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
