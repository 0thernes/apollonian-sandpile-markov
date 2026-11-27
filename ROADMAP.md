<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Roadmap (`ROADMAP.md`)

## Shipped — `v2.1.0` (2026-11-26)
- **3-Cycle Adversarial Hardening Release (`28` findings resolved):** Added exhaustive 818-declaration `Lean.collectAxioms` audit (`VerifyAllDecls.lean`), expanded `NonVacuity.lean` & `Adversarial.lean` (9 refutations including `T2d` & `T2a` hypothesis-necessity sharpness), added `python -m asm_verify` CLI + strict input validation + 6/6 Rust tests + 7-law `libFuzzer`, hardened `audit_repo.py` (unconditional local schema, Palomar, markdown links, HTML CSP/a11y, blueprint decls) & `check_citations.py` (`update-to` + `updated-by` retractions + title/author overlap), switched PDF bibliography to `plainurl` clickable DOIs, and added OpenSSL RFC 3161 verification and SWHID metadata.

## Shipped — `v2.0.0` (2026-11-26)
- **Full Statement-Audit Resolution (13 Paper + 9 Formal-Code Items, see `ERRATA.md`):** Added zero-Mathlib general `n × n` Laplace determinant `detMat` with verified row-operation soundness proving `detMat 9 (gridLap 3) = 100,352` directly inside `T2b` and `detMat 9 (a2GridLap 3) = 5,393,920` directly inside new theorem **`T2f`** (`t2f_a2_grid_orders_and_dhar_identity`, alongside Klein-4 similarity and legal `A_2` Dhar traces), expanded `T1e` to all 5 3D Soddy form preservations, exported `3 ∣ tr` in `T3a`, added `T2d`/`IsStabilizingOdometer` witnesses in `NonVacuity.lean`, renamed `rootSquareContrast`, and credited Zhang (2007), Shi et al. (2025), and Hurwitz (1907) across 23 live-verified BibTeX citations (`16` headline statements, `19` kernel-audited declarations).
- **100.0% Official Build Standard v1.2.0 Audit (`Audit-Repo.ps1` & `audit-repo.sh`):** Zero FAILs across all applicable items, zero `ruff`/`mypy`/`clippy` diagnostics, `#![forbid(unsafe_code)]`, 10/10 (100%) mutation kill rate, coverage-guided `libFuzzer`, live negative Lean kernel rejection gate, exact `< 1e-14` 3D Soddy tangency coordinates in `studio/index.html`, and dual RFC 3161 + OpenTimestamps cryptographic timestamps.

## Shipped — `v1.0.0` (2026-11-26)
- Zero-Mathlib Lean 4.35.0 formalization of 15 headline theorems (`T1a`–`T3e`), `NonVacuity`, and `Adversarial` (18 audited declarations, strictly `[propext, Classical.choice, Quot.sound]`).
- Six-kernel CI verification (`lean`, `leanchecker`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron` + `lake comparator --paranoid`).
- Independent Rust, ISO C11 (ASan/UBSan + 100k fuzz), and Python + Hypothesis + 8/8 (100%) mutation suite.
- Zero-warning AMS-LaTeX white paper, 4 vector PDF figures, deterministic clean-room arXiv tarball, and live 4-mode GitHub Pages Observatory + Proof Blueprint.

## Future Research Directions (`v2.2.0+`, Open)
- Extend Pillar I formalizations to additional Bianchi rings $\mathbb{Q}(\sqrt{-d})$ ($d \in \{3, 7, 11\}$) and higher-conductor Apollonian reciprocity obstructions.
- Extend symbolic Markov quiver cluster mutation proofs (`T3d`) beyond step 5 and explore formalizing Lee–Schiffler snake-graph positivity.
- Submit arXiv preprint (`dist/arxiv_submission.tar.gz`) and Zenodo archival deposit under independent researcher metadata.
