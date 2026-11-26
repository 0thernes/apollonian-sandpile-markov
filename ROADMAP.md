<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Roadmap (`ROADMAP.md`)

## Shipped — `v1.0.0` (2026-11-26)
- Zero-Mathlib Lean 4.35.0 formalization of all 15 headline theorems (`T1a`–`T3e`), `NonVacuity`, and `Adversarial` (18 audited declarations, strictly `[propext, Classical.choice, Quot.sound]`).
- Six-kernel CI verification (`lean`, `leanchecker`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron` + `lake comparator --paranoid`).
- Independent Rust, ISO C11 (ASan/UBSan + 100k fuzz), and Python + Hypothesis + 8/8 (100%) mutation suite.
- Zero-warning 13-page AMS-LaTeX white paper, 4 vector PDF figures, deterministic clean-room arXiv tarball, and live 4-mode GitHub Pages Observatory + Proof Blueprint.

## Future Research Directions (`v1.1.0+`, Open)
- Extend Pillar I formalizations to additional Bianchi rings $\mathbb{Q}(\sqrt{-d})$ ($d \in \{3, 7, 11\}$) and higher-conductor Apollonian reciprocity obstructions.
- Machine-check the $2\times 2$ and $3\times 3$ $\mathbb{A}_2$ Kronecker block-diagonalizations (`det = 1,092` and `5,393,920`) inside Lean 4 alongside the $\mathbb{Z}^2$ proofs in `T2b`.
- Extend symbolic Markov quiver cluster mutation proofs (`T3d`) beyond step 5 and explore formalizing Lee–Schiffler snake-graph positivity.
- Submit arXiv preprint (`dist/arxiv_submission.tar.gz`) and Zenodo archival deposit under independent researcher metadata.
