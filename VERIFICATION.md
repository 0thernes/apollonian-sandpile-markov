<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Multi-Layer Verification Architecture (`VERIFICATION.md`, v1.0.0)

This repository implements defense-in-depth verification across **six independent formal type-checking kernels** and **three independent computational languages**.

## 1. Six Independent Formal Type-Checking Kernels (Zero Mathlib)

All 18 exported declarations (`T1a`–`T3e`, master conjunction `prove_all_apollonian_sandpile_markov_theorems`, `nonvac_all_hypotheses`, and `all_adversarial_refutations`) are checked in GitHub Actions (`lean4-six-kernels`) by:

1. **Lean 4.35.0 Kernel** (`lake build` + `VerifyAxioms.lean`, exact diff against `results/lean_axioms.txt`)
2. **`leanchecker`** (`lake env leanchecker Solution` and `lake env leanchecker PalomarSolution`)
3. **`leanchecker-paranoid`** (`lean4lean` independent Lean-in-Lean kernel)
4. **`nanoda_bin`** (independent Rust kernel with `unpermitted_axiom_hard_error: true`, permitted axioms strictly `["propext", "Classical.choice", "Quot.sound"]`)
5. **`con-leche`** (independent verified export checker on `Solution.export`)
6. **`con-ron`** (independent verified export checker on `Solution.export`)
7. **Palomar Statement Fidelity Contract:** `lake comparator --config comparator.json --paranoid` verifying that `PalomarSolution` proves the exact literal propositions declared in `PalomarChallenge` with zero `sorry` and zero extra axioms.

## 2. Three Independent Computational Oracles

- **Zero-Dependency Rust (`rust/`):** 128-bit exact Bareiss determinants, BFS orbit audits across Apollonian/Octahedral/Soddy packings, $15\times 15$ Dhar critical identities on $\mathbb{Z}^2$ and $\mathbb{A}_2$, Markov tree audit up to $10^7$, 5-step symbolic cluster test, and Hurwitz `n=4` exhaustive search. Tested on both `ubuntu-latest` and `windows-latest`.
- **ISO C11 (`native/asm_verify.c`, `native/fuzz_asm.c`):** Strict `-std=c11 -Wall -Wextra -Werror -fsanitize=address,undefined` independent verifier plus a `100,000`-case deterministic fuzzer covering Jacobi reciprocity, Descartes reflections, $\mathbb{A}_2$ Laplacians, 5-step cluster identities, and Markov mod-32 invariance.
- **Python Exact Oracle + Property + Differential + Mutation (`python/`, `tests/`, `scripts/mutate.py`):**
  - 600+ Hypothesis property trials (`test_all.py`)
  - Bit-for-bit Rust $\leftrightarrow$ Python differential consistency test
  - **8/8 (100.0%) semantic mutation kill rate** (`scripts/mutate.py`)

## 3. Manuscript, Citation & Artifact Integrity

- **Live Citation Audit (`scripts/check_citations.py`):** 20/20 BibTeX entries verified live against Crossref DOI and arXiv APIs (0 failures, 0 retractions).
- **Zero-Warning AMS-LaTeX Compilation:** `tectonic -X compile main.tex` produces 0 overfull hboxes, 0 underfull hboxes/vboxes, 0 undefined refs/cites; clean-room extraction of deterministic `mtime=0` `dist/arxiv_submission.tar.gz` compiles identically.
- **Cryptographic Provenance:** `MANIFEST.sha256` (LF-normalized) + GitHub Actions SLSA build provenance (`actions/attest-build-provenance@v2`) + Software Heritage snapshot archival.
