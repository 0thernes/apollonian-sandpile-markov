<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Multi-Layer Verification Architecture (`VERIFICATION.md`, v3.0.0)

This repository implements defense-in-depth verification across **six independent formal type-checking kernels**, an **exhaustive 884-declaration `Lean.collectAxioms` metaprogram audit**, a **live negative kernel rejection gate**, and **three independent computational languages**.

## 1. Six Independent Formal Type-Checking Kernels (Zero Mathlib)

All **19 exported audited declarations** (`T1a`–`T3e`, `T2f`, master conjunction `prove_all_apollonian_sandpile_markov_theorems`, `nonvac_all_hypotheses`, and `all_adversarial_refutations` covering 10 refutations) — plus all **884 declarations** under `ApollonianSandpileMarkov.*` checked exhaustively by `lean/VerifyAllDecls.lean` — depend strictly on `[propext, Classical.choice, Quot.sound]` (`lean/PalomarChallenge.lean` holds 17 intentional `by sorry` stubs as the comparator contract and is not a build target). In GitHub Actions (`lean4-six-kernels`), verification runs across six independent kernels:

1. **Lean 4.35.0 Kernel** (`lake build` + `VerifyAxioms.lean` diffed against `results/lean_axioms.txt` + exhaustive `VerifyAllDecls.lean` across all 884 declarations)
2. **`leanchecker --fresh`** (replays `Solution` and `PalomarSolution`)
3. **`leanchecker-paranoid`** (`lean4lean` independent Lean-in-Lean kernel replaying `Solution` and `PalomarSolution`)
4. **`nanoda_bin`** (independent Rust kernel checking the exported three root declarations and their dependency closure with `unpermitted_axiom_hard_error: true`, permitted axioms strictly `["propext", "Classical.choice", "Quot.sound"]`)
5. **`con-leche`** (independent verified export checker on the exported three root declarations and their dependency closure)
6. **`con-ron`** (independent verified export checker on the exported three root declarations and their dependency closure)
7. **Palomar Statement Fidelity Contract:** `lake comparator --config comparator.json --paranoid` verifying that `PalomarSolution` proves all 17 literal propositions declared in `PalomarChallenge` with zero `sorry` and zero extra axioms.
8. **Live Negative Kernel Rejection Gate:** In CI, three hostile tamperings are tested in `/tmp` — (a) injecting a false theorem via `sorry`, (b) injecting a custom `axiom` bypass, and (c) altering a theorem statement in a temporary comparator check — proving the toolchain and axiom audit **fail closed** on every bypass attempt.

## 2. Three Independent Computational Oracles

- **Zero-Dependency Rust (`rust/`):** `#![forbid(unsafe_code)]`, zero warnings under `cargo clippy --all-targets -- -D warnings`, 6 unit & negative/edge-case tests (`cargo test --release`), 128-bit exact Bareiss determinants (`192, 100352, 1092, 5393920`), BFS orbit audits across Apollonian/Octahedral/Soddy packings, $15\times 15$ Dhar critical identities on $\mathbb{Z}^2$ and $\mathbb{A}_2$, Markov tree audit up to $10^7$, 5-step symbolic cluster test, and Hurwitz `n=4` exhaustive search. Tested on both `ubuntu-latest` and `windows-latest`.
- **ISO C11 (`native/asm_verify.c`, `native/fuzz_asm.c`, `native/fuzz_libfuzzer.c`):** Strict `-std=c11 -Wall -Wextra -Werror -fsanitize=address,undefined` independent verifier (Apollonian, Octahedral BFS, Bareiss determinants, $\mathbb{Z}^2$/$\mathbb{A}_2$ Dhar identities, 5-step cluster, Markov mod-32, Hurwitz `n=4`), `100,000`-iteration 7-law deterministic fuzzer, plus a 7-law coverage-guided `libFuzzer` target (`clang -fsanitize=fuzzer,address,undefined -max_total_time=5`).
- **Python Exact Oracle + Property + Differential + Mutation (`python/`, `tests/`, `scripts/mutate.py`):**
  - Zero errors under `ruff check python tests scripts examples` and `mypy python scripts tests examples` (10 Python source files)
  - `12/12` pytest tests including 600+ Hypothesis property trials, negative input validation, `python -m asm_verify --json` CLI verification, exact `< 1e-14` 3D Soddy tangency verification, and bit-for-bit Rust $\leftrightarrow$ Python differential consistency
  - **10/10 (100.0%) semantic mutation kill rate** (`scripts/mutate.py`)

## 3. Manuscript, Citation & Artifact Integrity

- **Live Citation Audit (`scripts/check_citations.py`):** 23/23 BibTeX entries verified live against Crossref DOI (`update-to` + `updated-by` retraction checks + title/author overlap) and arXiv APIs (0 failures, 0 retractions); PDF uses `plainurl` for clickable visible DOIs.
- **Zero-Warning AMS-LaTeX Compilation:** `tectonic -X compile main.tex` produces 0 overfull hboxes, 0 underfull hboxes/vboxes, 0 undefined refs/cites; clean-room extraction of deterministic `mtime=0` `dist/arxiv_submission.tar.gz` compiles identically.
- **Cryptographic Provenance:** `MANIFEST.sha256` + `SHA256SUMS` + `data/MANIFEST.sha256` (all LF-normalized) + dual DigiCert RFC 3161 (`data/MANIFEST.sha256.tsr`, verified with `openssl ts -reply` `Status: Granted.`) & 3-calendar Bitcoin OpenTimestamps (`data/MANIFEST.sha256.ots`) + GitHub Actions SLSA build provenance (`actions/attest-build-provenance@v2`) + Software Heritage snapshot archival (`swh:1:snp:392d116f12dbe6820df783848373d27bbf138c55` for `v2.0.0`).
