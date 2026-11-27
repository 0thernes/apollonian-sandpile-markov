<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Contributing to `apollonian-sandpile-markov`

Contributions, independent verification audits, and mathematical extensions are welcome.

## Standards
- **Lean 4 Proofs (`lean/`):** Must remain **zero-Mathlib** (`leanprover/lean4:v4.35.0`), zero `sorry`, zero `admit`, zero `native_decide`, zero custom axioms, passing `lake build`, `VerifyAxioms.lean`, `VerifyAllDecls.lean`, `leanchecker --fresh`, and all six CI kernels.
- **Computational Oracles (`rust/`, `native/`, `python/`):** Must remain zero-dependency for Rust and ISO C11 (zero `unsafe`, `-Wall -Wextra -Werror -fsanitize=address,undefined`), preserve bit-for-bit Rust $\leftrightarrow$ Python differential consistency, and maintain 100% mutation kill rate (`scripts/mutate.py`).
- **Dual License:** Code contributions are accepted under Apache-2.0 (`LICENSE-CODE`); scholarly prose/documentation/figures under CC-BY-4.0 (`LICENSE`). Every source file carries an `SPDX-License-Identifier` header.
- **Finding Taxonomy:** Report issues using the 10-class Build Standard v1.2.0 dropdown (`bug`, `error`, `issue`, `problem`, `concern`, `dilemma`, `conflict`, `gap`, `hole`, `blindspot`).
