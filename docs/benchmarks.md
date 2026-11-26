<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Measured Verification Runtime Budgets (`docs/benchmarks.md`)

All timings below are honest single-threaded wall-clock measurements recorded on the reference Windows development workstation (ReFS Dev Drive) during `v1.0.0` verification:

| Verification Component | Command | Measured Wall Time | Result |
| :--- | :--- | :--- | :--- |
| Lean 4.35.0 full clean build (15 targets, zero Mathlib) | `cd lean && lake build` | ~24 s | 0 errors, 0 warnings |
| Lean axiom audit + `leanchecker` (`Solution` + `PalomarSolution`) | `lake env lean VerifyAxioms.lean && leanchecker` | ~4 s | 18/18 strictly 3 axioms |
| Zero-dependency Rust unit tests (`--release`) | `cd rust && cargo test --release` | 0.04 s (exec) | 3/3 passed |
| Rust full JSON oracle export (Markov $\le 10^7$, BFS, Bareiss) | `cargo run --release -- --json ...` | ~0.2 s | Exact JSON emitted |
| Python pytest + Hypothesis (600+ trials) + differential | `pytest -v tests/test_all.py` | 0.50 s | 9/9 passed (1 C11 skipped on Win) |
| Semantic mutation suite (8 algebraic mutants) | `python scripts/mutate.py` | ~8 s | 8 of 8 killed |
| Publication figures (4 vector PDFs + 1280×640 PNG) | `python scripts/make_figures.py` | ~15 s | All 5 visually verified |
| AMS-LaTeX white paper + clean-room arXiv tarball compile | `tectonic -X compile main.tex` | ~5 s | 13 pages, **0 TeX warnings** |
