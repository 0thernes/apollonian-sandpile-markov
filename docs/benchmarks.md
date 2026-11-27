<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Measured Verification Runtime Budgets (`docs/benchmarks.md`, v2.1.0)

All timings below are honest single-threaded wall-clock measurements recorded on the reference Windows 11 development workstation (ReFS Dev Drive) during `v2.1.0` verification:

| Verification Component | Command | Measured Wall Time | Result |
| :--- | :--- | :--- | :--- |
| Lean 4.35.0 incremental/clean build (15 targets, zero Mathlib) | `cd lean && lake build` | ~5.4 s (incr.) / ~24 s (clean) | 0 errors, 0 warnings |
| Exhaustive Lean axiom metaprogram (all 818 declarations) | `cd lean && lake env lean VerifyAllDecls.lean` | 3.66 s | 818/818 strictly 3 axioms |
| Lean fresh kernel replay (`Solution` + `PalomarSolution`) | `lake env leanchecker --fresh Solution && ...` | 180.37 s | 0 errors (full `--fresh`) |
| Zero-dependency Rust clippy (`-D warnings`) | `cd rust && cargo clippy --all-targets -- -D warnings` | 0.57 s | 0 warnings (`#![forbid(unsafe_code)]`) |
| Zero-dependency Rust unit + negative tests (`--release`) | `cd rust && cargo test --release` | 0.04 s exec (9.29 s w/ LTO build) | 6/6 passed |
| Rust full JSON oracle export (Markov $\le 10^7$, BFS, Bareiss) | `cargo run --release -- --json ...` | 3.22 s (w/ bin link) | Exact JSON emitted |
| Python pytest + Hypothesis (600+ trials) + CLI + differential | `pytest -v tests/test_all.py` | 1.07 s exec (1.66 s total) | 12/12 passed |
| Semantic mutation suite (10 algebraic mutants) | `python scripts/mutate.py` | 15.52 s | 10/10 (100.0%) killed |
| Publication figures (4 vector PDFs + 1280×640 PNG) | `python scripts/make_figures.py` | ~15 s | All 5 visually verified |
| AMS-LaTeX white paper + clean-room arXiv tarball compile | `tectonic -X compile main.tex` | ~5 s | **0 TeX warnings**, clickable DOIs |
