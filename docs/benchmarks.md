<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Measured Verification Runtime Budgets (`docs/benchmarks.md`, v3.0.0)

All timings below are honest single-threaded wall-clock measurements recorded on the reference Windows 11 development workstation (ReFS Dev Drive) during `v3.0.0` verification:

| Verification Component | Command | Measured Wall Time | Result |
| :--- | :--- | :--- | :--- |
| Lean 4.35.0 incremental/clean build (15 targets, zero Mathlib) | `cd lean && lake build` | ~6 s (incr.) / ~28 s (clean) | 0 errors, 0 warnings |
| Exhaustive Lean axiom metaprogram (all 884 declarations) | `cd lean && lake env lean VerifyAllDecls.lean` | 5.76 s | 884/884 strictly 3 axioms |
| Lean fresh kernel replay (`Solution` + `PalomarSolution`) | `lake env leanchecker --fresh Solution && ...` | ~185 s | 0 errors (full `--fresh`) |
| Zero-dependency Rust clippy (`-D warnings`) | `cd rust && cargo clippy --all-targets -- -D warnings` | 0.80 s | 0 warnings (`#![forbid(unsafe_code)]`) |
| Zero-dependency Rust unit + negative tests (`--release`) | `cd rust && cargo test --release` | 11.84 s (w/ LTO build) | 6/6 passed |
| Rust full JSON oracle export (Markov $\le 10^7$, BFS, Bareiss) | `cargo run --release -- --json ...` | 3.80 s (w/ bin link) | Exact JSON emitted |
| Python pytest + Hypothesis (600+ trials) + CLI + differential | `pytest -v tests/test_all.py` | 0.96 s exec (1.68 s total) | 11 passed, 1 C11-skip on Win (12/12 in CI) |
| Semantic mutation suite (10 algebraic mutants) | `python scripts/mutate.py` | 17.55 s | 10/10 (100.0%) killed |
| Publication figures (4 vector PDFs + 1280×640 PNG) | `python scripts/make_figures.py` | ~15 s | All 5 visually verified |
| Clean-room arXiv tarball compile + dual RFC 3161 & OTS stamping | `python scripts/build_release_artifacts.py` | 6.99 s | **0 TeX warnings**, `Status: Granted.` |
