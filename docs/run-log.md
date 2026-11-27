<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Verification Run Log (`docs/run-log.md`)

Append-only audit trail of local and CI verification runs (`Build Standard B40`). Every recorded exit code, commit SHA, and CI run ID corresponds to an actually executed command.

## Run History

| Date (UTC) | Version | Commit / CI Run | Environment | Command / Job Summary | Exit | Key Observed Output |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 2026-11-26 | `v1.0.0` | `0cf60c5` / CI `45849166650` | GitHub Actions (`ubuntu-latest`, `windows-latest`) | 6 Lean kernels (`lean`, `leanchecker`, `lean4lean`, `nanoda_bin`, `con-leche` 5,012 decls, `con-ron` 5,012 decls, `comparator --paranoid`), Rust, C11 ASan/UBSan, Python/Hypothesis/8-mutant, Tectonic, SLSA `#72728455` (Rekor `4128618149`) | `0` | All 7 CI jobs + Pages `45849166342` green; SWHID `swh:1:snp:5dac6e269ff3c673fa6ee9b7520365de44109a16` |
| 2026-11-26 | `v2.0.0` (pre-push) | Local ReFS Dev Drive | Windows 11 · Lean 4.35.0 | `lake build && lake env lean VerifyAxioms.lean && lake env leanchecker --fresh Solution && lake env leanchecker --fresh PalomarSolution` | `0` | 15 lake jobs (`SandpileTropical` 5.0s), 19/19 decls strictly `[propext, Classical.choice, Quot.sound]`, direct `detMat 9` in `T2b`/`T2f`, `--fresh` passed |
| 2026-11-26 | `v2.0.0` (pre-push) | Local ReFS Dev Drive | Windows 11 · Rust stable (`cargo`) | `cargo clippy --all-targets -- -D warnings && cargo test --release && cargo run --release -- --json ../results/rust_summary.json` | `0` | 0 clippy warnings (`#![forbid(unsafe_code)]`), 3/3 release tests in 0.05s |
| 2026-11-26 | `v2.0.0` (pre-push) | Local ReFS Dev Drive | Windows 11 · Python 3.13.12 | `ruff check`, `mypy`, `pytest -v`, `scripts/mutate.py`, `scripts/make_figures.py`, Node JS syntax check | `0` | 0 ruff errors, 0 mypy errors (8 files), 11/11 pytest, 10/10 (100.0%) mutation kill rate, 4 PDFs + social preview regenerated, JS syntax OK |
| 2026-11-26 | `v2.0.0` (pre-push) | Local ReFS Dev Drive | Windows 11 · Tectonic + Official `Audit-Repo.ps1` | AMS-LaTeX compile (`0` warnings), clean-room arXiv tarball compile, live 23/23 citation check, dual RFC 3161 `.tsr` + Bitcoin `.ots` stamping, `Audit-Repo.ps1` | `0` | `TeX warning count: 0`, clean-room tarball PASS, DigiCert `.tsr` (5,995 B) + 3-calendar `.ots` (756 B), `23/23` citations live, `Audit-Repo.ps1` 100.0% / 0 FAILs |
