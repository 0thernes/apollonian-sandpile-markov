<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Configuration & Toolchain Reference (`docs/configuration.md`)

All builds, formal proofs, computational oracles, and manuscript compilations are fully deterministic and require **zero secrets or API keys** to reproduce offline.

## 1. Pinned Toolchains & Build Options

| Subsystem | Configuration File | Key Settings / Pins |
| :--- | :--- | :--- |
| Lean 4 Formal Proofs | `lean/lean-toolchain`, `lean/lakefile.toml` | `leanprover/lean4:v4.35.0`, zero Mathlib, `autoImplicit = false`, `relaxedAutoImplicit = false`, `linter.unusedVariables = true`, `linter.deprecated = true` |
| Palomar Contract Audit | `lean/comparator.json` | Challenge `PalomarChallenge`, Solution `PalomarSolution`, 17 theorems, permitted axioms strictly `["propext", "Quot.sound", "Classical.choice"]` |
| Rust Core Oracle | `rust/Cargo.toml` | Edition `2021`, zero external crates, `#![forbid(unsafe_code)]`, `opt-level = 3`, `lto = true`, `codegen-units = 1` |
| ISO C11 + Fuzzing | `native/asm_verify.c`, `native/fuzz_asm.c`, `native/fuzz_libfuzzer.c` | `-std=c11 -O2 -Wall -Wextra -Werror -fsanitize=address,undefined` (and `-fsanitize=fuzzer,address,undefined` for `libFuzzer`) |
| Python Oracle & Tooling | `pyproject.toml`, `requirements.txt` | Python `>= 3.11` (CI uses `3.13`), pinned `pytest`, `hypothesis`, `matplotlib`, `numpy`, `jsonschema`, `pyyaml`, `requests`, `ruff`, `mypy` |
| AMS-LaTeX Manuscript | `paper/main.tex` | `tectonic -X compile main.tex --outdir build --keep-logs --keep-intermediates` (strict zero-warning log check) |
| Secret Scanning | `.gitleaks.toml` | Standard gitleaks rules excluding compiled binaries and `.lake` caches |

## 2. Optional Environment Variables (`.env.example`)

None are required for default reproduction (`just reproduce`). Optional overrides:
- `PYTHONPATH=python`: exposes the zero-dependency `asm_verify` package without an editable install.
- `ASM_OFFLINE_CITATIONS=1`: runs `scripts/check_citations.py --offline` (structural BibTeX checks without live Crossref/arXiv HTTP calls).
- `GITHUB_TOKEN`: used only by maintainers when querying GitHub Releases / SLSA attestations via `gh`. Never commit tokens or `.env` files.

## 3. CLI Options

- **Rust binary:** `cargo run --release -- --json ../results/rust_summary.json` (omitting `--json` prints the exact JSON summary to stdout).
- **Citation auditor:** `python scripts/check_citations.py` (live Crossref/arXiv check) or `--offline` (offline structural check).
- **Browser Observatory & Blueprint:** Pure static HTML/CSS/JS with strict Content-Security-Policy meta tags (`default-src 'none'`); zero build step, zero network requests.
