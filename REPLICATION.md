<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Clean-Clone Replication Protocol (`REPLICATION.md`, v2.1.0)

## Prerequisites

- **Lean 4.35.0** via [elan](https://github.com/leanprover/elan) (automatically selects `leanprover/lean4:v4.35.0` from `lean/lean-toolchain`).
- **Rust stable** (`cargo`, `clippy`, zero external crates required).
- **Python 3.11+** with packages from `requirements.txt`.
- **GCC and Clang** (Linux/macOS, for ISO C11 ASan/UBSan + 100k 7-law fuzz + `libFuzzer`).
- **Tectonic** (for rebuilding the AMS-LaTeX white paper and verifying the clean-room arXiv tarball).

## Step-by-Step Clean-Clone Verification

```bash
git clone https://github.com/0thernes/apollonian-sandpile-markov.git
cd apollonian-sandpile-markov

# 1. Verify Lean 4.35.0 proofs, axiom footprints (19 exports + 818 decls), and --fresh kernel replay (zero Mathlib)
(cd lean && lake build && lake env lean VerifyAxioms.lean > /tmp/local_axioms.txt && diff -u --strip-trailing-cr ../results/lean_axioms.txt /tmp/local_axioms.txt && lake env lean VerifyAllDecls.lean && lake env leanchecker --fresh Solution && lake env leanchecker --fresh PalomarSolution)

# 2. Verify zero-unsafe Rust core (clippy -D warnings, release tests, JSON summary)
(cd rust && cargo clippy --all-targets -- -D warnings && cargo test --release && cargo run --release -- --json ../results/rust_summary.json)

# 3. Verify ISO C11 independent implementation, 100k 7-law fuzzer & libFuzzer (Linux/macOS)
gcc -std=c11 -O2 -Wall -Wextra -Werror -fsanitize=address,undefined native/asm_verify.c -o native/asm_verify && ./native/asm_verify
gcc -std=c11 -O2 -Wall -Wextra -Werror -fsanitize=address,undefined native/fuzz_asm.c -o native/fuzz_asm && ./native/fuzz_asm
clang -std=c11 -O2 -Wall -Wextra -Werror -fsanitize=fuzzer,address,undefined native/fuzz_libfuzzer.c -o native/fuzz_libfuzzer && ./native/fuzz_libfuzzer -max_total_time=5

# 4. Verify Python oracle, ruff, mypy, Hypothesis, differential tests & 10/10 (100%) mutation kill rate
python -m venv .venv && source .venv/bin/activate
pip install -r requirements.txt
ruff check python tests scripts examples
mypy python scripts tests examples
PYTHONPATH=python python -m asm_verify
PYTHONPATH=python pytest -v tests/test_all.py
PYTHONPATH=python python scripts/mutate.py
PYTHONPATH=python python examples/quickstart_demo.py

# 5. Regenerate figures, compile AMS-LaTeX white paper, and verify clean-room arXiv bundle
python scripts/make_figures.py
(cd paper && tectonic -X compile main.tex --outdir build --keep-logs --keep-intermediates)
mkdir -p /tmp/arxiv_verify && tar -xzf dist/arxiv_submission.tar.gz -C /tmp/arxiv_verify
(cd /tmp/arxiv_verify && tectonic -X compile main.tex)

# 6. Verify verbatim README axioms, citations, cryptographic manifests, and 90/90 audit
python scripts/check_readme_axioms.py
python scripts/check_citations.py --offline
sha256sum -c MANIFEST.sha256
sha256sum -c SHA256SUMS
sha256sum -c data/MANIFEST.sha256
python scripts/audit_repo.py
```

## Replication Log

> **Honesty Note:** Entries below record clean-clone automated CI runs on GitHub-hosted Ubuntu & Windows runners plus local Windows developer reproduction. External third-party human reproduction is welcomed via GitHub Issues and is currently pending.

| Date | Version | Commit / Tag | Environment | Scope Verified | Outcome |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 2026-11-26 | `v1.0.0` | `0cf60c5` | GitHub Actions (`ubuntu-latest` + `windows-latest`, CI run `45849166650`) | 6 Lean kernels (`lean`, `leanchecker`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`, `comparator --paranoid`), Rust, C11 ASan/UBSan, Python/Hypothesis/8-mutant, Tectonic PDF + arXiv tarball, SLSA `#72728455` | PASS (internal CI clean-clone) |
| 2026-11-26 | `v2.0.0` | `cdadedb` | GitHub Actions (`ubuntu-latest` + `windows-latest`, CI run `45943369402`, Pages `45943369337`) | All 19 Lean decls (`T1a`–`T3e` + `T2f`) + `--fresh` + 6 kernels + negative rejection gate, Rust `#![forbid(unsafe_code)]`, C11 + 7-law fuzz + `libFuzzer`, Python `ruff`/`mypy`/11 tests/10-mutant 100%, Tectonic + arXiv + SLSA `#72946806` (Rekor `4141939272`) + SWHID `swh:1:snp:392d116f12dbe6820df783848373d27bbf138c55` | PASS (internal CI clean-clone; 7/7 CI jobs green) |
| 2026-11-26 | `v2.1.0` | `v2.1.0` (verified locally & pushed to `origin main`) | Local Windows 11 (ReFS Dev Drive) + GitHub Actions (`ubuntu-latest` + `windows-latest`) | Exhaustive 818-decl `VerifyAllDecls.lean`, 9 adversarial refutations, 6/6 Rust tests, 7-law `libFuzzer`, 12/12 Python tests + `python -m asm_verify`, 10/10 mutants, live 23/23 Crossref (`updated-by` + title/author) & arXiv audit, `plainurl` clickable DOIs, OpenSSL RFC 3161 check, 100% `audit-repo.sh` | PASS (internal clean-clone; external human reproduction pending) |

## Windows PowerShell Note

If cloning into a path containing square brackets `[...]`, pass `-LiteralPath` to PowerShell file cmdlets (`Set-Location -LiteralPath`, `Get-Content -LiteralPath`).
