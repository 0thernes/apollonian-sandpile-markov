<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Clean-Clone Replication Protocol (`REPLICATION.md`, v1.0.0)

## Prerequisites

- **Lean 4.35.0** via [elan](https://github.com/leanprover/elan) (automatically selects `leanprover/lean4:v4.35.0` from `lean/lean-toolchain`).
- **Rust stable** (`cargo`, zero external crates required).
- **Python 3.11+** with packages from `requirements.txt`.
- **GCC or Clang** (Linux/macOS, for ISO C11 ASan/UBSan + fuzz suite).
- **Tectonic** (for rebuilding the AMS-LaTeX white paper and verifying the clean-room arXiv tarball).

## Step-by-Step Clean-Clone Verification

```bash
git clone https://github.com/0thernes/apollonian-sandpile-markov.git
cd apollonian-sandpile-markov

# 1. Verify Lean 4.35.0 proofs & axiom footprint (zero Mathlib)
(cd lean && lake build && lake env lean VerifyAxioms.lean > /tmp/local_axioms.txt && diff -u --strip-trailing-cr ../results/lean_axioms.txt /tmp/local_axioms.txt && lake env leanchecker Solution && lake env leanchecker PalomarSolution)

# 2. Verify Rust exact core and regenerate results/rust_summary.json
(cd rust && cargo test --release && cargo run --release -- --json ../results/rust_summary.json)

# 3. Verify ISO C11 independent implementation + 100k fuzzer (Linux/macOS)
gcc -std=c11 -O2 -Wall -Wextra -Werror -fsanitize=address,undefined native/asm_verify.c -o native/asm_verify
./native/asm_verify
gcc -std=c11 -O2 -Wall -Wextra -Werror -fsanitize=address,undefined native/fuzz_asm.c -o native/fuzz_asm
./native/fuzz_asm

# 4. Verify Python oracle, Hypothesis tests, Rust-Python differential tests, and 100% mutation kill rate
python -m venv .venv && source .venv/bin/activate
pip install -r requirements.txt
PYTHONPATH=python python python/asm_verify/__init__.py
PYTHONPATH=python pytest -v tests/test_all.py
PYTHONPATH=python python scripts/mutate.py
PYTHONPATH=python python examples/quickstart_demo.py

# 5. Regenerate figures, compile AMS-LaTeX white paper, and verify clean-room arXiv bundle
python scripts/make_figures.py
(cd paper && tectonic -X compile main.tex --outdir build --keep-logs --keep-intermediates)
mkdir -p /tmp/arxiv_verify && tar -xzf dist/arxiv_submission.tar.gz -C /tmp/arxiv_verify
(cd /tmp/arxiv_verify && tectonic -X compile main.tex)

# 6. Verify verbatim README axioms, citations, cryptographic manifest, and 90/90 audit
python scripts/check_readme_axioms.py
python scripts/check_citations.py --offline
sha256sum -c MANIFEST.sha256
python scripts/audit_repo.py
```

## Windows PowerShell Note

If cloning into a path containing square brackets `[...]`, pass `-LiteralPath` to PowerShell file cmdlets (`Set-Location -LiteralPath`, `Get-Content -LiteralPath`).
