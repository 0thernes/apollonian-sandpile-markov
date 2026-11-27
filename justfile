# SPDX-License-Identifier: Apache-2.0
# One-word verification, build, audit, and deployment commands (Build Standard A31, A36, B01)

default:
    @just --list

demo:
    PYTHONPATH=python python examples/quickstart_demo.py

rust:
    cd rust && cargo clippy --all-targets -- -D warnings && cargo test --release && cargo run --release -- --json ../results/rust_summary.json

c11:
    gcc -std=c11 -O2 -Wall -Wextra -Werror -fsanitize=address,undefined native/asm_verify.c -o native/asm_verify && ./native/asm_verify
    gcc -std=c11 -O2 -Wall -Wextra -Werror -fsanitize=address,undefined native/fuzz_asm.c -o native/fuzz_asm && ./native/fuzz_asm

fuzz:
    clang -std=c11 -O2 -Wall -Wextra -Werror -fsanitize=fuzzer,address,undefined native/fuzz_libfuzzer.c -o native/fuzz_libfuzzer && ./native/fuzz_libfuzzer -max_total_time=5

python:
    PYTHONPATH=python python -m asm_verify

lint:
    ruff check python tests scripts examples
    mypy python scripts tests examples
    cd rust && cargo clippy --all-targets -- -D warnings

test:
    PYTHONPATH=python pytest -v tests/test_all.py

mutate:
    PYTHONPATH=python python scripts/mutate.py

lean:
    cd lean && lake build && lake env lean VerifyAxioms.lean > /tmp/local_axioms.txt && diff -u --strip-trailing-cr ../results/lean_axioms.txt /tmp/local_axioms.txt && lake env lean VerifyAllDecls.lean && lake env leanchecker --fresh Solution && lake env leanchecker --fresh PalomarSolution

figures:
    python scripts/make_figures.py

paper:
    cd paper && tectonic -X compile main.tex --outdir build --keep-logs --keep-intermediates

citations:
    python scripts/check_citations.py

audit:
    python scripts/check_readme_axioms.py && python scripts/check_citations.py --offline && python scripts/audit_repo.py

reproduce: rust python lint test mutate lean figures paper audit
    sha256sum -c MANIFEST.sha256
    sha256sum -c SHA256SUMS
    sha256sum -c data/MANIFEST.sha256

deploy:
    git push origin main

rollback:
    @echo "Rollback Pages/main cleanly without force-push:"
    @echo "  git revert HEAD --no-edit && git push origin main"

all: rust python lint test mutate lean audit
