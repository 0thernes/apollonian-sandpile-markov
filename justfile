# SPDX-License-Identifier: Apache-2.0
# One-word verification & build commands (Build Standard A31)

default:
    @just --list

demo:
    PYTHONPATH=python python examples/quickstart_demo.py

rust:
    cd rust && cargo test --release && cargo run --release -- --json ../results/rust_summary.json

c11:
    gcc -std=c11 -O2 -Wall -Wextra -Werror -fsanitize=address,undefined native/asm_verify.c -o native/asm_verify && ./native/asm_verify
    gcc -std=c11 -O2 -Wall -Wextra -Werror -fsanitize=address,undefined native/fuzz_asm.c -o native/fuzz_asm && ./native/fuzz_asm

python:
    PYTHONPATH=python python python/asm_verify/__init__.py

test:
    PYTHONPATH=python pytest -v tests/test_all.py

mutate:
    PYTHONPATH=python python scripts/mutate.py

lean:
    cd lean && lake build && lake env lean VerifyAxioms.lean && lake env leanchecker Solution && lake env leanchecker PalomarSolution

figures:
    python scripts/make_figures.py

paper:
    cd paper && tectonic -X compile main.tex --outdir build --keep-logs --keep-intermediates

citations:
    python scripts/check_citations.py

audit:
    python scripts/check_readme_axioms.py && python scripts/check_citations.py --offline && python scripts/audit_repo.py

all: rust python test mutate lean audit
