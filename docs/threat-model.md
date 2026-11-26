<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Threat Model (`docs/threat-model.md`)

| Threat Vector | Concrete Risk | Mitigation Implemented |
| :--- | :--- | :--- |
| **Hidden Lean axioms / `sorry` / `native_decide`** | Soundness collapse or unverified compiler trust | Zero `sorry`/`admit`/`native_decide` in built modules (`lean/PalomarChallenge.lean` holds 16 intentional comparator stubs) audited by `VerifyAxioms.lean`, `scripts/check_readme_axioms.py`, `scripts/audit_repo.py`, and `nanoda_bin` with `unpermitted_axiom_hard_error: true`. |
| **Vacuous theorem statements / specification gaming** | Proving trivially true implications or weakened statements | Explicit `NonVacuity.lean` witnesses, `Adversarial.lean` sharp counterexamples, `docs/statement-fidelity.md`, and `lake comparator --paranoid` against `PalomarChallenge.lean`. |
| **Single proof-checker kernel bug** | Soundness bug in one Lean implementation | CI replay with `leanchecker` and `lean4lean` (modules `Solution`, `PalomarSolution`) and with `nanoda_bin`, `con-leche`, `con-ron` (export of three root declarations and their dependency closure), plus `lake comparator --paranoid` on the 16 comparator targets. |
| **Memory corruption / UB in native code** | Silent arithmetic overflow or buffer error in C11/Rust | Zero `unsafe` in Rust (`i128` exact arithmetic); ISO C11 compiled with `-std=c11 -Wall -Wextra -Werror -fsanitize=address,undefined` plus 100k deterministic fuzzer (`native/fuzz_asm.c`). |
| **Weak test suite / silent regressions** | Bugs slipping past unit tests | 600+ Hypothesis property tests, exact Rust $\leftrightarrow$ Python differential test, and 8 of 8 semantic mutants killed (`scripts/mutate.py`). |
| **Citation fabrication / artifact tampering** | Fake DOIs, drifted PDFs, or altered binaries | 20/20 live Crossref/arXiv citation audit (`scripts/check_citations.py`), deterministic `mtime=0` arXiv tarball, LF-normalized `MANIFEST.sha256`, SLSA `actions/attest-build-provenance@v2`, and Software Heritage archival. |
