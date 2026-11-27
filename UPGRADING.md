<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Upgrading & Compatibility Policy (`UPGRADING.md`)

This repository follows [Semantic Versioning 2.0.0](https://semver.org/) anchored in `VERSION` and synchronized across `pyproject.toml`, `rust/Cargo.toml`, `CITATION.cff`, `CITATION.bib`, `.zenodo.json`, `lean/lakefile.toml`, and `lean/formalization.yaml`.

## Upgrading from `v2.0.0` to `v2.1.0`

`v2.1.0` is a backwards-compatible hardening release across all Lean proofs, oracles, audit gates, manuscript bibliography, and static web apps (all 17 `PalomarChallenge`/`PalomarSolution` theorem statements remain unchanged):

1. **Lean 4:** Added exhaustive 818-declaration metaprogram audit `lean/VerifyAllDecls.lean`, expanded `NonVacuity.lean` (`rootHKRS2`/`rootHKRS3`, `lapZ2 uZ2_lap3a ≤ 3`, Cohn seed dets), and expanded `Adversarial.lean` to 9 refutations (`adv7`–`adv9`).
2. **Oracles & CLI:** Added `python -m asm_verify [--json PATH]`, strict `ValueError` validation on invalid lattice/size/index inputs, total Rust `exact_det_bareiss` with squareness check (`6/6` Rust tests), 7-law `native/fuzz_libfuzzer.c`, and renamed the last legacy JSON report key `"unobstructed_4899"` → `"square_contrast_4899"` in `results/rust_summary.json` and `results/exact_verification_report.json`.
3. **Manuscript, Web & Governance:** Switched PDF bibliography to `plainurl` (visible clickable DOIs), added SWHID to `CITATION.cff`/`.zenodo.json`, hardened `audit_repo.py` / `check_citations.py` / `check_readme_axioms.py`, and upgraded accessibility & safe DOM construction in `docs/index.html` and `blueprint/index.html`.

## Upgrading from `v1.0.0` to `v2.0.0`

`v2.0.0` is a comprehensive formalization, oracle, provenance, and Build Standard v1.2.0 / Playbook v1.3 hardening upgrade:

1. **Lean 4 Contract Extension & Statement-Audit Remediation (Breaking Change to `AllApollonianSandpileMarkovTheorems` arity):**
   - Added zero-Mathlib general `n × n` Laplace determinant `detMat` with verified row-operation soundness in `lean/ApollonianSandpileMarkov/SandpileTropical.lean`, proving `detMat 9 (gridLap 3) = 100,352` directly inside `T2b` AND adding **Theorem `T2f` (`t2f_a2_grid_orders_and_dhar_identity`)** proving `det4 (a2GridLap 2) = 1,092`, `detMat 9 (a2GridLap 3) = 5,393,920`, Klein-4 block similarity, and legal `A_2` Dhar toppling traces (`[4,3,3,4]`, `[4,2,3,2,0,2,3,2,4]`) in Lean 4 (no Matrix–Tree link is formalized).
   - Resolved all 9 formal-code statement-audit items (all 5 3D Soddy form preservations in `T1e`, explicit `3 ∣ tr` conjuncts in `T3a`, `rootSquareContrast` / `adv1_square_contrast_hits_square` rename, `T2d` & `IsStabilizingOdometer` witnesses in `NonVacuity.lean`, `lake-manifest.json` package name fix, `formalization.yaml` update).
   - `AllApollonianSandpileMarkovTheorems` now conjoins **16 headline statements** (`T1a`–`T3e` plus `T2f`), and `VerifyAxioms.lean` audits **19 declarations** (all strictly within `[propext, Classical.choice, Quot.sound]`). Any downstream Lean proof destructuring `AllApollonianSandpileMarkovTheorems` should add the `T2f` conjunct between `T2e` and `T3a`.
2. **Rust & Python Oracles (Backwards-Compatible Additions):**
   - Added `#![forbid(unsafe_code)]` to `rust/src/lib.rs` and `rust/src/main.rs` with zero `cargo clippy --all-targets -- -D warnings` diagnostics.
   - Python `asm_verify` now exposes `a2_2x2_id` in `full_oracle_report()["pillar2"]` and passes `ruff check` and `mypy` with zero errors across the entire repository.
   - `scripts/mutate.py` expanded from 8 to 10 semantic mutants (`10/10 = 100.0%` kill rate).
3. **ISO C11 & Fuzzing:**
   - `native/asm_verify.c` now verifies exact Bareiss determinants (`192, 100352, 1092, 5393920`), exact `A_2 3×3` Dhar identity vector, octahedral BFS orbit, 5-step symbolic cluster identities, and all four Hurwitz `n=4` entries.
   - Added `native/fuzz_libfuzzer.c` (`LLVMFuzzerTestOneInput`) compiled under `clang -fsanitize=fuzzer,address,undefined`.
4. **Interactive Observatory (`studio/index.html`):**
   - Fixed Mode 3 (`3D Soddy Sphere Cluster`) exact analytical center coordinates ($z_{13} = +1/78$, $z_{18} = +1/9$, $z_{15} = -1/10$, $\mathbf{p}_{25} = (-4/(25\sqrt{3}), 0, 13/150)$), achieving `< 1e-14` tangency error across all 10 sphere pairs (regression-tested in `tests/test_all.py`).
5. **Governance & Dual Cryptographic Timestamps:**
   - Split `docs/faq-glossary.md` into `docs/faq.md` and `docs/glossary.md`, added `docs/architecture.md`, `docs/configuration.md`, `docs/operations.md`, `docs/run-log.md`, `docs/reviews/`, `.github/labels.tsv`, `SHA256SUMS`, `data/MANIFEST.sha256`, `data/MANIFEST.sha256.tsr` (DigiCert RFC 3161), and `data/MANIFEST.sha256.ots` (Bitcoin OpenTimestamps).

## Deprecation Policy

- Existing theorem names (`t1a_...` through `t3e_...`) are never silently renamed or weakened.
- Any mathematical erratum is permanently documented in `ERRATA.md` and triggers a tagged patch/minor/major release rather than history rewrites.
