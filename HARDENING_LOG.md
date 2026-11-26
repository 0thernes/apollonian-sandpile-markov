<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Three-Cycle Hardening & Red-Team Audit Log (`HARDENING_LOG.md`)

Every defect, numerical discrepancy, formal proof obstacle, test-suite blindspot, and typographic issue uncovered across three full hardening cycles (following Build Standard v1.2.0 and Playbook v1.3 10-pass review) is recorded below with concrete fixes and verification evidence.

---

## Cycle 1 — Core Formalization, Multi-Language Numerics & Exact Algebra Audit

| # | Class | Target | Finding | Concrete Fix & Verification |
| :--- | :--- | :--- | :--- | :--- |
| 1.1 | `proof-soundness` | `lean/ApollonianSandpileMarkov/JacobiReciprocity.lean` | Missing `@[expose] public section` inside `module` blocked downstream unfolding of `IsPrime`, `jacobi`, and sign helpers. | Added `@[expose] public section`; verified clean downstream build across all 15 lake targets. |
| 1.2 | `proof-soundness` | `lean/ApollonianSandpileMarkov/ApollonianReciprocity.lean` | Core Lean 4.35.0 lacks Mathlib lemmas (`Int.natCast_dvd`, `Int.mul_self_nonneg`, `Int.ediv_add_emod`); initial `rootHKRS3` witness `(1,0)` had `gcd(21,45)=3`. | Replaced with self-contained core lemmas (`nat_dvd_natAbs_iff`, `sq_nonneg`, `omega`), switched witness to `(xb:=1, yb:=2)`, and corrected exact octahedral congruence RHS `b3*(b3-4*b1-4*b2)`. Built with 0 errors/0 warnings. |
| 1.3 | `proof-soundness` | `lean/ApollonianSandpileMarkov/SandpileTropical.lean` | Functional closure explosion during `decide` on 33-step `3×3` Dhar traces; `toppleListArr_sound` `Fin.cast` normalization mismatch. | Added `toppleListArr` + soundness lemma `toppleListArr_sound` with `Fin.cast_mk, Fin.eta`; built cleanly in 5.6s with 0 warnings. |
| 1.4 | `proof-soundness` | `lean/Challenge.lean`, `NonVacuity.lean` | `T1b_JacobiReciprocityMaster` had stale `jacobiNat` signature; `NonVacuity.lean:82` required beta-reduction before `omega`. | Synchronized `Challenge.lean` contract with `JacobiReciprocity.t1b_jacobi_reciprocity_master` and added `dsimp; omega`. All 18 declarations passed `lake build`, `VerifyAxioms.lean`, and `leanchecker`. |
| 1.5 | `numeric` | `rust/src/lib.rs` | Hardcoded initial expectation `det(L_{A_2, 2×2}) = 1056` and `det(L_{A_2, 3×3}) = 5,905,152` disagreed with exact Bareiss determinant. | Independently derived exact eigenvalues `6 * 7 * 26 = 1,092` and cross-checked Bareiss in both Rust (`i128`) and Python arbitrary-precision integers (`1,092` and `5,393,920`); updated assertions and passed `cargo test --release`. |

---

## Cycle 2 — Mutation Blindspots, Typing, Figure & Manuscript Visual Inspection

| # | Class | Target | Finding | Concrete Fix & Verification |
| :--- | :--- | :--- | :--- | :--- |
| 2.1 | `testing` | `scripts/mutate.py`, `tests/test_all.py` | Mutant `M06` (`deg=5` on 6-regular `A_2`) caused non-terminating sandpile toppling; `M05` allowed unbounded negative BFS drift; `M01` and `M06` survived because `tests/test_all.py` omitted direct tests for `jacobi(-1,n)`, `jacobi(2,n)`, and golden `e_{A_2, 3×3}`. | Fixed `M06` (`deg=7`), `M05` (`+1` perturbation), added 20s timeout + `-x` fail-fast, and added direct supplementary-law + golden `e_{A_2, 3×3} = [4,2,3,2,0,2,3,2,4]` assertions. Kill rate rose from 75% to **8/8 = 100.0%**. |
| 2.2 | `correctness` | `python/asm_verify/__init__.py` | `mypy` flagged `tuple(sorted(...))` returning `tuple[int, ...]` instead of `tuple[int, int, int]`. | Unpacked explicitly into 3-tuple; `mypy` passed with **0 issues**. |
| 2.3 | `visual` | `scripts/make_figures.py` (`fig1`–`fig4`) | Visual PDF inspection via `read_file` caught 4 defects: (1) `fig1(b)` legend listed `(9, 25, ..., 729)` instead of exact `(9, 36, ..., 900)`; (2) `fig2(b)` bottom annotation occluded pixels; (3) `fig3(c)` `P1/P4/P5` labels touched axis/curve and `fig3(a)` bottom leaves touched; (4) `fig4` top box title slightly overflowed box borders. | Corrected all 4 figures, regenerated vector PDFs, and visually re-verified every figure via `read_file` with 0 overlaps and 100% data fidelity. |
| 2.4 | `docs` | `paper/main.tex`, `paper/references.bib` | First Tectonic compile produced 7 overfull hboxes, 1 underfull hbox, 2 underfull vboxes, and hyperref PDF-string warnings; visual page-by-page inspection caught literal `\_` and `~` printed inside `\code{\detokenize{...}}`, draft notes in `T2d`/`T3b` proofs, and lowercased `Lean4lean` in Ref. 4. | Rewrote `T2d`/`T3b` proofs to match Lean verbatim, wrapped math/code in `\texorpdfstring`, removed redundant escapes inside `\code{...}`, protected `{Lean4Lean}` in BibTeX, verified 20/20 citations live via Crossref/arXiv, and achieved **0 TeX warnings** across all 13 pages + clean-room arXiv tarball compile. |

---

## Cycle 3 — Governance, Security, Provenance, Six-Kernel CI & Archival Audit

| # | Class | Target | Finding | Concrete Fix & Verification |
| :--- | :--- | :--- | :--- | :--- |
| 3.1 | `governance` | `repo.yaml`, `scripts/audit_repo.py` | Verified all 90 Build Standard v1.2.0 items (`A01`–`B45`) against `repo-standard.schema.json`, zero banned files (`dependabot.yml`, `renovate.json`, etc.), zero `sorry`/`admit`/`native_decide`, zero `"0thernes LLC"` policy violations, and version `1.0.0` sync across all 5 manifests. | `python scripts/audit_repo.py` passes cleanly. |
| 3.2 | `security` | `README.md`, `MANIFEST.sha256`, `.github/workflows/ci.yml` | Verified verbatim `results/lean_axioms.txt` match in `README.md`, LF-normalized SHA-256 checksums, Windows-safe CI paths (no `/tmp` on Windows), secret-scan hygiene, and SLSA build provenance (`actions/attest-build-provenance@v2`). | `check_readme_axioms.py`, `sha256sum -c MANIFEST.sha256`, and all multi-OS CI jobs verified green. |
| 3.3 | `deployment` | `studio/index.html`, `blueprint/index.html`, `docs/index.html`, `pages.yml` | Validated all inline JS with Node `new Function(...)`, audited WCAG landmarks/ARIA/skip-links (`A38`), and verified live HTTP 200 deployment on GitHub Pages plus Software Heritage snapshot and `0thernes-research-archive` registration (`0TH-2026-017`). | Verified live on GitHub Actions, GitHub Pages, and archive CI. |
