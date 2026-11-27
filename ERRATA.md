<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Errata & Corrections Policy (`ERRATA.md`)

This file records post-release mathematical, formal, computational, bibliographic and typographic corrections discovered after `v1.0.0`, together with their resolution in `v2.0.0`. Frozen release tags (`v1.0.0`) are never rewritten in place; all fixes ship cleanly in `v2.0.0`.

## `v2.0.0` Resolution of the 2026-11-26 Statement Audit

Every single one of the **13 paper/bibliography items** and **9 formal-code items** identified in the 2026-11-26 independent statement audit below has been resolved in release `v2.0.0`:

- **Paper, Figures & Bibliography (13/13 resolved):** `paper/main.tex`, `paper/references.bib`, `scripts/make_figures.py` (`fig1`–`fig4` + `social-preview.png`), `studio/index.html`, `blueprint/index.html`, `docs/index.html`, and all Markdown docs were updated and rebuilt in `v2.0.0`:
  1. `T3b` mod-32 theorem credited to Ying Zhang (`\cite{zhang2007}`, *Acta Arith.* 128 (2007) 295–301, `arXiv:math/0612620`).
  2. `(-4,8,9,9)` no longer called unobstructed (explicitly notes HKRS `3n^2, 6n^2, n^4, 4n^4` obstructions; called square-hitting contrast packing).
  3. `T1c` narrowed to the three specific HKRS packings `(-3,5,8,8)`, `(-7,17,12,20)`, `(-11,21,24,28)`.
  4. `T1d` narrowed to mod-8 residue locking `(2,2,1,0,0,1)` + 5 standalone closed Jacobi evaluations; cites Shi et al. (`\cite{shi2025}`, `arXiv:2510.21702`).
  5. `T1e` described as the divisibility criterion `(d-1) ∣ 2 ↔ d ∈ {2,3}` (LMW 2002) + all five 3D Soddy form-preserving involutions.
  6. `T2a` hypotheses (`SandpileGraph` symmetric zero-diagonal adjacency, arbitrary degrees, no sink condition) and conclusion (uniqueness of legal stabilizing traces; no termination proof) aligned with Lean.
  7. `T2b` and `T2f` now export direct 9×9 Laplace determinants `detMat 9` (`100,352` and `5,393,920`) alongside block similarities; paper explicitly notes no Matrix–Tree or group-identity theorem is formalized.
  8. `T2d` described as an elementary $\mathbb{A}_2$ parity lemma with full mean-curvature hypothesis `M*K = 4A - 2B + 4C`; unsupported causal claim tying `T2d` to height-5 sandpile plateaus removed from Remark 3.5, Figure 2 caption, and Figure 2(b).
  9. `T2e` described as a lattice-polygon edge-normal closure identity and `2×2` determinant identity (Kalinin–Shkolnikov theorem not formalized).
  10. Cohn root matrix typo fixed from `[[2,1],[5,3]]` to **`B_0 = [[1,2],[2,5]]`** (trace 6, matching `cohnB0`).
  11. `"Fibonacci-odd branch"` removed (`29`, `433` are not Fibonacci numbers); described as the mutation path through `(2,5,29)`, `(5,29,433)`, `(29,433,37666)`.
  12. `T3d` narrowed to value positivity at positive integers (coefficient positivity by inspection) and `T3e` credited to Hurwitz (`\cite{hurwitz1907}`) for admissible coefficients `a ∈ {1,4}` with parity.
  13. `paper/references.bib` expanded to 23 live-verified entries (`zhang2007`, `shi2025`, `hurwitz1907` added; `baragar1993` 2017 reprint note added).
- **Formal Lean Code (9/9 resolved):**
  1. `lean/lake-manifest.json` package name fixed to `"ApollonianSandpileMarkov"`.
  2. `SandpileTropical.lean` & `Challenge.lean` (`T2b`, `T2f`): added zero-Mathlib general `n × n` Laplace determinant `detMat` + verified elementary row-operation soundness proving `detMat 9 (gridLap 3) = 100352` and `detMat 9 (a2GridLap 3) = 5393920` directly in-kernel.
  3. `MarkovHurwitzCluster.lean` & `Challenge.lean` (`T3a`): added explicit `(3 : Int) ∣ A.tr ∧ (3 : Int) ∣ B.tr ∧ (3 : Int) ∣ (Mat2.mul A B).tr` conjuncts to the exported statement.
  4. `ApollonianReciprocity.lean` & `Challenge.lean` (`T1e`): added `soddy3Q` preservation for all five 3D Soddy reflections `soddy3Refl1`–`soddy3Refl5`.
  5. `NonVacuity.lean`: added explicit constructive joint witness for the `T2d` hypothesis bundle (`u(x,y)=x^2, M=1, A=1, K=4, ψ=0`) and `IsStabilizingOdometer` witnesses for `gridGraph 2` and `a2GridGraph 3`.
  6. `ApollonianReciprocity.lean`, `Challenge.lean`, and `Adversarial.lean`: renamed `rootUnobstructed` → `rootSquareContrast` and `adv1_unobstructed_hits_square` → `adv1_square_contrast_hits_square`.
  7. `Adversarial.lean` & docs: honestly described as six refutations of false variants (no claim that every hypothesis is tight).
  8. `lean/formalization.yaml`: explicitly documents `17` intentional `by sorry` stubs in `PalomarChallenge.lean`, `19` audited declarations, and exact kernel-replay coverage.
  9. Existing declaration names (`t1d_...`, `t2e_...`, `t3d_...`, `t3e_...`) retained for comparator continuity with exact narrowed scopes documented everywhere.

## Pre-release issues

Issues found during the three internal hardening cycles (for example the A2 determinants 1,092 and 5,393,920, mutation-harness test gaps, the Figure 1 legend square range, and LaTeX escape cleanup) were resolved before tagging `v1.0.0` and are logged in [`HARDENING_LOG.md`](HARDENING_LOG.md).

## 2026-11-26 statement audit

An independent statement audit of commit `0cf60c5` (audit log: <https://github.com/0thernes/0thernes-research-archive/blob/main/docs/reviews/2026-11-26-statement-audit.md>) rebuilt the Lean project, re-ran the axiom audit, and compared every headline statement with its public description and with prior work. All 15 Lean statements are true as written. The errors below concern wording, attribution and scope. `README.md`, `CLAIMS.md`, `LIMITATIONS.md`, `CITATION.cff`, `lean/formalization.yaml` and `docs/*.md` were corrected on 2026-11-26; the paper and frozen PDF were not.

### Errors in the paper (`paper/main.tex` and the frozen PDF)

1. **Missing attribution of the mod-32 theorem (`T3b`).**
   - Where: `paper/main.tex` line 64 (Introduction, Pillar III contributions); lines 327–339 (subsection on `T3b`, Theorem `thm:t3b`); `paper/references.bib`.
   - What is wrong: the statement that every even Markov number is 2 mod 32, with witnesses 2 and 34, is presented as new ("we prove an exact 2-adic locking theorem"). It is Ying Zhang's theorem, which is not cited.
   - Correction: "We give a zero-Mathlib formalization of Zhang's theorem [Y. Zhang, *Congruence and uniqueness of certain Markoff numbers*, Acta Arith. 128 (2007) 295–301, arXiv:math/0612620] that every even Markov number is congruent to 2 modulo 32." Add the reference.
   - Affects a theorem statement: no (the statement is correct; attribution only).
2. **`(-4,8,9,9)` called unobstructed (`T1c`).**
   - Where: `paper/main.tex` line 169 (Theorem on `T1c`, contrast sentence), line 210 (orbit table row "Unobstructed"), line 223 (Figure 1 caption).
   - What is wrong: Haag–Kertzer–Rickards–Stange (arXiv:2307.02749, Appendix Table A) list quadratic obstructions `3n^2`, `6n^2` and quartic obstructions `n^4`, `4n^4` for this packing. It only lacks a square obstruction.
   - Correction: "the packing `(-4,8,9,9)`, which has the same mod-24 residue set and contains the square 9 (HKRS list `3n^2`, `6n^2` and fourth-power obstructions for it)".
   - Affects a theorem statement: no.
3. **Scope of `T1c`.**
   - Where: `paper/main.tex` line 62.
   - What is wrong: "formal proof of the ... global square obstruction on Apollonian packings" reads as the HKRS theorem in general. Lean covers three specific packings.
   - Correction: "a zero-Mathlib formalization of the HKRS square obstruction for the three packings `(-3,5,8,8)`, `(-7,17,12,20)`, `(-11,21,24,28)`".
   - Affects a theorem statement: no.
4. **`T1d` described as a Jacobi / reciprocity obstruction; prior work missing.**
   - Where: `paper/main.tex` line 62 (Introduction) and line 186 (octahedral subsection).
   - What is wrong: Lean proves mod-8 residue locking `(2,2,1,0,0,1)` on one orbit, which excludes squares at `b1, b2` and twice-squares at `b3, b6`. The five Jacobi values are closed evaluations, not linked to the orbit; "enforce global reciprocity obstruction" is not proved. Shi, Shi, Whitehead, Williams-Tracy and Zhang (arXiv:2510.21702, 2025) gave reciprocity obstructions for octahedral packings and are not cited.
   - Correction: "octahedral mod-8 residue locking on `(-6,10,17,40,24,17)`, excluding squares at `b1, b2` and twice-squares at `b3, b6` by congruence"; cite arXiv:2510.21702.
   - Affects a theorem statement: no (the Lean statement is unchanged; its description is narrowed).
5. **`T1e` called a "sharp Soddy integrality dichotomy".**
   - Where: `paper/main.tex` line 62 and line 223 (Figure 1 caption, panel d).
   - What is wrong: Lean states the arithmetic fact `(d-1) ∣ 2 ↔ d ∈ {2,3}` without a link to `d`-dimensional Soddy reflections, and form preservation for one 3D reflection only.
   - Correction: describe it as the divisibility fact used in the classical integrality argument (Lagarias–Mallows–Wilks 2002).
   - Affects a theorem statement: no.
6. **`T2a` hypotheses and conclusion.**
   - Where: `paper/main.tex` line 63 ("Universal Abelian sandpile confluence") and lines 232–236 (definitions and theorem on `T2a`).
   - What is wrong: the paper describes "a finite sinked graph" with `deg(u) ≥ ∑_v A_uv` and confluence. The Lean structure `SandpileGraph` (`lean/ApollonianSandpileMarkov/SandpileTropical.lean` line 228) has symmetric zero-diagonal adjacency and arbitrary degrees, with no sink condition, and no termination theorem is proved.
   - Correction: "toppling commutativity, the least action bound, and uniqueness of legal stabilizing traces (termination is not proved)".
   - Affects a theorem statement: yes (the paper's statement of the hypotheses and of confluence does not match the Lean theorem).
7. **`T2b` "Matrix–Tree determinant" 100,352.**
   - Where: `paper/main.tex` line 63, line 104 (summary table), line 246 (theorem title "Exact Matrix–Tree Orders").
   - What is wrong: Lean proves `det(L_{2×2}) = 192` and, for the 3×3 grid, an integer similarity to a block-diagonal matrix whose block determinants multiply to 100,352. It does not state `det(L_{3×3}) = 100,352`, and no Matrix–Tree or sandpile-group-order link is formalized. The value itself is correct (recomputed by the audit).
   - Correction: "`det = 192`, and for the 3×3 grid a kernel-checked block similarity whose block determinants multiply to 100,352".
   - Affects a theorem statement: yes (the theorem title and summary claim more than Lean states).
8. **`T2d` called original and universal.**
   - Where: `paper/main.tex` line 63 (Introduction), line 264 ("a sharper, genuinely new lattice rigidity phenomenon"), line 310 (Figure 2 caption, panel b).
   - What is wrong: the Introduction drops the hypothesis `M*K = 4A - 2B + 4C`, which makes `K` the mean Laplacian, and says "every periodic integer superharmonic envelope". The argument is elementary. The lemma says nothing about sandpile configurations, so the Figure 2 caption ("solid height-5 seas are obstructed by Theorem `thm:t2d`") is not supported.
   - Correction: "an elementary A2 parity lemma, with no prior statement found: if `M*u` is a quadratic plus a periodic function, `M*K = 4A - 2B + 4C`, and the A2 Laplacian of `u` is at most `K`, then `K` is even". Remove the causal claim from the caption.
   - Affects a theorem statement: yes for the Introduction's summary (missing hypothesis); the formal Theorem `thm:t2d` matches Lean.
9. **`T2e` called Kalinin–Shkolnikov tropical balancing.**
   - Where: `paper/main.tex` line 63, line 107 (summary table), line 303 (subsection title).
   - What is wrong: Lean proves an edge-normal closure identity for lattice polygons and a 2×2 determinant identity. No sandpile, tropical curve or Kalinin–Shkolnikov statement is formalized.
   - Correction: "lattice-polygon edge-normal closure identity (the Kalinin–Shkolnikov theorem is not formalized)".
   - Affects a theorem statement: no.
10. **Cohn root matrix.**
    - Where: `paper/main.tex` line 323 (subsection on `T3a`).
    - What is wrong: `B_0` is printed as `[[2,1],[5,3]]` (trace 5, not divisible by 3), contradicting the same paragraph and the Lean root `cohnB0 = ⟨1, 2, 2, 5⟩` (`MarkovHurwitzCluster.lean` line 78, trace 6).
    - Correction: `B_0 = [[1,2],[2,5]]`.
    - Affects a theorem statement: yes (the root data of `T3a` as printed is wrong; the Lean statement is correct).
11. **Mutation path name (`T3d`).**
    - Where: `paper/main.tex` line 363.
    - What is wrong: the path is called the "Fibonacci-odd branch", but 29 and 433 are not Fibonacci numbers.
    - Correction: describe it as the mutation path through the Markov triples `(2,5,29)`, `(5,29,433)`, `(29,433,37666)`.
    - Affects a theorem statement: no.
12. **`T3d` "Laurent positivity" and `T3e` "complete classification".**
    - Where: `paper/main.tex` line 64.
    - What is wrong: Lean states positivity of values at positive integers (coefficient positivity holds by inspection only). For `T3e`, Lean states the admissible coefficients `a ∈ {1,4}` with parity constraints, not the orbit description of all solutions; the result is classical (Hurwitz, 1907) and Hurwitz is not cited.
    - Correction: "exchange identities with subtraction-free numerators along one five-step mutation path"; "the classical (Hurwitz 1907) classification of admissible coefficients for `n = 4`".
    - Affects a theorem statement: no.
13. **Bibliography.**
    - Where: `paper/references.bib`.
    - What is wrong: Zhang (2007), arXiv:2510.21702 and Hurwitz (1907) are missing. The DOI given for `baragar1993` (`10.1201/9780203747018-1`) resolves on Crossref to a 2017 reprint.
    - Correction: add the three references; note the reprint year for `baragar1993`.
    - Affects a theorem statement: no.

### Historical 2026-11-26 Audit Snapshot — Formal-Code Items (All 9 Resolved in `v2.0.0`–`v3.0.0`)

*(Items 1–9 below record the pre-`v2.0.0` findings verbatim; items 1–8 were resolved in `v2.0.0`–`v2.1.0`, and `v3.0.0` additionally closed the general `d`-dimensional Soddy reflection link in `T1e`, universal sandpile termination in `T2a`, Markov descent in `T3b`, and complete Hurwitz `n=4` Vieta orbits in `T3e`.)*

1. `lean/lake-manifest.json` line 4: package name `PromislowFracton` does not match `name = "ApollonianSandpileMarkov"` in `lean/lakefile.toml`. Fix: regenerate the manifest. Does not affect any theorem statement.
2. `lean/Challenge.lean` lines 88–94 (`T2b`): there is no 9×9 determinant statement. Fix: prove `det9 (gridLap 3) = 100352` directly, or keep the block-similarity statement and its description. Affects the scope of `T2b` only.
3. `lean/Challenge.lean` lines 150–153 (`T3a`): the export uses integer division `tr/3` without the conjuncts `3 ∣ tr` that the internal lemma `cohn_tree_markov` (`MarkovHurwitzCluster.lean` lines 84–87) proves. Fix: add the divisibility conjuncts. Affects the exported statement (it is weaker than the internal lemma, not false).
4. `lean/Challenge.lean` lines 65–76 (`T1e`): only `soddy3Refl1` is shown to preserve the Soddy form, and the divisibility fact is not linked to Soddy reflections. Fix: add the other four preservation conjuncts. Affects the scope of `T1e`.
5. `lean/ApollonianSandpileMarkov/NonVacuity.lean`: no joint witness for the `T2d` hypothesis bundle or for `IsStabilizingOdometer`. (`T2d` is non-vacuous by inspection: `u = x^2`, `M = 1`, `K = 4`.) Fix: add the witnesses.
6. `lean/ApollonianSandpileMarkov/ApollonianReciprocity.lean` line 1584 (`rootUnobstructed`) and `Adversarial.lean` line 27 (`adv1_unobstructed_hits_square`): the names call `(-4,8,9,9)` unobstructed, which is wrong per HKRS (item 2 above). Fix: rename (for example `rootSquareContrast`) in a version that also updates the comparator contract.
7. `lean/ApollonianSandpileMarkov/Adversarial.lean`: the suite has six refutations; `adv6_hurwitz4_no_a3_solution` is a corollary of `T3e`, and no refutation drops a hypothesis of `T2a`, `T2b`, `T2d`, `T1d`, `T3a` or `T3d`. Earlier text said every structural hypothesis is tight; that claim has been withdrawn.
8. `lean/formalization.yaml` line 20: `sorry_count: 0` counts built modules only; `lean/PalomarChallenge.lean` has 16 intentional `by sorry` stubs (comparator challenge, not a build target). A comment now says so.
9. Declaration names broader than their statements: `t2e_kalinin_shkolnikov_tropical_balancing_and_solitons`, `t3d_cluster_algebra_markov_laurent_positivity`, `t3e_markov_hurwitz_n4_complete_classification`, `t1d_octahedral_lorentzian_and_sqrt_neg2_obstruction`. They are kept unchanged so that `lean/comparator.json` and `results/lean_axioms.txt` stay valid; the documentation now describes what each one states.

## Correction Procedure

1. Open a GitHub Issue using the `Finding Report` template and select the applicable Build Standard v1.2.0 finding class (`bug`, `error`, `issue`, `problem`, `concern`, `dilemma`, `conflict`, `gap`, `hole`, or `blindspot`).
2. Confirmed errata are appended chronologically above with the affected file or theorem and the commit that records them. Frozen releases are not silently rewritten.
