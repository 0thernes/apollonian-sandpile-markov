<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Frequently Asked Questions (`docs/faq.md`, v3.0.0)

**Q: Does this paper solve the Markov Uniqueness Conjecture (`NT-083`), the full sandpile continuum scaling limit (`STAT-058`), or the Apollonian local-global classification?**  
No. All overarching conjectures remain explicitly open (see [`CLAIMS.md`](../CLAIMS.md) and [`LIMITATIONS.md`](../LIMITATIONS.md)). Most of the 16 Lean statements (`T1a`–`T3e` plus `T2f`) are zero-Mathlib formalizations of known results: HKRS (2024) for three Apollonian packings (`T1c`), Lagarias–Mallows–Wilks (2002) general `d`-dimensional Soddy integrality (`T1e`), Dhar (1990) Abelian sandpile confluence & universal sinked termination (`T2a`), Markov's (1879/1880) descent theorem combined with Ying Zhang's (2007) theorem that every even Markov number is `2 mod 32` (`T3b`), and Hurwitz's (1907) complete `n=4` classification with unique Vieta orbits (`T3e`). The remaining statements are finite computations (including direct 9×9 Laplace determinants `detMat 9` in `T2b` and `T2f`), elementary identities, and one elementary parity lemma on the triangular lattice (`T2d`) with no prior statement found.

**Q: Why build Lean 4 proofs without Mathlib?**  
Zero-Mathlib formalizations compile cleanly in seconds, eliminate external library supply-chain drift, keep kernel export streams compact enough to replay across six independent type-checking kernels (`lean 4.35.0`, `leanchecker --fresh`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`), and make it straightforward to audit that zero `native_decide`, zero `sorry`, and zero custom axioms appear in any built module.

**Q: Why do `(-7, 17, 12, 20)` and `(-4, 8, 9, 9)` behave oppositely for square curvatures despite identical mod-24 residues?**  
Computationally, both packings share the mod-24 residue set `{0, 8, 9, 12, 17, 20}`. However, `(-7, 17, 12, 20)` carries a global quadratic reciprocity obstruction (HKRS 2024, formalized in `T1c` via parabolic Dehn-twist CRT without Mathlib) forbidding every perfect square curvature, whereas `(-4, 8, 9, 9)` hits squares such as `9 = 3^2`. Note that `(-4, 8, 9, 9)` is **not** unobstructed overall: HKRS (Appendix Table A) list `3n^2`, `6n^2`, `n^4`, and `4n^4` obstructions for it.

**Q: Does Theorem `T2d` prove that the finite $\mathbb{A}_2$ sandpile identity cannot have height-5 plateaus?**  
No. `T2d` is strictly an elementary discrete-PDE parity lemma: if `M ≥ 1`, `ψ` is doubly periodic, `M*u = Ax^2 + Bxy + Cy^2 + Dx + Ey + ψ`, `M*K = 4A - 2B + 4C`, and `Δ_{A2} u ≤ K` everywhere, then `K` is even (so `K=5` cannot occur in that quadratic-plus-periodic class). It makes no formal statement about finite-grid sandpile configurations or the $\mathbb{A}_2$ sandpile identity.

**Q: What changed in `v2.0.0` for `T2b` and `T2f`?**  
In `v2.0.0`, `SandpileTropical.lean` adds a self-contained zero-Mathlib general `n × n` Laplace determinant `detMat` with verified elementary row-operation soundness, proving BOTH `detMat 9 (gridLap 3) = 100,352` directly inside `T2b` AND `detMat 9 (a2GridLap 3) = 5,393,920` directly inside `T2f` (alongside `det4`, `D_4`/Klein-4 block similarities, and explicit legal Dhar toppling traces). Neither theorem formalizes the Matrix–Tree theorem or proves abstractly that those configurations are critical-group identities.

**Q: How can I verify that the Lean formalization cannot be gamed by a hidden axiom or tampered statement?**  
Inspect `lean/Challenge.lean`, `lean/VerifyAxioms.lean`, and the CI `lean4-six-kernels` job, which runs `lake comparator --config comparator.json --paranoid` (against the 17 intentional `by sorry` targets in `PalomarChallenge.lean`), all six independent formal kernels, AND a live negative kernel rejection gate that injects a false `sorry` theorem, a custom `axiom`, and a tampered statement to verify hard rejection.
