<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# FAQ & Glossary (`docs/faq-glossary.md`)

## Frequently Asked Questions

**Q: Does this paper solve the Markov Uniqueness Conjecture (`NT-083`) or the full sandpile scaling limit (`STAT-058`)?**
No. Both remain open, and no theorem here is a bounded case of either (see `CLAIMS.md` and `LIMITATIONS.md`); the links are thematic. The 15 Lean statements are mostly formalizations of known results, for example Zhang's 2007 theorem that even Markov numbers are 2 mod 32 (`T3b`), uniqueness of $\sqrt{-1} \pmod{p^k}$ (`T3c`), exchange identities along one five-step Markov-quiver mutation path (`T3d`), and the classical Hurwitz (1907) classification of admissible coefficients for $n=4$ (`T3e`). `T2d` is an elementary parity lemma on the triangular lattice with no prior statement found.

**Q: Why build Lean 4 proofs without Mathlib?**
Zero-Mathlib formalizations compile in seconds, avoid supply-chain drift, and keep proof exports small enough for the additional kernels run in CI (`leanchecker`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`; the last three check an export of three root declarations and their dependency closure). The built modules use no `native_decide`.

**Q: Why do `(-7, 17, 12, 20)` and `(-4, 8, 9, 9)` differ on squares despite identical mod-24 residues?**
Both packings have the residue set `{0, 8, 9, 12, 17, 20} mod 24` (a computation), so congruences mod 24 cannot distinguish them. Haag, Kertzer, Rickards and Stange (Ann. of Math. 2024, arXiv:2307.02749) showed that a quadratic reciprocity invariant excludes all squares from `(-7, 17, 12, 20)`; `T1c` formalizes this exclusion for that packing and two others. `(-4, 8, 9, 9)` contains the square 9, but it is not unobstructed: HKRS list quadratic obstructions `3n^2`, `6n^2` and quartic obstructions `n^4`, `4n^4` for it.

**Q: Does `T2d` explain the 4-chip plateaus in the $65\times 65$ $\mathbb{A}_2$ sandpile identity?**
No such link is proved. `T2d` states: if $M u$ is a quadratic $Ax^2+Bxy+Cy^2+Dx+Ey$ plus a periodic function, $M K = 4A-2B+4C$, and $\Delta_{\mathbb{A}_2} u \le K$ everywhere, then $K$ is even. The hypotheses force a constant Laplacian, so the lemma is elementary. It says nothing about sandpile configurations of height 5; the plateaus in the figure are an observation from computation.

## Glossary
- **Vieta Involution:** The reflection $x_i \mapsto L_i(x_{-i}) - x_i$ flipping one root of a quadratic relation while holding the remaining coordinates fixed.
- **Dhar Critical Identity:** The unique idempotent recurrent configuration $e = \operatorname{stab}(2\mu_{\max} - \operatorname{stab}(2\mu_{\max}))$ of a finite Abelian sandpile.
- **Palomar Comparator:** Contract verification (`lake comparator --paranoid`) confirming that a solution module proves the exact literal theorem statements of a challenge contract with zero `sorry` and zero unpermitted axioms.
