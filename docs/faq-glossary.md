<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# FAQ & Glossary (`docs/faq-glossary.md`)

## Frequently Asked Questions

**Q: Does this paper solve the Markov Uniqueness Conjecture (`NT-083`) or the full sandpile scaling limit (`STAT-058`)?**
No. Both overarching conjectures remain explicitly open (see `CLAIMS.md` and `LIMITATIONS.md`). We prove 15 concrete unconditional theorems surrounding them, including our original Triangular Lattice $\mathbb{A}_2$ Even-Laplacian Rigidity Theorem (`T2d`), our Exact Mod-32 Theorem for even Markov numbers (`T3b`), universal Hensel $\sqrt{-1} \pmod{p^k}$ uniqueness (`T3c`), 5-step symbolic cluster positivity (`T3d`), and complete Hurwitz $n=4$ classification (`T3e`).

**Q: Why build Lean 4 proofs without Mathlib?**
Zero-Mathlib formalizations compile in seconds, avoid supply-chain drift, keep proof exports small enough to replay across six independent type-checking kernels (`lean 4.35.0`, `leanchecker`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`), and ensure zero `native_decide` or hidden tactics.

**Q: Why do `(-7, 17, 12, 20)` and `(-4, 8, 9, 9)` behave oppositely despite identical mod-24 residues?**
Both packings have the exact same local residue set `{0, 8, 9, 12, 17, 20} mod 24`, so local congruence tests cannot distinguish them. However, `(-7, 17, 12, 20)` carries a global quadratic reciprocity invariant `χ(q) = -1` (Theorem `T1c`), which forbids every perfect-square curvature across its entire infinite orbit.

**Q: Why does the $65\times 65$ $\mathbb{A}_2$ sandpile identity form solid 4-chip plateaus instead of solid 5-chip seas?**
By Theorem `T2d`, every integer-valued quadratic-plus-periodic function on $\mathbb{A}_2$ with $\Delta_{\mathbb{A}_2} u \le K$ and mean curvature $K$ MUST satisfy $K \equiv 0 \pmod 2$. Because $5$ is odd, solid $K=5$ seas are universally impossible on $\mathbb{A}_2$, forcing macroscopic flat plateaus down to even height $K=4$.

## Glossary
- **Vieta Involution:** The reflection $x_i \mapsto L_i(x_{-i}) - x_i$ flipping one root of a quadratic relation while holding the remaining coordinates fixed.
- **Dhar Critical Identity:** The unique idempotent recurrent configuration $e = \operatorname{stab}(2\mu_{\max} - \operatorname{stab}(2\mu_{\max}))$ of a finite Abelian sandpile.
- **Palomar Comparator:** Contract verification (`lake comparator --paranoid`) confirming that a solution module proves the exact literal theorem statements of a challenge contract with zero `sorry` and zero unpermitted axioms.
