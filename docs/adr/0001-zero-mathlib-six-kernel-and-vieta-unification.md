<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# ADR 0001: Zero-Mathlib Six-Kernel Formalization and Unified Vieta-Reflection Architecture

- **Status:** Accepted (v1.0.0, 2026-11-26)
- **Context:** Formalizing number theory (quadratic reciprocity, Apollonian/octahedral orbits, Hensel lifting, Markov trees) and discrete potential theory (sandpile confluence, discrete Green's First Identity) normally pulls in millions of lines of Mathlib, creating heavy build times, opaque dependency chains, and incompatibility with lightweight independent export kernels (`nanoda_bin`, `con-leche`, `con-ron`).
- **Decision:** Build the entire 15-theorem formalization strictly on **zero-Mathlib Lean 4.35.0 core** (`module`, `@[expose] public section`), formalizing Eisenstein's 1844 quadratic reciprocity proof, discrete Green's First Identity on $\mathbb{Z}^2$ and $\mathbb{A}_2$, and exact integer Kronecker block-diagonalization from first principles, and verify every exported declaration across **six independent type-checking kernels** plus **three independent computational languages** (zero-dep Rust, ISO C11 ASan/UBSan + fuzz, Python + Hypothesis + 100% mutation).
- **Consequences:**
  - Clean full Lean build finishes in under 25 seconds with zero external downloads.
  - Export size stays compact enough for instant multi-kernel replay (`leanchecker`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`) and `lake comparator --paranoid`.
  - Every mathematical prerequisite is transparent, auditable, and strictly within `[propext, Classical.choice, Quot.sound]`.
