<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# System & Verification Architecture (`docs/architecture.md`)

`apollonian-sandpile-markov` (`0TH-2026-018`, v3.0.0) is organized around a single mathematical abstraction—**quadratic Vieta involutions on integral forms**—and a layered, defense-in-depth verification architecture with zero hidden dependencies.

## 1. Repository Module Map

```text
apollonian-sandpile-markov/
├── lean/                         # Zero-Mathlib Lean 4.35.0 formal proofs (16 theorems, 19 exports, 884 audited decls)
│   ├── ApollonianSandpileMarkov/
│   │   ├── JacobiReciprocity.lean      # T1b: self-contained Legendre-Jacobi & Eisenstein (1844) QR
│   │   ├── ApollonianReciprocity.lean  # T1a, T1c, T1d, T1e: Descartes, HKRS (3 roots), Octahedral mod-8, General d-dim Soddy
│   │   ├── SandpileTropical.lean       # T2a-T2f: Abelian confluence & sinked termination, direct Z^2 & A_2 detMat 9 + Dhar traces, A_2 parity lemma, polygon closure
│   │   ├── MarkovHurwitzCluster.lean   # T3a-T3e: SL2(Z) Fricke/Cohn, Markov descent + Zhang Mod-32, Hensel, 5-step Cluster, Hurwitz n=4 Vieta orbits
│   │   ├── NonVacuity.lean             # Constructive premise witnesses across all pillars (incl. multi-hop gridGraph 3, soddyQ 3, InHurwitz4Orbit)
│   │   └── Adversarial.lean            # 10 false-variant & dropped-hypothesis refutations (adv1-adv10, incl. sinklessGraph2)
│   ├── Challenge.lean                  # Literal formal theorem statement contract
│   ├── PalomarChallenge.lean           # Contract interface for lake comparator --paranoid (17 intentional sorry stubs)
│   ├── PalomarSolution.lean            # Verified proofs matching PalomarChallenge verbatim
│   ├── Solution.lean                   # Top-level master conjunction export
│   ├── VerifyAxioms.lean               # Strict #print axioms allowlist audit (19 exported declarations)
│   ├── VerifyAllDecls.lean             # Exhaustive Lean.collectAxioms metaprogram audit (all 884 ApollonianSandpileMarkov.* decls)
│   └── comparator.json                 # Palomar comparator configuration
├── rust/                         # Zero-dependency Rust crate (#![forbid(unsafe_code)], i128 Bareiss, 10^7 Markov)
├── native/                       # Strict ISO C11 verifier, 100k 7-law fuzzer, and 7-law coverage-guided libFuzzer target
├── python/asm_verify/            # Independent arbitrary-precision Python reference oracle + `python -m asm_verify` CLI
├── tests/                        # pytest + Hypothesis (600+ trials) + negative/CLI + differential + 3D Soddy exact tangency tests
├── scripts/                      # Mutation harness (10/10), figure generator, live Crossref/arXiv citation auditor, repo auditor
├── paper/                        # AMS-LaTeX manuscript (main.tex, references.bib, 4 vector PDF figures, clickable plainurl DOIs)
├── dist/                         # Frozen compiled PDF + deterministic mtime=0 clean-room arXiv tarball
├── data/                         # Golden dataset manifest (data/MANIFEST.sha256) + RFC 3161 (.tsr) + OpenTimestamps (.ots)
├── results/                      # Verbatim Lean axiom log, Rust/Python JSON reports, figure stats
├── studio/                       # Zero-dependency 4-mode interactive HTML5 Canvas observatory
├── blueprint/                    # Interactive filterable Lean 4 proof dependency blueprint (safe DOM API, zero innerHTML)
└── docs/                         # Portal index, architecture, configuration, operations, ADRs, FAQ, glossary, reviews, run-log
```

## 2. Mathematical Dependency Flow

1. **Foundation (`JacobiReciprocity.lean`, `T1b`):** Proves Legendre–Jacobi arithmetic, Gauss's Lemma, Eisenstein's (1844) lattice-point Quadratic Reciprocity, and both supplementary laws directly over Lean 4 core.
2. **Pillar I (`ApollonianReciprocity.lean`, `T1a`, `T1c`–`T1e`):** Uses `T1a` + `T1b` to formalize the HKRS (2024) square obstruction on the three roots `(-3,5,8,8)`, `(-7,17,12,20)`, and `(-11,21,24,28)` (`T1c`, contrasted with `rootSquareContrast = (-4,8,9,9)`), octahedral mod-8 residue locking plus 5 standalone closed Jacobi evaluations (`T1d`; cf. Shi et al., `arXiv:2510.21702`), and the general `d`-dimensional Soddy–Gosset integrality dichotomy (LMW 2002: integer reflections preserving `soddyQ d` exist iff `d ∈ {2,3}`) with all five 3D Soddy involutions (`T1e`).
3. **Pillar II (`SandpileTropical.lean`, `T2a`–`T2f`):** Proves toppling commutativity, least-action bound, Church–Rosser confluence, and universal finite termination & existence of stabilization on every sinked dissipative graph via a constructive superharmonic potential (`T2a`), direct 4×4 and 9×9 Laplace determinants (`detMat 9`) plus block similarities and legal Dhar traces on $\mathbb{Z}^2$ (`T2b`: `192`, `100,352`) and $\mathbb{A}_2$ (`T2f`: `1,092`, `5,393,920`; no Matrix–Tree link formalized), one isotropic $\mathbb{Z}^2$ obstruction (`T2c`), an elementary $\mathbb{A}_2$ even-Laplacian parity lemma under `M*K = 4A - 2B + 4C` (`T2d`), and a lattice-polygon edge-normal closure identity (`T2e`; Kalinin–Shkolnikov theorem not formalized).
4. **Pillar III (`MarkovHurwitzCluster.lean`, `T3a`–`T3e`):** Proves $\mathrm{SL}_2(\mathbb{Z})$ Fricke–Cohn correspondence with explicit `3 ∣ tr` divisibility (`T3a`), Markov's classical descent theorem lifting pairwise coprimality, odd $p \equiv 1 \pmod 4$, and Ying Zhang's (2007) theorem $m \equiv 2 \pmod{32}$ to ALL positive integer Markov solutions (`T3b`), Hensel $\sqrt{-1} \pmod{p^k}$ uniqueness (`T3c`), 5-step Markov quiver exchange identities with value positivity at positive integers (`T3d`), and Hurwitz's (1907) complete `n=4` classification with exact Vieta-orbit bi-implications (`T3e`).

## 3. Six-Kernel & Three-Oracle Trust Boundary

Every push to `main` executes:
- **6 independent formal kernels:** `lean 4.35.0` (including `VerifyAxioms.lean` + exhaustive `VerifyAllDecls.lean` across all 884 declarations), `leanchecker --fresh`, `leanchecker-paranoid` (`lean4lean`), `nanoda_bin` (Rust kernel), `con-leche`, `con-ron`, plus `lake check --paranoid`, `lake comparator --config comparator.json --paranoid`, AND a **live negative kernel rejection gate** proving tampered `sorry`, custom `axiom`, and mismatched statements fail closed.
- **3 independent computational oracles:** Zero-dependency Rust (`#![forbid(unsafe_code)]`, `cargo clippy --all-targets -- -D warnings`, 6 unit/edge-case tests), ISO C11 (`-Wall -Wextra -Werror -fsanitize=address,undefined`, 100k 7-law fuzz, plus 5s coverage-guided 7-law `libFuzzer`), and Python (`ruff`, `mypy`, `pytest`, 600+ Hypothesis trials, CLI & negative input tests, bit-for-bit Rust–Python differential, 10/10 = 100% mutation kill rate).
- **Publication & Provenance:** Tectonic 0-warning PDF compile (with clickable `plainurl` DOIs), clean-room arXiv tarball compile, `MANIFEST.sha256` + `SHA256SUMS` + `data/MANIFEST.sha256` verification, dual DigiCert RFC 3161 (`.tsr`, verified with `openssl ts -reply`) and Bitcoin OpenTimestamps (`.ots`) proofs, GitHub Actions SLSA build provenance (`actions/attest-build-provenance@v2`), Software Heritage SWHID archival, and static GitHub Pages deployment with strict CSP headers.
