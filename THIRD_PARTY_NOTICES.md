<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Third-Party Notices (`THIRD_PARTY_NOTICES.md`)

## Zero External Core Dependencies
- **Lean 4 Formalization (`lean/`):** Zero Mathlib, zero Lake packages; depends solely on the Lean 4.35.0 core toolchain (`Apache-2.0`).
- **Rust Oracle (`rust/`):** Zero external crates (`std` only).
- **ISO C11 Verifier & Fuzzer (`native/`):** Standard C11 library only.
- **Browser Observatory & Proof Blueprint (`studio/`, `blueprint/`, `docs/`):** Zero external JS/CSS/CDN dependencies.

## Development & Verification Tooling (Not Bundled)
- Python ecosystem used for testing, figure generation, and auditing (`requirements.txt`): `pytest` (MIT), `hypothesis` (MPL-2.0), `numpy` (BSD-3-Clause), `matplotlib` (PSF-based), `requests` (Apache-2.0), `pyyaml` (MIT), `jsonschema` (MIT), `ruff` (MIT), `mypy` (MIT).
- CI formal verification kernels: Lean 4 / `leanchecker` (Apache-2.0), `lean4lean` (Apache-2.0), `nanoda` (Apache-2.0 / MIT), `con-leche`, `con-ron`, and Tectonic (MIT).
- All prior mathematical works are cited explicitly with verified DOIs / arXiv identifiers in [`paper/references.bib`](paper/references.bib).
