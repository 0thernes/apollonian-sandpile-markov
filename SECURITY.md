<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Security Policy (`SECURITY.md`)

## Scope
This repository contains offline mathematical formalizations (Lean 4.35.0), native verification binaries (Rust, ISO C11), Python scripts, and static browser visualizations (`studio/index.html`, `blueprint/index.html`, `docs/index.html`). No network services, authentication layers, or personal data stores are operated.

## Reporting
- For security, supply-chain, or proof-soundness issues (such as hidden axioms, kernel bypasses, memory safety in `native/*.c`, or secret leakage), email `0_0@0thernes.art` or open a GitHub Issue labeled `hole`, `bug`, or `concern` (see `.github/labels.tsv` for the full 10-class Build Standard v1.2.0 taxonomy).
- See [`docs/threat-model.md`](docs/threat-model.md) for our threat model covering proof soundness, specification gaming, and build provenance (`MANIFEST.sha256` + SLSA `actions/attest-build-provenance@v2`), and [`ERRATA.md`](ERRATA.md) for confirmed post-release corrections.
