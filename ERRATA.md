<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Errata & Corrections Policy (`ERRATA.md`)

This file records any post-release mathematical, formal, computational, or typographic corrections discovered after `v1.0.0`.

## Current Status (`v1.0.0`)

- **No open post-release errata.** All pre-release issues discovered during the three hardening cycles (e.g., `det(L_{A_2, 2×2}) = 1,092`, `det(L_{A_2, 3×3}) = 5,393,920`, mutation harness test-gap closure to 8/8 = 100%, Figure 1 legend square range `(9, 36, ..., 900)`, and LaTeX `\detokenize` escape cleanup) were resolved prior to tagging `v1.0.0` and are logged in [`HARDENING_LOG.md`](HARDENING_LOG.md).

## Correction Procedure

1. Open a GitHub Issue using the `Finding Report` template and select the applicable finding class (e.g., `correctness`, `proof-soundness`, `numeric`, `docs`).
2. Confirmed errata are appended chronologically below with severity, affected file/theorem, commit SHA, and patch release version (`v1.0.x`), and frozen releases are never silently rewritten.
