<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Agent & Contributor Canonical Guide (`AGENTS.md`)

- **Project:** `apollonian-sandpile-markov` (`0TH-2026-018`, v3.0.0)
- **Author Identity:** Alexander Stephen Donahue, Independent Researcher, Spokane, WA, USA (ORCID `0009-0006-8168-9648`, `0_0@0thernes.art`). Never insert commercial entity suffixes in scholarly metadata.
- **Hard Invariants:**
  1. `lean/` MUST stay zero-Mathlib (`leanprover/lean4:v4.35.0`), zero `sorry`, zero `admit`, zero `native_decide`, strictly within `[propext, Classical.choice, Quot.sound]`, across all 19 exported audited declarations AND all 884 `ApollonianSandpileMarkov.*` declarations (`VerifyAllDecls.lean`).
  2. `README.md` MUST reproduce `results/lean_axioms.txt` verbatim (`python scripts/check_readme_axioms.py`).
  3. All numerical values in `paper/main.tex` and `paper/figures/` MUST match `results/rust_summary.json`, `results/exact_verification_report.json`, and `results/figure_stats.json` exactly.
  4. Never overclaim open conjectures (`STAT-058`, `NT-083`, full Apollonian local-global classification); see `CLAIMS.md` and `LIMITATIONS.md`.
  5. Direct commits to `main` (Build Standard R1/R2); no banned files (`dependabot.yml`, `renovate.json`, `copilot-instructions.md`, `PULL_REQUEST_TEMPLATE.md`, `FUNDING.yml`).
  6. Keep `ruff check`, `mypy`, and `cargo clippy --all-targets -- -D warnings` at zero errors/warnings.
- **One-Command Audit:** `python scripts/audit_repo.py` or `just reproduce`
