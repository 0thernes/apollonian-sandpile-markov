<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Build Standard v1.2.0 Deviations (`DEVIATIONS.md`)

Items marked `n/a` in `repo.yaml` are justified below per Build Standard for LLMs v1.2.0:

- **`A34` (Healthcheck / observability):** Offline deterministic mathematical research repository and static GitHub Pages site; no long-running server process or runtime telemetry endpoint exists.
- **`A35` (Database backup / disaster recovery):** No mutable database; permanent archival preservation is handled via GitHub Releases, Software Heritage SWHID snapshots, and the pinned submodule in `0thernes-research-archive`.
- **`A40` & `B34` (Runtime AI safety / LLM prompt-injection defenses):** The repository ships no AI/ML models and calls no LLM APIs at runtime. Transparent authoring AI-assistance disclosure is provided in `paper/main.tex` (Section 5.3) and `lean/formalization.yaml`.
- **`A45` (Personal data / privacy compliance):** Zero personal data is collected, transmitted, stored, or logged by any code or static page in this repository.
- **`B19` (Concurrency / race-condition testing):** All Lean, Rust, C11, Python, and browser verification routines are strictly single-threaded and deterministic.
- **`B21` (Distributed fault-injection testing):** No distributed service or network protocol is shipped.
- **`B23` (TLA+ / finite-state protocol model checking):** Mathematical properties are proved directly as universal theorems in Lean 4.35.0 rather than bounded state-space models.
- **`B25` (CBMC bounded model checking):** Native C11 verification is covered by strict `-Wall -Wextra -Werror -fsanitize=address,undefined` compilation plus a 100,000-case deterministic fuzzer (`native/fuzz_asm.c`) alongside universal Lean 4 proofs.
- **`B28`–`B33` (Multi-seed stochastic benchmarks, statistical hypothesis tests, effect sizes, multiple-comparison corrections, clinical pre-registration, ML held-out splits):** All results are exact deterministic algebraic theorems and exact integer computations; no stochastic experiments, p-values, or ML models are claimed.
