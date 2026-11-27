#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Automated Build Standard v1.2.0 & Playbook v1.3 repository hygiene auditor (v2.0.0)."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

import jsonschema
import yaml

ROOT = Path(__file__).resolve().parents[1]

REQUIRED_FILES = [
    "README.md",
    "AGENTS.md",
    "CLAUDE.md",
    "GEMINI.md",
    ".cursor/rules/build-standard.mdc",
    ".env.example",
    ".github/labels.tsv",
    "llms.txt",
    "llms-full.txt",
    "LICENSE",
    "LICENSE-CODE",
    "VERSION",
    "CHANGELOG.md",
    "UPGRADING.md",
    "CLAIMS.md",
    "LIMITATIONS.md",
    "REPLICATION.md",
    "VERIFICATION.md",
    "HARDENING_LOG.md",
    "ERRATA.md",
    "DEVIATIONS.md",
    "ROADMAP.md",
    "SECURITY.md",
    "SUPPORT.md",
    "CONTRIBUTING.md",
    "CODE_OF_CONDUCT.md",
    "THIRD_PARTY_NOTICES.md",
    "CITATION.cff",
    "CITATION.bib",
    ".zenodo.json",
    ".gitignore",
    ".gitattributes",
    ".editorconfig",
    ".gitleaks.toml",
    "justfile",
    "pyproject.toml",
    "requirements.txt",
    "repo.yaml",
    "MANIFEST.sha256",
    "SHA256SUMS",
    "data/MANIFEST.sha256",
    "data/MANIFEST.sha256.tsr",
    "data/MANIFEST.sha256.ots",
    "docs/architecture.md",
    "docs/configuration.md",
    "docs/operations.md",
    "docs/faq.md",
    "docs/glossary.md",
    "docs/run-log.md",
    "docs/reviews/2026-11-26-10-pass-red-team-review.md",
    "lean/lean-toolchain",
    "lean/lakefile.toml",
    "lean/comparator.json",
    "lean/formalization.yaml",
    "lean/VerifyAxioms.lean",
    "rust/Cargo.toml",
    "native/asm_verify.c",
    "native/fuzz_asm.c",
    "native/fuzz_libfuzzer.c",
    "studio/index.html",
    "blueprint/index.html",
    "docs/index.html",
    "paper/main.tex",
    "paper/references.bib",
    "dist/Donahue_2026_apollonian_sandpile_markov.pdf",
    "dist/arxiv_submission.tar.gz",
]

BANNED_FILES = [
    ".github/dependabot.yml",
    ".github/renovate.json",
    "renovate.json",
    ".github/copilot-instructions.md",
    ".github/PULL_REQUEST_TEMPLATE.md",
    ".github/FUNDING.yml",
]


def main() -> int:
    errors: list[str] = []

    for rel in REQUIRED_FILES:
        if not (ROOT / rel).exists():
            errors.append(f"Missing required file: {rel}")

    for rel in BANNED_FILES:
        if (ROOT / rel).exists():
            errors.append(f"Banned file present (Build Standard R1/R4): {rel}")

    # Agent pointer contract (Build Standard A32)
    claude_md = ROOT / "CLAUDE.md"
    if claude_md.exists() and "@AGENTS.md" not in claude_md.read_text(encoding="utf-8"):
        errors.append("CLAUDE.md missing @AGENTS.md import")
    gemini_md = ROOT / "GEMINI.md"
    if gemini_md.exists() and "@./AGENTS.md" not in gemini_md.read_text(encoding="utf-8"):
        errors.append("GEMINI.md missing @./AGENTS.md pointer")

    repo_yaml_path = ROOT / "repo.yaml"
    if repo_yaml_path.exists():
        data = yaml.safe_load(repo_yaml_path.read_text(encoding="utf-8"))
        schema_path = Path(r"I:\All GH Repos\Repo Checklist\build-standard\repo-standard.schema.json")
        if schema_path.exists():
            schema = json.loads(schema_path.read_text(encoding="utf-8"))
            try:
                jsonschema.validate(instance=data, schema=schema)
            except jsonschema.ValidationError as exc:
                errors.append(f"repo.yaml schema violation: {exc.message}")
        items = data.get("items", {})
        expected_keys = [f"A{i:02d}" for i in range(1, 46)] + [f"B{i:02d}" for i in range(1, 46)]
        missing_keys = [k for k in expected_keys if k not in items]
        if missing_keys:
            errors.append(f"repo.yaml missing item keys: {missing_keys}")
        todos = [k for k, v in items.items() if v.get("status") == "todo"]
        if todos:
            errors.append(f"repo.yaml has unresolved 'todo' items: {todos}")
        na_without_note = [k for k, v in items.items() if v.get("status") == "n/a" and not v.get("note")]
        if na_without_note:
            errors.append(f"repo.yaml has 'n/a' items without note: {na_without_note}")

    # Playbook v1.3 no-LLC policy check across published metadata/manuscript
    check_no_llc = [
        "README.md",
        "LICENSE",
        "LICENSE-CODE",
        "CITATION.cff",
        "CITATION.bib",
        ".zenodo.json",
        "lean/formalization.yaml",
        "paper/main.tex",
        "docs/index.html",
        "studio/index.html",
        "blueprint/index.html",
    ]
    for rel in check_no_llc:
        p = ROOT / rel
        if p.exists():
            txt = p.read_text(encoding="utf-8", errors="ignore")
            if re.search(r"0thernes\s+LLC", txt, re.IGNORECASE):
                errors.append(f"Playbook v1.3 policy violation ('0thernes LLC' found) in {rel}")

    # Dual cryptographic timestamp integrity check (RFC 3161 .tsr + OpenTimestamps .ots)
    data_manifest = ROOT / "data" / "MANIFEST.sha256"
    if data_manifest.exists():
        digest = hashlib.sha256(data_manifest.read_bytes()).digest()
        tsr = ROOT / "data" / "MANIFEST.sha256.tsr"
        if tsr.exists():
            tsr_bytes = tsr.read_bytes()
            if len(tsr_bytes) < 500 or tsr_bytes[0] != 0x30 or digest not in tsr_bytes:
                errors.append("data/MANIFEST.sha256.tsr is invalid or does not embed current data/MANIFEST.sha256 digest")
        ots = ROOT / "data" / "MANIFEST.sha256.ots"
        if ots.exists():
            ots_bytes = ots.read_bytes()
            if not ots_bytes.startswith(b"\x00OpenTimestamps\x00\x00Proof\x00\xbf\x89\xe2\xe8\x84\xe8\x92\x94") or digest not in ots_bytes:
                errors.append("data/MANIFEST.sha256.ots is invalid or does not embed current data/MANIFEST.sha256 digest")

    # Zero sorry / admit / native_decide in verified Lean proof files (PalomarChallenge.lean is the contract file)
    lean_dir = ROOT / "lean"
    for lf in lean_dir.rglob("*.lean"):
        if ".lake" in lf.parts or lf.name == "PalomarChallenge.lean":
            continue
        code_lines = [ln for ln in lf.read_text(encoding="utf-8").splitlines() if not ln.strip().startswith("--")]
        body = "\n".join(code_lines)
        for bad in ("sorry", "admit", "native_decide"):
            if re.search(rf"\b{bad}\b", body):
                stripped = re.sub(r"/-.*?-/", "", body, flags=re.DOTALL)
                if re.search(rf"\b{bad}\b", stripped):
                    errors.append(f"Forbidden token {bad!r} in Lean source {lf.relative_to(ROOT)}")

    # Version consistency across VERSION, pyproject.toml, rust/Cargo.toml, CITATION.cff, lean/lakefile.toml, lean/formalization.yaml
    if (ROOT / "VERSION").exists():
        ver = (ROOT / "VERSION").read_text(encoding="utf-8").strip()
        for rel, pat in [
            ("pyproject.toml", rf'version\s*=\s*"{re.escape(ver)}"'),
            ("rust/Cargo.toml", rf'version\s*=\s*"{re.escape(ver)}"'),
            ("CITATION.cff", rf'version:\s*"{re.escape(ver)}"'),
            ("lean/lakefile.toml", rf'version\s*=\s*"{re.escape(ver)}"'),
            ("lean/formalization.yaml", rf'release_version:\s*"{re.escape(ver)}"'),
        ]:
            p = ROOT / rel
            if p.exists() and not re.search(pat, p.read_text(encoding="utf-8")):
                errors.append(f"Version mismatch (expected {ver}) in {rel}")

    if errors:
        print("AUDIT FAILED:")
        for e in errors:
            print(f"  - {e}")
        return 1

    print("AUDIT PASSED: all required files, 90 repo.yaml items, dual timestamps, zero banned/sorry tokens, no-LLC policy, and version sync verified.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
