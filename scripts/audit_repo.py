#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Automated Build Standard v1.2.0 & Playbook v1.3 repository hygiene auditor (v3.0.0)."""

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
    "repo-standard.schema.json",
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
    "docs/adr/0001-zero-mathlib-six-kernel-and-vieta-unification.md",
    "docs/adr/0002-direct-detmat-and-statement-audit-remediation.md",
    "docs/adr/0003-v3-termination-descent-and-general-soddy.md",
    "docs/reviews/2026-11-26-10-pass-red-team-review.md",
    "lean/lean-toolchain",
    "lean/lakefile.toml",
    "lean/comparator.json",
    "formalization.yaml",
    "lean/formalization.yaml",
    "lean/VerifyAxioms.lean",
    "lean/VerifyAllDecls.lean",
    "rust/Cargo.toml",
    "native/asm_verify.c",
    "native/fuzz_asm.c",
    "native/fuzz_libfuzzer.c",
    "python/asm_verify/__init__.py",
    "python/asm_verify/__main__.py",
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


def strip_lean_comments(src: str) -> str:
    no_block = re.sub(r"/-.*?-/", "", src, flags=re.DOTALL)
    return "\n".join(ln for ln in no_block.splitlines() if not ln.strip().startswith("--"))


def check_markdown_links(errors: list[str]) -> None:
    link_pat = re.compile(r"!?\[[^\]]*\]\(([^)]+)\)")
    for md in ROOT.rglob("*.md"):
        if any(part in {".git", ".lake", "target", "node_modules", ".venv"} for part in md.parts):
            continue
        text = md.read_text(encoding="utf-8", errors="ignore")
        # Ignore fenced code blocks
        cleaned = re.sub(r"```.*?```", "", text, flags=re.DOTALL)
        for m in link_pat.finditer(cleaned):
            raw_target = m.group(1).strip()
            if not raw_target or raw_target.startswith(("#", "http://", "https://", "mailto:")):
                continue
            target_path = raw_target.split("#", 1)[0].split("?", 1)[0].strip()
            if not target_path:
                continue
            resolved = (md.parent / target_path).resolve()
            if not resolved.exists():
                errors.append(f"Broken relative markdown link in {md.relative_to(ROOT)}: {raw_target}")


def check_html_security_and_a11y(errors: list[str]) -> None:
    for rel in ("docs/index.html", "studio/index.html", "blueprint/index.html"):
        p = ROOT / rel
        if not p.exists():
            continue
        html = p.read_text(encoding="utf-8")
        if "Content-Security-Policy" not in html or "default-src 'none'" not in html:
            errors.append(f"Missing strict CSP header in {rel}")
        if 'class="skip-link"' not in html or 'id="main-content"' not in html:
            errors.append(f"Missing skip-link or #main-content landmark in {rel}")
        if ".innerHTML" in html:
            errors.append(f"Unsafe .innerHTML assignment detected in {rel}")
        if re.search(r"<[a-zA-Z][^>]*\bstyle\s*=", html):
            errors.append(f"Inline style= attribute detected in {rel}")
        for btn in re.findall(r"<button\b[^>]*>", html):
            if 'type="button"' not in btn:
                errors.append(f"Button missing type=\"button\" in {rel}: {btn}")
    bp = ROOT / "blueprint" / "index.html"
    if bp.exists():
        bp_text = bp.read_text(encoding="utf-8")
        # Verify every Lean declaration listed in blueprint/index.html exists in lean/
        lean_corpus = "\n".join(
            lf.read_text(encoding="utf-8", errors="ignore")
            for lf in (ROOT / "lean").rglob("*.lean")
            if ".lake" not in lf.parts
        )
        for decl in re.findall(r'decl:\s*"([A-Za-z0-9_]+)"', bp_text):
            if not re.search(rf"\b(?:theorem|def)\s+{re.escape(decl)}\b", lean_corpus):
                errors.append(f"Blueprint declaration {decl!r} not found in lean/ sources")


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

    # Unconditional repo.yaml validation against committed repo-standard.schema.json
    repo_yaml_path = ROOT / "repo.yaml"
    schema_path = ROOT / "repo-standard.schema.json"
    if repo_yaml_path.exists():
        data = yaml.safe_load(repo_yaml_path.read_text(encoding="utf-8"))
        if not schema_path.exists():
            errors.append("Missing committed repo-standard.schema.json for repo.yaml validation")
        else:
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
        "formalization.yaml",
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

    # CITATION.cff SWHID archival identifier check
    cff_path = ROOT / "CITATION.cff"
    if cff_path.exists() and "swh:1:" not in cff_path.read_text(encoding="utf-8"):
        errors.append("CITATION.cff missing Software Heritage swh:1: archival identifier")

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

    # Lean 4 Playbook §1 forbidden-token & Palomar structural audit
    lean_dir = ROOT / "lean"
    for lf in lean_dir.rglob("*.lean"):
        if ".lake" in lf.parts:
            continue
        raw = lf.read_text(encoding="utf-8")
        lines = raw.splitlines()
        if not any(ln.strip() == "module" for ln in lines[:5]):
            errors.append(f"Missing Lean 4 `module` header in {lf.relative_to(ROOT)}")
        if len(lines) > 10_000:
            errors.append(f"Lean file exceeds 10,000 lines ({len(lines)}): {lf.relative_to(ROOT)}")
        if lf.name in ("Challenge.lean", "PalomarChallenge.lean"):
            if len(lines) > 1_000 or lf.stat().st_size > 100 * 1024:
                errors.append(f"Challenge file exceeds Palomar 1,000-line / 100 KiB limit: {lf.relative_to(ROOT)}")
        stripped = strip_lean_comments(raw)
        always_forbidden = ("admit", "native_decide", "implemented_by")
        for bad in always_forbidden:
            if re.search(rf"\b{bad}\b", stripped):
                errors.append(f"Forbidden token {bad!r} in Lean source {lf.relative_to(ROOT)}")
        if "@[extern" in stripped:
            errors.append(f"Forbidden @[extern attribute in Lean source {lf.relative_to(ROOT)}")
        if re.search(r"^\s*(?:private\s+|public\s+)?axiom\b", stripped, flags=re.MULTILINE):
            errors.append(f"Custom `axiom` declaration in Lean source {lf.relative_to(ROOT)}")
        if lf.name != "PalomarChallenge.lean" and re.search(r"\bsorry\b", stripped):
            errors.append(f"Forbidden token 'sorry' in built Lean source {lf.relative_to(ROOT)}")

    # Markdown relative-link integrity & HTML security/a11y/blueprint checks
    check_markdown_links(errors)
    check_html_security_and_a11y(errors)

    # Version consistency across VERSION and all package/citation/formal manifests
    if (ROOT / "VERSION").exists():
        ver = (ROOT / "VERSION").read_text(encoding="utf-8").strip()
        for rel, pat in [
            ("pyproject.toml", rf'version\s*=\s*"{re.escape(ver)}"'),
            ("rust/Cargo.toml", rf'version\s*=\s*"{re.escape(ver)}"'),
            ("CITATION.cff", rf'version:\s*"{re.escape(ver)}"'),
            ("CITATION.bib", rf"version\s*=\s*\{{{re.escape(ver)}\}}"),
            (".zenodo.json", rf'"version":\s*"{re.escape(ver)}"'),
            ("lean/lakefile.toml", rf'version\s*=\s*"{re.escape(ver)}"'),
            ("formalization.yaml", rf'release_version:\s*"{re.escape(ver)}"'),
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

    print(
        "AUDIT PASSED: all required files, repo.yaml schema (90/90), Palomar & Lean forbidden-token scan, "
        "markdown links, HTML CSP/a11y/blueprint declarations, dual timestamps, SWHID, no-LLC policy, and version sync verified."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
