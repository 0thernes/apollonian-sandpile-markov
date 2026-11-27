#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Live citation, retraction (`update-to` & `updated-by`), and title/author audit for paper/references.bib (v2.1.0)."""

from __future__ import annotations

import argparse
import re
import sys
import time
import unicodedata
import xml.etree.ElementTree as ET
from pathlib import Path
from urllib.parse import quote

import requests

ROOT = Path(__file__).resolve().parents[1]

STOP_WORDS = {
    "the", "and", "for", "with", "from", "that", "this", "into", "over",
    "der", "die", "das", "des", "fur", "eine", "und", "uber", "some", "through",
}


def normalize_tokens(text: str) -> set[str]:
    # Strip TeX accent commands and braces
    cleaned = re.sub(r'\\["\'`^~=.]{?([A-Za-z])}?', r"\1", text)
    cleaned = re.sub(r"\\[A-Za-z]+\s*", " ", cleaned)
    cleaned = cleaned.replace("{", "").replace("}", "")
    cleaned = unicodedata.normalize("NFKD", cleaned).encode("ascii", "ignore").decode("ascii").lower()
    return {tok for tok in re.findall(r"[a-z0-9]{3,}", cleaned) if tok not in STOP_WORDS}


def bib_surnames(author_field: str) -> set[str]:
    surnames: set[str] = set()
    for person in re.split(r"\s+and\s+", author_field):
        part = person.strip()
        if not part:
            continue
        fam = part.split(",", 1)[0] if "," in part else part.split()[-1]
        for tok in normalize_tokens(fam):
            surnames.add(tok)
    return surnames


def parse_bib_entries(bib_text: str) -> list[dict[str, str]]:
    entries: list[dict[str, str]] = []
    chunks = re.split(r"\n(?=@\w+\{)", bib_text.strip())
    for chunk in chunks:
        m_key = re.match(r"@(\w+)\{([^,]+),", chunk.strip())
        if not m_key:
            continue
        entry: dict[str, str] = {"type": m_key.group(1), "key": m_key.group(2).strip()}
        for field in ("title", "doi", "eprint", "url", "year", "author"):
            m = re.search(rf"\b{field}\s*=\s*\{{((?:[^{{}}]|\{{[^{{}}]*\}})*)\}}", chunk, re.IGNORECASE)
            if m:
                entry[field] = re.sub(r"\s+", " ", m.group(1)).strip()
        entries.append(entry)
    return entries


def verify_entry(entry: dict[str, str], offline: bool = False) -> tuple[bool, str]:
    key = entry["key"]
    doi = entry.get("doi", "").strip()
    eprint = entry.get("eprint", "").strip()
    url = entry.get("url", "").strip()
    bib_title = entry.get("title", "")
    bib_author = entry.get("author", "")

    if not (doi or eprint or url):
        return False, f"[{key}] missing doi/eprint/url identifier"

    if offline:
        if not bib_title or not bib_author:
            return False, f"[{key}] missing title or author in BibTeX entry"
        return True, f"[{key}] structural identifier + title/author present (offline mode)"

    headers = {"User-Agent": "apollonian-sandpile-markov/2.1.0 (mailto:0_0@0thernes.art)"}
    expected_title_toks = normalize_tokens(bib_title)
    expected_surnames = bib_surnames(bib_author)

    if doi:
        cr_url = f"https://api.crossref.org/works/{quote(doi, safe='')}"
        try:
            time.sleep(0.25)
            r = requests.get(cr_url, headers=headers, timeout=15)
            if r.status_code != 200:
                return False, f"[{key}] Crossref HTTP {r.status_code} for DOI {doi}"
            msg = r.json().get("message", {})
            # Check BOTH update-to AND updated-by (and relation.is-retracted-by) for retractions!
            for field_name in ("update-to", "updated-by"):
                for upd in msg.get(field_name, []):
                    upd_type = str(upd.get("type", "")).lower()
                    upd_label = str(upd.get("label", "")).lower()
                    if "retract" in upd_type or "retract" in upd_label:
                        return False, f"[{key}] RETRACTED per Crossref {field_name} ({doi})"
            rel = msg.get("relation", {})
            if isinstance(rel, dict) and rel.get("is-retracted-by"):
                return False, f"[{key}] RETRACTED per Crossref relation.is-retracted-by ({doi})"

            cr_title_raw = " ".join(
                msg.get("title", []) + msg.get("subtitle", []) + msg.get("container-title", [])
            )
            if "retracted:" in cr_title_raw.lower() or "retraction:" in cr_title_raw.lower():
                return False, f"[{key}] RETRACTED title detected ({doi})"

            cr_title_toks = normalize_tokens(cr_title_raw)
            title_overlap = len(expected_title_toks & cr_title_toks) / max(1, len(expected_title_toks))
            if expected_title_toks and title_overlap < 0.40:
                return (
                    False,
                    f"[{key}] Crossref title mismatch ({title_overlap:.0%} overlap) for {doi}: got {msg.get('title', [])!r}",
                )

            cr_people = msg.get("author", []) or msg.get("editor", [])
            cr_surnames: set[str] = set()
            for p in cr_people:
                cr_surnames |= normalize_tokens(str(p.get("family", "")) + " " + str(p.get("name", "")))
            if cr_surnames and expected_surnames and not (expected_surnames & cr_surnames):
                return (
                    False,
                    f"[{key}] Crossref author surname mismatch for {doi}: expected one of {sorted(expected_surnames)}, got {sorted(cr_surnames)}",
                )
            return True, f"[{key}] Crossref OK ({doi}; title_overlap={title_overlap:.0%})"
        except (requests.RequestException, ValueError) as exc:
            return False, f"[{key}] Crossref request error for {doi}: {exc}"

    if eprint:
        ax_url = f"https://export.arxiv.org/api/query?id_list={quote(eprint, safe='')}"
        try:
            time.sleep(0.25)
            r = requests.get(ax_url, headers=headers, timeout=15)
            if r.status_code != 200 or "<entry>" not in r.text:
                return False, f"[{key}] arXiv API lookup failed for {eprint}"
            if "this paper has been withdrawn" in r.text.lower():
                return False, f"[{key}] WITHDRAWN arXiv paper ({eprint})"
            root_xml = ET.fromstring(r.text)
            ns = {"atom": "http://www.w3.org/2005/Atom"}
            entry_el = root_xml.find("atom:entry", ns)
            if entry_el is None:
                return False, f"[{key}] arXiv XML missing <entry> for {eprint}"
            ax_title = entry_el.findtext("atom:title", default="", namespaces=ns)
            ax_title_toks = normalize_tokens(ax_title)
            title_overlap = len(expected_title_toks & ax_title_toks) / max(1, len(expected_title_toks))
            if expected_title_toks and title_overlap < 0.40:
                return False, f"[{key}] arXiv title mismatch ({title_overlap:.0%} overlap) for {eprint}: got {ax_title!r}"
            ax_surnames: set[str] = set()
            for auth_el in entry_el.findall("atom:author/atom:name", ns):
                if auth_el.text:
                    ax_surnames |= normalize_tokens(auth_el.text)
            if ax_surnames and expected_surnames and not (expected_surnames & ax_surnames):
                return False, f"[{key}] arXiv author mismatch for {eprint}"
            return True, f"[{key}] arXiv API OK ({eprint}; title_overlap={title_overlap:.0%})"
        except (requests.RequestException, ET.ParseError) as exc:
            return False, f"[{key}] arXiv API error for {eprint}: {exc}"

    try:
        r = requests.head(url, headers=headers, allow_redirects=True, timeout=15)
        if r.status_code >= 400:
            r = requests.get(url, headers=headers, allow_redirects=True, timeout=15)
        if r.status_code >= 400:
            return False, f"[{key}] URL HTTP {r.status_code} ({url})"
        return True, f"[{key}] URL HTTP {r.status_code} OK ({url})"
    except requests.RequestException as exc:
        return False, f"[{key}] URL error for {url}: {exc}"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--offline", action="store_true", help="Check structure without network calls")
    args = ap.parse_args()

    bib_path = ROOT / "paper" / "references.bib"
    if not bib_path.exists():
        print(f"ERROR: missing {bib_path}", file=sys.stderr)
        return 1

    entries = parse_bib_entries(bib_path.read_text(encoding="utf-8"))
    if not entries:
        print("ERROR: no BibTeX entries parsed", file=sys.stderr)
        return 1

    failures = 0
    for entry in entries:
        ok, msg = verify_entry(entry, offline=args.offline)
        print(("PASS " if ok else "FAIL ") + msg)
        if not ok:
            failures += 1

    print(f"\nChecked {len(entries)} BibTeX references: {len(entries) - failures} passed, {failures} failed.")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
