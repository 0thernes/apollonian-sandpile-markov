#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Verify zero-warning TeX log, build clean-room arXiv tarball, stamp RFC 3161 + OTS, and write checksums."""

from __future__ import annotations

import gzip
import hashlib
import io
import re
import shutil
import subprocess
import tarfile
import tempfile
from pathlib import Path

import requests

ROOT = Path(__file__).resolve().parents[1]


def write_manifest(path: Path, rels: list[str]) -> None:
    lines = []
    for rel in rels:
        h = hashlib.sha256((ROOT / rel).read_bytes()).hexdigest()
        lines.append(f"{h}  {rel}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(("\n".join(lines) + "\n").encode("utf-8"))


def find_openssl() -> str | None:
    cand = shutil.which("openssl")
    if cand:
        return cand
    git_openssl = Path(r"C:\Program Files\Git\usr\bin\openssl.exe")
    if git_openssl.exists():
        return str(git_openssl)
    return None


def main() -> int:
    log_path = ROOT / "paper" / "build" / "main.log"
    log = log_path.read_text(encoding="utf-8", errors="replace")
    pat = r"Overfull \\hbox|Underfull \\hbox|Overfull \\vbox|Underfull \\vbox|LaTeX Warning:|Package hyperref Warning:"
    bad_lines = [ln for ln in log.splitlines() if re.search(pat, ln)]
    print(f"TeX warning count: {len(bad_lines)}")
    for ln in bad_lines[:20]:
        print(f"  WARN: {ln}")
    if bad_lines:
        return 1

    # 1. Build deterministic clean-room mtime=0 arXiv tarball
    tar_path = ROOT / "dist" / "arxiv_submission.tar.gz"
    files_to_pack = [
        ("paper/main.tex", "main.tex"),
        ("paper/references.bib", "references.bib"),
        ("paper/build/main.bbl", "main.bbl"),
        ("paper/figures/fig1_apollonian_octahedral_reciprocity.pdf", "figures/fig1_apollonian_octahedral_reciprocity.pdf"),
        ("paper/figures/fig2_sandpile_apollonian_a2_tropical.pdf", "figures/fig2_sandpile_apollonian_a2_tropical.pdf"),
        ("paper/figures/fig3_markov_cohn_mod32_hurwitz.pdf", "figures/fig3_markov_cohn_mod32_hurwitz.pdf"),
        ("paper/figures/fig4_unified_vieta_architecture.pdf", "figures/fig4_unified_vieta_architecture.pdf"),
    ]
    with (
        tar_path.open("wb") as raw_f,
        gzip.GzipFile(filename="", mode="wb", fileobj=raw_f, mtime=0) as gz,
        tarfile.open(fileobj=gz, mode="w", format=tarfile.GNU_FORMAT) as tf,
    ):
        for src_rel, arcname in files_to_pack:
            data = (ROOT / src_rel).read_bytes()
            ti = tarfile.TarInfo(name=arcname)
            ti.size = len(data)
            ti.mtime = 0
            ti.uid = 0
            ti.gid = 0
            ti.uname = ""
            ti.gname = ""
            ti.mode = 0o644
            tf.addfile(ti, io.BytesIO(data))

    # 2. Verify clean-room arXiv tarball compiles cleanly with Tectonic
    with tempfile.TemporaryDirectory() as td:
        with tarfile.open(tar_path, "r:gz") as tf:
            tf.extractall(td, filter="data")
        subprocess.run(["tectonic", "-X", "compile", "main.tex"], cwd=td, check=True)
    print("Clean-room arXiv tarball compile: PASS")

    # 3. Normalize LF on text/JSON result artifacts & write data/MANIFEST.sha256
    data_rels = [
        "results/lean_axioms.txt",
        "results/rust_summary.json",
        "results/exact_verification_report.json",
        "results/figure_stats.json",
    ]
    for rel in data_rels:
        p = ROOT / rel
        p.write_bytes(p.read_bytes().replace(b"\r\n", b"\n"))
    data_manifest = ROOT / "data" / "MANIFEST.sha256"
    write_manifest(data_manifest, data_rels)

    # 4. Stamp data/MANIFEST.sha256 with DigiCert RFC 3161 (.tsr) & verify ASN.1 reply via openssl
    digest = hashlib.sha256(data_manifest.read_bytes()).digest()
    digest_hex = digest.hex()
    alg_id = bytes.fromhex("300d06096086480165030402010500")
    msg_imprint = b"\x30" + bytes([len(alg_id) + 2 + len(digest)]) + alg_id + b"\x04\x20" + digest
    body = bytes.fromhex("020101") + msg_imprint + bytes.fromhex("0101ff")
    tsq = b"\x30" + bytes([len(body)]) + body
    r_tsa = requests.post(
        "http://timestamp.digicert.com",
        data=tsq,
        headers={"Content-Type": "application/timestamp-query"},
        timeout=20,
    )
    r_tsa.raise_for_status()
    tsr_bytes = r_tsa.content
    if not (tsr_bytes[0] == 0x30 and len(tsr_bytes) > 500 and digest in tsr_bytes):
        print("ERROR: invalid RFC 3161 TSR returned by DigiCert")
        return 1
    tsr_path = ROOT / "data" / "MANIFEST.sha256.tsr"
    tsr_path.write_bytes(tsr_bytes)
    print(f"DigiCert RFC 3161 TSR written: {len(tsr_bytes)} bytes")

    openssl_bin = find_openssl()
    if openssl_bin:
        proc = subprocess.run(
            [openssl_bin, "ts", "-reply", "-in", str(tsr_path), "-text"],
            capture_output=True,
            text=True,
            check=True,
        )
        reply_out = proc.stdout
        if "Status: Granted." not in reply_out:
            print("ERROR: openssl ts -reply did not report 'Status: Granted.'")
            return 1
        # Reconstruct exact hex imprint from OpenSSL `0000 - xx xx ...   <ascii>` lines
        hex_chunks = re.findall(
            r"^\s*[0-9a-fA-F]{4}\s*-\s*([0-9a-fA-F -]+?)\s{2,}",
            reply_out,
            flags=re.MULTILINE,
        )
        parsed_imprint = re.sub(r"[^0-9a-fA-F]", "", "".join(hex_chunks)).lower()
        if parsed_imprint != digest_hex:
            print(f"ERROR: openssl ts -reply imprint mismatch: {parsed_imprint} != {digest_hex}")
            return 1
        print(f"OpenSSL RFC 3161 TSR ASN.1 reply check: PASS (Status: Granted., SHA-256={parsed_imprint[:16]}...)")

    # 5. Stamp data/MANIFEST.sha256 with 3 independent Bitcoin OpenTimestamps calendars (.ots)
    calendars = [
        "https://a.pool.opentimestamps.org/digest",
        "https://b.pool.opentimestamps.org/digest",
        "https://alice.btc.calendar.opentimestamps.org/digest",
    ]
    cal_resps: list[bytes] = []
    for url in calendars:
        r = requests.post(
            url,
            data=digest,
            headers={
                "Accept": "application/vnd.opentimestamps.v1",
                "Content-Type": "application/x-www-form-urlencoded",
            },
            timeout=20,
        )
        if r.status_code == 200 and len(r.content) > 20:
            cal_resps.append(r.content)
            print(f"OTS calendar OK: {url} ({len(r.content)} bytes)")
    if len(cal_resps) < 2:
        print(f"ERROR: expected >=2 OTS calendars, got {len(cal_resps)}")
        return 1
    ots_magic = b"\x00OpenTimestamps\x00\x00Proof\x00\xbf\x89\xe2\xe8\x84\xe8\x92\x94"
    ots_payload = bytearray(ots_magic + b"\x01\x08" + digest)
    for i, resp in enumerate(cal_resps):
        if i < len(cal_resps) - 1:
            ots_payload.append(0xFF)
        ots_payload.extend(resp)
    (ROOT / "data" / "MANIFEST.sha256.ots").write_bytes(bytes(ots_payload))
    print(f"OpenTimestamps OTS written: {len(ots_payload)} bytes ({len(cal_resps)} calendars)")

    # 6. Write MANIFEST.sha256 and SHA256SUMS
    all_rels = [
        "dist/Donahue_2026_apollonian_sandpile_markov.pdf",
        "dist/arxiv_submission.tar.gz",
        "results/lean_axioms.txt",
        "results/rust_summary.json",
        "results/exact_verification_report.json",
        "results/figure_stats.json",
        "data/MANIFEST.sha256",
        "data/MANIFEST.sha256.tsr",
        "data/MANIFEST.sha256.ots",
    ]
    write_manifest(ROOT / "MANIFEST.sha256", all_rels)
    write_manifest(ROOT / "SHA256SUMS", all_rels)
    print("MANIFEST.sha256 and SHA256SUMS written successfully.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
