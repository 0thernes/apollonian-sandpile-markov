<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Archival Operations, Offsite Mirroring & Rollback (`docs/operations.md`)

This repository contains no mutable runtime database or long-running server process. Operational resilience focuses on **immutable archival preservation**, **offsite git bundle/mirror recovery**, and **zero-downtime static GitHub Pages rollback**.

## 1. Multi-Site Offsite Preservation & Mirroring

Every tagged release (`v1.0.0`, `v2.0.0`, …) is preserved across four independent layers:
1. **Primary GitHub Repository & Release Assets:** `https://github.com/0thernes/apollonian-sandpile-markov` with unsigned annotated release tags, frozen PDF, deterministic `mtime=0` arXiv tarball, `SHA256SUMS`, `data/MANIFEST.sha256.tsr`, and `data/MANIFEST.sha256.ots` attached.
2. **Master Research Archive Submodule Mirror:** Pinned exact commit SHA + frozen PDF copy + RFC 3161 timestamp inside the independent repository [`0thernes-research-archive`](https://github.com/0thernes/0thernes-research-archive) under permanent ID `0TH-2026-018`.
3. **Software Heritage Public Archive (SWHID):** Every release commit is submitted to Software Heritage Save Code Now and its verified `swh:1:snp:...` snapshot identifier is recorded in `docs/run-log.md` and `0thernes-research-archive`.
4. **Offline Git Bundle Backup (`git bundle`):** Maintainers can generate a self-contained, verifiable offline repository mirror at any time:
   ```bash
   git bundle create ../apollonian-sandpile-markov-v2.0.0.bundle --all
   git bundle verify ../apollonian-sandpile-markov-v2.0.0.bundle
   ```
   A full repository can be restored offline from the bundle via `git clone apollonian-sandpile-markov-v2.0.0.bundle apollonian-sandpile-markov`.

## 2. Dual Cryptographic Timestamping

- **RFC 3161 Trusted Timestamp (`data/MANIFEST.sha256.tsr`):** Issued by DigiCert TSA (`http://timestamp.digicert.com`) over the exact SHA-256 digest of `data/MANIFEST.sha256`.
- **Bitcoin OpenTimestamps (`data/MANIFEST.sha256.ots`):** Submitted to three independent public calendars (`a.pool.opentimestamps.org`, `b.pool.opentimestamps.org`, `alice.btc.calendar.opentimestamps.org`) over the identical digest.
- **GitHub Actions SLSA Provenance:** Every `main` push emits a signed Sigstore/Rekor SLSA v1 attestation (`actions/attest-build-provenance@v2`) covering `dist/Donahue_2026_apollonian_sandpile_markov.pdf`, `dist/arxiv_submission.tar.gz`, `MANIFEST.sha256`, `SHA256SUMS`, `data/MANIFEST.sha256`, and `results/lean_axioms.txt`.

## 3. Static Site Deployment & Instant Rollback (`A36`)

- **Deploy:** Pushing to `main` triggers `.github/workflows/pages.yml`, assembling `docs/index.html`, `studio/index.html`, `blueprint/index.html`, `docs/media/social-preview.png`, and `dist/Donahue_2026_apollonian_sandpile_markov.pdf` into GitHub Pages.
- **Rollback (zero force-push):** To roll back a defective deployment without rewriting public git history:
  ```bash
  git revert HEAD --no-edit
  git push origin main
  ```
  GitHub Actions immediately redeploys the previous clean commit to GitHub Pages within ~45 seconds.
