<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Literature & Citation Verification Log (`docs/literature-log.md`, v2.0.0)

All **23 citations** in `paper/references.bib` were audited live against Crossref DOI and arXiv APIs via `python scripts/check_citations.py` on 2026-11-26 (`23 passed, 0 failed, 0 retractions`):

- **Pillar I (Apollonian, Bianchi Octahedral, Soddy & Reciprocity):**
  - `hkrs2024` (`10.4007/annals.2024.200.2.6` / `arXiv:2307.02749`) — Haag, Kertzer, Rickards, Stange (2024)
  - `shi2025` (`arXiv:2510.21702`) — Shi, Shi, Whitehead, Williams-Tracy, Zhang (2025), generalized & octahedral circle packing reciprocity obstructions (added in `v2.0.0`)
  - `glmw2003` (`10.1016/S0022-314X(03)00015-5`) — Graham, Lagarias, Mallows, Wilks, Yan (2003)
  - `bf2011` (`10.1090/S0894-0347-2011-00707-8`) — Bourgain, Fuchs (2011)
  - `fs2011` (`10.1080/10586458.2011.565255`) — Fuchs, Sanden (2011)
  - `stange2018` (`10.1090/tran/7111`) — Stange (2018)
  - `kn2019` (`10.1073/pnas.1721104116`) — Kontorovich, Nakamura (2019)
  - `lmw2002` (`10.1080/00029890.2002.11920896`) — Lagarias, Mallows, Wilks (2002)
  - `eisenstein1844` (`10.1515/crll.1844.28.246`) — Eisenstein (1844)
- **Pillar II (Abelian Sandpile, Superharmonic Envelopes & Tropical Curves):**
  - `dhar1990` (`10.1103/PhysRevLett.64.1613`) — Dhar (1990)
  - `lps2016` (`10.1007/s00039-016-0358-7`) — Levine, Pegden, Smart (2016)
  - `lps2017` (`10.4007/annals.2017.186.1.1`) — Levine, Pegden, Smart (2017)
  - `ks2016` (`10.1016/j.crma.2015.11.003`) — Kalinin, Shkolnikov (2016)
  - `kalinin2018` (`10.1073/pnas.1805847115`) — Kalinin et al. (2018)
- **Pillar III (Markov, Cohn, Zhang Mod-32, Cluster Algebras & Hurwitz):**
  - `zhang2007` (`10.4064/aa128-3-7` / `arXiv:math/0612620`) — Ying Zhang (2007), *Congruence and uniqueness of certain Markoff numbers* (mod-32 theorem formalized in `T3b`; added in `v2.0.0`)
  - `hurwitz1907` (`10.1007/978-3-0348-4160-3_27`) — Adolf Hurwitz (1907), *Über eine Aufgabe der unbestimmten Analysis* (classical `n=4` classification formalized in `T3e`; added in `v2.0.0`)
  - `aigner2013` (`10.1007/978-3-319-00888-2`) — Aigner (2013)
  - `cohn1955` (`10.2307/1969618`) — Cohn (1955)
  - `fz2002` (`10.1090/S0894-0347-01-00385-X`) — Fomin, Zelevinsky (2002)
  - `ls2015` (`10.4007/annals.2015.182.1.2`) — Lee, Schiffler (2015)
  - `baragar1993` (`10.1201/9780203747018-1`) — Baragar (1993; Crossref DOI resolves to 2017 reprint, noted in BibTeX)
- **Formal Verification & Independent Kernels:**
  - `moura2021` (`10.1007/978-3-030-79876-5_37`) — de Moura, Ullrich (2021)
  - `carneiro2024` (`arXiv:2403.14064`) — Carneiro (2024)
