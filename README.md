# Machine-Checked Dual-Write Recovery from a Committed Log

[![Paper (arXiv)](https://img.shields.io/badge/paper-arXiv%3A2608.00501-b31b1b)](https://arxiv.org/abs/2608.00501)
[![Artifact 1.0 DOI](https://img.shields.io/badge/artifact-10.5281%2Fzenodo.21734366-1682D4)](https://doi.org/10.5281/zenodo.21734366)

Sources for the paper **"Machine-Checked Dual-Write Recovery from a Committed
Log"** (Andreas Andreakis, 2026) and the Isabelle/HOL development that
accompanies it.

An application commits an operation to one durable system and causes an effect
in another, with no transaction spanning both. The paper gives a machine-checked
information bound for recovery at that boundary — source-side state alone cannot
distinguish whether the sink accepted an operation during a crash window — and
the constructive results that follow from reading the sink's durable acceptance
record, fencing stale actors at acceptance, and retaining the evidence. Twelve
principal results, T1–T12, proved in Isabelle/HOL with no `axiomatization`, no
`consts`, and no unfinished proof.

The negative results quantify over named policy classes on constructed reachable
witnesses; the positive results carry explicit observation, identity, atomicity,
ordering, and retention premises. Nothing here is a liveness claim, and no
production system is verified. The kernel checks proofs from their hypotheses;
it cannot establish that a deployment satisfies them.

**Links** — [paper on arXiv](https://arxiv.org/abs/2608.00501) ·
[archived artifact (Zenodo)](https://doi.org/10.5281/zenodo.21734366) ·
[theorem scope notes](docs/THEOREMS.md) ·
[paper-to-Isabelle map](formal/THEOREM_INDEX.md) ·
[provenance](docs/PROVENANCE.md) ·
[AGENTS.md](AGENTS.md) for AI tools

## Repository map

| Path | What it is |
|---|---|
| [paper/](paper/) | Exact arXiv v4 manuscript files, the five source figures, and arXiv's stamped PDF. |
| [formal/](formal/) | The complete eight-session Isabelle/HOL artifact, **byte-identical to Zenodo version 1.0**. Do not edit. |
| [formal/THEOREM_INDEX.md](formal/THEOREM_INDEX.md) | Authoritative navigation map from T1–T12 and corollaries to Isabelle theorem names and files. |
| [formal/README.md](formal/README.md) | The artifact's own README: session layout, trust base, build notes. |
| [docs/THEOREMS.md](docs/THEOREMS.md) | Reader-oriented scope notes for each result — including what each does *not* say. |
| [docs/PROVENANCE.md](docs/PROVENANCE.md) | Paper and artifact version history, DOIs, hashes. |
| [AGENTS.md](AGENTS.md) | Source precedence, terminology, non-claims, and verification instructions for AI tools. |

## The paper

- **arXiv v4:** [abstract](https://arxiv.org/abs/2608.00501v4) ·
  [PDF](https://arxiv.org/pdf/2608.00501v4) — 22 pages, 5 figures,
  cs.DB + cs.DC + cs.LO, CC BY 4.0.
- **In this repository:** [machine-checked-dual-write-recovery.pdf](paper/machine-checked-dual-write-recovery.pdf) — arXiv's own stamped v4 PDF.
- **Build from source** (the bundle carries `main.bbl`, so BibTeX is not
  required for this exact rebuild):

~~~bash
cd paper
pdflatex main
pdflatex main
pdflatex main
~~~

## The proofs

Verified with [Isabelle2025-2](https://isabelle.in.tum.de/). From the
repository root:

~~~bash
isabelle build -b -j 8 -o quick_and_dirty=false \
  -d formal/isabelle/dual_write_layer0 \
  -d formal/isabelle/dual_write_core \
  -d formal/isabelle/dual_write_effect \
  -d formal/isabelle/dual_write_unified \
  -d formal/isabelle/dual_write_transit \
  -d formal/isabelle/dual_write_schedule_validator \
  -d formal/isabelle/formal \
  -d formal/isabelle/dual_write_dblog_instance \
  Dual_Write_Transit Dual_Write_Schedule_Validator Dual_Write_DBLog_Instance
~~~

The three named targets close all eight sessions and 127 theory files. The build
is `sorry`-intolerant, declares no `axiomatization` and no `consts`, and uses one
conservative `typedef` whose order is proved rather than assumed. Complete
trust-base and build notes: [formal/README.md](formal/README.md).

To check this tree against the archived deposit:

~~~bash
curl -sL https://zenodo.org/records/21734366/files/Dual_Write_Recovery-1.0.tar.gz | tar xz
diff -r Dual_Write_Recovery-1.0 formal
~~~

No output from `diff` means the trees are identical. Zenodo remains the archival
identifier; this repository is a convenience mirror.

## Versions and DOIs

| | Paper | Formal development |
|---|---|---|
| Current | [arXiv:2608.00501v4](https://arxiv.org/abs/2608.00501v4), 13 Aug 2026 | `1.0` — [10.5281/zenodo.21734366](https://doi.org/10.5281/zenodo.21734366), 1 Aug 2026 |
| Previous paper versions | [v3](https://arxiv.org/abs/2608.00501v3), 8 Aug · [v2](https://arxiv.org/abs/2608.00501v2), 4 Aug · [v1](https://arxiv.org/abs/2608.00501v1), 1 Aug | — |
| Always-latest artifact DOI | — | [10.5281/zenodo.21734365](https://doi.org/10.5281/zenodo.21734365) (concept DOI) |

The arXiv v4 paper cites the exact Zenodo version DOI
`10.5281/zenodo.21734366`, and this repository's `formal/` tree is
byte-identical to that deposit. Full hashes and the relationship between the
public records: [docs/PROVENANCE.md](docs/PROVENANCE.md).

## Citing

The paper:

~~~bibtex
@misc{andreakis2026dual_write_recovery,
  author        = {Andreas Andreakis},
  title         = {Machine-Checked Dual-Write Recovery from a Committed Log},
  year          = {2026},
  eprint        = {2608.00501},
  archivePrefix = {arXiv},
  primaryClass  = {cs.DB},
  doi           = {10.48550/arXiv.2608.00501}
}
~~~

The formal development:

~~~bibtex
@misc{andreakis2026dual_write_recovery_formal,
  author    = {Andreas Andreakis},
  title     = {Isabelle/HOL formal development for
               "Machine-Checked Dual-Write Recovery from a Committed Log"},
  year      = {2026},
  publisher = {Zenodo},
  version   = {1.0},
  doi       = {10.5281/zenodo.21734366},
  note      = {Software, BSD 3-Clause License.}
}
~~~

GitHub's **Cite this repository** button reads [CITATION.cff](CITATION.cff).

## Licence

- **Paper text and figures** (`paper/` and reader documentation) — Creative
  Commons Attribution 4.0 International, matching the arXiv posting. See
  [LICENSES/CC-BY-4.0.txt](LICENSES/CC-BY-4.0.txt).
- **Isabelle/HOL development** (`formal/`) — BSD 3-Clause. See
  [LICENSE](LICENSE), copied from the archived artifact.

## Author

**Andreas Andreakis** — independent researcher ·
[ORCID 0009-0003-9025-9402](https://orcid.org/0009-0003-9025-9402)
