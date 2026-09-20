# Isabelle/HOL formal development for "Machine-Checked Dual-Write Recovery from a Commit Log"

This archive contains the complete Isabelle/HOL dependency closure for
**Machine-Checked Dual-Write Recovery from a Commit Log** by Andreas Andreakis.
It provides the source needed to rebuild the proofs with Isabelle2025-2 and
a theorem index linking the paper's numbered results to their formal statements.
The manuscript itself is not included.

## Version 1.0.1

This is a documentation-only update to version 1.0. This README was
rewritten, the document bibliography uses the paper's current title, and
the theorem index uses the paper's current display names. All 127 theory
files, all eight session ROOT files, and the remaining build inputs are
byte-identical to version 1.0. No definitions, theorem statements, proofs,
or session dependencies changed.

This release supersedes version 1.0 in the same Zenodo version series.
The archive embeds no Zenodo identifier of its own. Those identifiers are
recorded in the Zenodo metadata and cited from the paper.

## Scope

The development studies recovery between a source with a durable record of
committed events and an independently accepting sink. It constructs states
that recovery cannot distinguish from source-side information alone, and
proves the resulting limits on recovery policies. Positive results specify
conditions under which sink acceptance records and fencing support recovery.
Further results examine concurrent workers, finite deduplication memory,
and loss of source history.

The negative results concern the modeled machines and specified policy
classes. Positive results depend on their stated assumptions. The proofs
do not verify a deployed broker, connector, mail provider, or recovery
implementation. Exactly-once results are relative to the event, frontier,
and retained history specified by each statement.

## Contents

There are 147 files, including 127 Isabelle theory files. The archive root is
`Dual_Write_Recovery-1.0.1/` and contains:

- `README.md`: release and build information.
- `LICENSE`: the BSD 3-Clause license.
- `THEOREM_INDEX.md`: the mapping from paper results to Isabelle statements.
- `isabelle/`: the complete eight-session source closure.

| Directory under isabelle/ | Session | Theory files |
|---|---|---:|
| dual_write_layer0 | Dual_Write_Layer0 | 5 |
| dual_write_core | Dual_Write_Core | 23 |
| dual_write_effect | Dual_Write_Effect | 42 |
| dual_write_unified | Dual_Write_Unified | 14 |
| dual_write_transit | Dual_Write_Transit | 7 |
| dual_write_schedule_validator | Dual_Write_Schedule_Validator | 1 |
| formal | DBLog_Virtual_Cuts | 34 |
| dual_write_dblog_instance | Dual_Write_DBLog_Instance | 1 |

The main dependency chain is HOL-Library, Dual_Write_Layer0,
Dual_Write_Core, Dual_Write_Effect, Dual_Write_Unified, and
Dual_Write_Transit. The schedule validator depends on Dual_Write_Core.
DBLog_Virtual_Cuts depends on Dual_Write_Layer0, and
Dual_Write_DBLog_Instance provides the worked-instance bridge.
No Archive of Formal Proofs entries are required.

The paths in `THEOREM_INDEX.md` resolve directly inside this archive.
That index is a navigation aid. The Isabelle statements and their
assumptions determine what is proved.

## Build

Use a stock **Isabelle2025-2** installation and a working LaTeX toolchain.
Run this command from the extracted archive root:

```bash
isabelle build -b -j 8 -o quick_and_dirty=false \
  -d isabelle/dual_write_layer0 -d isabelle/dual_write_core \
  -d isabelle/dual_write_effect -d isabelle/dual_write_unified \
  -d isabelle/dual_write_transit -d isabelle/dual_write_schedule_validator \
  -d isabelle/formal -d isabelle/dual_write_dblog_instance \
  Dual_Write_Transit Dual_Write_Schedule_Validator Dual_Write_DBLog_Instance
```

These three targets build the complete dependency closure. The `-b` option
saves heap images. The `quick_and_dirty=false` option rejects unfinished
proofs. Four sessions also generate entry-document PDFs, so LaTeX and
BibTeX must be available.

For an isolated build, set `USER_HOME` to a fresh directory for this
command. Isabelle derives its user settings and session databases from
that directory. Do not reuse session databases from a different version
of this development.

## Verification limits

The Isabelle kernel checks the formal statements under their assumptions.
A successful build does not establish that a deployed system satisfies
those assumptions. In particular, the formal durability, acceptance,
fencing, and retention rules must be justified for the implementation.
The safety predicates and completeness predicates are separate, and the
frontier-relative completeness results do not make an eventual-delivery
claim for arbitrary future execution.

## Included DBLog development

The `isabelle/formal/` directory contains the DBLog_Virtual_Cuts development
needed by the worked instance. Its separately published version 2.1 is at
[10.5281/zenodo.21732790](https://doi.org/10.5281/zenodo.21732790), with concept
DOI [10.5281/zenodo.20389696](https://doi.org/10.5281/zenodo.20389696).
Its own README and license remain unchanged in this archive.

## Release identification

- Version: **1.0.1**.
- Prepared: **2026-09-11**.
- Theorem index and document bibliography as of commit
  `5bf0b541797bb57345c5a6ff9ec710753857ffc3`.
- Formal source baseline: version 1.0, archive SHA-256
  `b18fe3d6ad2a56f5f3269460ec8f87a83504ffbd006d10f3e8db25801bf3a713`.

The release DOI is recorded in the Zenodo metadata and cited from the
paper's bibliography. It is not embedded in this archive, so obtaining it
does not require another archive build.

## License and author

BSD 3-Clause, as provided in `LICENSE`. The bundled DBLog session retains
its own copy of that license.

Andreas Andreakis, ORCID
[0009-0003-9025-9402](https://orcid.org/0009-0003-9025-9402).
