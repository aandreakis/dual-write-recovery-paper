# Isabelle/HOL formal development for "Machine-Checked Dual-Write Recovery from a Committed Log"

This is the complete Isabelle/HOL session dependency closure behind
the paper

> **Machine-Checked Dual-Write Recovery from a Committed Log**,
> by Andreas Andreakis.

This deposit is an audit and reproducibility artifact: the paper is
written to be read without it, and every numbered result in the paper
is understandable from the paper alone. What this archive adds is the
machine check — the ability to rebuild every proof from source under
Isabelle2025-2 and to trace each numbered paper result to the exact
mechanized theorem it reports.

The subject is the delivery boundary of dual-write systems in the
change-data-capture (CDC) setting: a source database's committed log is
the authority, effects are delivered to an external sink, and the
relay's delivery and its progress record are two separate durable acts.
The paper's spine is an information bound (two reachable post-crash
states can agree on everything the crashed side durably knows and still
differ in what the sink accepted), the sink-reading escape from it, the
staleness and concurrency fences at the sink's acceptance boundary, and
the proved lifetime limits of the evidence (bounded deduplication
memory, truncated source history).

## Contents

The archive contains this `README.md`, `LICENSE`, the paper-to-theorem
map `THEOREM_INDEX.md`, and the eight-session closure under
`isabelle/` (127 theory files in total).

```text
Dual_Write_Recovery-1.0/
├── README.md
├── LICENSE
├── THEOREM_INDEX.md            maps paper results T1–T12 to theorems + sources
└── isabelle/
    ├── dual_write_layer0/            session Dual_Write_Layer0   (5 theories)
    │                                 shared source/replay substrate; parent HOL-Library;
    │                                 the one conservative typedef, its order proved
    ├── dual_write_core/              session Dual_Write_Core     (23 theories)
    │                                 store tier: crash partition, verified relay,
    │                                 faithful-image converse, completeness, decider
    ├── dual_write_effect/            session Dual_Write_Effect   (42 theories)
    │                                 emitted-effect tier: append-only emission ledger,
    │                                 observation/control-plane bounds, checkpoint
    │                                 dilemma, sink-reading escape, wire bound,
    │                                 arrival fence, dedup-view coverage identity
    ├── dual_write_unified/           session Dual_Write_Unified  (14 theories)
    │                                 unified machine: concurrent recovery, claim
    │                                 fences, journal-grade closures, truncation,
    │                                 shared-core agreement
    ├── dual_write_transit/           session Dual_Write_Transit  (7 theories)
    │                                 acceptance-level transit interface
    ├── dual_write_schedule_validator/ session Dual_Write_Schedule_Validator (1 theory)
    │                                 certified schedule validator companion
    ├── formal/                       session DBLog_Virtual_Cuts  (34 theories)
    │                                 the DBLog virtual-cut development (see below);
    │                                 carries its own README.md and LICENSE
    └── dual_write_dblog_instance/    session Dual_Write_DBLog_Instance (1 theory)
                                      the DBLog worked-instance bridge
```

Session parentage: `HOL-Library` → `Dual_Write_Layer0` →
`Dual_Write_Core` → `Dual_Write_Effect` → `Dual_Write_Unified` →
`Dual_Write_Transit`; `Dual_Write_Schedule_Validator` sits on
`Dual_Write_Core`; `DBLog_Virtual_Cuts` sits on `Dual_Write_Layer0`,
and `Dual_Write_DBLog_Instance` — its sole importer here — exhibits one
certified wellformed DBLog run as a worked instance of the shared
virtual-cut-state interface. No Archive of Formal Proofs entries are
required; a stock Isabelle distribution suffices.

`THEOREM_INDEX.md` maps every numbered result in the paper (T1–T12,
their corollaries, and the named supporting results) to its principal
Isabelle theorem(s) and source file; its `isabelle/...` paths resolve
verbatim inside this archive. The Isabelle statements are authoritative;
the index is a navigation map, not a second specification.

## Building

Verified with **Isabelle2025-2**. From the archive root:

```bash
isabelle build -b -j 8 -o quick_and_dirty=false \
  -d isabelle/dual_write_layer0 -d isabelle/dual_write_core \
  -d isabelle/dual_write_effect -d isabelle/dual_write_unified \
  -d isabelle/dual_write_transit -d isabelle/dual_write_schedule_validator \
  -d isabelle/formal -d isabelle/dual_write_dblog_instance \
  Dual_Write_Transit Dual_Write_Schedule_Validator Dual_Write_DBLog_Instance
```

The three named targets close the whole development: `Dual_Write_Transit`
pulls the Layer-0 → Core → Effect → Unified → Transit chain,
`Dual_Write_Schedule_Validator` adds the certified validator, and
`Dual_Write_DBLog_Instance` builds the worked DBLog bridge through
`DBLog_Virtual_Cuts`. The `-b` flag saves heap images so a partial
build cannot leave ancestor sessions unloadable.

Notes:

- The `sorry`-intolerant `quick_and_dirty=false` build **is** the check.
- Four sessions (`Dual_Write_Layer0`, `Dual_Write_Core`,
  `Dual_Write_Effect`, `DBLog_Virtual_Cuts`) generate entry documents
  (PDFs), so the documented build needs a working LaTeX toolchain.
  Their `ROOT` files pin `document = pdf`, and session options take
  precedence over command-line `-o` options; to check the proofs
  without LaTeX, remove the `document = pdf, document_output = "output"`
  options from those `ROOT` files before building.
- If a pre-existing `~/.isabelle` holds conflicting session databases
  from older builds, run with a fresh user home, e.g.
  `USER_HOME=$(mktemp -d) isabelle build ...` (Isabelle derives its
  user home from `$USER_HOME`; exporting `ISABELLE_HOME_USER` directly
  is ignored by the settings mechanism).
- The full chain is quick: a from-scratch run of the exact command
  above — `HOL-Library` compilation and all four entry documents
  included — completes in about five minutes on a modern laptop
  (Apple Silicon M-class, 8 parallel jobs).

## Verification

The development builds `sorry`-free under `quick_and_dirty=false` and
is axiom-free: it declares no `axiomatization` and no `consts`; every
type it introduces is a `datatype` or `record` except one conservative
`typedef` — the shared source-coordinate type in `Dual_Write_Layer0` —
whose order is *proved*, not assumed. Witnesses and
counterexample fixtures are constructed instances. The corpus was
closed after a multi-round adversarial review program in which every
landed slice was gated by full-chain clean builds on an isolated
Isabelle home.

The kernel checks each theorem under the premises stated in its own
statement. It does not, and cannot, discharge the modelling assumptions
a real deployment must establish — faithful capture and delivery
plumbing, the durability of what the model calls durable, and the
sink-side acceptance discipline actually being enforced at the claimed
boundary.

## Scope and non-claims

- The paper studies one configuration — the *studied shape*: exactly
  one side (the source) holds the durable, ordered, per-operation
  record that defines what is owed, and the obligation runs one way,
  toward the sink. This is not a general theory of arbitrary dual
  writes; the paper states the shape and its exclusions explicitly.
- The impossibility results are exists-system statements proved at
  designed witness machines or schedules — information bounds, not
  for-all laws over implementations. The positive results (the
  discipline theorems, the fences, the equivalences) are parametric
  under their stated premises.
- Effect-safety never means delivery: the safety predicates are blind
  to never-emitted deliveries, and no liveness is claimed. The
  append-only emission ledger is a disclosed modeling decision ("the
  world does not roll back"), not a discovered law.
- Nothing here claims general transactional atomicity, serializability,
  isolation, or multidatabase atomic commitment; the results are
  crash-durability facts, not FLP-style asynchronous-consensus results.

## Relationship to prior artifacts

The bundled `isabelle/formal/` session is the **DBLog_Virtual_Cuts**
development — the formal artifact of the separate paper *A
Theoretical Study of DBLog* — whose published archival record is
[10.5281/zenodo.20389696](https://doi.org/10.5281/zenodo.20389696)
(the concept DOI, resolving to the latest version; version 2.1 at
[10.5281/zenodo.21732790](https://doi.org/10.5281/zenodo.21732790)). It is included here so the archive is a self-contained
build closure for the one worked instance; its own `README.md`
documents that development in full. No part of the dual-write
development itself has been deposited before — this is its first
published version.

## Release identification

```text
Version:        1.0
Release date:   2026-08-01
Source commit:  d40f550f
```

The deposit's DOI lives on the Zenodo record page and in the
accompanying paper's bibliography; it is deliberately not embedded in
the archive itself (an artifact citing its own version identifier is
a cyclical dependency).

## License

BSD 3-Clause "New" or "Revised" License — see `LICENSE`. The bundled
DBLog session carries its own copy of the same license.

## Author

Andreas Andreakis — ORCID
[0009-0003-9025-9402](https://orcid.org/0009-0003-9025-9402).
