# AGENTS.md

## Purpose

This repository is the public information hub for the paper
"Machine-Checked Dual-Write Recovery from a Committed Log." It combines:

- the exact arXiv v4 paper source and stamped PDF;
- the complete Isabelle/HOL artifact archived as
  Dual_Write_Recovery version 1.0;
- reader-oriented summaries and figures.

Use this file before answering questions about the results or modifying
derived documentation.

## Source precedence

When sources differ, use this order:

1. **Isabelle theorem statements and definitions** under
   <code>formal/isabelle/</code> are authoritative for what is proved.
2. **formal/THEOREM_INDEX.md** is the authoritative navigation map from
   paper numbering T1-T12 to principal Isabelle theorem names and paths.
   Its titles are handles, not substitute statements.
3. **paper/main.tex** is authoritative for the paper's exposition,
   theorem statements as published, scope discussion, and proof ideas.
4. **README.md** and <code>docs/</code> are derived reader aids.

The kernel checks the theorem statements under their named premises. It
does not check whether a real deployment satisfies those premises.

## Frozen and editable areas

| Path | Role | Edit policy |
|---|---|---|
| <code>formal/</code> | Exact Zenodo 1.0 artifact bytes | Do not edit. Publish a new artifact version instead. |
| <code>paper/</code> | Exact arXiv v4 source and PDF | Do not edit in place. Refresh only from a new public arXiv version. |
| <code>assets/</code> | Renderings of paper figures | Regenerate from <code>paper/figures/</code>; do not redraw semantically. |
| <code>README.md</code>, <code>docs/</code>, this file | Derived orientation | May be clarified if every claim remains traceable to the frozen sources. |
| <code>CITATION.cff</code> | Repository citation metadata | Update only when the public paper or artifact record changes. |

## Studied shape

The theory studies exactly one configuration:

- one side holds a durable, ordered, per-operation source record;
- that record defines which work is owed;
- effects travel in one direction toward one accepting endpoint;
- the sink's durable acceptance record defines which effects are done.

Do not generalize the results to arbitrary multidatabase topologies,
bidirectional obligations, atomic commit, transaction isolation, or
asynchronous consensus.

## Vocabulary

| Term | Meaning here | Common mistake |
|---|---|---|
| source history | Durable ordered record of committed obligations | Treating a broker offset or wall-clock time as the source coordinate |
| frontier | Source coordinate at which a recovery verdict is judged | Reading it as a global timestamp |
| send / emission | An attempt leaves the producer side | Equating send with sink acceptance |
| accepted record | Durable sink-side record of accepted operation identities | Replacing it with current sink contents |
| durable-local view | Source-side state available to the checkpointed recovery policy, cursor included | Assuming the cursor records sink acceptance |
| hazard-free | No modeled premature or duplicate effect | Inferring that every owed effect was delivered |
| exactly-once at f | Hazard-freedom plus coverage at the named frontier | Treating it as timeless or unconditional |
| arrival fence | Sink acceptance guard for old in-flight requests | Raising it before the recovery batch and stopping the batch itself |
| claim fence | Atomic claim/read/arm discipline for competing recoverers | Treating it as the same transition as the arrival fence |
| retained view | Source evidence still visible after truncation | Treating it as the full journal specification |
| deduplicated view | Absorbing permanent-memory view using stable identities | Assuming bounded caches have the same property |

## Paper result map

| Paper | Title | Principal Isabelle result | Principal source |
|---|---|---|---|
| T1 | Observation Bound | <code>observation_measured_dilemma</code> | <code>formal/isabelle/dual_write_effect/Dual_Write_Effect_Observation_Bound.thy</code> |
| T2 | Control-Plane Bound | <code>recovery_information_dilemma_pair</code>, <code>epoch_measured_dilemma_pair</code> | <code>formal/isabelle/dual_write_effect/Dual_Write_Effect_Dilemma.thy</code> |
| T3 | Checkpoint Dilemma | <code>checkpoint_dilemma_pair</code>, <code>same_protocol_batch_agreement_dilemma</code> | <code>formal/isabelle/dual_write_effect/Dual_Write_Effect_Cursor.thy</code> |
| T4 | Sink-Reading Escape | <code>sink_reading_escape_general</code> | <code>formal/isabelle/dual_write_effect/Dual_Write_Effect_Dilemma.thy</code> |
| T5 | Wire Bound | <code>no_channel_blind_policy_escapes</code> | <code>formal/isabelle/dual_write_effect/Dual_Write_Effect_Channel_Blind.thy</code> |
| T6 | Arrival Fence | <code>fenced_redrive_exactly_once</code> | <code>formal/isabelle/dual_write_effect/Dual_Write_Effect_Fencing.thy</code> |
| T7 | Second-Recoverer Bound | <code>u_concurrent_recovery_dilemma</code> | <code>formal/isabelle/dual_write_unified/DWU_Concurrent_Recovery.thy</code> |
| T8 | Completed-Claim Exactness | <code>u_exactly_once_at_completed_claim</code> | <code>formal/isabelle/dual_write_unified/DWU_Fenced_Discipline.thy</code> |
| T9 | Deduplicated-View Coverage Identity | <code>dedup_sink_exactly_once_iff_at_least_once</code> | <code>formal/isabelle/dual_write_effect/Dual_Write_Effect_Exactly_Once.thy</code> |
| T10 | Truncation Dilemma | <code>u_truncation_recovery_dilemma</code> | <code>formal/isabelle/dual_write_unified/DWU_Truncation.thy</code> |
| T11 | Faithful-Image Equivalence | <code>safe_iff_running_image_faithful</code> | <code>formal/isabelle/dual_write_core/Dual_Write_Converse.thy</code> |
| T12 | Shared-Core Agreement | <code>Π_section</code>, <code>u_landed_embedding</code>, <code>u_solo_projection</code> | <code>formal/isabelle/dual_write_unified/DWU_Machine.thy</code>, <code>DWU_Conservativity.thy</code> |

For corollaries, supporting results, historical numbering, and exact scope
reminders, read <code>formal/THEOREM_INDEX.md</code>.

## High-risk misreadings

| Misreading | Correction |
|---|---|
| "The paper proves that every source-only recovery algorithm is impossible." | T1, T2, T3, T5, T7, and T10 quantify over named policy classes on constructed machines or schedules. Preserve those quantifiers. |
| "A correct checkpoint is enough." | T3 deliberately includes the durable cursor in the equal local view. The missing fact is sink acceptance during the deliver-to-persist window. |
| "Reading downstream contents escapes the bound." | The positive theorem reads an authoritative per-operation accepted record. Current contents can merge, overwrite, or omit the relevant history. |
| "The sink read remains true after it is taken." | In-flight arrivals and competing recoverers can make it stale. T6 and T8 impose distinct acceptance-side disciplines. |
| "The Wire Bound covers every policy unable to read the network." | T5 is scoped to channel-blind batch selectors inserted into one fixed unfenced re-drive relation at the designed pair. |
| "Ordering two recoverers is sufficient." | T7's full scope is subtle. The loose grammar's duplicate witness uses a zombie fire; the phase-ordered addendum changes the boundary and does not establish the same for-all conclusion. |
| "The arrival fence is free." | Corollary 6.1 proves rescue conversion: rejecting a stale duplicate can also drop an old request that would have rescued missing work. |
| "Fence raising may be split from the recovery delta." | T6's immediate exactness uses one atomic act that heals, lands the accepted delta, and raises the fence. |
| "Exactly-once on the deduplicated view proves a consumer transaction." | T9's displayed identity is definitional on an absorbing permanent-memory deduplicated view; the substantive per-instance result has its own premises. |
| "Truncated recovery is judged only against retained data." | T10 grades loss against the full journal specification while policies see only the retained view. |
| "The model proves delivery." | Safety predicates are blind to never-emitted effects; no liveness theorem is claimed. |
| "T12 merges all machines." | T12 proves selected relations under alignment premises. The wire does not lift and the machines retain distinct hazards. |

## Artifact facts

- Zenodo version DOI: <code>10.5281/zenodo.21734366</code>
- Zenodo concept DOI: <code>10.5281/zenodo.21734365</code>
- Version: <code>1.0</code>
- Release date: <code>2026-08-01</code>
- Archive SHA-256:
  <code>b18fe3d6ad2a56f5f3269460ec8f87a83504ffbd006d10f3e8db25801bf3a713</code>
- Eight Isabelle sessions, 127 theory files, three named build targets.
- Verified with Isabelle2025-2 and
  <code>quick_and_dirty=false</code>.
- No <code>axiomatization</code>, no <code>consts</code>, no proof
  oracles, and no unfinished proof.
- One conservative source-coordinate <code>typedef</code>; its order is
  proved.

## Verification commands

### Paper source

~~~bash
cd paper
pdflatex main
pdflatex main
pdflatex main
pdfinfo machine-checked-dual-write-recovery.pdf
~~~

Expected public PDF: 22 pages, letter size, five figures.

### Formal artifact

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

### Deposit fidelity

~~~bash
curl -sL https://zenodo.org/records/21734366/files/Dual_Write_Recovery-1.0.tar.gz | tar xz
diff -r Dual_Write_Recovery-1.0 formal
~~~

No output from <code>diff</code> means byte identity.

## Safe summary

A short accurate summary is:

> The paper gives a machine-checked information bound for recovery at a
> one-way dual-write delivery boundary. Source-side state alone cannot
> distinguish whether an independent sink accepted an operation during a
> crash window. Under stated identity and completeness premises, reading
> the sink's durable acceptance record supplies the missing information;
> arrival and claim fences keep that read current, while deduplication and
> source-history retention bound how long the guarantee remains available.

Do not shorten this to "exactly once is impossible" or "fencing guarantees
exactly once."
