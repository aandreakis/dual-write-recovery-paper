# Theorem index

## How to read this map

This is a navigation map, not a second specification. The one-line
result titles are handles, not statements: the Isabelle theorem
statements and definitions, with the premises they carry, are
authoritative. The scope reminders at the end of this file are part
of the map — read a title together with its reminder before citing
the result.

## Numbering

The paper — *Machine-Checked Dual-Write Recovery from a Committed
Log* — numbers its principal results T1–T12 in narrative order, and
every table and note below uses that numbering. The development's
source history and some theory comments use an older historical
numbering; this map converts between the two.

| Paper | Title in paper | Historical row |
|---|---|---|
| T1 | Observation Bound | T1 |
| T2 | Control-Plane Bound | T2 |
| T3 | Checkpoint Dilemma | Same-protocol checkpoint dilemma |
| T4 | Sink-Reading Escape | T3 |
| T5 | Wire Bound | T4 |
| T6 | Arrival Fence (Cor. 6.1 rescue conversion; Cor. 6.2 residual-wire stability) | T5 + corollary rows |
| T7 | Second-Recoverer Bound | T6 |
| T8 | Completed-Claim Exactness (Lem. 7.1 claim-fence safety; Cor. 7.1 journal-grade endpoint equivalence) | Claim-fence safety and exactness |
| T9 | Deduplicated-View Coverage Identity | T7 |
| T10 | Truncation Dilemma | T8 |
| T11 | Faithful-Image Equivalence | T9 |
| T12 | Shared-Core Agreement | T10 |

| Paper result | Principal Isabelle result(s) | Source |
|---|---|---|
| T1 Observation Bound | `observation_measured_dilemma`; two-horn practitioner form `observation_duplicate_or_lost` (kernel `pair_agreeing_observation_duplicate_or_lost`) | `isabelle/dual_write_effect/Dual_Write_Effect_Observation_Bound.thy` |
| T2 Control-Plane Bound | `recovery_information_dilemma_pair`, `epoch_measured_dilemma_pair` (fixed-pair principals; the reordered `recovery_information_dilemma` / `epoch_measured_dilemma` are their corollaries); two-horn practitioner forms `recovery_duplicate_or_lost_pair`, `epoch_duplicate_or_lost_pair` (kernel `pair_batch_agreement_duplicate_or_lost`) | `isabelle/dual_write_effect/Dual_Write_Effect_Dilemma.thy` |
| T3 Checkpoint Dilemma (same-protocol) | `checkpoint_dilemma_pair`, `same_protocol_batch_agreement_dilemma`; two-horn practitioner form `checkpoint_duplicate_or_lost_pair` (kernel `window_pair_duplicate_or_lost`) | `isabelle/dual_write_effect/Dual_Write_Effect_Cursor.thy` |
| T4 Sink-Reading Escape | `sink_reading_escape_general` | `isabelle/dual_write_effect/Dual_Write_Effect_Dilemma.thy` |
| T5 Wire Bound | `no_channel_blind_policy_escapes` | `isabelle/dual_write_effect/Dual_Write_Effect_Channel_Blind.thy` |
| T6 Arrival Fence | `fenced_redrive_exactly_once`; packaged reachable-state citation form `fenced_redrive_reachable_package` (existence + heal + exactness at `f` + all-stale residual wire + arrive/lose-only continuation preservation under one premise list) | `isabelle/dual_write_effect/Dual_Write_Effect_Fencing.thy` |
| Cor. 6.1 Rescue Conversion | `fence_rescue_conversion` | `isabelle/dual_write_effect/Dual_Write_Effect_Fencing.thy` |
| Cor. 6.2 Residual-Wire Stability | `fenced_redrive_all_stale`, `fenced_result_wire_preserves_eo` | `isabelle/dual_write_effect/Dual_Write_Effect_Fencing.thy` |
| T7 Second-Recoverer Bound | `u_concurrent_recovery_dilemma`; two-horn practitioner form `u_concurrent_recovery_duplicate_or_lost` (the TT cell's proved duplicate exported); phase-ordered addendum: grammar `u_pair_steps_phased` / `u_oneshot_pair_extension_phased` with simulation `phased_extension_imp_extension` (per-run transport `phased_defeat_is_loose_defeat`), ordered silent-death defeat `u_ordered_silent_death_defeat`, and the ordering boundary `u_ordered_pair_exact_completion` / `u_ordered_dilemma_fails_at_rf_W` | `isabelle/dual_write_unified/DWU_Concurrent_Recovery.thy` |
| T8 Completed-Claim Exactness (incl. Lem. 7.1 claim-fence safety, Cor. 7.1 journal-grade endpoint equivalence) | `u_fenced_multiwriter_discipline_safe`, `u_exactly_once_at_completed_claim`; journal-grade forms `permanent_source_journal_coincidence`, `u_exactly_once_at_completed_claim_journal`, `retention_sound_bridge`, `disciplined_retention_sound_journal_grade`, endpoint exchange-rate equivalence `journal_grade_iff_retained_grade_and_prefix_covered` (banked controls `journal_grade_divergence_control`, `cw4_completed_claim_journal_grade`) | `isabelle/dual_write_unified/DWU_Fenced_Discipline.thy`; `isabelle/dual_write_unified/DWU_Journal_Grade.thy` |
| T9 Deduplicated-View Coverage Identity | `dedup_sink_exactly_once_iff_at_least_once` (definitional over the absorbing `remdups` view — the biconditional reduces to coverage); the substantive per-instance form is `dedup_sink_instance_exact_iff` (ascending-coordinate corollary) | `isabelle/dual_write_effect/Dual_Write_Effect_Exactly_Once.thy` |
| T10 Truncation Dilemma | `u_truncation_recovery_dilemma`; two-horn practitioner form `u_truncation_fabricate_or_abandon` (the FABRICATE branch's proved `u_premature` exported) | `isabelle/dual_write_unified/DWU_Truncation.thy` |
| T11 Faithful-Image Equivalence | `safe_iff_running_image_faithful` | `isabelle/dual_write_core/Dual_Write_Converse.thy` |
| T12 Shared-Core Agreement | `Π_section`, `u_landed_embedding`, `u_solo_projection`, `u_hazards_once`, `u_sink_delta_commutes` | `isabelle/dual_write_unified/DWU_Machine.thy`; `isabelle/dual_write_unified/DWU_Conservativity.thy` |
| Acceptance interface | locale `transit_iface` and theorem `a_safety` | `isabelle/dual_write_transit/DWT_Interface.thy` |
| Schedule validator | exported validator and correctness results | `isabelle/dual_write_schedule_validator/Dual_Write_Schedule_Validator.thy` |
| DBLog worked-instance bridge | `virtual_cut_certifies_dblog` | `isabelle/dual_write_dblog_instance/DBLog_Instance.thy` |

## Scope reminders

- T1, T2, T5, T7, and T10 use constructed reachable machines or
  schedules. Preserve their quantifier scope.
- T5, the Wire Bound, quantifies over channel-blind batch selectors
  inserted into the one fixed unfenced re-drive relation — which heals
  the store, lands the selected batch in the sent ledger and
  synchronously in the accepted record, and never touches the wire or
  the fence — at the designed reachable pair. It is not a bound on
  every recovery algorithm that cannot read the wire: the policy
  chooses the batch, the relation fixes everything else.
- T7's pair grammar records final armed/fired/healer SETS only, so its
  extension predicate also admits schedules where a member fires without
  its own heal; the phase-ordered addendum carries per-member
  arm-heal-fire order in the statement. Fully ordered silent-death
  schedules exist for every chooser and lose whenever a member's
  crash-time batch misses the owed payload
  (`u_ordered_silent_death_defeat`), and every ordered defeat transports
  to the landed loose shape (`phased_extension_imp_extension`). But the
  T7 conclusion with the ordered extension substituted for the loose one
  is FALSE at the landed witness (`u_ordered_dilemma_fails_at_rf_W`):
  the machine admits one store reconcile per crash, so an ordered pair
  degenerates to at most one completed recovery, and `u_exact_chooser`
  then completes exactly-once (`u_ordered_pair_exact_completion`). T7's
  TT duplicate cell needs the sibling's heal-free (zombie) fire — the
  loose final-set bookkeeping is load-bearing content, not an oversight.
- The two-horn (`*_duplicate_or_lost*`) forms are facts of the designed
  pairs, not new for-all laws: at those pairs the premature case of the
  three-horn kernels also leaves the second member's committed effect
  uncovered, so the defeat disjunct sharpens to duplicate-or-lost. The
  three-horn statements of record are unchanged. The unified-tier
  two-horn forms carry the same discipline at their designed witnesses:
  `u_concurrent_recovery_duplicate_or_lost` (T7) exports the TT cell's
  proved duplicate and `u_truncation_fabricate_or_abandon` (T10) the
  FABRICATE branch's proved `u_premature` in place of the
  `u_effect_unsafe` disjunct — facts of the designed witnesses; the
  statements of record (`u_concurrent_recovery_dilemma`,
  `u_truncation_recovery_dilemma`) are unchanged.
- T6's immediate exactness at `f` rides the fenced re-drive being one
  atomic act whose delta lands synchronously in the accepted record —
  a recovery's own re-sends never traverse the fenced wire. The raised
  fence supplies the separate stale-arrival stability (Cor. 6.2), and
  the exactness verdict is qualified to the recovery's own frontier
  `f`.
- `fenced_redrive_reachable_package` re-packages T6 plus the
  residual-wire corollaries under a reachability premise; its
  continuation conjunct is scoped to arrive/lose-only traces exactly as
  `fenced_result_wire_preserves_eo` is (unscoped preservation is false —
  a post-resume application re-publish breaks the safety conjunct).
- T1's and T2's reconcile index `m` is a rule/action parameter
  abstracting the persisted cursor used by that recovery action; it is
  not a field of `dwe_state`. Their designed pair uses different earlier
  `m` choices, and the policy defeated on the resulting pair need not
  have generated those prior histories — an information bound. The
  Checkpoint Dilemma (T3) closes `m` with a durable cursor:
  its pair is generated by one deterministic protocol with crash timing
  as the only nondeterminism, is equal on the durable-local view (the
  cursor included) and core-divergent (`pair_cores_differ` discloses
  it), and defeats the durable-local-measured class; downstream-content,
  pending-window, and emission-ledger reads sit on the escape side of
  its dichotomy.
- T4, T6, the completed-claim exactness result (T8), T9’s per-instance
  form, and T11 are conditional on their stated premises; T11's
  crash-closure premise binds only trace-reachable states.
- T11's safe-side boundary is effectiveness, not scope size: the
  partition obstruction rules out crash-closed, refining
  implementations containing an EFFECTIVE in-scope separable
  non-atomic completion (the completion classes carry
  `effective_source_effect`); it does not rule out safe nonempty-scope
  executions whose monitored writes are value-preserving or
  authority-neutral. No richer safe inhabitant is currently exhibited.
- The claim-fence exactness verdict (T8) is retained-suffix-relative:
  `u_exactly_once_at` grades coverage against the source history above
  `dwu_floor`, and the guard-free `URetain` lets a disciplined run drop
  an undelivered committed obligation without disturbing it
  (`journal_grade_divergence_control` banks the witness run). The
  journal-graded closures live in `DWU_Journal_Grade.thy`:
  `permanent_source_journal_coincidence` on the permanent-source
  fragment, and `retention_sound_bridge` /
  `disciplined_retention_sound_journal_grade` under the floor-prefix
  coverage premise `retained_prefix_covered` (delivered trace-level by
  `u_retention_sound_steps`).
- The DBLog worked-instance bridge certifies interface inhabitation
  (one certified wellformed run inhabits the virtual-cut-state
  interface); it does not re-prove the cited development's watermark
  algorithm.
- The paper's “generation” register `γ` corresponds to the effect
  artifact's `dwe_epoch` / emission epoch.
- T9, the Deduplicated-View Coverage Identity (historically labeled T7,
  relabeled at the terminal review round), is payload-counted over an
  absorbing permanent-memory deduplicated
  view; it does not verify a consumer transaction. Its displayed
  biconditional is definitional at the view layer (duplicate-freedom
  holds by construction, so the equivalence reduces to coverage); the
  substantive per-instance exactness is the ascending-coordinate
  corollary.
- T10 grades loss against the journal specification field while policies
  see only the retained view.
- T12 proves selected relations under alignment premises; it does not
  merge the wire and concurrency machines.
- The transit interface transports safety, not an unconditional
  exactly-once result. Its fire instance is pulled back from the unified
  concurrency machine; its wire instance is the sibling `DWT_Wire`
  grammar, not the channel machine of T5–T6.

## Session closure

`Dual_Write_Transit` builds the Layer-0 → Core → Effect → Unified →
Transit chain. `Dual_Write_Schedule_Validator` adds the certified
validator. `Dual_Write_DBLog_Instance` builds the worked DBLog bridge
through `DBLog_Virtual_Cuts`.
