(*  Title:       Dual_Write_Effect_Presence_Bound.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE ESCAPE'S INFORMATION BOUND, UPPER SIDE (discovery lens C,
    candidate C1) --- an additive post-freeze slice under the freeze's own
    protocol: no landed statement, proof, definition, name, import, or
    session-DAG change to the frozen corpus.

    The landed record pins the sink-reading escape from BELOW: the landed
    B2 (sink_reading_escape_not_store_measured) proves the escape policy
    does not factor through the durable store, and the Dichotomy lane's
    sink_delta_not_ledger_blind (cited as prose --- that theory is not in
    this import cone) shows it genuinely reads the ledger.  A systems
    referee's natural next question --- real sinks are RETAINED and
    COMPACTED; does the escape need the unbounded raw ledger? --- is
    answered here from ABOVE, premise-free, at the function level: the
    landed sink_delta reads the emission ledger ONLY through the PRESENCE
    SET of delivered payloads, e_payload ` set (dwe_emitted t).  It is
    therefore invariant under every presence-preserving ledger rewrite
    (reordering, duplicate collapse, stamp loss, epoch loss, and
    keep-latest-per-payload log compaction, the latter proved against a
    concrete compaction function), it factors through
    (core, delivered-payload presence) as a machine-checked class
    membership (presence_measured), and only the presence bits of the
    current scoped, frontier-bounded replay ever matter --- the needed
    view is finite and recovery-window-local.

    UPPER BOUND ONLY (binding fence).  Every statement below is about THE
    landed policy sink_delta.  No minimality claim, no characterization,
    no "the escape needs exactly X": the honest two-sided form is that
    the landed escape provably reads MORE than the store (the landed B2,
    re-exported below in escape_information_bound) and needs NO MORE
    than the recovery window's delivered-payload presence (new),
    premise-free.  Whether some other correct policy could read even
    less is deliberately not asked.

    CLASS PATTERN.  presence_measured mirrors the landed store_measured
    factoring shape (and the Dichotomy lane's ledger_blind /
    store_epoch_measured pattern, cited as prose) one observation rung
    up: the measuring function sees the crashed core AND the delivered-
    payload presence set.  This does NOT re-open the shelved parametric
    effect-algebra: the machine's observable stays the landed raw
    emission ledger; the presence set enters only as the argument of the
    factoring function, exactly as the core does in store_measured.

    PROVENANCE: discovery wave, lens C, candidate C1
    (paper/dual_write/theory_review/discovery/LENS_C_BOUNDARY.md); probe
    C_Probe.thy GREEN x2 in two fresh isolated homes, all six pinned
    statements ported verbatim, plus the spec-mandated containment rung
    (store_measured ==> presence_measured) and strictness control (a
    stamp-reading policy that is not presence-measured, at a designed
    state pair of the pinned type).

    In-source ML oracle gates are STRIPPED at landing: oracle-freedom is
    certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Presence_Bound
  imports Dual_Write_Effect_Dilemma
begin

section \<open>Scope: the upper side of the escape's information requirement\<close>

text \<open>
  The landed escape policy @{const sink_delta} filters the scoped,
  frontier-bounded replay of the committed source prefix against the
  payloads already present in the emission ledger
  (@{thm [source] sink_delta_def}).  The ledger enters that computation
  through ONE projection: @{term "e_payload ` set (dwe_emitted t)"}, the
  set of delivered payloads --- no stamp, no epoch tag, no multiplicity,
  no order.  This theory makes that observation a theorem set.

  Practitioner reading (softening no formal scope): the presence set is
  the view an idempotence-keyed consumer table or a keep-latest-per-
  payload compacted log already retains.  So the sink-reading escape
  does not require the unbounded raw ledger: every statement below is a
  function equation saying the landed policy cannot see the difference
  between the raw ledger and its compacted or re-ordered or stamp-stripped
  rewriting, and --- the last theorem --- cannot see presence bits
  outside the current recovery window's replay.

  Every statement is at ANY state of the pinned type
  @{typ "(nat, nat) dwe_state"}, deliberately premise-free (not even the
  named ascending premise): pure filter algebra over the landed
  definitions, the same any-state posture as the landed premise-free B1
  general form @{thm [source] sink_reading_escape_general}.  The
  machine's observable stays the landed raw emission ledger; nothing
  here re-opens the shelved parametric effect-algebra, and the landed
  hazard taxonomy is not touched.
\<close>

section \<open>The invariance law\<close>

text \<open>
  Equal core and equal delivered-payload presence force equal deltas ---
  the whole theory in one equation.  The ledgers themselves may differ
  arbitrarily: only their payload presence sets matter.
\<close>

lemma sink_delta_payload_presence_invariant:
  assumes core: "dwe_core t' = dwe_core t"
      and pres: "e_payload ` set (dwe_emitted t')
                   = e_payload ` set (dwe_emitted t)"
  shows "sink_delta f t' = sink_delta f t"
  by (simp add: sink_delta_def core pres)

section \<open>The factoring class: presence-measured policies\<close>

text \<open>
  The factoring form, mirroring the landed @{const store_measured}
  (@{thm [source] store_measured_def}) one observation rung up: the
  measuring function sees the crashed core and the delivered-payload
  presence set.  Pinned at the witness instantiation
  @{typ "(nat, nat) dwe_state"}, like the landed policy classes; the
  Dichotomy lane's @{text ledger_blind} / @{text store_epoch_measured}
  bridge is the same pattern at the (core, epoch) rung (cited as prose
  --- that theory is not in this import cone).
\<close>

definition presence_measured :: "redrive_policy \<Rightarrow> bool" where
  "presence_measured P \<longleftrightarrow>
     (\<exists>g. \<forall>t. P t = g (dwe_core t) (e_payload ` set (dwe_emitted t)))"

theorem sink_delta_presence_measured:
  "presence_measured (sink_delta f)"
  unfolding presence_measured_def
  by (intro exI[where x =
        "\<lambda>c S. filter (\<lambda>p. p \<notin> S)
                 (replay_down_hist (exec_src_hist c) (exec_scope c) f)"])
     (simp add: sink_delta_def)

text \<open>
  THE CONTAINMENT RUNG: every store-measured policy is presence-measured
  --- the measuring function ignores the presence argument.  Together
  with @{thm [source] sink_reading_escape_not_store_measured} (via
  @{text escape_information_bound} below) the containment is strict:
  the landed escape inhabits the gap.
\<close>

lemma store_measured_imp_presence_measured:
  assumes "store_measured P"
  shows "presence_measured P"
proof -
  from assms obtain g where g: "\<forall>t. P t = g (dwe_core t)"
    unfolding store_measured_def by blast
  show ?thesis
    unfolding presence_measured_def
    by (intro exI[where x = "\<lambda>c S. g c"]) (simp add: g)
qed

text \<open>
  STRICTNESS / BITING CONTROL for the class definition: a policy that
  reads fire-time STAMPS is not presence-measured.  The state pair is
  the landed decider lane's core-invisible premature posture, re-declared
  locally because that lane is not in this import cone (the house
  precedent): the landed @{const W3} against its stamp-0 twin --- the
  landed @{text tb2_w} of the decider theory, byte for byte --- equal
  cores, equal epochs, equal delivered-payload presence
  @{term "{(ec1, e1)}"}, ledgers differing ONLY in the stamp.  A pair of
  the pinned type in the house control posture (reachability neither
  claimed nor needed: the class quantifies over all states; the decider
  lane realizes the same stamps-only axis at reachable states).

  The control policy re-emits unless every retained emission is stamped
  after some commit --- a rule keying on fire-time justification data,
  which retention and compaction do NOT preserve.  It computes
  differently across the pair, so no (core, presence) function equals
  it: @{text presence_measured} is a genuine restriction, not a vacuously
  inhabited class.
\<close>

definition sp0_w :: "(nat, nat) dwe_state" where
  "sp0_w = mkT (mkC [(ec1, e1)] [(ec1, e1)] [(ec1, e1)] {} Running)
               [(0, 0, ec1, e1)] 0"

definition stamp_gate_policy :: redrive_policy where
  "stamp_gate_policy t =
     (if \<forall>x \<in> set (dwe_emitted t). 0 < e_stamp x
      then [] else [(ec1, e1)])"

lemma stamp_gate_not_presence_measured:
  "\<not> presence_measured stamp_gate_policy"
proof
  assume "presence_measured stamp_gate_policy"
  then obtain g where g: "\<forall>t. stamp_gate_policy t
      = g (dwe_core t) (e_payload ` set (dwe_emitted t))"
    unfolding presence_measured_def by blast
  have cores: "dwe_core sp0_w = dwe_core W3"
    by (simp add: sp0_w_def W3_def mkT_def)
  have pres: "e_payload ` set (dwe_emitted sp0_w)
      = e_payload ` set (dwe_emitted W3)"
    by (simp add: sp0_w_def W3_def mkT_def)
  have "stamp_gate_policy sp0_w = stamp_gate_policy W3"
    using g cores pres by metis
  moreover have "stamp_gate_policy sp0_w = [(ec1, e1)]"
    by (simp add: stamp_gate_policy_def sp0_w_def mkT_def)
  moreover have "stamp_gate_policy W3 = []"
    by (simp add: stamp_gate_policy_def W3_def mkT_def)
  ultimately show False by simp
qed

section \<open>Presence-preserving ledger rewrites are invisible\<close>

text \<open>
  The general rewrite form: replace the ledger by ANY list with the same
  payload presence --- reordering, duplicate collapse, stamp loss, epoch
  loss, retention-window re-encoding --- and the computed delta is
  unchanged.  Log compaction is the next section's concrete instance.
\<close>

lemma sink_delta_compaction_invariant:
  assumes "e_payload ` set L' = e_payload ` set (dwe_emitted t)"
  shows "sink_delta f (t\<lparr>dwe_emitted := L'\<rparr>) = sink_delta f t"
  by (rule sink_delta_payload_presence_invariant) (simp_all add: assms)

section \<open>Log compaction (keep-latest-per-payload), concretely\<close>

text \<open>
  The log-compaction shape as a function: keep the LATEST entry per
  payload (the recursion keeps an entry exactly when its payload does
  not recur later in the list).  This is the keep-latest-per-key
  compaction discipline of production log stores, at the payload
  granularity the escape reads.  The compacted ledger has payload-
  distinct entries --- it IS a consumer table --- with the same presence
  set, so the landed escape computes the identical batch on it.
\<close>

fun payload_compact :: "('k, 'v) emission list \<Rightarrow> ('k, 'v) emission list" where
  "payload_compact [] = []"
| "payload_compact (x # xs) =
     (if e_payload x \<in> e_payload ` set xs
      then payload_compact xs
      else x # payload_compact xs)"

lemma payload_compact_presence:
  "e_payload ` set (payload_compact L) = e_payload ` set L"
  by (induction L) (force simp: e_payload_def)+

lemma payload_compact_distinct:
  "distinct (map e_payload (payload_compact L))"
  by (induction L) (auto simp: payload_compact_presence)

theorem sink_delta_log_compaction:
  "sink_delta f (t\<lparr>dwe_emitted := payload_compact (dwe_emitted t)\<rparr>)
     = sink_delta f t"
  by (rule sink_delta_compaction_invariant[OF payload_compact_presence])

section \<open>The two-sided information bound (with the landed B2)\<close>

text \<open>
  The juxtaposition, in one statement at the landed B2's own frontier
  instance: the landed escape policy provably does NOT factor through
  the durable store (the landed lower side, @{thm [source]
  sink_reading_escape_not_store_measured}) and DOES factor through
  (core, delivered-payload presence) (the new upper side).  With the
  containment rung above, the two conjuncts also witness that
  store-measured sits strictly inside presence-measured.  Read against
  the landed headline law: exactly-once effect recovery in the dilemma's
  sense requires more than the store --- and the landed escape needs no
  more than the recovery window's delivered-payload presence.  An upper
  bound about THE landed policy; minimality is deliberately not claimed.
\<close>

theorem escape_information_bound:
  "\<not> store_measured (sink_delta ec2) \<and> presence_measured (sink_delta ec2)"
  using sink_reading_escape_not_store_measured sink_delta_presence_measured
  by simp

section \<open>Only the recovery window's presence bits matter\<close>

text \<open>
  Retention may forget any payload outside the current scoped,
  frontier-bounded replay: the membership test is only ever applied to
  replay members, so intersecting the presence set with the replay
  changes nothing.  The view the escape needs is FINITE and
  recovery-window-local --- the presence bits of the payloads the
  current recovery could re-drive, nothing else.  (A bounded-memory
  IMPOSSIBILITY converse --- what a recency-limited sink reader provably
  cannot do --- is deliberately NOT claimed or built here; it is
  recorded future work in the discovery record.)
\<close>

lemma sink_delta_needs_only_scoped_presence:
  "sink_delta f t =
     filter (\<lambda>p. p \<notin> (e_payload ` set (dwe_emitted t))
                       \<inter> set (replay_down_hist
                                (exec_src_hist (dwe_core t))
                                (exec_scope (dwe_core t)) f))
       (replay_down_hist (exec_src_hist (dwe_core t))
          (exec_scope (dwe_core t)) f)"
  unfolding sink_delta_def
  by (rule filter_cong) auto


end
