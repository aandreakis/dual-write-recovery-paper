(*  Title:       Dual_Write_Effect_Sink_Delta_Idempotence.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Retry-idempotence of the sink-reading delta across a partial append
    (theory-backlog item C) --- an additive post-freeze slice under the
    freeze's own protocol: no landed statement, proof, definition, name,
    import, or session-DAG change to the frozen corpus.

    THE PARTIAL STATE IS A MODELED INTERMEDIATE.  The landed re-drive
    reconcile is an atomic big-step rule (disclosed model boundary: store
    heal and ledger append happen together), so a crash DURING a re-drive
    is inexpressible on the machine --- and this theory does NOT change
    that: it adds no rule, no machine, and no claim that mid-redrive
    states are reachable.  What it proves is FUNCTION-LEVEL algebra about
    the landed sink_delta at states of the partial-append SHAPE: the
    ledger extended by emissions whose payloads form a prefix of the
    sink-computed batch --- exactly the ledger footprint an interrupted
    re-drive would leave if only a prefix of the batch had landed.  Under
    the named strictly-ascending-source premise, re-computing sink_delta
    at such a state yields exactly the remainder of the batch
    (sink_delta_partial_append_remainder); once the whole batch's
    payloads have landed, it yields nothing
    (sink_delta_full_append_empty); and after the landed rule's own
    completed sink-delta redrive the recomputed delta is empty with no
    premise at all (sink_delta_after_policy_redrive_empty).  This is
    interim crash-during-redrive evidence for the POSITIVE side: it
    SOFTENS the atomic-reconcile boundary's bite for the sink-reading
    escape without removing the boundary.

    WHAT THIS THEORY DOES NOT DISCHARGE.  The priced small-step reconcile
    contingency (the boundary disclosure's +1-2 week item) remains the
    machine-level answer to interleaved re-drives; nothing here subsumes
    it, makes it unnecessary, or claims machine-level expressibility for
    intermediate states.  This theory is the function-level answer only.

    VOCABULARY FENCES (binding, from the freeze documents): "idempotent
    completion" and "retry-idempotence" below are prose descriptions of
    the FUNCTION equations at modeled-intermediate states, never delivery
    or liveness claims; no unqualified exactly-once claim is made or
    implied.  The strictly-ascending-source premise (per-event unique
    coordinates, the CDC practitioner reading) is consumed load-bearing
    for distinctness of the computed batch, exactly as in the landed B1
    escape, and the control theorem at the end witnesses it biting; the
    impossibility half of the landed corpus consumes NO ordering premise
    --- this theory sits entirely on the positive side.

    PROVENANCE: theory-backlog item C
    (paper/dual_write/theory_backlog/BACKLOG_EXPLORATION.md section 1;
    "interim crash-during-redrive evidence", boundary row 1 of
    MODEL_BOUNDARY_CONTRACTS.md).  Everything below is about the landed
    sink_delta of the cyclic-branch Dilemma theory; the import is that
    single sibling, and no machine extension was needed (confirmed:
    every statement is filter/take/drop algebra over the landed
    definitions).

    In-source ML oracle gates are STRIPPED at landing: oracle-freedom is
    certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Sink_Delta_Idempotence
  imports Dual_Write_Effect_Dilemma
begin

section \<open>Scope: function-level algebra at modeled-intermediate states\<close>

text \<open>
  The landed escape policy @{const sink_delta} filters the scoped,
  frontier-bounded replay of the committed source prefix against the
  payloads already in the emission ledger.  A re-drive never changes the
  committed prefix or the scope --- @{thm [source]
  policy_redrive_src_same} / @{thm [source] policy_redrive_scope_same}
  --- only the ledger grows.  So the state an INTERRUPTED re-drive would
  leave behind (only a prefix of the computed batch appended before a
  crash) differs from the crashed pre-state only by a ledger extension
  whose payloads are that prefix, and re-computing @{const sink_delta}
  there is pure filter algebra over the landed definitions.

  The statements below are at ANY state of the pinned type
  @{typ "(nat, nat) dwe_state"} --- deliberately NO reachability premise,
  the same any-state posture as the landed premise-free B1 general form
  @{thm [source] sink_reading_escape_general}: the equations are
  function-level facts, and a crash during a re-drive is inexpressible on
  the machine anyway (the atomic big-step reconcile boundary, which this
  theory softens for the escape but does not remove; the priced
  small-step reconcile remains the machine-level contingency).
\<close>

text \<open>
  Ledger extension refines the delta by payload-blocking the new
  entries: premise-free filter algebra, the shared engine of everything
  below.
\<close>

lemma sink_delta_ledger_append:
  "sink_delta f (t\<lparr>dwe_emitted := dwe_emitted t @ X\<rparr>)
     = filter (\<lambda>p. p \<notin> e_payload ` set X) (sink_delta f t)"
  by (simp add: sink_delta_def image_Un de_Morgan_disj)

text \<open>
  Distinctness of the computed batch itself, from the named ascending
  premise --- the landed B1 distinctness pipeline (@{thm [source]
  strictly_ascending_distinct}, then two filters), packaged at the
  @{const sink_delta} level for reuse.
\<close>

lemma ascending_sink_delta_distinct:
  assumes "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "distinct (sink_delta f t)"
  using strictly_ascending_distinct[OF assms]
  unfolding sink_delta_def replay_down_hist_def by simp


section \<open>The partial-append remainder law\<close>

text \<open>
  THE MAIN THEOREM.  At any state of the pinned type with a strictly
  ascending committed source: extend the ledger by ANY emission list
  whose payload projection is the length-@{term n} prefix of the
  sink-computed batch, and the recomputed delta is exactly the
  @{term "drop n"} remainder.  The statement is deliberately STAMP- and
  EPOCH-AGNOSTIC: @{const sink_delta} reads payloads only, so one
  equation covers every stamping scheme at once (the landed rule's own
  stamping is the corollary below).  The partial-append state is a
  MODELED INTERMEDIATE --- the shape an interrupted re-drive would
  leave, not a state any machine rule produces mid-flight; no
  reachability is claimed, and none is assumed.

  Where the ascending premise bites: it makes the computed batch
  internally DISTINCT (the landed B1 pipeline), so the surviving suffix
  is not payload-blocked by the fired prefix.  The control theorem at
  the end of this theory exhibits the equation FAILING without it.
\<close>

theorem sink_delta_partial_append_remainder:
  fixes t :: "(nat, nat) dwe_state"
    and X :: "(nat, nat) emission list"
  assumes asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
      and pay: "map e_payload X = take n (sink_delta f t)"
  shows "sink_delta f (t\<lparr>dwe_emitted := dwe_emitted t @ X\<rparr>)
           = drop n (sink_delta f t)"
proof -
  define B where "B = sink_delta f t"
  have dist_B: "distinct B"
    unfolding B_def by (rule ascending_sink_delta_distinct[OF asc])
  have payX: "e_payload ` set X = set (take n B)"
    unfolding B_def pay[symmetric] by simp
  have take_part: "filter (\<lambda>p. p \<notin> set (take n B)) (take n B) = []"
    by (simp add: filter_empty_conv)
  have disj: "set (take n B) \<inter> set (drop n B) = {}"
    by (rule set_take_disj_set_drop_if_distinct[OF dist_B order.refl])
  have drop_part: "filter (\<lambda>p. p \<notin> set (take n B)) (drop n B) = drop n B"
    using disj by (auto simp: filter_id_conv)
  have "sink_delta f (t\<lparr>dwe_emitted := dwe_emitted t @ X\<rparr>)
      = filter (\<lambda>p. p \<notin> e_payload ` set X) B"
    by (simp add: sink_delta_ledger_append B_def)
  also have "\<dots> = filter (\<lambda>p. p \<notin> set (take n B)) B"
    by (simp only: payX)
  also have "\<dots> = filter (\<lambda>p. p \<notin> set (take n B)) (take n B @ drop n B)"
    by simp
  also have "\<dots> = filter (\<lambda>p. p \<notin> set (take n B)) (take n B)
                @ filter (\<lambda>p. p \<notin> set (take n B)) (drop n B)"
    by (simp only: filter_append)
  also have "\<dots> = drop n B"
    by (simp only: take_part drop_part append_Nil)
  also have "\<dots> = drop n (sink_delta f t)"
    by (simp add: B_def)
  finally show ?thesis .
qed


section \<open>The landed rule's own stamping, and completion\<close>

text \<open>
  THE CITABLE PRACTITIONER FORM: the prefix stamped exactly as the
  landed re-drive rule stamps its batch --- committed-prefix length and
  current epoch, the @{thm [source] policy_redrive_emitted} shape ---
  i.e. the precise ledger footprint a crash midway through a sink-delta
  re-drive would leave under the landed stamping.  Re-computing the
  delta at the partial state emits exactly the remainder: the escape's
  recomputation COMPLETES an interrupted delivery instead of restarting
  it.  Same modeled-intermediate status as the main theorem.
\<close>

corollary sink_delta_partial_redrive_remainder:
  fixes t :: "(nat, nat) dwe_state"
  assumes asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "sink_delta f
           (t\<lparr>dwe_emitted := dwe_emitted t
                @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                                 dwe_epoch t, c, e))
                    (take n (sink_delta f t))\<rparr>)
       = drop n (sink_delta f t)"
proof -
  have "map e_payload
          (map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                          dwe_epoch t, c, e))
             (take n (sink_delta f t)))
      = take n (sink_delta f t)"
    by simp
  then show ?thesis
    by (rule sink_delta_partial_append_remainder[OF asc])
qed

text \<open>Completion, prefix form: once the whole batch's payloads have
  landed (@{term "n \<ge> length (sink_delta f t)"}, so the appended prefix
  IS the batch), the recomputed delta is empty --- a retry after full
  delivery re-emits nothing.\<close>

corollary sink_delta_full_append_empty:
  fixes t :: "(nat, nat) dwe_state"
    and X :: "(nat, nat) emission list"
  assumes asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
      and pay: "map e_payload X = take n (sink_delta f t)"
      and len: "length (sink_delta f t) \<le> n"
  shows "sink_delta f (t\<lparr>dwe_emitted := dwe_emitted t @ X\<rparr>) = []"
  using sink_delta_partial_append_remainder[OF asc pay] len by simp

text \<open>
  Completion, REAL-TRANSITION form --- the one statement here whose
  post-state is a machine state, produced by the landed rule itself
  (@{const policy_redrive} with the sink-delta policy), so nothing about
  it is hypothetical and no boundary is softened: after a completed
  sink-delta re-drive, re-computing the delta at the post-state yields
  nothing.  PREMISE-FREE beyond the transition --- not even the
  ascending premise is consumed: every replay payload is either already
  in the old ledger (then the appended batch never contained it) or in
  the batch the redrive just appended, so the recomputation is blocked
  pointwise by construction, duplicates and all.
\<close>

corollary sink_delta_after_policy_redrive_empty:
  assumes pr: "policy_redrive (sink_delta f) t f t'"
  shows "sink_delta f t' = []"
proof -
  have src': "exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t)"
    by (rule policy_redrive_src_same[OF pr])
  have scope': "exec_scope (dwe_core t') = exec_scope (dwe_core t)"
    by (rule policy_redrive_scope_same[OF pr])
  have em': "dwe_emitted t'
      = dwe_emitted t
        @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                         dwe_epoch t, c, e))
            (sink_delta f t)"
    by (rule policy_redrive_emitted[OF pr])
  have cover: "\<And>p. p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                               (exec_scope (dwe_core t)) f) \<Longrightarrow>
                  p \<in> e_payload ` set (dwe_emitted t')"
    by (simp add: em' sink_delta_def image_Un image_image)
  show ?thesis
    using cover by (auto simp: sink_delta_def src' scope' filter_empty_conv)
qed


section \<open>The stamped partial state is still effect-safe\<close>

text \<open>
  The modeled intermediate is not merely delta-recomputable --- it is
  still EFFECT-SAFE: from an effect-safe pre-state, appending the
  stamped prefix preserves both hazard-freedom verdicts.  This is the
  landed B1 safety pipeline applied to a PREFIX of the batch: prefix
  entries are justified at their fire-time stamp (@{thm [source]
  redrive_emissions_justified} --- the stamp here is NOT agnostic, the
  committed-prefix-length stamp is exactly what makes fire-time
  justification hold), internally distinct (ascending premise, via a
  prefix of a distinct batch), and ledger-fresh (the batch was computed
  against the ledger).  The epoch stays agnostic: no safety predicate
  reads it.  Premises: exactly effect-safety of the pre-state and the
  ascending premise --- no crashed-status or frontier premise, because
  no machine transition is involved; same modeled-intermediate status
  as the main theorem.
\<close>

theorem sink_delta_partial_state_effect_safe:
  fixes t :: "(nat, nat) dwe_state"
  assumes safe: "\<not> effect_unsafe t"
      and asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "\<not> effect_unsafe
           (t\<lparr>dwe_emitted := dwe_emitted t
                @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                                 ep, c, e))
                    (take n (sink_delta f t))\<rparr>)"
proof -
  let ?S = "exec_src_hist (dwe_core t)"
  let ?B = "sink_delta f t"
  let ?X = "map (\<lambda>(c, e). (length ?S, ep, c, e)) (take n ?B)"
  let ?t' = "t\<lparr>dwe_emitted := dwe_emitted t @ ?X\<rparr>"

  have old_just: "\<forall>x \<in> set (dwe_emitted t). justified_at ?S x"
    using safe by (simp add: effect_unsafe_def premature_def)
  have old_dist: "distinct (map e_payload (dwe_emitted t))"
    using safe by (simp add: effect_unsafe_def duplicate_def)
  have dist_B: "distinct ?B"
    by (rule ascending_sink_delta_distinct[OF asc])
  have B_replay: "set ?B \<subseteq> set (replay_down_hist ?S (exec_scope (dwe_core t)) f)"
    by (auto simp: sink_delta_def)

  \<comment> \<open>NOT premature: old entries frozen, prefix entries stamp-justified\<close>
  have "\<forall>x \<in> set (dwe_emitted ?t'). justified_at ?S x"
  proof
    fix x assume "x \<in> set (dwe_emitted ?t')"
    then consider (old) "x \<in> set (dwe_emitted t)" | (new) "x \<in> set ?X"
      by auto
    then show "justified_at ?S x"
    proof cases
      case old
      then show ?thesis using old_just by blast
    next
      case new
      have st: "e_stamp x = length ?S" and pl: "e_payload x \<in> set (take n ?B)"
        using stamped_elem[OF new] by simp_all
      have "e_payload x \<in> set ?B"
        by (rule subsetD[OF set_take_subset pl])
      then have mem_R: "e_payload x
          \<in> set (replay_down_hist ?S (exec_scope (dwe_core t)) f)"
        by (rule subsetD[OF B_replay])
      show ?thesis
        by (rule redrive_emissions_justified[OF mem_R st])
    qed
  qed
  then have not_prem: "\<not> premature ?t'"
    by (auto simp: premature_def)

  \<comment> \<open>NOT duplicate: old distinct, prefix distinct, disjoint by the filter\<close>
  have pay': "map e_payload (dwe_emitted ?t')
      = map e_payload (dwe_emitted t) @ take n ?B"
    by simp
  have dist_take: "distinct (take n ?B)"
    by (rule distinct_take[OF dist_B])
  have disj: "set (take n ?B) \<inter> set (map e_payload (dwe_emitted t)) = {}"
  proof -
    have "set ?B \<inter> set (map e_payload (dwe_emitted t)) = {}"
      by (auto simp: sink_delta_def)
    then show ?thesis
      using set_take_subset[of n ?B] by blast
  qed
  have "distinct (map e_payload (dwe_emitted ?t'))"
    unfolding pay' using old_dist dist_take disj by auto
  then have not_dup: "\<not> duplicate ?t'"
    by (simp add: duplicate_def)

  show ?thesis
    using not_prem not_dup by (simp add: effect_unsafe_def)
qed


section \<open>Load-bearing control: the ascending premise bites\<close>

text \<open>
  THE CONTROL.  Drop the ascending premise and the remainder law FAILS,
  at a concrete WF-H1-LEGAL state: the locked core's wellformedness
  admits equal-coordinate re-commits (non-strict WF-H1, the landed
  aliasing axis), so the history
  @{term "[(ec1, e1), (ec1, e1)]"} --- one business payload committed
  twice --- is wellformed, and the sink-computed batch at it contains
  the payload TWICE.  Appending the take-1 prefix payload-blocks BOTH
  occurrences: the recomputed delta is @{term "[]"} instead of the
  one-element remainder --- a committed instance is silently starved by
  the retry.  The control state is a state of the type, not claimed
  reachable --- the main theorem carries no reachability premise either,
  so the control refutes exactly the premise-dropped variant of what is
  claimed.  (Payload-level counting under aliasing is exactly the
  boundary the ascending premise names in the landed corpus; this is
  its partial-append face.)
\<close>

definition psl_w :: "(nat, nat) dwe_state" where
  "psl_w = mkT (mkC [(ec1, e1), (ec1, e1)] [] [] {} Running) [] 0"

lemma psl_wf: "wellformed_src_history (exec_src_hist (dwe_core psl_w))"
proof -
  have "exec_src_hist (dwe_core psl_w) = [(ec1, e1), (ec1, e1)]"
    by (simp add: psl_w_def mkT_def mkC_def)
  moreover have "wellformed_src_history [(ec1, e1), (ec1, e1)]"
    by (rule wf_hist_pair) (simp_all add: ec_defs)
  ultimately show ?thesis by simp
qed

lemma psl_not_asc:
  "\<not> strictly_ascending_source (exec_src_hist (dwe_core psl_w))"
  by (simp add: strictly_ascending_source_def psl_w_def mkT_def mkC_def
                ec_defs)

lemma psl_batch: "sink_delta ec1 psl_w = [(ec1, e1), (ec1, e1)]"
  by (simp add: sink_delta_def psl_w_def mkT_def mkC_def
                replay_down_hist_def e1_def ec_defs)

lemma psl_batch_duplicate: "\<not> distinct (sink_delta ec1 psl_w)"
  by (simp add: psl_batch)

lemma psl_recompute_starves:
  "sink_delta ec1
     (psl_w\<lparr>dwe_emitted := dwe_emitted psl_w @ [(0, 0, ec1, e1)]\<rparr>) = []"
  by (simp add: sink_delta_def psl_w_def mkT_def mkC_def
                replay_down_hist_def e1_def ec_defs)

lemma psl_remainder: "drop 1 (sink_delta ec1 psl_w) = [(ec1, e1)]"
  by (simp add: psl_batch)

theorem partial_append_asc_load_bearing:
  "\<exists>(t :: (nat, nat) dwe_state) X f n.
     wellformed_src_history (exec_src_hist (dwe_core t))
   \<and> map e_payload X = take n (sink_delta f t)
   \<and> sink_delta f (t\<lparr>dwe_emitted := dwe_emitted t @ X\<rparr>)
       \<noteq> drop n (sink_delta f t)"
proof -
  have pay1: "map e_payload [(0, 0, ec1, e1)] = take 1 (sink_delta ec1 psl_w)"
    by (simp add: psl_batch)
  have "sink_delta ec1
          (psl_w\<lparr>dwe_emitted := dwe_emitted psl_w @ [(0, 0, ec1, e1)]\<rparr>)
      \<noteq> drop 1 (sink_delta ec1 psl_w)"
    by (simp add: psl_recompute_starves psl_batch)
  then show ?thesis
    using psl_wf pay1 by blast
qed

end
