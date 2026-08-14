(*  Title:       Dual_Write_Effect_Delta_Order.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    ORDER PRESERVATION OF THE SINK-READING DELTA (roadmap Wave 2, slice
    W2b) --- an additive post-freeze slice under the freeze's own
    protocol: no landed statement, proof, definition, name, import, or
    session-DAG change to the frozen corpus.

    THE POLICY SIDE OF THE ORDER AXIS, THEOREM-BACKED.  The landed
    escape policy sink_delta filters the scoped, frontier-bounded replay
    of the committed source prefix (itself a filter of that prefix)
    against delivered-payload presence, so the batch it computes --- and
    therefore the ledger segment its re-drive appends --- enumerates
    payloads in COMMITTED ORDER.  This theory pins that boundary
    statement as theorems, in two disclosed strengths:

    - PREMISE-FREE (positional order): the computed batch is a
      subsequence (HOL-Library Sublist.subseq) of the scoped replay
      (sink_delta_subseq_replay) and hence of the committed source
      prefix itself (sink_delta_subseq_src_hist); its coordinate
      sequence is a subsequence of the replay's coordinate sequence
      (sink_delta_coords_subseq).  The same holds verbatim for the
      ledger segment the sink-delta re-drive appends, because that
      segment's payload projection IS the batch
      (sink_redrive_appended_payloads, sink_redrive_batch_subseq_replay).

    - UNDER THE NAMED PREMISE (coordinate order): with a strictly
      ascending committed source (per-event unique coordinates, the CDC
      practitioner reading --- exactly the landed B1/T2.9--T2.12 premise,
      consumed on the positive side only; the impossibility half of the
      landed corpus consumes NO ordering premise), the scoped replay and
      the batch are themselves strictly ascending
      (replay_down_hist_ascending, sink_delta_ascending), the batch's
      coordinate sequence is strictly increasing
      (sink_delta_coords_sorted) and hence duplicate-free
      (sink_delta_coords_distinct), and so is the coordinate sequence of
      the payloads the re-drive appends
      (sink_redrive_batch_coords_sorted).

    The landed corpus's named sortedness family is ledger-side (epoch
    and stamp monotonicity in the Completeness lane); the replay-side
    order fact the coordinate forms need, replay_down_hist_ascending,
    is proved here from the layer-0 filter definition and is the
    supporting lemma of everything under the ascending premise.

    WHAT THIS THEORY DOES NOT CLAIM (the rank-8 boundary, fold-in (d)):
    committed-order emission is a property of the batch the policy HANDS
    the channel, never a delivery-order guarantee.  On-the-wire
    reordering, loss, and duplication belong to the delayed-delivery
    channel variant (ladder sections 32--35), which is deliberately
    outside this theory's import cone; and the landed hazard and
    exactly-once predicates remain payload-set/multiset views --- an
    order-sensitive consumer needs a guarantee this model does not
    provide, and nothing here upgrades the observables.  One theorem,
    one honest scope line: order loss is the channel's, never the
    policy's.

    WITNESS AND CONTROL: a reachable crashed state with a two-element
    delta in visible committed order (committed_order_witness; commit
    two, deliver none, crash) whose admissible re-drive lands exactly
    those two payloads in order (ow_redrive_fires_in_committed_order);
    and a proper-subsequence control at the landed skip-side witness
    d2_w (delta_proper_subsequence_control): the batch is strictly
    shorter than the replay exactly when deliveries are skipped, so the
    subsequence law is not list equality in disguise.

    PROVENANCE: THEORY_IMPROVEMENT_ROADMAP.md Wave 2 slice W2b
    (paper/dual_write/theory_backlog/THEORY_IMPROVEMENT_ROADMAP.md) +
    GAP_HUNT_FLEET_CAPTURE.md section A2 (paper/dual_write/prose_phase/
    framing_exploration/gap_hunt_2026-07-07/; fleet register rank 8
    "order-sensitive consumers"; the solo hunter priced this slice
    near-definitional).  Everything below is about the landed sink_delta
    of the cyclic-branch Dilemma theory; the import is that single
    sibling plus HOL-Library.Sublist for the subsequence vocabulary.

    No in-source ML oracle gates: oracle-freedom is certified by the
    wave's scratch-side gate session with confirmed-biting negative
    controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Delta_Order
  imports Dual_Write_Effect_Dilemma "HOL-Library.Sublist"
begin

section \<open>Scope: the policy side of the order axis\<close>

text \<open>
  The landed escape policy @{const sink_delta} computes the batch a
  sink-reading re-drive fires: the scoped, frontier-bounded replay of
  the committed source prefix, filtered against the payloads already in
  the emission ledger.  Both stages are @{const filter}s, so the batch
  is a subsequence of the replay and of the committed prefix itself ---
  the escape never permutes what the source committed.  This theory
  states that order inheritance premise-free in positional form
  (@{text subseq}), and in coordinate form under the named
  @{const strictly_ascending_source} premise (per-event unique
  coordinates, the CDC practitioner reading; the same premise the
  landed escape theorems consume, positive side only).

  BOUNDARY (register rank 8, carried honestly): these are statements
  about the batch the policy hands the channel --- equivalently, about
  the ledger segment its re-drive appends --- not about arrival order.
  The delayed-delivery channel variant owns the on-the-wire reordering
  axis (ladder sections 32--35; not in this import cone), and the landed
  hazard/exactly-once predicates are payload-set/multiset views, so an
  order-sensitive OBSERVABLE stays outside the model's scope.  Order
  loss is the channel's, never the policy's.
\<close>

section \<open>The subsequence law: the batch inherits committed order, premise-free\<close>

text \<open>
  The list-level sharpening of the landed set-level fact
  @{thm [source] replay_down_hist_subset}: the replay keeps the
  committed prefix's ORDER, not merely its membership.
\<close>

lemma replay_down_hist_subseq:
  "subseq (replay_down_hist S K f) S"
  unfolding replay_down_hist_def by (rule subseq_filter_left)

text \<open>
  THE SUBSEQUENCE LEMMA.  The computed batch is a subsequence of the
  scoped, frontier-bounded replay: whatever the delta fires, it fires
  in the replay's committed order.  Near-definitional by design ---
  @{const sink_delta} IS a filter --- and stated with NO premise: no
  reachability, no ascending source, no effect-safety.
\<close>

theorem sink_delta_subseq_replay:
  "subseq (sink_delta f t)
     (replay_down_hist (exec_src_hist (dwe_core t))
        (exec_scope (dwe_core t)) f)"
  unfolding sink_delta_def by (rule subseq_filter_left)

text \<open>Composing the two filter stages: the batch is a subsequence of
  the committed source prefix itself.\<close>

theorem sink_delta_subseq_src_hist:
  "subseq (sink_delta f t) (exec_src_hist (dwe_core t))"
  unfolding sink_delta_def replay_down_hist_def by simp

text \<open>The positional order form on coordinates, still premise-free:
  the batch's coordinate sequence is a subsequence of the replay's
  coordinate sequence.\<close>

theorem sink_delta_coords_subseq:
  "subseq (map fst (sink_delta f t))
     (map fst (replay_down_hist (exec_src_hist (dwe_core t))
                 (exec_scope (dwe_core t)) f))"
  by (rule subseq_map[OF sink_delta_subseq_replay])

section \<open>Coordinate order under the named ascending premise\<close>

text \<open>
  The replay's own order fact, named for reuse: a filter of a strictly
  ascending history is strictly ascending.  This is the supporting
  lemma behind every coordinate-order form below.
\<close>

lemma replay_down_hist_ascending:
  assumes "strictly_ascending_source H"
  shows "strictly_ascending_source (replay_down_hist H K f)"
  using assms
  unfolding strictly_ascending_source_def replay_down_hist_def
  by (rule sorted_wrt_filter)

text \<open>The batch inherits strict ascent: one more filter stage.\<close>

theorem sink_delta_ascending:
  assumes "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "strictly_ascending_source (sink_delta f t)"
  using replay_down_hist_ascending[OF assms]
  unfolding strictly_ascending_source_def sink_delta_def
  by (rule sorted_wrt_filter)

text \<open>The readable coordinate form: under the named premise the
  batch's coordinate sequence is strictly increasing --- the escape
  emits in strictly ascending committed-coordinate order.\<close>

theorem sink_delta_coords_sorted:
  assumes "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "sorted_wrt (<) (map fst (sink_delta f t))"
  using sink_delta_ascending[OF assms]
  unfolding strictly_ascending_source_def
  by (simp add: sorted_wrt_map)

text \<open>Strict ascent makes the fired coordinate sequence duplicate-free
  --- the coordinate-level companion of the landed payload-distinctness
  pipeline (@{thm [source] strictly_ascending_distinct} and the batch
  distinctness inside the landed B1 proof).\<close>

corollary sink_delta_coords_distinct:
  assumes "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "distinct (map fst (sink_delta f t))"
  using sink_delta_coords_sorted[OF assms]
  by (simp add: strict_sorted_iff)

section \<open>The re-drive's appended segment fires in committed order\<close>

text \<open>
  Lifting the function-level facts to the rule: the ledger segment the
  sink-delta re-drive appends has the batch as its payload projection
  (the fire-time stamping is right-nested pairing, so payload
  extraction is the identity on the batch --- the landed
  @{thm [source] map_payload_stamped} bookkeeping).  Hence every order
  fact about the batch transfers verbatim to what actually lands in
  the ledger.
\<close>

lemma sink_redrive_appended_payloads:
  assumes "policy_redrive (sink_delta f) t f t'"
  shows "map e_payload (drop (length (dwe_emitted t)) (dwe_emitted t'))
           = sink_delta f t"
  by (simp add: policy_redrive_emitted[OF assms])

text \<open>THE BOUNDARY STATEMENT, theorem-backed and premise-free: the
  payloads the escape's re-drive appends form a subsequence of the
  scoped replay --- the re-drive emits in committed order.\<close>

theorem sink_redrive_batch_subseq_replay:
  assumes "policy_redrive (sink_delta f) t f t'"
  shows "subseq (map e_payload (drop (length (dwe_emitted t))
                                  (dwe_emitted t')))
           (replay_down_hist (exec_src_hist (dwe_core t))
              (exec_scope (dwe_core t)) f)"
  unfolding sink_redrive_appended_payloads[OF assms]
  by (rule sink_delta_subseq_replay)

text \<open>And in coordinate form under the named premise: the appended
  payloads' coordinates strictly increase.\<close>

theorem sink_redrive_batch_coords_sorted:
  assumes "policy_redrive (sink_delta f) t f t'"
      and "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "sorted_wrt (<)
           (map fst (map e_payload (drop (length (dwe_emitted t))
                                      (dwe_emitted t'))))"
  unfolding sink_redrive_appended_payloads[OF assms(1)]
  by (rule sink_delta_coords_sorted[OF assms(2)])

section \<open>Non-vacuity: a reachable two-element delta in visible committed order\<close>

text \<open>
  A reachable crashed state whose computed delta has TWO elements, so
  the order content is visible (a singleton batch carries none): from
  the landed @{const W1} (one committed event, nothing delivered),
  commit the second event and crash before any delivery.  The ledger is
  empty, so the delta is the whole scoped replay
  @{term "[(ec1, e1), (ec2, e2)]"} --- both committed effects, in
  committed order, with strictly increasing coordinates.  The chain
  reuses the landed witness scaffolding (@{thm [source] reach_W1}, the
  step intro rules, the wellformedness helpers).
\<close>

definition ow_run_w :: "(nat, nat) dwe_state" where
  "ow_run_w = mkT (mkC [(ec1, e1), (ec2, e2)] [] [] {} Running) [] 0"

definition ow_crash_w :: "(nat, nat) dwe_state" where
  "ow_crash_w = mkT (mkC [(ec1, e1), (ec2, e2)] [] [] {} (Crashed ec2)) [] 0"

lemma ow_g_src2:
  "exec_label_preserves_history_wf (dwe_core W1) (DoSource ec2 e2)"
  by (simp add: W1_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma ow_ws1: "dwe_step W1 (DoSource ec2 e2) ow_run_w"
proof -
  have c: "dw_exec_step (dwe_core W1) (DoSource ec2 e2) (dwe_core ow_run_w)"
    by (rule do_sourceI) (simp_all add: W1_def ow_run_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: W1_def ow_run_w_def mkT_def)
qed

lemma ow_wf_run: "wellformed_exec_state (dwe_core ow_run_w)"
  by (simp add: ow_run_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_pair)

lemma ow_g_crash:
  "exec_label_preserves_history_wf (dwe_core ow_run_w) (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma ow_ws2: "dwe_step ow_run_w (Crash ec2) ow_crash_w"
proof -
  have c: "dw_exec_step (dwe_core ow_run_w) (Crash ec2) (dwe_core ow_crash_w)"
    by (rule crashI) (simp_all add: ow_run_w_def ow_crash_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c])
       (simp_all add: ow_run_w_def ow_crash_w_def mkT_def)
qed

lemma ow_reach_run: "dwe_reachable ow_run_w"
  by (rule dwe_reachable_label_ext[OF reach_W1 wf_W1 ow_g_src2 ow_ws1])

lemma ow_reach_crash: "dwe_reachable ow_crash_w"
  by (rule dwe_reachable_label_ext[OF ow_reach_run ow_wf_run ow_g_crash ow_ws2])

text \<open>Field-level normal forms and the delta evaluations.\<close>

lemma ow_crash_fields:
  "exec_status (dwe_core ow_crash_w) = Crashed ec2"
  "exec_finish (dwe_core ow_crash_w) = ec2"
  "exec_src_hist (dwe_core ow_crash_w) = [(ec1, e1), (ec2, e2)]"
  "exec_scope (dwe_core ow_crash_w) = {0, 1}"
  "dwe_emitted ow_crash_w = []"
  "dwe_epoch ow_crash_w = 0"
  by (simp_all add: ow_crash_w_def mkT_def mkC_def)

lemma ow_delta_is_replay:
  "sink_delta ec2 ow_crash_w
     = replay_down_hist (exec_src_hist (dwe_core ow_crash_w))
         (exec_scope (dwe_core ow_crash_w)) ec2"
  by (simp add: sink_delta_def ow_crash_w_def mkT_def)

lemma ow_delta_eval:
  "sink_delta ec2 ow_crash_w = [(ec1, e1), (ec2, e2)]"
  by (simp add: sink_delta_def ow_crash_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs)

lemma ow_asc: "strictly_ascending_source (exec_src_hist (dwe_core ow_crash_w))"
  by (simp add: strictly_ascending_source_def ow_crash_w_def mkT_def mkC_def
                e1_def e2_def ec_defs)

text \<open>The general coordinate theorem, biting at the witness.\<close>

corollary ow_delta_coords_sorted:
  "sorted_wrt (<) (map fst (sink_delta ec2 ow_crash_w))"
  by (rule sink_delta_coords_sorted[OF ow_asc])

text \<open>
  The packaged witness: reachable, the delta is the WHOLE scoped replay
  (empty ledger), it has two elements, and its coordinate sequence is
  the visibly increasing @{term "[ec1, ec2]"}.
\<close>

theorem committed_order_witness:
  "dwe_reachable ow_crash_w
 \<and> sink_delta ec2 ow_crash_w
     = replay_down_hist (exec_src_hist (dwe_core ow_crash_w))
         (exec_scope (dwe_core ow_crash_w)) ec2
 \<and> sink_delta ec2 ow_crash_w = [(ec1, e1), (ec2, e2)]
 \<and> 2 \<le> length (sink_delta ec2 ow_crash_w)
 \<and> map fst (sink_delta ec2 ow_crash_w) = [ec1, ec2]
 \<and> ec1 < ec2"
proof (intro conjI)
  show "dwe_reachable ow_crash_w" by (rule ow_reach_crash)
  show "sink_delta ec2 ow_crash_w
          = replay_down_hist (exec_src_hist (dwe_core ow_crash_w))
              (exec_scope (dwe_core ow_crash_w)) ec2"
    by (rule ow_delta_is_replay)
  show "sink_delta ec2 ow_crash_w = [(ec1, e1), (ec2, e2)]"
    by (rule ow_delta_eval)
  show "2 \<le> length (sink_delta ec2 ow_crash_w)"
    by (simp add: ow_delta_eval eval_nat_numeral)
  show "map fst (sink_delta ec2 ow_crash_w) = [ec1, ec2]"
    by (simp add: ow_delta_eval)
  show "ec1 < ec2"
    by (simp add: ec_defs)
qed

text \<open>
  Control: the subsequence is PROPER when the filter bites.  At the
  landed dilemma skip-side witness @{const d2_w} (reachable,
  @{thm [source] reach_d2}) one committed payload is already in the
  ledger; the delta drops it and keeps the remainder --- strictly
  shorter than the replay, still a subsequence of it.  So the
  subsequence law is not list equality in disguise: it survives exactly
  the deliveries the escape is designed to skip.
\<close>

lemma d2_delta_eval: "sink_delta ec2 d2_w = [(ec2, e2)]"
  by (simp add: sink_delta_def d2_w_def mkT_def mkC_def replay_down_hist_def
                e1_def e2_def ec_defs)

theorem delta_proper_subsequence_control:
  "dwe_reachable d2_w
 \<and> sink_delta ec2 d2_w = [(ec2, e2)]
 \<and> length (sink_delta ec2 d2_w)
     < length (replay_down_hist (exec_src_hist (dwe_core d2_w))
                 (exec_scope (dwe_core d2_w)) ec2)
 \<and> subseq (sink_delta ec2 d2_w)
     (replay_down_hist (exec_src_hist (dwe_core d2_w))
        (exec_scope (dwe_core d2_w)) ec2)"
proof (intro conjI)
  show "dwe_reachable d2_w" by (rule reach_d2)
  show "sink_delta ec2 d2_w = [(ec2, e2)]" by (rule d2_delta_eval)
  show "length (sink_delta ec2 d2_w)
          < length (replay_down_hist (exec_src_hist (dwe_core d2_w))
                      (exec_scope (dwe_core d2_w)) ec2)"
    unfolding d2_delta_eval
    by (simp add: d2_w_def mkT_def mkC_def replay_down_hist_def
                  e1_def e2_def ec_defs)
  show "subseq (sink_delta ec2 d2_w)
          (replay_down_hist (exec_src_hist (dwe_core d2_w))
             (exec_scope (dwe_core d2_w)) ec2)"
    by (rule sink_delta_subseq_replay)
qed

text \<open>
  And the rule-level bite: the sink-delta re-drive is admissible at the
  witness (crashed, at its own finish frontier), and the ledger it
  produces carries exactly the two committed payloads in committed
  order --- the whole post-state ledger, since the pre-state ledger is
  empty.
\<close>

theorem ow_redrive_fires_in_committed_order:
  "policy_redrive (sink_delta ec2) ow_crash_w ec2
     (redrive_result (sink_delta ec2) ow_crash_w ec2)
 \<and> map e_payload (dwe_emitted (redrive_result (sink_delta ec2) ow_crash_w ec2))
     = [(ec1, e1), (ec2, e2)]"
proof (rule conjI)
  have grd: "\<exists>c. exec_status (dwe_core ow_crash_w) = Crashed c"
    by (simp add: ow_crash_fields)
  have fin: "ec2 \<le> exec_finish (dwe_core ow_crash_w)"
    by (simp add: ow_crash_fields)
  show "policy_redrive (sink_delta ec2) ow_crash_w ec2
          (redrive_result (sink_delta ec2) ow_crash_w ec2)"
    by (rule policy_redriveI[OF grd fin])
next
  show "map e_payload
          (dwe_emitted (redrive_result (sink_delta ec2) ow_crash_w ec2))
          = [(ec1, e1), (ec2, e2)]"
    by (simp add: redrive_result_def ow_crash_fields ow_delta_eval)
qed

end
