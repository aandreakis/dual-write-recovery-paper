(*  Title:       Dual_Write_Defect_Regressions.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Permanent kernel-checked regressions for externally reported defects.
    Each section records the original counterexample shape.  During repair,
    the pre-fix conclusions are replaced by the intended post-fix guarantees;
    the witnesses themselves remain so that the defects cannot silently
    return.

    The external report defining the D-numbering is archived verbatim in
    the development repository at
    sink_and_fence/reviews/incoming/R07_isabelle_defect_report.md.
*)

theory Dual_Write_Defect_Regressions
  imports
    Dual_Write_Crash_Truncation
    Dual_Write_Multikey
    Dual_Write_Image_Completeness
begin

section \<open>D1 regression: duplicate pending occurrences survive reconstruction\<close>

definition d1_msg :: "(nat, nat) delivery_msg" where
  "d1_msg = (ec1, Insert 0 7)"

definition d1_s0 :: "(nat, nat) dw_delivery_state" where
  "d1_s0 =
     \<lparr>del_exec = initial_exec_state (\<lambda>_. None) {0} ec1,
      del_pending = [], del_partitioned = False\<rparr>"

definition d1_s1 :: "(nat, nat) dw_delivery_state" where
  "d1_s1 =
     d1_s0\<lparr>
       del_exec := (del_exec d1_s0)\<lparr>
         exec_enqueued := exec_enqueued (del_exec d1_s0) @ [d1_msg],
         exec_pending := insert d1_msg (exec_pending (del_exec d1_s0))\<rparr>,
       del_pending := del_pending d1_s0 @ [d1_msg]\<rparr>"

definition d1_s2 :: "(nat, nat) dw_delivery_state" where
  "d1_s2 =
     d1_s1\<lparr>
       del_exec := (del_exec d1_s1)\<lparr>
         exec_enqueued := exec_enqueued (del_exec d1_s1) @ [d1_msg],
         exec_pending := insert d1_msg (exec_pending (del_exec d1_s1))\<rparr>,
       del_pending := del_pending d1_s1 @ [d1_msg]\<rparr>"

definition d1_s3 :: "(nat, nat) dw_delivery_state" where
  "d1_s3 =
     d1_s2\<lparr>
       del_exec := (del_exec d1_s2)\<lparr>
         exec_down_hist := exec_down_hist (del_exec d1_s2) @ [d1_msg],
         exec_pending := set [d1_msg]\<rparr>,
       del_pending := [d1_msg]\<rparr>"

lemma d1_step1:
  "delivery_step d1_s0 (DelEnqueue ec1 (Insert 0 7)) d1_s1"
  unfolding d1_s1_def d1_msg_def
  by (rule delivery_step.del_enqueue)
     (simp add: d1_s0_def initial_exec_state_def)

lemma d1_step2:
  "delivery_step d1_s1 (DelEnqueue ec1 (Insert 0 7)) d1_s2"
  unfolding d1_s2_def d1_msg_def
  by (rule delivery_step.del_enqueue)
     (simp add: d1_s1_def d1_s0_def initial_exec_state_def d1_msg_def)

lemma d1_step3:
  "delivery_step d1_s2 (DelDeliver ec1 (Insert 0 7)) d1_s3"
  unfolding d1_s3_def d1_msg_def
  by (rule delivery_step.del_deliver)
     (simp_all add: d1_s2_def d1_s1_def d1_s0_def
                    initial_exec_state_def d1_msg_def)

lemma d1_reachable:
  "delivery_trace d1_s0
     [DelEnqueue ec1 (Insert 0 7),
      DelEnqueue ec1 (Insert 0 7),
      DelDeliver ec1 (Insert 0 7)]
     d1_s3"
  by (rule delivery_trace.delivery_trace_step[OF d1_step1],
      rule delivery_trace.delivery_trace_step[OF d1_step2],
      rule delivery_trace.delivery_trace_step[OF d1_step3],
      rule delivery_trace.delivery_trace_refl)

lemma d1_reachable_fields:
  "exec_enqueued (del_exec d1_s3) = [d1_msg, d1_msg]"
  "exec_down_hist (del_exec d1_s3) = [d1_msg]"
  "del_pending d1_s3 = [d1_msg]"
  by (simp_all add: d1_s3_def d1_s2_def d1_s1_def d1_s0_def
                    initial_exec_state_def)

lemma d1_occurrence_preserved:
  "durable_pending_queue_at_boundary (single_durable_boundary ec1) d1_s3
     = [d1_msg]"
  by (simp add: durable_pending_queue_at_boundary_def
                durable_history_prefix_at_def single_durable_boundary_def
                d1_reachable_fields d1_msg_def)

lemma d1_crash_state_preserves_queue_and_set_view:
  "del_pending
      (truncating_delivery_crash_state_at_boundary d1_s3
        (single_durable_boundary ec1) ec1) = [d1_msg]"
  "exec_pending
      (del_exec
        (truncating_delivery_crash_state_at_boundary d1_s3
          (single_durable_boundary ec1) ec1)) = {d1_msg}"
  by (simp_all add: truncating_delivery_crash_state_at_boundary_def
                    d1_occurrence_preserved)

lemma d1_precrash_wellformed:
  "wellformed_exec_state (del_exec d1_s3)"
proof -
  have empty: "wellformed_src_history ([] :: (nat, nat) src_history)"
    by (simp add: wellformed_src_history_def)
  have can_empty: "history_can_append [] d1_msg"
    by (simp add: history_can_append_def d1_msg_def ec_defs)
  have one_raw: "wellformed_src_history ([] @ [d1_msg])"
    by (rule wellformed_src_history_append_one[OF empty can_empty])
  have one: "wellformed_src_history [d1_msg]"
    using one_raw by simp
  have can_one: "history_can_append [d1_msg] d1_msg"
    by (simp add: history_can_append_def d1_msg_def ec_defs)
  have two_raw: "wellformed_src_history ([d1_msg] @ [d1_msg])"
    by (rule wellformed_src_history_append_one[OF one can_one])
  have two: "wellformed_src_history [d1_msg, d1_msg]"
    using two_raw by simp
  show ?thesis
    using one two
    by (simp add: d1_s3_def d1_s2_def d1_s1_def d1_s0_def
                  initial_exec_state_def wellformed_exec_state_def
                  exec_histories_wellformed_def
                  pending_enqueued_consistent_def
                  acked_source_consistent_def wellformed_src_history_def)
qed

lemma d1_truncating_crash_enabled:
  "\<exists>S'. truncating_delivery_crash_step_at_boundary d1_s3
       (single_durable_boundary ec1) ec1 S'"
proof -
  have core:
    "truncating_crash_step_at_boundary (del_exec d1_s3)
       (single_durable_boundary ec1) ec1
       (truncating_crash_state_at_boundary (del_exec d1_s3)
          (single_durable_boundary ec1) ec1)"
    by (rule truncating_crash_step_at_boundary.truncating_crash)
       (rule d1_precrash_wellformed,
        simp add: d1_s3_def d1_s2_def d1_s1_def d1_s0_def initial_exec_state_def,
        simp add: durable_boundary_within_finish_def single_durable_boundary_def
                  d1_s3_def d1_s2_def d1_s1_def d1_s0_def initial_exec_state_def)
  from core show ?thesis
    by (blast intro: truncating_delivery_crash_step_at_boundary.truncating_delivery_crash)
qed


section \<open>D2--D3 regressions: full recovery execution and strict witness\<close>

lemma nonrunning_trace_preserves_down_history:
  assumes tr: "dw_exec_trace s xs s'"
      and nr: "exec_status s \<noteq> Running"
  shows "exec_down_hist s' = exec_down_hist s"
  using tr nr
proof (induction rule: dw_exec_trace.induct)
  case (trace_refl s)
  show ?case by simp
next
  case (trace_step s a s' as s'')
  have nr': "exec_status s' \<noteq> Running"
    by (rule dw_exec_step_not_running_preserved
        [OF trace_step.hyps(1) trace_step.prems])
  have down: "exec_down_hist s' = exec_down_hist s"
    using trace_step.hyps(1) trace_step.prems
    by (cases rule: dw_exec_step.cases) auto
  show ?case using trace_step.IH[OF nr'] down by simp
qed

text \<open>The old running-label projection remains intentionally unable to mutate
  downstream history after a crash.  This boundary check prevents the complete
  recovery semantics from being silently confused with a status-only label.\<close>

lemma d2_label_projection_cannot_recover:
  "\<forall>xs. \<not> dwi_trace (I_relay_labels w0) w_crash xs w_recovered"
proof (intro allI notI)
  fix xs
  assume tr: "dwi_trace (I_relay_labels w0) w_crash xs w_recovered"
  have raw: "dw_exec_trace w_crash xs w_recovered"
    using dwi_trace_refines_exec[OF I_relay_labels_refines_exec tr]
    by (simp add: I_relay_labels_def)
  have "exec_down_hist w_recovered = exec_down_hist w_crash"
    by (rule nonrunning_trace_preserves_down_history[OF raw])
       (simp add: w_crash_fields)
  then show False
    by (simp add: w_recovered_def w_crash_fields replay_down_hist_def ec_defs)
qed

lemma d2_complete_relay_executes_recovery:
  "relay_trace (I_relay w0) (relay_initial (I_relay w0))
     [Relay_Label (DoSource ec2 (Insert 0 7)),
      Relay_Label (EnqueueDownstream ec2 (Insert 0 7)),
      Relay_Label (DoDownstream ec2 (Insert 0 7)),
      Relay_Label (DoSource ec3 (Insert 0 9)),
      Relay_Label (Crash ec3),
      Relay_Reconcile ec3]
     w_recovered"
  by (rule w_recovered_full_relay_trace)

lemma d3_atomic_coincidence_control:
  "w_recovered = recovery_reconciled_state w_crash"
  by (rule w_recovery_coincides_with_atomic_control)

lemma d3_executable_witness_is_strictly_non_atomic:
  "relay_trace (I_relay na0) (relay_initial (I_relay na0))
     [Relay_Label (DoSource ec2 (Insert 0 7)),
      Relay_Label (DoSource ec3 (Insert 1 9)),
      Relay_Label (Crash ec3),
      Relay_Reconcile ec3]
     na_recovered
   \<and> na_recovered \<noteq> recovery_reconciled_state na_crash"
  using na_recovered_full_relay_trace na_recovery_strictly_non_atomic
  by blast


section \<open>D5 regression: strictness uses an implementation-level no-ack witness\<close>

definition d5_w_ack :: "(nat, nat) dw_exec_state" where
  "d5_w_ack =
     w_src3\<lparr>exec_acked := exec_acked w_src3 @ [(ec3, Insert 0 9)]\<rparr>"

definition d5_w_ack_crash :: "(nat, nat) dw_exec_state" where
  "d5_w_ack_crash = d5_w_ack\<lparr>exec_status := Crashed ec3\<rparr>"

lemma d5_w_src3_aux_fields:
  "exec_status w_src3 = Running"
  "exec_acked w_src3 = []"
  by (simp_all add: w_src3_def w_down2_def w_enq2_def w_src2_def
                    w0_def initial_exec_state_def)

lemma d5_ack_step:
  "relay_step w_src3 (Ack ec3 (Insert 0 9)) d5_w_ack"
  unfolding relay_step_def relay_admits_def d5_w_ack_def
  by (intro conjI dw_exec_step.ack)
     (simp_all add: w_src3_fields d5_w_src3_aux_fields
                    exec_label_preserves_history_wf_def
                    history_can_append_def ec_defs)

lemma d5_crash_step:
  "relay_step d5_w_ack (Crash ec3) d5_w_ack_crash"
  unfolding relay_step_def relay_admits_def d5_w_ack_crash_def
  by (intro conjI dw_exec_step.crash)
     (simp_all add: d5_w_ack_def w_src3_fields d5_w_src3_aux_fields
                    exec_label_preserves_history_wf_def)

lemma d5_reachable:
  "dwi_trace (I_relay_labels w0) (dwi_initial (I_relay_labels w0))
     [DoSource ec2 (Insert 0 7), EnqueueDownstream ec2 (Insert 0 7),
      DoDownstream ec2 (Insert 0 7), DoSource ec3 (Insert 0 9),
      Ack ec3 (Insert 0 9), Crash ec3]
     d5_w_ack_crash"
proof -
  have init: "dwi_initial (I_relay_labels w0) = w0"
    by (simp add: I_relay_labels_def)
  show ?thesis
    unfolding init
    by (rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF w_step_src2]],
        rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF w_step_enq2]],
        rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF w_step_down2]],
        rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF w_step_src3]],
        rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF d5_ack_step]],
        rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF d5_crash_step]],
        rule dwi_trace.dwi_trace_refl)
qed

lemma d5_acked_mismatch:
  "acked_observable_mismatch d5_w_ack_crash ec3 0"
  by (simp add: acked_observable_mismatch_def acked_source_effect_at_def
                observable_mismatch_def d5_w_ack_crash_def d5_w_ack_def
                w_src3_fields d5_w_src3_aux_fields
                mismatch_at_def proto_of_exec_at_def
                store2_of_exec_def log_image_def restrict_def
                down_image_ec3 src_image_ec3)

lemma d5_ack_capable_label_projection_is_not_acked_durable:
  "\<not> implementation_acked_durable (I_relay_labels w0)"
  unfolding implementation_acked_durable_def
  apply simp
  using d5_reachable d5_acked_mismatch
  by (auto simp: I_relay_labels_def)

lemma d5_no_ack_implementation_is_acked_durable_but_image_unsafe:
  "implementation_acked_durable (I_relay_no_ack w0)
   \<and> implementation_has_reachable_observable_bad_crash (I_relay_no_ack w0)
   \<and> \<not> running_image_faithful (I_relay_no_ack w0)"
  using I_relay_no_ack_w0_acked_durable I_relay_no_ack_w0_unsafe
        I_relay_no_ack_w0_not_running_image_faithful
  by blast


section \<open>D9 regression: a cross-key violation requires distinct keys\<close>

lemma d9_aliased_key_rejected:
  "\<not> cross_key_invariant_violation_at multikey_partial_proto
     (pcrash multikey_partial_proto) 1 1 (\<lambda>x y. x = y)"
  by (simp add: cross_key_invariant_violation_at_def
                source_relation_invariant_at_def
                downstream_relation_invariant_at_def relation2_holds_on_def
                multikey_partial_proto_def log_image_def Src_def
                latest_src_event_def restrict_def ec_defs Let_def)


section \<open>D12 regression: applied duplicates and reversals are detected\<close>

definition d12_m1 :: "(nat, nat) delivery_msg" where
  "d12_m1 = (ec1, Insert 0 7)"

definition d12_m2 :: "(nat, nat) delivery_msg" where
  "d12_m2 = (ec1, Insert 1 9)"

definition d12_s0 :: "(nat, nat) dw_delivery_state" where
  "d12_s0 =
     \<lparr>del_exec = initial_exec_state (\<lambda>_. None) {0, 1} ec1,
      del_pending = [], del_partitioned = False\<rparr>"

definition d12_dup_s1 :: "(nat, nat) dw_delivery_state" where
  "d12_dup_s1 =
     d12_s0\<lparr>
       del_exec := (del_exec d12_s0)\<lparr>
         exec_enqueued := exec_enqueued (del_exec d12_s0) @ [d12_m1],
         exec_pending := insert d12_m1 (exec_pending (del_exec d12_s0))\<rparr>,
       del_pending := del_pending d12_s0 @ [d12_m1]\<rparr>"

definition d12_dup_s2 :: "(nat, nat) dw_delivery_state" where
  "d12_dup_s2 =
     d12_dup_s1\<lparr>
       del_exec := (del_exec d12_dup_s1)\<lparr>
         exec_pending := set (del_pending d12_dup_s1 @ [d12_m1])\<rparr>,
       del_pending := del_pending d12_dup_s1 @ [d12_m1]\<rparr>"

definition d12_dup_s3 :: "(nat, nat) dw_delivery_state" where
  "d12_dup_s3 =
     d12_dup_s2\<lparr>
       del_exec := (del_exec d12_dup_s2)\<lparr>
         exec_down_hist := exec_down_hist (del_exec d12_dup_s2) @ [d12_m1],
         exec_pending := set [d12_m1]\<rparr>,
       del_pending := [d12_m1]\<rparr>"

definition d12_dup_final :: "(nat, nat) dw_delivery_state" where
  "d12_dup_final =
     d12_dup_s3\<lparr>
       del_exec := (del_exec d12_dup_s3)\<lparr>
         exec_down_hist := exec_down_hist (del_exec d12_dup_s3) @ [d12_m1],
         exec_pending := set []\<rparr>,
       del_pending := []\<rparr>"

definition d12_rev_s2 :: "(nat, nat) dw_delivery_state" where
  "d12_rev_s2 =
     d12_dup_s1\<lparr>
       del_exec := (del_exec d12_dup_s1)\<lparr>
         exec_enqueued := exec_enqueued (del_exec d12_dup_s1) @ [d12_m2],
         exec_pending := insert d12_m2 (exec_pending (del_exec d12_dup_s1))\<rparr>,
       del_pending := del_pending d12_dup_s1 @ [d12_m2]\<rparr>"

definition d12_rev_s3 :: "(nat, nat) dw_delivery_state" where
  "d12_rev_s3 =
     d12_rev_s2\<lparr>
       del_exec := (del_exec d12_rev_s2)\<lparr>
         exec_pending := set [d12_m2, d12_m1]\<rparr>,
       del_pending := [d12_m2, d12_m1]\<rparr>"

definition d12_rev_s4 :: "(nat, nat) dw_delivery_state" where
  "d12_rev_s4 =
     d12_rev_s3\<lparr>
       del_exec := (del_exec d12_rev_s3)\<lparr>
         exec_down_hist := exec_down_hist (del_exec d12_rev_s3) @ [d12_m2],
         exec_pending := set [d12_m1]\<rparr>,
       del_pending := [d12_m1]\<rparr>"

definition d12_rev_final :: "(nat, nat) dw_delivery_state" where
  "d12_rev_final =
     d12_rev_s4\<lparr>
       del_exec := (del_exec d12_rev_s4)\<lparr>
         exec_down_hist := exec_down_hist (del_exec d12_rev_s4) @ [d12_m1],
         exec_pending := set []\<rparr>,
       del_pending := []\<rparr>"

lemma d12_dup_steps:
  "delivery_step d12_s0 (DelEnqueue ec1 (Insert 0 7)) d12_dup_s1"
  "delivery_step d12_dup_s1 (DelDuplicate ec1 (Insert 0 7)) d12_dup_s2"
  "delivery_step d12_dup_s2 (DelDeliver ec1 (Insert 0 7)) d12_dup_s3"
  "delivery_step d12_dup_s3 (DelDeliver ec1 (Insert 0 7)) d12_dup_final"
proof -
  show "delivery_step d12_s0 (DelEnqueue ec1 (Insert 0 7)) d12_dup_s1"
    unfolding d12_dup_s1_def d12_m1_def
    by (rule delivery_step.del_enqueue)
       (simp add: d12_s0_def initial_exec_state_def)
  show "delivery_step d12_dup_s1 (DelDuplicate ec1 (Insert 0 7)) d12_dup_s2"
    unfolding d12_dup_s2_def d12_m1_def
    by (rule delivery_step.del_duplicate)
       (simp add: d12_dup_s1_def d12_s0_def d12_m1_def
                  initial_exec_state_def)
  show "delivery_step d12_dup_s2 (DelDeliver ec1 (Insert 0 7)) d12_dup_s3"
    unfolding d12_dup_s3_def d12_m1_def
    by (rule delivery_step.del_deliver)
       (simp_all add: d12_dup_s2_def d12_dup_s1_def d12_s0_def
                      d12_m1_def initial_exec_state_def)
  show "delivery_step d12_dup_s3 (DelDeliver ec1 (Insert 0 7)) d12_dup_final"
    unfolding d12_dup_final_def d12_m1_def
    by (rule delivery_step.del_deliver)
       (simp_all add: d12_dup_s3_def d12_dup_s2_def d12_dup_s1_def
                      d12_s0_def d12_m1_def initial_exec_state_def)
qed

lemma d12_duplicate_state_reachable:
  "delivery_trace d12_s0
     [DelEnqueue ec1 (Insert 0 7), DelDuplicate ec1 (Insert 0 7),
      DelDeliver ec1 (Insert 0 7), DelDeliver ec1 (Insert 0 7)]
     d12_dup_final"
  using d12_dup_steps
  by (meson delivery_trace.delivery_trace_refl
            delivery_trace.delivery_trace_step)

lemma d12_rev_steps:
  "delivery_step d12_dup_s1 (DelEnqueue ec1 (Insert 1 9)) d12_rev_s2"
  "delivery_step d12_rev_s2 (DelReorder [d12_m2, d12_m1]) d12_rev_s3"
  "delivery_step d12_rev_s3 (DelDeliver ec1 (Insert 1 9)) d12_rev_s4"
  "delivery_step d12_rev_s4 (DelDeliver ec1 (Insert 0 7)) d12_rev_final"
proof -
  show "delivery_step d12_dup_s1 (DelEnqueue ec1 (Insert 1 9)) d12_rev_s2"
    unfolding d12_rev_s2_def d12_m2_def
    by (rule delivery_step.del_enqueue)
       (simp add: d12_dup_s1_def d12_s0_def initial_exec_state_def
                  d12_m1_def)
  show "delivery_step d12_rev_s2 (DelReorder [d12_m2, d12_m1]) d12_rev_s3"
    unfolding d12_rev_s3_def
    by (rule delivery_step.del_reorder)
       (simp add: d12_rev_s2_def d12_dup_s1_def d12_s0_def
                  d12_m1_def d12_m2_def initial_exec_state_def)
  show "delivery_step d12_rev_s3 (DelDeliver ec1 (Insert 1 9)) d12_rev_s4"
    unfolding d12_rev_s4_def d12_m2_def
    by (rule delivery_step.del_deliver)
       (simp_all add: d12_rev_s3_def d12_rev_s2_def d12_dup_s1_def
                      d12_s0_def d12_m1_def d12_m2_def
                      initial_exec_state_def)
  show "delivery_step d12_rev_s4 (DelDeliver ec1 (Insert 0 7)) d12_rev_final"
    unfolding d12_rev_final_def d12_m1_def
    by (rule delivery_step.del_deliver)
       (simp_all add: d12_rev_s4_def d12_rev_s3_def d12_rev_s2_def
                      d12_dup_s1_def d12_s0_def d12_m1_def d12_m2_def
                      initial_exec_state_def)
qed

lemma d12_reversal_state_reachable:
  "delivery_trace d12_s0
     [DelEnqueue ec1 (Insert 0 7), DelEnqueue ec1 (Insert 1 9),
      DelReorder [d12_m2, d12_m1], DelDeliver ec1 (Insert 1 9),
      DelDeliver ec1 (Insert 0 7)]
     d12_rev_final"
proof -
  have first:
    "delivery_trace d12_s0 [DelEnqueue ec1 (Insert 0 7)] d12_dup_s1"
    by (rule delivery_trace.delivery_trace_step[OF d12_dup_steps(1)
            delivery_trace.delivery_trace_refl])
  have rest:
    "delivery_trace d12_dup_s1
       [DelEnqueue ec1 (Insert 1 9), DelReorder [d12_m2, d12_m1],
        DelDeliver ec1 (Insert 1 9), DelDeliver ec1 (Insert 0 7)]
       d12_rev_final"
    using d12_rev_steps
    by (meson delivery_trace.delivery_trace_refl
              delivery_trace.delivery_trace_step)
  show ?thesis
    using delivery_trace_append[OF first rest] by simp
qed

lemma d12_duplicate_final_fields:
  "exec_enqueued (del_exec d12_dup_final) = [d12_m1]"
  "exec_down_hist (del_exec d12_dup_final) = [d12_m1, d12_m1]"
  by (simp_all add: d12_dup_final_def d12_dup_s3_def d12_dup_s2_def
                    d12_dup_s1_def d12_s0_def initial_exec_state_def)

lemma d12_reversal_final_fields:
  "exec_enqueued (del_exec d12_rev_final) = [d12_m1, d12_m2]"
  "exec_down_hist (del_exec d12_rev_final) = [d12_m2, d12_m1]"
  by (simp_all add: d12_rev_final_def d12_rev_s4_def d12_rev_s3_def
                    d12_rev_s2_def d12_dup_s1_def d12_s0_def
                    initial_exec_state_def)

lemma d12_applied_duplicate_detected:
  "\<not> delivery_deduplicating_apply d12_dup_final"
  by (simp add: delivery_deduplicating_apply_def
                d12_duplicate_final_fields)

lemma d12_applied_reversal_detected:
  "\<not> delivery_source_ordered_apply d12_rev_final"
  by (simp add: delivery_source_ordered_apply_def
                d12_reversal_final_fields d12_m1_def d12_m2_def)


section \<open>D18 regression: tied-coordinate occurrences make ordered progress\<close>

definition d18_e1 :: "(nat, nat) source_event" where
  "d18_e1 = Insert 0 7"

definition d18_e2 :: "(nat, nat) source_event" where
  "d18_e2 = Insert 1 9"

definition d18_s0 :: "(nat, nat) dw_exec_state" where
  "d18_s0 = initial_exec_state (\<lambda>_. None) {0, 1} ec1"

definition d18_s1 :: "(nat, nat) dw_exec_state" where
  "d18_s1 =
     d18_s0\<lparr>exec_src_hist := exec_src_hist d18_s0 @ [(ec1, d18_e1)]\<rparr>"

definition d18_s2 :: "(nat, nat) dw_exec_state" where
  "d18_s2 =
     d18_s1\<lparr>exec_src_hist := exec_src_hist d18_s1 @ [(ec1, d18_e2)]\<rparr>"

definition d18_s3 :: "(nat, nat) dw_exec_state" where
  "d18_s3 =
     d18_s2\<lparr>
       exec_enqueued := exec_enqueued d18_s2 @ [(ec1, d18_e1)],
       exec_pending := insert (ec1, d18_e1) (exec_pending d18_s2)\<rparr>"

definition d18_s4 :: "(nat, nat) dw_exec_state" where
  "d18_s4 =
     d18_s3\<lparr>
       exec_enqueued := exec_enqueued d18_s3 @ [(ec1, d18_e2)],
       exec_pending := insert (ec1, d18_e2) (exec_pending d18_s3)\<rparr>"

definition d18_after_e1 :: "(nat, nat) dw_exec_state" where
  "d18_after_e1 =
     d18_s4\<lparr>
       exec_down_hist := exec_down_hist d18_s4 @ [(ec1, d18_e1)],
       exec_pending := exec_pending d18_s4 - {(ec1, d18_e1)}\<rparr>"

definition d18_after_e2 :: "(nat, nat) dw_exec_state" where
  "d18_after_e2 =
     d18_s4\<lparr>
       exec_down_hist := exec_down_hist d18_s4 @ [(ec1, d18_e2)],
       exec_pending := exec_pending d18_s4 - {(ec1, d18_e2)}\<rparr>"

definition d18_done :: "(nat, nat) dw_exec_state" where
  "d18_done =
     d18_after_e1\<lparr>
       exec_down_hist := exec_down_hist d18_after_e1 @ [(ec1, d18_e2)],
       exec_pending := exec_pending d18_after_e1 - {(ec1, d18_e2)}\<rparr>"

lemma d18_step_src1:
  "relay_step d18_s0 (DoSource ec1 d18_e1) d18_s1"
  unfolding relay_step_def relay_admits_def d18_s1_def
  by (intro conjI dw_exec_step.do_source)
     (simp_all add: d18_s0_def d18_e1_def initial_exec_state_def
                    exec_label_preserves_history_wf_def history_can_append_def
                    adv_def src_lt_eq_less ec_defs)

lemma d18_step_src2:
  "relay_step d18_s1 (DoSource ec1 d18_e2) d18_s2"
  unfolding relay_step_def relay_admits_def d18_s2_def
  by (intro conjI dw_exec_step.do_source)
     (simp_all add: d18_s1_def d18_s0_def d18_e1_def d18_e2_def
                    initial_exec_state_def exec_label_preserves_history_wf_def
                    history_can_append_def adv_def src_lt_eq_less ec_defs)

lemma d18_step_enq1:
  "relay_step d18_s2 (EnqueueDownstream ec1 d18_e1) d18_s3"
  unfolding relay_step_def relay_admits_def d18_s3_def
  by (intro conjI dw_exec_step.enqueue_downstream)
     (simp_all add: d18_s2_def d18_s1_def d18_s0_def d18_e1_def d18_e2_def
                    initial_exec_state_def exec_label_preserves_history_wf_def
                    history_can_append_def ec_defs)

lemma d18_step_enq2:
  "relay_step d18_s3 (EnqueueDownstream ec1 d18_e2) d18_s4"
  unfolding relay_step_def relay_admits_def d18_s4_def
  by (intro conjI dw_exec_step.enqueue_downstream)
     (simp_all add: d18_s3_def d18_s2_def d18_s1_def d18_s0_def
                    d18_e1_def d18_e2_def initial_exec_state_def
                    exec_label_preserves_history_wf_def history_can_append_def
                    ec_defs)

lemma d18_pending_reachable:
  "dwi_trace (I_relay_labels d18_s0) (dwi_initial (I_relay_labels d18_s0))
     [DoSource ec1 d18_e1, DoSource ec1 d18_e2,
      EnqueueDownstream ec1 d18_e1, EnqueueDownstream ec1 d18_e2]
     d18_s4"
proof -
  have init: "dwi_initial (I_relay_labels d18_s0) = d18_s0"
    by (simp add: I_relay_labels_def)
  have step1:
    "dwi_step (I_relay_labels d18_s0) d18_s0 (DoSource ec1 d18_e1) d18_s1"
    using d18_step_src1 by (simp add: I_relay_labels_def)
  have step2:
    "dwi_step (I_relay_labels d18_s0) d18_s1 (DoSource ec1 d18_e2) d18_s2"
    using d18_step_src2 by (simp add: I_relay_labels_def)
  have step3:
    "dwi_step (I_relay_labels d18_s0) d18_s2
       (EnqueueDownstream ec1 d18_e1) d18_s3"
    using d18_step_enq1 by (simp add: I_relay_labels_def)
  have step4:
    "dwi_step (I_relay_labels d18_s0) d18_s3
       (EnqueueDownstream ec1 d18_e2) d18_s4"
    using d18_step_enq2 by (simp add: I_relay_labels_def)
  show ?thesis
    unfolding init
    by (rule dwi_trace.dwi_trace_step[OF step1],
        rule dwi_trace.dwi_trace_step[OF step2],
        rule dwi_trace.dwi_trace_step[OF step3],
        rule dwi_trace.dwi_trace_step[OF step4],
        rule dwi_trace.dwi_trace_refl)
qed

lemma d18_deliver_first:
  "relay_step d18_s4 (DoDownstream ec1 d18_e1) d18_after_e1"
  unfolding relay_step_def relay_admits_def d18_after_e1_def
  by (intro conjI dw_exec_step.do_downstream)
     (simp_all add: d18_s4_def d18_s3_def d18_s2_def d18_s1_def
                    d18_s0_def d18_e1_def d18_e2_def
                    initial_exec_state_def exec_label_preserves_history_wf_def
                    history_can_append_def relay_history_prefix_def
                    scoped_replay_history_def ec_defs)

lemma d18_cannot_reverse_source_order:
  "\<not> relay_step d18_s4 (DoDownstream ec1 d18_e2) d18_after_e2"
  by (simp add: relay_step_def relay_admits_def
                d18_s4_def d18_after_e2_def d18_s3_def d18_s2_def
                d18_s1_def d18_s0_def d18_e1_def d18_e2_def
                initial_exec_state_def exec_label_preserves_history_wf_def
                history_can_append_def relay_history_prefix_def
                scoped_replay_history_def ec_defs)

lemma d18_deliver_second:
  "relay_step d18_after_e1 (DoDownstream ec1 d18_e2) d18_done"
  unfolding relay_step_def relay_admits_def d18_done_def
  by (intro conjI dw_exec_step.do_downstream)
     (simp_all add: d18_after_e1_def d18_s4_def d18_s3_def d18_s2_def
                    d18_s1_def d18_s0_def d18_e1_def d18_e2_def
                    initial_exec_state_def exec_label_preserves_history_wf_def
                    history_can_append_def relay_history_prefix_def
                    scoped_replay_history_def ec_defs)

lemma d18_tied_occurrences_progress_in_source_order:
  "relay_step d18_s4 (DoDownstream ec1 d18_e1) d18_after_e1
   \<and> \<not> relay_step d18_s4 (DoDownstream ec1 d18_e2) d18_after_e2
   \<and> relay_step d18_after_e1 (DoDownstream ec1 d18_e2) d18_done"
  using d18_deliver_first d18_cannot_reverse_source_order d18_deliver_second
  by blast

lemma d18_first_occurrence_does_not_complete_tied_frontier:
  "\<not> relay_complete_through d18_after_e1 ec1"
  by (simp add: relay_complete_through_def replay_down_hist_def
                d18_after_e1_def d18_s4_def d18_s3_def d18_s2_def
                d18_s1_def d18_s0_def d18_e1_def d18_e2_def
                initial_exec_state_def ec_defs)

lemma d18_both_occurrences_complete_tied_frontier:
  "relay_complete_through d18_done ec1"
  by (simp add: relay_complete_through_def replay_down_hist_def
                d18_done_def d18_after_e1_def d18_s4_def d18_s3_def
                d18_s2_def d18_s1_def d18_s0_def d18_e1_def d18_e2_def
                initial_exec_state_def ec_defs)

end
