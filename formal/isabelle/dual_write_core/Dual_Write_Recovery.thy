(*  Title:       Dual_Write_Recovery.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Recovery-facing facts for the dual-write execution semantics. The existing
    Recover and Observe labels do not reconcile stores; this theory makes that
    non-claim explicit by proving that they preserve the underlying scoped
    mismatch predicate.
*)

theory Dual_Write_Recovery
  imports Dual_Write_Replay_Safety
begin

section \<open>Status-only recovery preserves unreconciled mismatch\<close>

fun recovery_observation_label :: "('k, 'v) dw_exec_label \<Rightarrow> bool" where
  "recovery_observation_label Recover = True"
| "recovery_observation_label (Observe _) = True"
| "recovery_observation_label (DoSource _ _) = False"
| "recovery_observation_label (EnqueueDownstream _ _) = False"
| "recovery_observation_label (DoDownstream _ _) = False"
| "recovery_observation_label (Ack _ _) = False"
| "recovery_observation_label (Crash _) = False"

lemma recovery_observation_step_preserves_proto:
  assumes step: "dw_exec_step s a s'"
      and label: "recovery_observation_label a"
  shows "proto_of_exec_at s' c = proto_of_exec_at s c"
  using step label
  by (cases rule: dw_exec_step.cases) simp_all

theorem recover_preserves_mismatch:
  assumes "dw_exec_step s Recover s'"
  shows
    "mismatch_at (proto_of_exec_at s' c) c k =
     mismatch_at (proto_of_exec_at s c) c k"
  using assms
  by (cases rule: dw_exec_step.cases) simp_all

theorem observe_preserves_mismatch:
  assumes "dw_exec_step s (Observe f) s'"
  shows
    "mismatch_at (proto_of_exec_at s' c) c k =
     mismatch_at (proto_of_exec_at s c) c k"
  using assms
  by (cases rule: dw_exec_step.cases) simp_all

lemma recovery_observation_step_preserves_mismatch:
  assumes step: "dw_exec_step s a s'"
      and label: "recovery_observation_label a"
  shows
    "mismatch_at (proto_of_exec_at s' c) c k =
     mismatch_at (proto_of_exec_at s c) c k"
  using recovery_observation_step_preserves_proto[OF step label]
  by simp

lemma recovery_observation_trace_preserves_proto:
  assumes trace: "dw_exec_trace s xs s'"
      and labels: "list_all recovery_observation_label xs"
  shows "proto_of_exec_at s' c = proto_of_exec_at s c"
  using trace labels
proof (induction rule: dw_exec_trace.induct)
  case (trace_refl s)
  show ?case by simp
next
  case (trace_step s a s' xs s'')
  have label_a: "recovery_observation_label a"
    using trace_step.prems by simp
  have labels_xs: "list_all recovery_observation_label xs"
    using trace_step.prems by simp
  have step_proto: "proto_of_exec_at s' c = proto_of_exec_at s c"
    by (rule recovery_observation_step_preserves_proto
        [OF trace_step.hyps(1) label_a])
  have tail_proto: "proto_of_exec_at s'' c = proto_of_exec_at s' c"
    by (rule trace_step.IH[OF labels_xs])
  from tail_proto step_proto show ?case by simp
qed

theorem no_reconciliation_mismatch_persists:
  assumes trace: "dw_exec_trace s xs s'"
      and labels: "list_all recovery_observation_label xs"
      and mismatch: "mismatch_at (proto_of_exec_at s c) c k"
  shows "mismatch_at (proto_of_exec_at s' c) c k"
  using recovery_observation_trace_preserves_proto[OF trace labels] mismatch
  by simp

corollary no_reconciliation_divergence_persists:
  assumes trace: "dw_exec_trace s xs s'"
      and labels: "list_all recovery_observation_label xs"
      and div: "diverges (proto_of_exec_at s c) c"
  shows "diverges (proto_of_exec_at s' c) c"
  using recovery_observation_trace_preserves_proto[OF trace labels] div
  by simp

lemma recovery_observation_trace_preserves_mismatch_iff:
  assumes trace: "dw_exec_trace s xs s'"
      and labels: "list_all recovery_observation_label xs"
  shows
    "mismatch_at (proto_of_exec_at s' c) c k =
     mismatch_at (proto_of_exec_at s c) c k"
  using recovery_observation_trace_preserves_proto[OF trace labels]
  by simp

lemma downstream_first_stale_update_crashed_has_mismatch:
  "mismatch_at
    (proto_of_exec_at
      (downstream_first_stale_update_down_done
        \<lparr>exec_status := Crashed ec1\<rparr>)
      ec1)
    ec1 0"
  by (simp add: mismatch_at_def proto_of_exec_at_def store2_of_exec_def
                log_image_def restrict_def
                downstream_first_stale_update_initial_def
                downstream_first_stale_update_enqueued_def
                downstream_first_stale_update_down_done_def
                initial_exec_state_def Src_def latest_src_event_def
                Let_def ec_defs)

corollary recovered_state_still_diverges:
  "\<exists>s_crashed s_recovered.
      admissible_dw_exec_trace downstream_first_stale_update_initial
        (separated_completion_bad_crash_labels Downstream_Effect
          downstream_first_stale_update_completion)
        s_crashed
    \<and> admissible_dw_exec_trace downstream_first_stale_update_initial
        (separated_completion_bad_crash_labels Downstream_Effect
          downstream_first_stale_update_completion @ [Recover])
        s_recovered
    \<and> observable_mismatch s_crashed ec1 0
    \<and> \<not> observable_mismatch s_recovered ec1 0
    \<and> exec_status s_recovered = Recovered
    \<and> mismatch_at (proto_of_exec_at s_recovered ec1) ec1 0
    \<and> diverges (proto_of_exec_at s_recovered ec1) ec1"
proof -
  let ?s_crashed =
    "downstream_first_stale_update_down_done
      \<lparr>exec_status := Crashed ec1\<rparr>"
  let ?s_recovered = "?s_crashed\<lparr>exec_status := Recovered\<rparr>"
  have bad_adm:
    "admissible_dw_exec_trace downstream_first_stale_update_initial
      (separated_completion_bad_crash_labels Downstream_Effect
        downstream_first_stale_update_completion)
      ?s_crashed"
    using downstream_first_stale_update_bad_crash_admissible_trace
    by simp
  have wf_crashed: "wellformed_exec_state ?s_crashed"
    by (rule admissible_dw_exec_trace_final_wellformed[OF bad_adm])
  have step: "dw_exec_step ?s_crashed Recover ?s_recovered"
    by (rule dw_exec_step.recover) simp
  have recover_preserves:
    "exec_label_preserves_history_wf ?s_crashed Recover"
    by (simp add: exec_label_preserves_history_wf_def)
  have recover_adm: "admissible_dw_exec_trace ?s_crashed [Recover] ?s_recovered"
    by (rule admissible_dw_exec_trace_single
        [OF step wf_crashed recover_preserves])
  have full_adm:
    "admissible_dw_exec_trace downstream_first_stale_update_initial
      (separated_completion_bad_crash_labels Downstream_Effect
        downstream_first_stale_update_completion @ [Recover])
      ?s_recovered"
    by (rule admissible_dw_exec_trace_append[OF bad_adm recover_adm])
  have trace: "dw_exec_trace ?s_crashed [Recover] ?s_recovered"
    by (rule dw_exec_trace.trace_step[OF step dw_exec_trace.trace_refl])
  have le_fin_crashed: "ec1 \<le> exec_finish ?s_crashed"
    by (simp add: downstream_first_stale_update_initial_def
                  downstream_first_stale_update_enqueued_def
                  downstream_first_stale_update_down_done_def
                  initial_exec_state_def ec_defs)
  have obs_crashed: "observable_mismatch ?s_crashed ec1 0"
    using downstream_first_stale_update_crashed_has_mismatch le_fin_crashed
    by (simp add: observable_mismatch_def)
  have no_obs_recovered: "\<not> observable_mismatch ?s_recovered ec1 0"
    by (simp add: observable_mismatch_def)
  have mismatch: "mismatch_at (proto_of_exec_at ?s_recovered ec1) ec1 0"
    using no_reconciliation_mismatch_persists
        [OF trace _ downstream_first_stale_update_crashed_has_mismatch]
    by simp
  have div: "diverges (proto_of_exec_at ?s_recovered ec1) ec1"
  proof -
    have le_fin: "ec1 \<le> exec_finish ?s_recovered"
      by (simp add: downstream_first_stale_update_initial_def
                    downstream_first_stale_update_enqueued_def
                    downstream_first_stale_update_down_done_def
                    initial_exec_state_def ec_defs)
    from le_fin mismatch show ?thesis
      by (auto simp: diverges_iff_mismatch_at proto_of_exec_at_def)
  qed
  from bad_adm full_adm obs_crashed no_obs_recovered mismatch div show ?thesis
    by (intro exI[where x = ?s_crashed] exI[where x = ?s_recovered]) simp
qed

lemma downstream_first_stale_update_completion_heals_mismatch:
  "\<not> mismatch_at (proto_of_exec_at downstream_first_stale_update_acked ec3) ec3 0"
  by (simp add: mismatch_at_def proto_of_exec_at_def store2_of_exec_def
                log_image_def restrict_def
                downstream_first_stale_update_initial_def
                downstream_first_stale_update_enqueued_def
                downstream_first_stale_update_down_done_def
                downstream_first_stale_update_source_done_def
                downstream_first_stale_update_acked_def
                initial_exec_state_def Src_def latest_src_event_def
                Let_def ec_defs)

lemma downstream_first_stale_update_down_done_has_boundary_mismatch:
  "mismatch_at (proto_of_exec_at downstream_first_stale_update_down_done ec3)
    ec3 0"
  by (simp add: mismatch_at_def proto_of_exec_at_def store2_of_exec_def
                log_image_def restrict_def
                downstream_first_stale_update_initial_def
                downstream_first_stale_update_enqueued_def
                downstream_first_stale_update_down_done_def
                initial_exec_state_def Src_def latest_src_event_def
                Let_def ec_defs)

corollary source_catchup_can_heal_downstream_first_mismatch:
  "\<exists>s_healed.
      dw_exec_trace
        downstream_first_stale_update_down_done
        [DoSource ec3 (Update 0 2), Ack ec3 (Update 0 2)] s_healed
    \<and> mismatch_at
        (proto_of_exec_at downstream_first_stale_update_down_done ec3)
        ec3 0
    \<and> \<not> mismatch_at (proto_of_exec_at s_healed ec3) ec3 0"
proof -
  have trace:
    "dw_exec_trace
      downstream_first_stale_update_down_done
      [DoSource ec3 (Update 0 2), Ack ec3 (Update 0 2)]
      downstream_first_stale_update_acked"
  proof -
    have source:
      "dw_exec_step downstream_first_stale_update_down_done
        (DoSource ec3 (Update 0 2))
        downstream_first_stale_update_source_done"
      unfolding downstream_first_stale_update_source_done_def
      by (rule dw_exec_step.do_source)
         (simp add: downstream_first_stale_update_initial_def
                    downstream_first_stale_update_enqueued_def
                    downstream_first_stale_update_down_done_def
                    initial_exec_state_def)
    have ack:
      "dw_exec_step downstream_first_stale_update_source_done
        (Ack ec3 (Update 0 2))
        downstream_first_stale_update_acked"
      unfolding downstream_first_stale_update_acked_def
      by (rule dw_exec_step.ack)
         (simp_all add: downstream_first_stale_update_initial_def
                        downstream_first_stale_update_enqueued_def
                        downstream_first_stale_update_down_done_def
                        downstream_first_stale_update_source_done_def
                        initial_exec_state_def)
    show ?thesis
      by (rule dw_exec_trace.trace_step
          [OF source dw_exec_trace.trace_step[OF ack dw_exec_trace.trace_refl]])
  qed
  from trace downstream_first_stale_update_down_done_has_boundary_mismatch
    downstream_first_stale_update_completion_heals_mismatch
  show ?thesis
    by blast
qed

lemma source_first_stale_update_pending_has_mismatch:
  "mismatch_at (proto_of_exec_at (plan_after_enqueue_state stale_update_plan) ec3)
    ec3 0"
  by (simp add: mismatch_at_def proto_of_exec_at_def store2_of_exec_def
                log_image_def restrict_def stale_update_plan_def
                plan_after_enqueue_state_def plan_after_ack_state_def
                plan_after_source_state_def plan_prefix_state_def
                initial_exec_state_def Src_def latest_src_event_def
                Let_def ec_defs)

lemma source_first_stale_update_downstream_done_no_boundary_mismatch:
  "\<not> mismatch_at
    (proto_of_exec_at
      ((plan_after_enqueue_state stale_update_plan)
        \<lparr>exec_down_hist :=
           exec_down_hist (plan_after_enqueue_state stale_update_plan)
             @ [(ec3, Update 0 2)],
         exec_pending :=
           exec_pending (plan_after_enqueue_state stale_update_plan)
             - {(ec3, Update 0 2)}\<rparr>)
      ec3)
    ec3 0"
  by (simp add: mismatch_at_def proto_of_exec_at_def store2_of_exec_def
                log_image_def restrict_def stale_update_plan_def
                plan_after_enqueue_state_def plan_after_ack_state_def
                plan_after_source_state_def plan_prefix_state_def
                initial_exec_state_def Src_def latest_src_event_def
                Let_def ec_defs)

corollary downstream_step_can_heal_source_first_mismatch:
  "\<exists>s_healed.
      dw_exec_trace
        (plan_after_enqueue_state stale_update_plan)
        [DoDownstream ec3 (Update 0 2)] s_healed
    \<and> mismatch_at
        (proto_of_exec_at (plan_after_enqueue_state stale_update_plan) ec3)
        ec3 0
    \<and> \<not> mismatch_at (proto_of_exec_at s_healed ec3) ec3 0"
proof -
  let ?s0 = "plan_after_enqueue_state stale_update_plan"
  let ?s_healed =
    "?s0\<lparr>exec_down_hist := exec_down_hist ?s0 @ [(ec3, Update 0 2)],
        exec_pending := exec_pending ?s0 - {(ec3, Update 0 2)}\<rparr>"
  have step: "dw_exec_step ?s0 (DoDownstream ec3 (Update 0 2)) ?s_healed"
    by (rule dw_exec_step.do_downstream)
       (simp_all add: stale_update_plan_def plan_after_enqueue_state_def
                      plan_after_ack_state_def plan_after_source_state_def
                      plan_prefix_state_def initial_exec_state_def)
  have trace: "dw_exec_trace ?s0 [DoDownstream ec3 (Update 0 2)] ?s_healed"
    by (rule dw_exec_trace.trace_step[OF step dw_exec_trace.trace_refl])
  from trace source_first_stale_update_pending_has_mismatch
    source_first_stale_update_downstream_done_no_boundary_mismatch
  show ?thesis
    by blast
qed

lemma recovered_cannot_do_downstream:
  assumes "exec_status s = Recovered"
  shows "\<not> dw_exec_step s (DoDownstream c e) s'"
  using assms by (auto elim: dw_exec_step.cases)

lemma recovered_cannot_do_source:
  assumes "exec_status s = Recovered"
  shows "\<not> dw_exec_step s (DoSource c e) s'"
  using assms by (auto elim: dw_exec_step.cases)


section \<open>Recovery-mode reconciliation repairs the downstream image\<close>

text \<open>
  The ordinary \<open>Recover\<close> transition is status-only.  A post-crash repair must
  be an explicit reconciliation action: the downstream durable image is made to
  match the committed source history, and any in-flight downstream work is no
  longer pending.
\<close>

definition recovery_reconciled_state
  :: "('k, 'v) dw_exec_state \<Rightarrow> ('k, 'v) dw_exec_state"
where
  "recovery_reconciled_state s =
     s\<lparr>exec_down_hist := exec_src_hist s,
       exec_pending := {},
       exec_status := Recovered\<rparr>"

inductive recovery_reconcile_step
  :: "('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  reconcile_from_crash:
    "\<lbrakk>exec_status s = Crashed c; f \<le> exec_finish s\<rbrakk> \<Longrightarrow>
     recovery_reconcile_step s f (recovery_reconciled_state s)"
| reconcile_from_recovered:
    "\<lbrakk>exec_status s = Recovered; f \<le> exec_finish s\<rbrakk> \<Longrightarrow>
     recovery_reconcile_step s f (recovery_reconciled_state s)"

lemma recovery_reconcile_step_eq:
  assumes "recovery_reconcile_step s f s'"
  shows "s' = recovery_reconciled_state s"
  using assms by (cases rule: recovery_reconcile_step.cases) simp_all

lemma recovery_reconcile_step_status:
  assumes "recovery_reconcile_step s f s'"
  shows "exec_status s' = Recovered"
  using recovery_reconcile_step_eq[OF assms]
  by (simp add: recovery_reconciled_state_def)

lemma recovery_reconcile_step_finish:
  assumes "recovery_reconcile_step s f s'"
  shows "exec_finish s' = exec_finish s"
  using recovery_reconcile_step_eq[OF assms]
  by (simp add: recovery_reconciled_state_def)

lemma recovery_reconcile_step_frontier_le_finish:
  assumes "recovery_reconcile_step s f s'"
  shows "f \<le> exec_finish s'"
  using assms recovery_reconcile_step_finish[OF assms]
  by (cases rule: recovery_reconcile_step.cases) simp_all

lemma recovery_reconciled_state_wellformed:
  assumes "wellformed_exec_state s"
  shows "wellformed_exec_state (recovery_reconciled_state s)"
  using assms
  by (auto simp: recovery_reconciled_state_def wellformed_exec_state_def
                 exec_histories_wellformed_def
                 pending_enqueued_consistent_def
                 acked_source_consistent_def)

theorem recovery_reconcile_step_wellformed:
  assumes step: "recovery_reconcile_step s f s'"
      and wf: "wellformed_exec_state s"
  shows "wellformed_exec_state s'"
  using recovery_reconcile_step_eq[OF step]
    recovery_reconciled_state_wellformed[OF wf]
  by simp

theorem recovery_reconcile_step_no_mismatch:
  assumes step: "recovery_reconcile_step s f s'"
  shows "\<forall>k. \<not> mismatch_at (proto_of_exec_at s' f) f k"
  using recovery_reconcile_step_eq[OF step]
  by (auto simp: recovery_reconciled_state_def mismatch_at_def
                 proto_of_exec_at_def store2_of_exec_def log_image_def
                 restrict_def)

corollary recovery_reconcile_step_no_divergence:
  assumes step: "recovery_reconcile_step s f s'"
  shows "\<not> diverges (proto_of_exec_at s' f) f"
  using recovery_reconcile_step_no_mismatch[OF step]
  by (auto simp: diverges_iff_mismatch_at)

theorem recovery_reconcile_step_no_observable_mismatch:
  assumes step: "recovery_reconcile_step s f s'"
  shows "\<not> observable_mismatch (s'\<lparr>exec_status := Crashed f\<rparr>) f k"
proof -
  have "\<not> mismatch_at (proto_of_exec_at s' f) f k"
    using recovery_reconcile_step_no_mismatch[OF step] by blast
  thus ?thesis
    by (simp add: observable_mismatch_def)
qed

corollary recovery_reconcile_step_status_not_observable:
  assumes step: "recovery_reconcile_step s f s'"
  shows "\<not> observable_mismatch s' f k"
  using recovery_reconcile_step_status[OF step]
  by (simp add: observable_mismatch_def)

theorem reconciled_exec_state_cdc_replay_derived_at:
  assumes wf: "wellformed_src_history (exec_src_hist s)"
      and base: "exec_base s = (\<lambda>_. None)"
      and reconciled: "exec_down_hist s = exec_src_hist s"
  shows
    "cdc_only (cdc_replay_prefix (proto_of_exec_at s f) f)
    \<and> execution_replay_derived_at s
      (cdc_replay_prefix (proto_of_exec_at s f) f) f"
proof -
  let ?P = "proto_of_exec_at s f"
  let ?sigma = "cdc_replay_prefix ?P f"
  have wfP: "wellformed_src_history (psrc ?P)"
    using wf by (simp add: proto_of_exec_at_def)
  have baseP: "pbase ?P = (\<lambda>_. None)"
    using base by (simp add: proto_of_exec_at_def)
  have seg: "cdc_segment_between (psrc ?P) (pscope ?P) c0 f ?sigma"
    by (rule cdc_replay_prefix_segment)
  have cut0:
    "virtual_cut_state (\<lambda>_. None) ?sigma (pscope ?P) f (psrc ?P)"
    using virtual_cut_certifies_outbox[OF wfP seg] by blast
  have cutP:
    "virtual_cut_state (pbase ?P) ?sigma (pscope ?P) f (psrc ?P)"
    using cut0 baseP by simp
  have storeP: "s2 ?P f = restrict (Apply ?sigma) (pscope ?P)"
    using cut0 base reconciled
    by (simp add: virtual_cut_state_def proto_of_exec_at_def
                  store2_of_exec_def)
  have derived: "replay_derived_at ?P ?sigma f"
    using cutP storeP by (simp add: replay_derived_at_def)
  have cdc: "cdc_only ?sigma"
    by (rule cdc_replay_prefix_cdc_only)
  from cdc derived show ?thesis
    by (simp add: execution_replay_derived_at_def)
qed

lemma recovery_reconciled_state_cdc_prefix_store:
  assumes wf: "wellformed_src_history (exec_src_hist s)"
      and base: "exec_base s = (\<lambda>_. None)"
  shows
    "s2 (proto_of_exec_at (recovery_reconciled_state s) f) f =
      restrict
        (Apply
          (cdc_replay_prefix
            (proto_of_exec_at (recovery_reconciled_state s) f) f))
        (pscope (proto_of_exec_at (recovery_reconciled_state s) f))"
proof -
  let ?P = "proto_of_exec_at (recovery_reconciled_state s) f"
  have wfP: "wellformed_src_history (psrc ?P)"
    using wf by (simp add: proto_of_exec_at_def
                           recovery_reconciled_state_def)
  have seg:
    "cdc_segment_between (psrc ?P) (pscope ?P) c0 f
      (cdc_replay_prefix ?P f)"
    by (rule cdc_replay_prefix_segment)
  have cut:
    "virtual_cut_state (\<lambda>_. None) (cdc_replay_prefix ?P f)
      (pscope ?P) f (psrc ?P)"
    using virtual_cut_certifies_outbox[OF wfP seg] by blast
  show ?thesis
    using cut base
    by (simp add: virtual_cut_state_def recovery_reconciled_state_def
                  proto_of_exec_at_def store2_of_exec_def)
qed

theorem recovery_reconciled_state_execution_replay_derived_at:
  assumes wf: "wellformed_src_history (exec_src_hist s)"
      and base: "exec_base s = (\<lambda>_. None)"
  shows
    "cdc_only
      (cdc_replay_prefix
        (proto_of_exec_at (recovery_reconciled_state s) f) f)
    \<and> execution_replay_derived_at (recovery_reconciled_state s)
      (cdc_replay_prefix
        (proto_of_exec_at (recovery_reconciled_state s) f) f)
      f"
  by (rule reconciled_exec_state_cdc_replay_derived_at)
     (simp_all add: wf base recovery_reconciled_state_def)

corollary recovery_reconcile_step_execution_replay_derived_at:
  assumes step: "recovery_reconcile_step s f s'"
      and wf: "wellformed_src_history (exec_src_hist s)"
      and base: "exec_base s = (\<lambda>_. None)"
  shows
    "cdc_only (cdc_replay_prefix (proto_of_exec_at s' f) f)
    \<and> execution_replay_derived_at s'
      (cdc_replay_prefix (proto_of_exec_at s' f) f) f"
proof -
  have s': "s' = recovery_reconciled_state s"
    by (rule recovery_reconcile_step_eq[OF step])
  show ?thesis
    using recovery_reconciled_state_execution_replay_derived_at[OF wf base, of f]
      s'
    by simp
qed

corollary recovery_reconcile_step_cdc_prefix_no_observable_mismatch:
  assumes step: "recovery_reconcile_step s f s'"
      and wf: "wellformed_src_history (exec_src_hist s)"
      and base: "exec_base s = (\<lambda>_. None)"
  shows "\<not> observable_mismatch (s'\<lparr>exec_status := Crashed f\<rparr>) f k"
proof -
  have derived:
    "execution_replay_derived_at s'
      (cdc_replay_prefix (proto_of_exec_at s' f) f) f"
    using recovery_reconcile_step_execution_replay_derived_at[OF step wf base]
    by blast
  show ?thesis
    by (rule execution_replay_derived_at_no_observable_mismatch
        [OF derived recovery_reconcile_step_frontier_le_finish[OF step]])
qed

corollary recovered_mismatch_reconciliation_witness:
  "\<exists>s_recovered s_repaired.
      admissible_dw_exec_trace downstream_first_stale_update_initial
        (separated_completion_bad_crash_labels Downstream_Effect
          downstream_first_stale_update_completion @ [Recover])
        s_recovered
    \<and> exec_status s_recovered = Recovered
    \<and> mismatch_at (proto_of_exec_at s_recovered ec1) ec1 0
    \<and> diverges (proto_of_exec_at s_recovered ec1) ec1
    \<and> recovery_reconcile_step s_recovered ec1 s_repaired
    \<and> exec_status s_repaired = Recovered
    \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at s_repaired ec1) ec1 k)
    \<and> \<not> diverges (proto_of_exec_at s_repaired ec1) ec1"
proof -
  from recovered_state_still_diverges obtain s_crashed s_recovered
    where trace:
      "admissible_dw_exec_trace downstream_first_stale_update_initial
        (separated_completion_bad_crash_labels Downstream_Effect
          downstream_first_stale_update_completion @ [Recover])
        s_recovered"
      and status: "exec_status s_recovered = Recovered"
      and mismatch:
        "mismatch_at (proto_of_exec_at s_recovered ec1) ec1 0"
      and div: "diverges (proto_of_exec_at s_recovered ec1) ec1"
    by blast
  have le_fin: "ec1 \<le> exec_finish s_recovered"
    using div by (simp add: diverges_iff_mismatch_at proto_of_exec_at_def)
  let ?s_repaired = "recovery_reconciled_state s_recovered"
  have step: "recovery_reconcile_step s_recovered ec1 ?s_repaired"
    by (rule recovery_reconcile_step.reconcile_from_recovered[OF status le_fin])
  have repaired_status: "exec_status ?s_repaired = Recovered"
    by (rule recovery_reconcile_step_status[OF step])
  have no_mismatch:
    "\<forall>k. \<not> mismatch_at (proto_of_exec_at ?s_repaired ec1) ec1 k"
    by (rule recovery_reconcile_step_no_mismatch[OF step])
  have no_div: "\<not> diverges (proto_of_exec_at ?s_repaired ec1) ec1"
    by (rule recovery_reconcile_step_no_divergence[OF step])
  from trace status mismatch div step repaired_status no_mismatch no_div
  show ?thesis
    by blast
qed

corollary recovered_mismatch_reconciliation_changes_downstream_value:
  "\<exists>s_recovered s_repaired.
      admissible_dw_exec_trace downstream_first_stale_update_initial
        (separated_completion_bad_crash_labels Downstream_Effect
          downstream_first_stale_update_completion @ [Recover])
        s_recovered
    \<and> recovery_reconcile_step s_recovered ec1 s_repaired
    \<and> store2_of_exec s_recovered ec1 0 = Some 2
    \<and> store2_of_exec s_repaired ec1 0 = Some 1
    \<and> store2_of_exec s_recovered ec1 0 \<noteq>
        store2_of_exec s_repaired ec1 0"
proof -
  let ?s_crashed =
    "downstream_first_stale_update_down_done
      \<lparr>exec_status := Crashed ec1\<rparr>"
  let ?s_recovered = "?s_crashed\<lparr>exec_status := Recovered\<rparr>"
  let ?s_repaired = "recovery_reconciled_state ?s_recovered"
  have trace:
    "admissible_dw_exec_trace downstream_first_stale_update_initial
      (separated_completion_bad_crash_labels Downstream_Effect
        downstream_first_stale_update_completion @ [Recover])
      ?s_recovered"
  proof -
    have bad_adm:
      "admissible_dw_exec_trace downstream_first_stale_update_initial
        (separated_completion_bad_crash_labels Downstream_Effect
          downstream_first_stale_update_completion)
        ?s_crashed"
      using downstream_first_stale_update_bad_crash_admissible_trace
      by simp
    have wf_crashed: "wellformed_exec_state ?s_crashed"
      by (rule admissible_dw_exec_trace_final_wellformed[OF bad_adm])
    have step_recover: "dw_exec_step ?s_crashed Recover ?s_recovered"
      by (rule dw_exec_step.recover) simp
    have recover_preserves:
      "exec_label_preserves_history_wf ?s_crashed Recover"
      by (simp add: exec_label_preserves_history_wf_def)
    have recover_adm:
      "admissible_dw_exec_trace ?s_crashed [Recover] ?s_recovered"
      by (rule admissible_dw_exec_trace_single
          [OF step_recover wf_crashed recover_preserves])
    show ?thesis
      by (rule admissible_dw_exec_trace_append[OF bad_adm recover_adm])
  qed
  have status: "exec_status ?s_recovered = Recovered" by simp
  have le_fin: "ec1 \<le> exec_finish ?s_recovered"
    by (simp add: downstream_first_stale_update_initial_def
                  downstream_first_stale_update_enqueued_def
                  downstream_first_stale_update_down_done_def
                  initial_exec_state_def ec_defs)
  have step: "recovery_reconcile_step ?s_recovered ec1 ?s_repaired"
    by (rule recovery_reconcile_step.reconcile_from_recovered[OF status le_fin])
  have before: "store2_of_exec ?s_recovered ec1 0 = Some 2"
    by (simp add: store2_of_exec_def
                  downstream_first_stale_update_initial_def
                  downstream_first_stale_update_enqueued_def
                  downstream_first_stale_update_down_done_def
                  initial_exec_state_def Src_def latest_src_event_def
                  Let_def ec_defs)
  have after: "store2_of_exec ?s_repaired ec1 0 = Some 1"
    by (simp add: recovery_reconciled_state_def store2_of_exec_def
                  downstream_first_stale_update_initial_def
                  downstream_first_stale_update_enqueued_def
                  downstream_first_stale_update_down_done_def
                  initial_exec_state_def Src_def latest_src_event_def
                  Let_def ec_defs)
  have changed:
    "store2_of_exec ?s_recovered ec1 0 \<noteq>
     store2_of_exec ?s_repaired ec1 0"
    using before after by simp
  from trace step before after changed show ?thesis
    by (intro exI[where x = ?s_recovered] exI[where x = ?s_repaired])
       simp
qed

definition recovery_source_first_empty_crashed :: "(nat, nat) dw_exec_state" where
  "recovery_source_first_empty_crashed =
     source_crashed_state (\<lambda>(_::nat). None) {0::nat} ec1 ec1
       (Insert (0::nat) (2::nat))"

definition recovery_source_first_empty_recovered :: "(nat, nat) dw_exec_state" where
  "recovery_source_first_empty_recovered =
     recovery_source_first_empty_crashed\<lparr>exec_status := Recovered\<rparr>"

definition recovery_source_first_empty_repaired :: "(nat, nat) dw_exec_state" where
  "recovery_source_first_empty_repaired =
     recovery_reconciled_state recovery_source_first_empty_recovered"

lemma recovery_source_first_empty_recovered_trace:
  "dw_exec_trace
    (initial_exec_state (\<lambda>(_::nat). None) {0::nat} ec1)
    [DoSource ec1 (Insert (0::nat) (2::nat)),
     Ack ec1 (Insert (0::nat) (2::nat)), Crash ec1, Recover]
    recovery_source_first_empty_recovered"
proof -
  let ?b = "(\<lambda>(_::nat). None)"
  let ?K = "{0::nat}"
  let ?e = "Insert (0::nat) (2::nat)"
  let ?s0 = "initial_exec_state ?b ?K ec1"
  let ?s1 = "after_source_state ?b ?K ec1 ec1 ?e"
  let ?s2 = "after_source_ack_state ?b ?K ec1 ec1 ?e"
  let ?s3 = "recovery_source_first_empty_crashed"
  have step1: "dw_exec_step ?s0 (DoSource ec1 ?e) ?s1"
  proof -
    have raw:
      "dw_exec_step ?s0 (DoSource ec1 ?e)
        (?s0\<lparr>exec_src_hist := exec_src_hist ?s0 @ [(ec1, ?e)]\<rparr>)"
      by (rule dw_exec_step.do_source) (simp add: initial_exec_state_def)
    thus ?thesis
      by (simp add: after_source_state_def initial_exec_state_def)
  qed
  have step2: "dw_exec_step ?s1 (Ack ec1 ?e) ?s2"
  proof -
    have raw:
      "dw_exec_step ?s1 (Ack ec1 ?e)
        (?s1\<lparr>exec_acked := exec_acked ?s1 @ [(ec1, ?e)]\<rparr>)"
      by (rule dw_exec_step.ack)
         (simp_all add: after_source_state_def initial_exec_state_def)
    thus ?thesis
      by (simp add: after_source_ack_state_def after_source_state_def
                    initial_exec_state_def)
  qed
  have step3: "dw_exec_step ?s2 (Crash ec1) ?s3"
    unfolding recovery_source_first_empty_crashed_def source_crashed_state_def
    by (rule dw_exec_step.crash)
       (simp add: after_source_ack_state_def after_source_state_def
                  initial_exec_state_def)
  have step4: "dw_exec_step ?s3 Recover recovery_source_first_empty_recovered"
    unfolding recovery_source_first_empty_recovered_def
    by (rule dw_exec_step.recover)
       (simp add: recovery_source_first_empty_crashed_def
                  source_crashed_state_def)
  show ?thesis
    by (rule dw_exec_trace.trace_step[OF step1],
        rule dw_exec_trace.trace_step[OF step2],
        rule dw_exec_trace.trace_step[OF step3],
        rule dw_exec_trace.trace_step[OF step4],
        rule dw_exec_trace.trace_refl)
qed

lemma recovery_source_first_empty_recovered_has_mismatch:
  "mismatch_at
    (proto_of_exec_at recovery_source_first_empty_recovered ec1) ec1 0"
  by (simp add: mismatch_at_def proto_of_exec_at_def store2_of_exec_def
                log_image_def restrict_def recovery_source_first_empty_recovered_def
                recovery_source_first_empty_crashed_def source_crashed_state_def
                after_source_ack_state_def after_source_state_def
                initial_exec_state_def Src_single_event_at_key)

lemma recovery_source_first_empty_repaired_prefix_nonempty:
  "cdc_replay_prefix
    (proto_of_exec_at recovery_source_first_empty_repaired ec1) ec1 =
    [Cdc ec1 (Insert 0 2)]"
  by (simp add: cdc_replay_prefix_def cdc_lift_def
                recovery_source_first_empty_repaired_def
                recovery_reconciled_state_def
                recovery_source_first_empty_recovered_def
                recovery_source_first_empty_crashed_def source_crashed_state_def
                after_source_ack_state_def after_source_state_def
                initial_exec_state_def proto_of_exec_at_def ec_defs)

lemma recovery_source_first_empty_repaired_replay_derived:
  "cdc_only
    (cdc_replay_prefix
      (proto_of_exec_at recovery_source_first_empty_repaired ec1) ec1)
  \<and> execution_replay_derived_at recovery_source_first_empty_repaired
    (cdc_replay_prefix
      (proto_of_exec_at recovery_source_first_empty_repaired ec1) ec1)
    ec1"
  unfolding recovery_source_first_empty_repaired_def
  by (rule recovery_reconciled_state_execution_replay_derived_at)
     (simp_all add: recovery_source_first_empty_recovered_def
                    recovery_source_first_empty_crashed_def
                    source_crashed_state_def after_source_ack_state_def
                    after_source_state_def initial_exec_state_def
                    wellformed_src_history_def ec_defs)

lemma recovery_source_first_empty_repair_changes_downstream_value:
  "store2_of_exec recovery_source_first_empty_recovered ec1 0 = None
   \<and> store2_of_exec recovery_source_first_empty_repaired ec1 0 = Some 2"
  by (simp add: store2_of_exec_def recovery_source_first_empty_repaired_def
                recovery_reconciled_state_def
                recovery_source_first_empty_recovered_def
                recovery_source_first_empty_crashed_def source_crashed_state_def
                after_source_ack_state_def after_source_state_def
                initial_exec_state_def Src_single_event_at_key)

corollary source_first_nonempty_replay_reconciliation_witness:
  "\<exists>s_recovered s_repaired \<sigma>.
      dw_exec_trace
        (initial_exec_state (\<lambda>(_::nat). None) {0::nat} ec1)
        [DoSource ec1 (Insert (0::nat) (2::nat)),
         Ack ec1 (Insert (0::nat) (2::nat)),
         Crash ec1, Recover]
        s_recovered
    \<and> exec_status s_recovered = Recovered
    \<and> 0 \<in> exec_scope s_recovered
    \<and> mismatch_at (proto_of_exec_at s_recovered ec1) ec1 0
    \<and> recovery_reconcile_step s_recovered ec1 s_repaired
    \<and> \<sigma> = cdc_replay_prefix (proto_of_exec_at s_repaired ec1) ec1
    \<and> \<sigma> \<noteq> []
    \<and> cdc_only \<sigma>
    \<and> execution_replay_derived_at s_repaired \<sigma> ec1
    \<and> store2_of_exec s_recovered ec1 0 \<noteq>
        store2_of_exec s_repaired ec1 0
    \<and> \<not> mismatch_at (proto_of_exec_at s_repaired ec1) ec1 0"
proof -
  let ?s_recovered = recovery_source_first_empty_recovered
  let ?s_repaired = recovery_source_first_empty_repaired
  let ?sigma = "cdc_replay_prefix (proto_of_exec_at ?s_repaired ec1) ec1"
  have status: "exec_status ?s_recovered = Recovered"
    by (simp add: recovery_source_first_empty_recovered_def)
  have le_fin: "ec1 \<le> exec_finish ?s_recovered"
    by (simp add: recovery_source_first_empty_recovered_def
                  recovery_source_first_empty_crashed_def source_crashed_state_def
                  after_source_ack_state_def after_source_state_def
                  initial_exec_state_def)
  have step: "recovery_reconcile_step ?s_recovered ec1 ?s_repaired"
    unfolding recovery_source_first_empty_repaired_def
    by (rule recovery_reconcile_step.reconcile_from_recovered[OF status le_fin])
  have nonempty: "?sigma \<noteq> []"
    by (simp add: recovery_source_first_empty_repaired_prefix_nonempty)
  have replay:
    "cdc_only ?sigma
     \<and> execution_replay_derived_at ?s_repaired ?sigma ec1"
    by (rule recovery_source_first_empty_repaired_replay_derived)
  have changed:
    "store2_of_exec ?s_recovered ec1 0 \<noteq>
     store2_of_exec ?s_repaired ec1 0"
    using recovery_source_first_empty_repair_changes_downstream_value by simp
  have no_mismatch:
    "\<not> mismatch_at (proto_of_exec_at ?s_repaired ec1) ec1 0"
    using recovery_reconcile_step_no_mismatch[OF step] by blast
  have scoped: "0 \<in> exec_scope ?s_recovered"
    by (simp add: recovery_source_first_empty_recovered_def
                  recovery_source_first_empty_crashed_def
                  source_crashed_state_def after_source_ack_state_def
                  after_source_state_def initial_exec_state_def)
  from recovery_source_first_empty_recovered_trace status scoped
    recovery_source_first_empty_recovered_has_mismatch step nonempty replay
    changed no_mismatch
  show ?thesis
    by blast
qed


section \<open>Temporal convergence requires reconciliation delivery to remain reachable\<close>

datatype ('k, 'v) recovery_temporal_action =
    Recovery_Label "('k, 'v) dw_exec_label"
  | Recovery_Reconcile frontier

inductive recovery_temporal_trace
  :: "('k, 'v) dw_exec_state \<Rightarrow>
      ('k, 'v) recovery_temporal_action list \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  recovery_temporal_refl:
    "recovery_temporal_trace s [] s"
| recovery_temporal_label_step:
    "\<lbrakk>dw_exec_step s a s';
      recovery_temporal_trace s' as s''\<rbrakk> \<Longrightarrow>
     recovery_temporal_trace s (Recovery_Label a # as) s''"
| recovery_temporal_reconcile_step:
    "\<lbrakk>recovery_reconcile_step s f s';
      recovery_temporal_trace s' as s''\<rbrakk> \<Longrightarrow>
     recovery_temporal_trace s (Recovery_Reconcile f # as) s''"

lemma recovery_temporal_trace_append:
  assumes first: "recovery_temporal_trace s as s'"
      and second: "recovery_temporal_trace s' bs s''"
  shows "recovery_temporal_trace s (as @ bs) s''"
  using first second
proof (induction arbitrary: bs s'' rule: recovery_temporal_trace.induct)
  case (recovery_temporal_refl s)
  thus ?case by simp
next
  case (recovery_temporal_label_step s a s' as s'')
  thus ?case
    by (auto intro: recovery_temporal_trace.recovery_temporal_label_step)
next
  case (recovery_temporal_reconcile_step s f s' as s'')
  thus ?case
    by (auto intro: recovery_temporal_trace.recovery_temporal_reconcile_step)
qed

lemma dw_exec_trace_imp_recovery_temporal_trace:
  assumes "dw_exec_trace s xs s'"
  shows
    "recovery_temporal_trace s (map Recovery_Label xs) s'"
  using assms
proof (induction rule: dw_exec_trace.induct)
  case (trace_refl s)
  show ?case by (simp add: recovery_temporal_trace.recovery_temporal_refl)
next
  case (trace_step s a s' xs s'')
  have "recovery_temporal_trace s (Recovery_Label a # map Recovery_Label xs) s''"
    by (rule recovery_temporal_trace.recovery_temporal_label_step
        [OF trace_step.hyps(1) trace_step.IH])
  thus ?case by simp
qed

definition no_permanent_recovery_loss
  :: "('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow> bool"
where
  "no_permanent_recovery_loss s f \<longleftrightarrow>
     (\<exists>wait s_wait s_repaired.
        list_all recovery_observation_label wait
      \<and> dw_exec_trace s wait s_wait
      \<and> recovery_reconcile_step s_wait f s_repaired)"

definition recovery_delivery_reachable
  :: "(('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow>
        ('k, 'v) dw_exec_state \<Rightarrow> bool) \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow> bool"
where
  "recovery_delivery_reachable R s f \<longleftrightarrow>
     (\<exists>wait s_wait s_done.
        list_all recovery_observation_label wait
      \<and> dw_exec_trace s wait s_wait
      \<and> R s_wait f s_done)"

text \<open>
  Both predicates above are POSSIBILITY-form: each asserts the existence
  of one finite observation-only waiting prefix after which the repair
  (reconciliation delivery) is enabled --- repair remains REACHABLE.
  Neither states fairness liveness: this finite-trace model makes no
  eventually-on-every-fair-run claim, and a run may defer reconciliation
  indefinitely without falsifying either predicate.  The results below
  consume them on this honest reading.
\<close>

definition recovery_reconcile_delivery
  :: "('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "recovery_reconcile_delivery s f s' \<longleftrightarrow>
     recovery_reconcile_step s f s'"

lemma no_permanent_recovery_loss_iff_recovery_delivery_reachable:
  "no_permanent_recovery_loss s f \<longleftrightarrow>
   recovery_delivery_reachable recovery_reconcile_delivery s f"
  by (auto simp: no_permanent_recovery_loss_def
                 recovery_delivery_reachable_def
                 recovery_reconcile_delivery_def)

definition source_image_equiv_on
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k set \<Rightarrow> frontier \<Rightarrow>
      ('k, 'v) src_history \<Rightarrow> ('k, 'v) src_history \<Rightarrow> bool"
where
  "source_image_equiv_on b K f H D \<longleftrightarrow>
     restrict (Src b D f) K = restrict (Src b H f) K"

definition recovery_redelivers_source_history
  :: "('k, 'v) dw_exec_state \<Rightarrow> ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "recovery_redelivers_source_history s s' \<longleftrightarrow>
     exec_base s' = exec_base s
   \<and> exec_scope s' = exec_scope s
   \<and> exec_finish s' = exec_finish s
   \<and> exec_src_hist s' = exec_src_hist s
   \<and> exec_acked s' = exec_acked s
   \<and> exec_enqueued s' = exec_enqueued s
   \<and> exec_down_hist s' = exec_src_hist s
   \<and> exec_pending s' = {}
   \<and> exec_status s' = Recovered"

definition recovery_effectively_redelivers_source_history_at
  :: "('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "recovery_effectively_redelivers_source_history_at s f s' \<longleftrightarrow>
     exec_base s' = exec_base s
   \<and> exec_scope s' = exec_scope s
   \<and> exec_finish s' = exec_finish s
   \<and> exec_src_hist s' = exec_src_hist s
   \<and> exec_acked s' = exec_acked s
   \<and> exec_enqueued s' = exec_enqueued s
   \<and> exec_pending s' = {}
   \<and> exec_status s' = Recovered
   \<and> source_image_equiv_on (exec_base s) (exec_scope s) f
        (exec_src_hist s) (exec_down_hist s')"

lemma recovery_reconcile_step_redelivers:
  assumes step: "recovery_reconcile_step s f s'"
  shows "recovery_redelivers_source_history s s'"
  using recovery_reconcile_step_eq[OF step]
  by (simp add: recovery_redelivers_source_history_def
                recovery_reconciled_state_def)

lemma recovery_redelivers_source_history_imp_effective_at:
  assumes redelivery: "recovery_redelivers_source_history s s'"
  shows "recovery_effectively_redelivers_source_history_at s f s'"
  using redelivery
  by (auto simp: recovery_redelivers_source_history_def
                 recovery_effectively_redelivers_source_history_at_def
                 source_image_equiv_on_def)

theorem recovery_effective_redelivery_no_mismatch:
  assumes redelivery: "recovery_effectively_redelivers_source_history_at s f s'"
  shows "\<forall>k. \<not> mismatch_at (proto_of_exec_at s' f) f k"
proof
  fix k
  show "\<not> mismatch_at (proto_of_exec_at s' f) f k"
  proof
    assume mismatch: "mismatch_at (proto_of_exec_at s' f) f k"
    from redelivery have base: "exec_base s' = exec_base s"
        and scope: "exec_scope s' = exec_scope s"
        and src: "exec_src_hist s' = exec_src_hist s"
        and image:
          "source_image_equiv_on (exec_base s) (exec_scope s) f
            (exec_src_hist s) (exec_down_hist s')"
      by (auto simp: recovery_effectively_redelivers_source_history_at_def)
    from mismatch have scoped': "k \<in> exec_scope s'"
        and neq:
          "Src (exec_base s') (exec_down_hist s') f k
           \<noteq> Src (exec_base s') (exec_src_hist s') f k"
      by (auto simp: mismatch_at_def proto_of_exec_at_def
                     store2_of_exec_def log_image_def restrict_def)
    from scoped' scope have scoped: "k \<in> exec_scope s" by simp
    have image_eq:
      "restrict (Src (exec_base s) (exec_down_hist s') f) (exec_scope s) =
       restrict (Src (exec_base s) (exec_src_hist s) f) (exec_scope s)"
      using image by (simp add: source_image_equiv_on_def)
    have point_eq:
      "restrict (Src (exec_base s) (exec_down_hist s') f) (exec_scope s) k =
       restrict (Src (exec_base s) (exec_src_hist s) f) (exec_scope s) k"
      using image_eq by simp
    from point_eq scoped have eq:
      "Src (exec_base s) (exec_down_hist s') f k =
       Src (exec_base s) (exec_src_hist s) f k"
      by (simp add: restrict_def)
    from neq eq base src scoped' show False by (simp add: restrict_def)
  qed
qed

corollary recovery_effective_redelivery_no_divergence:
  assumes redelivery: "recovery_effectively_redelivers_source_history_at s f s'"
  shows "\<not> diverges (proto_of_exec_at s' f) f"
  using recovery_effective_redelivery_no_mismatch[OF redelivery]
  by (auto simp: diverges_iff_mismatch_at)

theorem recovery_redelivery_no_mismatch:
  assumes redelivery: "recovery_redelivers_source_history s s'"
  shows "\<forall>k. \<not> mismatch_at (proto_of_exec_at s' f) f k"
  by (rule recovery_effective_redelivery_no_mismatch
      [OF recovery_redelivers_source_history_imp_effective_at[OF redelivery]])

corollary recovery_redelivery_no_divergence:
  assumes redelivery: "recovery_redelivers_source_history s s'"
  shows "\<not> diverges (proto_of_exec_at s' f) f"
  by (rule recovery_effective_redelivery_no_divergence
      [OF recovery_redelivers_source_history_imp_effective_at[OF redelivery]])

theorem recovery_temporal_convergence_with_redelivery:
  assumes trace: "dw_exec_trace s wait s_wait"
      and labels: "list_all recovery_observation_label wait"
      and before: "diverges (proto_of_exec_at s f) f"
      and redelivery: "recovery_redelivers_source_history s_wait s_done"
  shows
    "diverges (proto_of_exec_at s_wait f) f
   \<and> \<not> diverges (proto_of_exec_at s_done f) f"
  using no_reconciliation_divergence_persists[OF trace labels before]
    recovery_redelivery_no_divergence[OF redelivery]
  by blast

theorem recovery_temporal_convergence_with_effective_redelivery:
  assumes trace: "dw_exec_trace s wait s_wait"
      and labels: "list_all recovery_observation_label wait"
      and before: "diverges (proto_of_exec_at s f) f"
      and redelivery:
        "recovery_effectively_redelivers_source_history_at s_wait f s_done"
  shows
    "diverges (proto_of_exec_at s_wait f) f
   \<and> \<not> diverges (proto_of_exec_at s_done f) f"
  using no_reconciliation_divergence_persists[OF trace labels before]
    recovery_effective_redelivery_no_divergence[OF redelivery]
  by blast

corollary recovery_reconcile_temporal_convergence:
  assumes trace: "dw_exec_trace s wait s_wait"
      and labels: "list_all recovery_observation_label wait"
      and before: "diverges (proto_of_exec_at s f) f"
      and reconcile: "recovery_reconcile_step s_wait f s_done"
  shows
    "diverges (proto_of_exec_at s_wait f) f
   \<and> \<not> diverges (proto_of_exec_at s_done f) f"
  using recovery_temporal_convergence_with_redelivery
      [OF trace labels before recovery_reconcile_step_redelivers[OF reconcile]]
  .

theorem no_permanent_recovery_loss_temporal_convergence:
  assumes no_loss: "no_permanent_recovery_loss s f"
  shows "\<exists>wait s_wait s_repaired.
      list_all recovery_observation_label wait
    \<and> dw_exec_trace s wait s_wait
    \<and> recovery_reconcile_step s_wait f s_repaired
    \<and> recovery_temporal_trace s
        (map Recovery_Label wait @ [Recovery_Reconcile f]) s_repaired
    \<and> exec_status s_repaired = Recovered
    \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at s_repaired f) f k)
    \<and> \<not> diverges (proto_of_exec_at s_repaired f) f"
proof -
  from no_loss obtain wait s_wait s_repaired where labels:
      "list_all recovery_observation_label wait"
      and wait_trace: "dw_exec_trace s wait s_wait"
      and reconcile: "recovery_reconcile_step s_wait f s_repaired"
    by (auto simp: no_permanent_recovery_loss_def)
  have wait_temporal:
    "recovery_temporal_trace s (map Recovery_Label wait) s_wait"
    by (rule dw_exec_trace_imp_recovery_temporal_trace[OF wait_trace])
  have reconcile_temporal:
    "recovery_temporal_trace s_wait [Recovery_Reconcile f] s_repaired"
    by (rule recovery_temporal_trace.recovery_temporal_reconcile_step
        [OF reconcile recovery_temporal_trace.recovery_temporal_refl])
  have temporal:
    "recovery_temporal_trace s
      (map Recovery_Label wait @ [Recovery_Reconcile f]) s_repaired"
    by (rule recovery_temporal_trace_append
        [OF wait_temporal reconcile_temporal])
  have status: "exec_status s_repaired = Recovered"
    by (rule recovery_reconcile_step_status[OF reconcile])
  have no_mismatch:
    "\<forall>k. \<not> mismatch_at (proto_of_exec_at s_repaired f) f k"
    by (rule recovery_reconcile_step_no_mismatch[OF reconcile])
  have no_div: "\<not> diverges (proto_of_exec_at s_repaired f) f"
    by (rule recovery_reconcile_step_no_divergence[OF reconcile])
  from labels wait_trace reconcile temporal status no_mismatch no_div
  show ?thesis by blast
qed

theorem observation_only_recovery_does_not_converge_from_mismatch:
  assumes trace: "dw_exec_trace s wait s_wait"
      and labels: "list_all recovery_observation_label wait"
      and mismatch: "mismatch_at (proto_of_exec_at s f) f k"
  shows "\<not> (\<forall>k. \<not> mismatch_at (proto_of_exec_at s_wait f) f k)"
proof
  assume no_mismatch: "\<forall>k. \<not> mismatch_at (proto_of_exec_at s_wait f) f k"
  have "mismatch_at (proto_of_exec_at s_wait f) f k"
    by (rule no_reconciliation_mismatch_persists[OF trace labels mismatch])
  with no_mismatch show False by blast
qed

corollary recovered_status_not_enough_for_no_divergence:
  "\<not> (\<forall>s :: (nat, nat) dw_exec_state. \<forall>f.
      exec_status s = Recovered \<longrightarrow>
      \<not> diverges (proto_of_exec_at s f) f)"
proof
  assume all_recovered_safe:
    "\<forall>s :: (nat, nat) dw_exec_state. \<forall>f.
      exec_status s = Recovered \<longrightarrow>
      \<not> diverges (proto_of_exec_at s f) f"
  have exists_recovered_diverges:
    "\<exists>s_recovered :: (nat, nat) dw_exec_state.
      exec_status s_recovered = Recovered
    \<and> diverges (proto_of_exec_at s_recovered ec1) ec1"
    using recovered_state_still_diverges by blast
  then obtain s_recovered :: "(nat, nat) dw_exec_state"
    where status: "exec_status s_recovered = Recovered"
      and div: "diverges (proto_of_exec_at s_recovered ec1) ec1"
    by blast
  from all_recovered_safe status have
    "\<not> diverges (proto_of_exec_at s_recovered ec1) ec1"
    by blast
  with div show False by simp
qed

corollary recovered_mismatch_observe_then_redeliver_converges:
  "\<exists>s_recovered s_repaired.
      admissible_dw_exec_trace downstream_first_stale_update_initial
        (separated_completion_bad_crash_labels Downstream_Effect
          downstream_first_stale_update_completion @ [Recover])
        s_recovered
    \<and> exec_status s_recovered = Recovered
    \<and> mismatch_at (proto_of_exec_at s_recovered ec1) ec1 0
    \<and> diverges (proto_of_exec_at s_recovered ec1) ec1
    \<and> no_permanent_recovery_loss s_recovered ec1
    \<and> dw_exec_trace s_recovered [Observe ec1] s_recovered
    \<and> recovery_reconcile_step s_recovered ec1 s_repaired
    \<and> recovery_temporal_trace s_recovered
        [Recovery_Label (Observe ec1), Recovery_Reconcile ec1] s_repaired
    \<and> exec_status s_repaired = Recovered
    \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at s_repaired ec1) ec1 k)
    \<and> \<not> diverges (proto_of_exec_at s_repaired ec1) ec1"
proof -
  from recovered_mismatch_reconciliation_witness obtain s_recovered s_repaired
    where trace:
      "admissible_dw_exec_trace downstream_first_stale_update_initial
        (separated_completion_bad_crash_labels Downstream_Effect
          downstream_first_stale_update_completion @ [Recover])
        s_recovered"
      and status: "exec_status s_recovered = Recovered"
      and mismatch:
        "mismatch_at (proto_of_exec_at s_recovered ec1) ec1 0"
      and div: "diverges (proto_of_exec_at s_recovered ec1) ec1"
      and reconcile: "recovery_reconcile_step s_recovered ec1 s_repaired"
      and repaired_status: "exec_status s_repaired = Recovered"
      and no_mismatch:
        "\<forall>k. \<not> mismatch_at (proto_of_exec_at s_repaired ec1) ec1 k"
      and no_div: "\<not> diverges (proto_of_exec_at s_repaired ec1) ec1"
    by blast
  have observe_step:
    "dw_exec_step s_recovered (Observe ec1) s_recovered"
    by (rule dw_exec_step.observe)
  have observe_trace:
    "dw_exec_trace s_recovered [Observe ec1] s_recovered"
    by (rule dw_exec_trace.trace_step
        [OF observe_step dw_exec_trace.trace_refl])
  have no_loss: "no_permanent_recovery_loss s_recovered ec1"
    unfolding no_permanent_recovery_loss_def
    by (intro exI[where x = "[Observe ec1]"]
        exI[where x = s_recovered] exI[where x = s_repaired])
       (simp add: observe_trace reconcile)
  have temporal:
    "recovery_temporal_trace s_recovered
      [Recovery_Label (Observe ec1), Recovery_Reconcile ec1] s_repaired"
    by (rule recovery_temporal_trace.recovery_temporal_label_step
        [OF observe_step
          recovery_temporal_trace.recovery_temporal_reconcile_step
            [OF reconcile recovery_temporal_trace.recovery_temporal_refl]])
  from trace status mismatch div no_loss observe_trace reconcile temporal
    repaired_status no_mismatch no_div show ?thesis
    by blast
qed

corollary source_first_no_permanent_loss_redelivery_witness:
  "\<exists>s_recovered s_repaired \<sigma>.
      dw_exec_trace
        (initial_exec_state (\<lambda>(_::nat). None) {0::nat} ec1)
        [DoSource ec1 (Insert (0::nat) (2::nat)),
         Ack ec1 (Insert (0::nat) (2::nat)),
         Crash ec1, Recover]
        s_recovered
    \<and> exec_status s_recovered = Recovered
    \<and> acked_source_effect_at s_recovered ec1 0
    \<and> store2_of_exec s_recovered ec1 0 = None
    \<and> mismatch_at (proto_of_exec_at s_recovered ec1) ec1 0
    \<and> no_permanent_recovery_loss s_recovered ec1
    \<and> recovery_reconcile_step s_recovered ec1 s_repaired
    \<and> recovery_redelivers_source_history s_recovered s_repaired
    \<and> recovery_effectively_redelivers_source_history_at
        s_recovered ec1 s_repaired
    \<and> \<sigma> = [Cdc ec1 (Insert 0 2)]
    \<and> cdc_only \<sigma>
    \<and> execution_replay_derived_at s_repaired \<sigma> ec1
    \<and> store2_of_exec s_repaired ec1 0 = Some 2
    \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at s_repaired ec1) ec1 k)
    \<and> \<not> diverges (proto_of_exec_at s_repaired ec1) ec1"
proof -
  let ?s_recovered = recovery_source_first_empty_recovered
  let ?s_repaired = recovery_source_first_empty_repaired
  let ?sigma = "cdc_replay_prefix (proto_of_exec_at ?s_repaired ec1) ec1"
  have status: "exec_status ?s_recovered = Recovered"
    by (simp add: recovery_source_first_empty_recovered_def)
  have le_fin: "ec1 \<le> exec_finish ?s_recovered"
    by (simp add: recovery_source_first_empty_recovered_def
                  recovery_source_first_empty_crashed_def source_crashed_state_def
                  after_source_ack_state_def after_source_state_def
                  initial_exec_state_def)
  have step: "recovery_reconcile_step ?s_recovered ec1 ?s_repaired"
    unfolding recovery_source_first_empty_repaired_def
    by (rule recovery_reconcile_step.reconcile_from_recovered[OF status le_fin])
  have no_loss: "no_permanent_recovery_loss ?s_recovered ec1"
    unfolding no_permanent_recovery_loss_def
    by (rule exI[where x = "[]"],
        rule exI[where x = ?s_recovered],
        rule exI[where x = ?s_repaired])
       (simp add: step dw_exec_trace.trace_refl)
  have redelivery:
    "recovery_redelivers_source_history ?s_recovered ?s_repaired"
    by (rule recovery_reconcile_step_redelivers[OF step])
  have effective_redelivery:
    "recovery_effectively_redelivers_source_history_at
      ?s_recovered ec1 ?s_repaired"
    by (rule recovery_redelivers_source_history_imp_effective_at[OF redelivery])
  have acked: "acked_source_effect_at ?s_recovered ec1 0"
    by (simp add: acked_source_effect_at_def
                  recovery_source_first_empty_recovered_def
                  recovery_source_first_empty_crashed_def source_crashed_state_def
                  after_source_ack_state_def after_source_state_def
                  initial_exec_state_def Src_single_event_at_key ec_defs)
  have before_empty: "store2_of_exec ?s_recovered ec1 0 = None"
    using recovery_source_first_empty_repair_changes_downstream_value by simp
  have sigma_eq: "?sigma = [Cdc ec1 (Insert 0 2)]"
    by (simp add: recovery_source_first_empty_repaired_prefix_nonempty)
  have replay:
    "cdc_only ?sigma
     \<and> execution_replay_derived_at ?s_repaired ?sigma ec1"
    by (rule recovery_source_first_empty_repaired_replay_derived)
  have after_value: "store2_of_exec ?s_repaired ec1 0 = Some 2"
    using recovery_source_first_empty_repair_changes_downstream_value by simp
  have no_mismatch:
    "\<forall>k. \<not> mismatch_at (proto_of_exec_at ?s_repaired ec1) ec1 k"
    by (rule recovery_reconcile_step_no_mismatch[OF step])
  have no_div: "\<not> diverges (proto_of_exec_at ?s_repaired ec1) ec1"
    by (rule recovery_reconcile_step_no_divergence[OF step])
  from recovery_source_first_empty_recovered_trace status acked before_empty
    recovery_source_first_empty_recovered_has_mismatch no_loss step redelivery
    effective_redelivery sigma_eq replay after_value no_mismatch no_div
  show ?thesis
    by (intro exI[where x = ?s_recovered] exI[where x = ?s_repaired]
        exI[where x = ?sigma]) simp
qed

end
