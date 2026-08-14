(*  Title:       Dual_Write_Operational_Definition_Audit.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Definition-strength negative controls for the operational layer.  The
    witnesses below exercise the load-bearing clauses of observable mismatch,
    crash-closed implementations, and source-first separable completions.
*)

theory Dual_Write_Operational_Definition_Audit
  imports Dual_Write_Admissibility_Hardening
begin

section \<open>Operational definition-strength negative controls\<close>

subsection \<open>Observable mismatch\<close>

definition audit_update :: "(nat, nat) source_event"
where
  "audit_update = Update 0 2"

definition observable_status_drop_state :: "(nat, nat) dw_exec_state"
where
  "observable_status_drop_state =
     (initial_exec_state [0 \<mapsto> 1] {0} ec3)
       \<lparr>exec_src_hist := [(ec1, audit_update)]\<rparr>"

definition observable_finish_drop_state :: "(nat, nat) dw_exec_state"
where
  "observable_finish_drop_state =
     (initial_exec_state [0 \<mapsto> 1] {0} ec1)
       \<lparr>exec_src_hist := [(ec3, audit_update)],
         exec_status := Crashed ec3\<rparr>"

definition observable_scope_drop_state :: "(nat, nat) dw_exec_state"
where
  "observable_scope_drop_state =
     (initial_exec_state [0 \<mapsto> 1] {1} ec3)
       \<lparr>exec_src_hist := [(ec1, audit_update)],
         exec_status := Crashed ec1\<rparr>"

definition observable_equal_drop_state :: "(nat, nat) dw_exec_state"
where
  "observable_equal_drop_state =
     (initial_exec_state [0 \<mapsto> 1] {0} ec3)
       \<lparr>exec_status := Crashed ec1\<rparr>"

lemma observable_mismatch_status_conjunct_load_bearing:
  "exec_status observable_status_drop_state \<noteq> Crashed ec1
   \<and> ec1 \<le> exec_finish observable_status_drop_state
   \<and> mismatch_at (proto_of_exec_at observable_status_drop_state ec1) ec1 0
   \<and> \<not> observable_mismatch observable_status_drop_state ec1 0"
  by (simp add: observable_status_drop_state_def audit_update_def
                observable_mismatch_def mismatch_at_def proto_of_exec_at_def
                store2_of_exec_def log_image_def restrict_def
                initial_exec_state_def Src_single_event_at_key ec_defs)

lemma observable_mismatch_finish_conjunct_load_bearing:
  "exec_status observable_finish_drop_state = Crashed ec3
   \<and> \<not> ec3 \<le> exec_finish observable_finish_drop_state
   \<and> mismatch_at (proto_of_exec_at observable_finish_drop_state ec3) ec3 0
   \<and> \<not> observable_mismatch observable_finish_drop_state ec3 0"
  by (simp add: observable_finish_drop_state_def audit_update_def
                observable_mismatch_def mismatch_at_def proto_of_exec_at_def
                store2_of_exec_def log_image_def restrict_def
                initial_exec_state_def Src_single_event_at_key ec_defs)

lemma observable_mismatch_scope_conjunct_load_bearing:
  "exec_status observable_scope_drop_state = Crashed ec1
   \<and> ec1 \<le> exec_finish observable_scope_drop_state
   \<and> 0 \<notin> exec_scope observable_scope_drop_state
   \<and> Src (exec_base observable_scope_drop_state)
        (exec_down_hist observable_scope_drop_state) ec1 0
      \<noteq> Src (exec_base observable_scope_drop_state)
        (exec_src_hist observable_scope_drop_state) ec1 0
   \<and> \<not> mismatch_at (proto_of_exec_at observable_scope_drop_state ec1) ec1 0
   \<and> \<not> observable_mismatch observable_scope_drop_state ec1 0"
  by (simp add: observable_scope_drop_state_def audit_update_def
                observable_mismatch_def mismatch_at_def proto_of_exec_at_def
                store2_of_exec_def log_image_def restrict_def
                initial_exec_state_def Src_single_event_at_key ec_defs)

lemma observable_mismatch_store_disagreement_conjunct_load_bearing:
  "exec_status observable_equal_drop_state = Crashed ec1
   \<and> ec1 \<le> exec_finish observable_equal_drop_state
   \<and> 0 \<in> exec_scope observable_equal_drop_state
   \<and> \<not> mismatch_at (proto_of_exec_at observable_equal_drop_state ec1) ec1 0
   \<and> \<not> observable_mismatch observable_equal_drop_state ec1 0"
  by (simp add: observable_equal_drop_state_def observable_mismatch_def
                mismatch_at_def proto_of_exec_at_def store2_of_exec_def
                log_image_def restrict_def initial_exec_state_def ec_defs)

lemma observable_mismatch_definition_conjuncts_load_bearing:
  "(\<exists>s::(nat, nat) dw_exec_state.
      exec_status s \<noteq> Crashed ec1
    \<and> ec1 \<le> exec_finish s
    \<and> mismatch_at (proto_of_exec_at s ec1) ec1 0
    \<and> \<not> observable_mismatch s ec1 0)
   \<and> (\<exists>s::(nat, nat) dw_exec_state.
      exec_status s = Crashed ec3
    \<and> \<not> ec3 \<le> exec_finish s
    \<and> mismatch_at (proto_of_exec_at s ec3) ec3 0
    \<and> \<not> observable_mismatch s ec3 0)
   \<and> (\<exists>s::(nat, nat) dw_exec_state.
      exec_status s = Crashed ec1
    \<and> ec1 \<le> exec_finish s
    \<and> 0 \<notin> exec_scope s
    \<and> Src (exec_base s) (exec_down_hist s) ec1 0
      \<noteq> Src (exec_base s) (exec_src_hist s) ec1 0
    \<and> \<not> observable_mismatch s ec1 0)
   \<and> (\<exists>s::(nat, nat) dw_exec_state.
      exec_status s = Crashed ec1
    \<and> ec1 \<le> exec_finish s
    \<and> 0 \<in> exec_scope s
    \<and> \<not> mismatch_at (proto_of_exec_at s ec1) ec1 0
    \<and> \<not> observable_mismatch s ec1 0)"
  using observable_mismatch_status_conjunct_load_bearing
        observable_mismatch_finish_conjunct_load_bearing
        observable_mismatch_scope_conjunct_load_bearing
        observable_mismatch_store_disagreement_conjunct_load_bearing
  by blast


subsection \<open>Crash closure\<close>

definition crash_audit_running_state :: "(nat, nat) dw_exec_state"
where
  "crash_audit_running_state = initial_exec_state [0 \<mapsto> 1] {0} ec1"

definition crash_audit_crashed_state :: "(nat, nat) dw_exec_state"
where
  "crash_audit_crashed_state =
     crash_audit_running_state\<lparr>exec_status := Crashed ec1\<rparr>"

definition no_crash_step_implementation
  :: "(unit, nat, nat) dual_write_implementation"
where
  "no_crash_step_implementation =
     \<lparr> dwi_initial = (),
       dwi_step = (\<lambda>_ _ _. False),
       dwi_state = (\<lambda>_. crash_audit_running_state) \<rparr>"

definition crashed_no_step_implementation
  :: "(unit, nat, nat) dual_write_implementation"
where
  "crashed_no_step_implementation =
     \<lparr> dwi_initial = (),
       dwi_step = (\<lambda>_ _ _. False),
       dwi_state = (\<lambda>_. crash_audit_crashed_state) \<rparr>"

definition bounded_crash_step_implementation
  :: "(unit, nat, nat) dual_write_implementation"
where
  "bounded_crash_step_implementation =
     \<lparr> dwi_initial = (),
       dwi_step =
         (\<lambda>_ a _.
            case a of
              Crash c \<Rightarrow> c \<le> ec1
            | _ \<Rightarrow> False),
       dwi_state = (\<lambda>_. crash_audit_running_state) \<rparr>"

lemma crash_closed_step_availability_load_bearing:
  "\<not> crash_closed_implementation no_crash_step_implementation
   \<and> exec_status
        (dwi_state no_crash_step_implementation
          (dwi_initial no_crash_step_implementation)) = Running
   \<and> ec1 \<le> exec_finish
        (dwi_state no_crash_step_implementation
          (dwi_initial no_crash_step_implementation))
   \<and> \<not> (\<exists>s'. dwi_step no_crash_step_implementation ()
        (Crash ec1) s')"
  by (auto simp: no_crash_step_implementation_def
                 crash_audit_running_state_def
                 crash_closed_implementation_def
                 initial_exec_state_def ec_defs
           intro: dwi_trace.dwi_trace_refl)

lemma crash_closed_running_guard_load_bearing:
  "crash_closed_implementation crashed_no_step_implementation
   \<and> exec_status
        (dwi_state crashed_no_step_implementation
          (dwi_initial crashed_no_step_implementation)) = Crashed ec1
   \<and> ec1 \<le> exec_finish
        (dwi_state crashed_no_step_implementation
          (dwi_initial crashed_no_step_implementation))
   \<and> \<not> (\<exists>s'. dwi_step crashed_no_step_implementation ()
        (Crash ec1) s')"
  by (auto simp: crashed_no_step_implementation_def
                 crash_audit_crashed_state_def
                 crash_audit_running_state_def
                 crash_closed_implementation_def
                 initial_exec_state_def ec_defs)

lemma crash_closed_finish_guard_load_bearing:
  "crash_closed_implementation bounded_crash_step_implementation
   \<and> exec_status
        (dwi_state bounded_crash_step_implementation
          (dwi_initial bounded_crash_step_implementation)) = Running
   \<and> \<not> ec3 \<le> exec_finish
        (dwi_state bounded_crash_step_implementation
          (dwi_initial bounded_crash_step_implementation))
   \<and> \<not> (\<exists>s'. dwi_step bounded_crash_step_implementation ()
        (Crash ec3) s')"
  by (auto simp: bounded_crash_step_implementation_def
                 crash_audit_running_state_def
                 crash_closed_implementation_def
                 initial_exec_state_def ec_defs
           split: dw_exec_label.splits)

lemma crash_closed_definition_conjuncts_load_bearing:
  "(\<exists>I::(unit, nat, nat) dual_write_implementation.
      \<not> crash_closed_implementation I
    \<and> exec_status (dwi_state I (dwi_initial I)) = Running
    \<and> ec1 \<le> exec_finish (dwi_state I (dwi_initial I))
    \<and> \<not> (\<exists>s'. dwi_step I (dwi_initial I) (Crash ec1) s'))
   \<and> (\<exists>I::(unit, nat, nat) dual_write_implementation.
      crash_closed_implementation I
    \<and> exec_status (dwi_state I (dwi_initial I)) = Crashed ec1
    \<and> ec1 \<le> exec_finish (dwi_state I (dwi_initial I))
    \<and> \<not> (\<exists>s'. dwi_step I (dwi_initial I) (Crash ec1) s'))
   \<and> (\<exists>I::(unit, nat, nat) dual_write_implementation.
      crash_closed_implementation I
    \<and> exec_status (dwi_state I (dwi_initial I)) = Running
    \<and> \<not> ec3 \<le> exec_finish (dwi_state I (dwi_initial I))
    \<and> \<not> (\<exists>s'. dwi_step I (dwi_initial I) (Crash ec3) s'))"
  using crash_closed_step_availability_load_bearing
        crash_closed_running_guard_load_bearing
        crash_closed_finish_guard_load_bearing
proof (intro conjI)
  show "\<exists>I::(unit, nat, nat) dual_write_implementation.
      \<not> crash_closed_implementation I
    \<and> exec_status (dwi_state I (dwi_initial I)) = Running
    \<and> ec1 \<le> exec_finish (dwi_state I (dwi_initial I))
    \<and> \<not> (\<exists>s'. dwi_step I (dwi_initial I) (Crash ec1) s')"
    by (intro exI[where x = no_crash_step_implementation])
       (use crash_closed_step_availability_load_bearing in
          \<open>simp add: no_crash_step_implementation_def\<close>)
next
  show "\<exists>I::(unit, nat, nat) dual_write_implementation.
      crash_closed_implementation I
    \<and> exec_status (dwi_state I (dwi_initial I)) = Crashed ec1
    \<and> ec1 \<le> exec_finish (dwi_state I (dwi_initial I))
    \<and> \<not> (\<exists>s'. dwi_step I (dwi_initial I) (Crash ec1) s')"
    by (intro exI[where x = crashed_no_step_implementation])
       (use crash_closed_running_guard_load_bearing in
          \<open>simp add: crashed_no_step_implementation_def\<close>)
next
  show "\<exists>I::(unit, nat, nat) dual_write_implementation.
      crash_closed_implementation I
    \<and> exec_status (dwi_state I (dwi_initial I)) = Running
    \<and> \<not> ec3 \<le> exec_finish (dwi_state I (dwi_initial I))
    \<and> \<not> (\<exists>s'. dwi_step I (dwi_initial I) (Crash ec3) s')"
    by (intro exI[where x = bounded_crash_step_implementation])
       (use crash_closed_finish_guard_load_bearing in
          \<open>simp add: bounded_crash_step_implementation_def\<close>)
qed


subsection \<open>Source-first separable completions\<close>

definition sf_start_state
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) dw_exec_state"
where
  "sf_start_state I = dwi_state I (dwi_initial I)"

definition sf_refines
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "sf_refines I \<longleftrightarrow> dwi_refines_exec I"

definition sf_schedule
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) separated_dual_write_completion \<Rightarrow> bool"
where
  "sf_schedule I C \<longleftrightarrow> source_first_separated_dual_write_schedule I C"

definition sf_pre_running
  :: "('k, 'v) separated_dual_write_completion \<Rightarrow> bool"
where
  "sf_pre_running C \<longleftrightarrow> running_labels (sdwc_pre C)"

definition sf_start_running
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "sf_start_running I \<longleftrightarrow> exec_status (sf_start_state I) = Running"

definition sf_key_matches
  :: "('k, 'v) separated_dual_write_completion \<Rightarrow> bool"
where
  "sf_key_matches C \<longleftrightarrow> key_of (sdwc_event C) = sdwc_key C"

definition sf_effective_source
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) separated_dual_write_completion \<Rightarrow> bool"
where
  "sf_effective_source I C \<longleftrightarrow>
     effective_source_effect
       (exec_base (sf_start_state I)) (sdwc_event C) (sdwc_key C)"

definition sf_same_downstream
  :: "('k, 'v) separated_dual_write_completion \<Rightarrow> bool"
where
  "sf_same_downstream C \<longleftrightarrow>
     same_downstream_effect (sdwc_event C) (sdwc_down_event C) (sdwc_key C)"

definition sf_scoped
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) separated_dual_write_completion \<Rightarrow> bool"
where
  "sf_scoped I C \<longleftrightarrow> sdwc_key C \<in> exec_scope (sf_start_state I)"

definition sf_source_before_downstream
  :: "('k, 'v) separated_dual_write_completion \<Rightarrow> bool"
where
  "sf_source_before_downstream C \<longleftrightarrow> sdwc_source_at C < sdwc_down_at C"

definition sf_source_within_finish
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) separated_dual_write_completion \<Rightarrow> bool"
where
  "sf_source_within_finish I C \<longleftrightarrow>
     sdwc_source_at C \<le> exec_finish (sf_start_state I)"

definition sf_downstream_within_finish
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) separated_dual_write_completion \<Rightarrow> bool"
where
  "sf_downstream_within_finish I C \<longleftrightarrow>
     sdwc_down_at C \<le> exec_finish (sf_start_state I)"

definition sf_no_prior_downstream
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) separated_dual_write_completion \<Rightarrow> bool"
where
  "sf_no_prior_downstream I C \<longleftrightarrow>
     no_visible_key_events
       (exec_down_hist (sf_start_state I) @ down_hist_of_labels (sdwc_pre C))
       (sdwc_source_at C) (sdwc_key C)"

lemma source_first_separable_completion_side_condition_expansion:
  "source_first_separable_completion I C \<longleftrightarrow>
     sf_refines I
   \<and> sf_schedule I C
   \<and> sf_pre_running C
   \<and> sf_start_running I
   \<and> sf_key_matches C
   \<and> sf_effective_source I C
   \<and> sf_same_downstream C
   \<and> sf_scoped I C
   \<and> sf_source_before_downstream C
   \<and> sf_source_within_finish I C
   \<and> sf_downstream_within_finish I C
   \<and> sf_no_prior_downstream I C"
  by (simp add: source_first_separable_completion_def sf_refines_def
                sf_schedule_def sf_pre_running_def sf_start_running_def
                sf_key_matches_def sf_effective_source_def
                sf_same_downstream_def sf_scoped_def
                sf_source_before_downstream_def sf_source_within_finish_def
                sf_downstream_within_finish_def sf_no_prior_downstream_def
                sf_start_state_def)

lemma source_first_completion_imp_sf_refines:
  assumes "source_first_separable_completion I C"
  shows "sf_refines I"
  using assms
  by (simp add: source_first_separable_completion_side_condition_expansion)

lemma source_first_completion_imp_sf_schedule:
  assumes "source_first_separable_completion I C"
  shows "sf_schedule I C"
  using assms
  by (simp add: source_first_separable_completion_side_condition_expansion)

lemma source_first_completion_imp_sf_effective_source:
  assumes "source_first_separable_completion I C"
  shows "sf_effective_source I C"
  using assms
  by (simp add: source_first_separable_completion_side_condition_expansion)

lemma source_first_completion_imp_sf_same_downstream:
  assumes "source_first_separable_completion I C"
  shows "sf_same_downstream C"
  using assms
  by (simp add: source_first_separable_completion_side_condition_expansion)

lemma source_first_completion_imp_sf_scoped:
  assumes "source_first_separable_completion I C"
  shows "sf_scoped I C"
  using assms
  by (simp add: source_first_separable_completion_side_condition_expansion)

lemma source_first_completion_imp_sf_source_before_downstream:
  assumes "source_first_separable_completion I C"
  shows "sf_source_before_downstream C"
  using assms
  by (simp add: source_first_separable_completion_side_condition_expansion)

lemma source_first_completion_imp_sf_downstream_within_finish:
  assumes "source_first_separable_completion I C"
  shows "sf_downstream_within_finish I C"
  using assms
  by (simp add: source_first_separable_completion_side_condition_expansion)

lemma source_first_completion_imp_sf_no_prior_downstream:
  assumes "source_first_separable_completion I C"
  shows "sf_no_prior_downstream I C"
  using assms
  by (simp add: source_first_separable_completion_side_condition_expansion)

lemma dw_exec_step_result_running_imp_start_running:
  assumes "dw_exec_step s a s'"
      and "exec_status s' = Running"
  shows "exec_status s = Running"
  using assms by cases auto

lemma dw_exec_trace_to_running_imp_start_running:
  assumes "dw_exec_trace s xs s'"
      and "exec_status s' = Running"
  shows "exec_status s = Running"
  using assms
proof (induction rule: dw_exec_trace.induct)
  case (trace_refl s)
  thus ?case by simp
next
  case (trace_step s a s' as s'')
  have "exec_status s' = Running"
    using trace_step.IH trace_step.prems by blast
  thus "exec_status s = Running"
    by (rule dw_exec_step_result_running_imp_start_running
        [OF trace_step.hyps(1)])
qed

lemma dw_exec_step_result_running_imp_running_label:
  assumes "dw_exec_step s a s'"
      and "exec_status s' = Running"
  shows "running_label a"
  using assms by cases (auto simp: running_label_def)

lemma dw_exec_trace_to_running_imp_running_labels:
  assumes "dw_exec_trace s xs s'"
      and "exec_status s' = Running"
  shows "running_labels xs"
  using assms
proof (induction rule: dw_exec_trace.induct)
  case (trace_refl s)
  thus ?case by (simp add: running_labels_def)
next
  case (trace_step s a s' as s'')
  have s'_running: "exec_status s' = Running"
    by (rule dw_exec_trace_to_running_imp_start_running
        [OF trace_step.hyps(2) trace_step.prems])
  have label: "running_label a"
    by (rule dw_exec_step_result_running_imp_running_label
        [OF trace_step.hyps(1) s'_running])
  have rest: "running_labels as"
    using trace_step.IH trace_step.prems by blast
  from label rest show ?case
    by (simp add: running_labels_def)
qed

lemma source_first_schedule_refines_imp_running_guards:
  assumes refines: "sf_refines I"
      and schedule: "sf_schedule I C"
  shows "sf_pre_running C \<and> sf_start_running I"
proof -
  from schedule obtain s_pre s_src s_ack s_enq s_down where
      pre: "dwi_trace I (dwi_initial I) (sdwc_pre C) s_pre"
      and source:
        "dwi_step I s_pre
          (DoSource (sdwc_source_at C) (sdwc_event C)) s_src"
    by (auto simp: sf_schedule_def source_first_separated_dual_write_schedule_def)
  from refines have ref: "dwi_refines_exec I"
    by (simp add: sf_refines_def)
  have exec_pre:
    "dw_exec_trace (sf_start_state I) (sdwc_pre C) (dwi_state I s_pre)"
    using dwi_trace_refines_exec[OF ref pre]
    by (simp add: sf_start_state_def)
  have exec_source:
    "dw_exec_step (dwi_state I s_pre)
      (DoSource (sdwc_source_at C) (sdwc_event C)) (dwi_state I s_src)"
    using ref source by (auto simp: dwi_refines_exec_def)
  have pre_running: "exec_status (dwi_state I s_pre) = Running"
    using exec_source by cases auto
  have labels: "running_labels (sdwc_pre C)"
    by (rule dw_exec_trace_to_running_imp_running_labels
        [OF exec_pre pre_running])
  have start: "exec_status (sf_start_state I) = Running"
    by (rule dw_exec_trace_to_running_imp_start_running
        [OF exec_pre pre_running])
  from labels start show ?thesis
    by (simp add: sf_pre_running_def sf_start_running_def)
qed

lemma source_first_effective_source_imp_key_clause:
  assumes "sf_effective_source I C"
  shows "sf_key_matches C"
  using assms
  by (simp add: sf_effective_source_def sf_key_matches_def
                effective_source_effect_def)

lemma source_first_order_and_down_finish_imp_source_finish:
  assumes "sf_source_before_downstream C"
      and "sf_downstream_within_finish I C"
  shows "sf_source_within_finish I C"
  using assms
  by (auto simp: sf_source_before_downstream_def
                 sf_downstream_within_finish_def
                 sf_source_within_finish_def sf_start_state_def
           intro: order_trans[OF order_less_imp_le])

lemma source_first_redundant_side_conditions_are_derivable:
  assumes "sf_refines I"
      and "sf_schedule I C"
      and "sf_effective_source I C"
      and "sf_source_before_downstream C"
      and "sf_downstream_within_finish I C"
  shows "sf_pre_running C
   \<and> sf_start_running I
   \<and> sf_key_matches C
   \<and> sf_source_within_finish I C"
  using source_first_schedule_refines_imp_running_guards[OF assms(1,2)]
        source_first_effective_source_imp_key_clause[OF assms(3)]
        source_first_order_and_down_finish_imp_source_finish[OF assms(4,5)]
  by blast

lemma audit_canonical_dw_implementation_initial [simp]:
  "dwi_initial (canonical_dw_implementation s0) = s0"
  by (simp add: canonical_dw_implementation_def)

lemma audit_canonical_dw_implementation_state [simp]:
  "dwi_state (canonical_dw_implementation s0) s = s"
  by (simp add: canonical_dw_implementation_def)

definition sf_audit_initial :: "(nat, nat) dw_exec_state"
where
  "sf_audit_initial = initial_exec_state [0 \<mapsto> 1] {0} ec3"

definition sf_audit_completion :: "(nat, nat) separated_dual_write_completion"
where
  "sf_audit_completion =
     \<lparr> sdwc_pre = [],
       sdwc_key = 0,
       sdwc_source_at = ec1,
       sdwc_event = audit_update,
       sdwc_down_at = ec3,
       sdwc_down_event = audit_update \<rparr>"

definition sf_audit_implementation
  :: "((nat, nat) dw_exec_state, nat, nat) dual_write_implementation"
where
  "sf_audit_implementation = canonical_dw_implementation sf_audit_initial"

lemma sf_audit_completion_inhabits_source_first:
  "source_first_separable_completion sf_audit_implementation sf_audit_completion"
proof -
  have refines: "sf_refines sf_audit_implementation"
    by (simp add: sf_refines_def sf_audit_implementation_def)
  have schedule: "sf_schedule sf_audit_implementation sf_audit_completion"
    by (auto simp: sf_schedule_def
                   source_first_separated_dual_write_schedule_def
                   sf_audit_implementation_def sf_audit_initial_def
                   sf_audit_completion_def audit_update_def
                   canonical_dw_implementation_def initial_exec_state_def ec_defs
             intro!: exI dw_exec_step.do_source dw_exec_step.ack
                     dw_exec_step.enqueue_downstream dw_exec_step.do_downstream
                     dwi_trace.dwi_trace_refl)
  have side_conditions:
    "sf_pre_running sf_audit_completion
   \<and> sf_start_running sf_audit_implementation
   \<and> sf_key_matches sf_audit_completion
   \<and> sf_effective_source sf_audit_implementation sf_audit_completion
   \<and> sf_same_downstream sf_audit_completion
   \<and> sf_scoped sf_audit_implementation sf_audit_completion
   \<and> sf_source_before_downstream sf_audit_completion
   \<and> sf_source_within_finish sf_audit_implementation sf_audit_completion
   \<and> sf_downstream_within_finish sf_audit_implementation sf_audit_completion
   \<and> sf_no_prior_downstream sf_audit_implementation sf_audit_completion"
    by (simp add: sf_pre_running_def sf_start_running_def
                  sf_key_matches_def sf_effective_source_def
                  sf_same_downstream_def sf_scoped_def
                  sf_source_before_downstream_def sf_source_within_finish_def
                  sf_downstream_within_finish_def sf_no_prior_downstream_def
                  sf_start_state_def sf_audit_implementation_def
                  sf_audit_initial_def sf_audit_completion_def audit_update_def
                  canonical_dw_implementation_def initial_exec_state_def
                  running_labels_def effective_source_effect_def
                  same_downstream_effect_def no_visible_key_events_def
                  visible_src_event_at_def ec_defs)
  from refines schedule side_conditions show ?thesis
    by (simp add: source_first_separable_completion_side_condition_expansion)
qed

definition sf_non_refining_implementation
  :: "((nat, nat) dw_exec_state, nat, nat) dual_write_implementation"
where
  "sf_non_refining_implementation =
     \<lparr> dwi_initial = sf_audit_initial,
       dwi_step =
         (\<lambda>s a s'. dw_exec_step s a s'
           \<or> (s = sf_audit_initial \<and> a = Recover \<and> s' = s)),
       dwi_state = (\<lambda>s. s) \<rparr>"

definition sf_no_step_implementation
  :: "((nat, nat) dw_exec_state, nat, nat) dual_write_implementation"
where
  "sf_no_step_implementation =
     \<lparr> dwi_initial = sf_audit_initial,
       dwi_step = (\<lambda>_ _ _. False),
       dwi_state = (\<lambda>s. s) \<rparr>"

definition sf_no_effect_completion :: "(nat, nat) separated_dual_write_completion"
where
  "sf_no_effect_completion =
     sf_audit_completion
       \<lparr>sdwc_event := Update 0 1,
         sdwc_down_event := Update 0 1\<rparr>"

definition sf_bad_downstream_effect_completion
  :: "(nat, nat) separated_dual_write_completion"
where
  "sf_bad_downstream_effect_completion =
     sf_audit_completion\<lparr>sdwc_down_event := Update 0 3\<rparr>"

definition sf_unscoped_initial :: "(nat, nat) dw_exec_state"
where
  "sf_unscoped_initial = initial_exec_state [0 \<mapsto> 1] {1} ec3"

definition sf_unscoped_implementation
  :: "((nat, nat) dw_exec_state, nat, nat) dual_write_implementation"
where
  "sf_unscoped_implementation = canonical_dw_implementation sf_unscoped_initial"

definition sf_bad_order_completion :: "(nat, nat) separated_dual_write_completion"
where
  "sf_bad_order_completion =
     sf_audit_completion\<lparr>sdwc_source_at := ec3, sdwc_down_at := ec1\<rparr>"

definition sf_down_beyond_finish_completion
  :: "(nat, nat) separated_dual_write_completion"
where
  "sf_down_beyond_finish_completion =
     sf_audit_completion\<lparr>sdwc_down_at := ec4\<rparr>"

definition sf_visible_downstream_initial :: "(nat, nat) dw_exec_state"
where
  "sf_visible_downstream_initial =
     sf_audit_initial\<lparr>exec_down_hist := [(ec1, Update 0 9)]\<rparr>"

definition sf_visible_downstream_implementation
  :: "((nat, nat) dw_exec_state, nat, nat) dual_write_implementation"
where
  "sf_visible_downstream_implementation =
     canonical_dw_implementation sf_visible_downstream_initial"

lemma source_first_refinement_clause_negative_control:
  "\<not> sf_refines sf_non_refining_implementation
   \<and> \<not> source_first_separable_completion
        sf_non_refining_implementation sf_audit_completion"
proof -
  have bad_step:
    "dwi_step sf_non_refining_implementation sf_audit_initial
      Recover sf_audit_initial"
    by (simp add: sf_non_refining_implementation_def)
  have no_ref: "\<not> sf_refines sf_non_refining_implementation"
  proof
    assume "sf_refines sf_non_refining_implementation"
    hence "dw_exec_step sf_audit_initial Recover sf_audit_initial"
      using bad_step
      by (auto simp: sf_refines_def dwi_refines_exec_def
                     sf_non_refining_implementation_def)
    thus False
      by cases (simp_all add: sf_audit_initial_def initial_exec_state_def)
  qed
  hence "\<not> source_first_separable_completion
      sf_non_refining_implementation sf_audit_completion"
    using source_first_completion_imp_sf_refines by blast
  with no_ref show ?thesis by simp
qed

lemma source_first_schedule_clause_negative_control:
  "\<not> sf_schedule sf_no_step_implementation sf_audit_completion
   \<and> \<not> source_first_separable_completion
        sf_no_step_implementation sf_audit_completion"
proof -
  have no_sched:
    "\<not> sf_schedule sf_no_step_implementation sf_audit_completion"
    by (simp add: sf_schedule_def sf_no_step_implementation_def
                  source_first_separated_dual_write_schedule_def)
  hence "\<not> source_first_separable_completion
      sf_no_step_implementation sf_audit_completion"
    using source_first_completion_imp_sf_schedule by blast
  with no_sched show ?thesis by simp
qed

lemma source_first_effective_source_clause_negative_control:
  "\<not> sf_effective_source sf_audit_implementation sf_no_effect_completion
   \<and> \<not> source_first_separable_completion
        sf_audit_implementation sf_no_effect_completion"
  by (auto simp: sf_effective_source_def sf_start_state_def
                 sf_audit_implementation_def sf_audit_initial_def
                 sf_no_effect_completion_def sf_audit_completion_def
                 audit_update_def initial_exec_state_def
                 effective_source_effect_def
           dest: source_first_completion_imp_sf_effective_source)

lemma source_first_same_downstream_clause_negative_control:
  "\<not> sf_same_downstream sf_bad_downstream_effect_completion
   \<and> \<not> source_first_separable_completion
        sf_audit_implementation sf_bad_downstream_effect_completion"
  by (auto simp: sf_same_downstream_def
                 sf_bad_downstream_effect_completion_def
                 sf_audit_completion_def audit_update_def
                 same_downstream_effect_def
           dest: source_first_completion_imp_sf_same_downstream)

lemma source_first_scope_clause_negative_control:
  "\<not> sf_scoped sf_unscoped_implementation sf_audit_completion
   \<and> \<not> source_first_separable_completion
        sf_unscoped_implementation sf_audit_completion"
  by (auto simp: sf_scoped_def sf_start_state_def
                 sf_unscoped_implementation_def sf_unscoped_initial_def
                 sf_audit_completion_def initial_exec_state_def
           dest: source_first_completion_imp_sf_scoped)

lemma source_first_order_clause_negative_control:
  "\<not> sf_source_before_downstream sf_bad_order_completion
   \<and> \<not> source_first_separable_completion
        sf_audit_implementation sf_bad_order_completion"
  by (auto simp: sf_source_before_downstream_def
                 sf_bad_order_completion_def sf_audit_completion_def ec_defs
           dest: source_first_completion_imp_sf_source_before_downstream)

lemma source_first_downstream_finish_clause_negative_control:
  "\<not> sf_downstream_within_finish sf_audit_implementation
        sf_down_beyond_finish_completion
   \<and> \<not> source_first_separable_completion
        sf_audit_implementation sf_down_beyond_finish_completion"
  by (auto simp: sf_downstream_within_finish_def sf_start_state_def
                 sf_audit_implementation_def sf_audit_initial_def
                 sf_down_beyond_finish_completion_def sf_audit_completion_def
                 initial_exec_state_def ec_defs
           dest: source_first_completion_imp_sf_downstream_within_finish)

lemma source_first_no_visible_clause_negative_control:
  "\<not> sf_no_prior_downstream
        sf_visible_downstream_implementation sf_audit_completion
   \<and> \<not> source_first_separable_completion
        sf_visible_downstream_implementation sf_audit_completion"
  by (auto simp: sf_no_prior_downstream_def sf_start_state_def
                 sf_visible_downstream_implementation_def
                 sf_visible_downstream_initial_def sf_audit_completion_def
                 sf_audit_initial_def initial_exec_state_def
                 no_visible_key_events_def visible_src_event_at_def ec_defs
           dest: source_first_completion_imp_sf_no_prior_downstream)

lemma source_first_load_bearing_side_conditions_have_negative_controls:
  "\<not> source_first_separable_completion
      sf_non_refining_implementation sf_audit_completion
   \<and> \<not> source_first_separable_completion
      sf_no_step_implementation sf_audit_completion
   \<and> \<not> source_first_separable_completion
      sf_audit_implementation sf_no_effect_completion
   \<and> \<not> source_first_separable_completion
      sf_audit_implementation sf_bad_downstream_effect_completion
   \<and> \<not> source_first_separable_completion
      sf_unscoped_implementation sf_audit_completion
   \<and> \<not> source_first_separable_completion
      sf_audit_implementation sf_bad_order_completion
   \<and> \<not> source_first_separable_completion
      sf_audit_implementation sf_down_beyond_finish_completion
   \<and> \<not> source_first_separable_completion
      sf_visible_downstream_implementation sf_audit_completion"
  using source_first_refinement_clause_negative_control
        source_first_schedule_clause_negative_control
        source_first_effective_source_clause_negative_control
        source_first_same_downstream_clause_negative_control
        source_first_scope_clause_negative_control
        source_first_order_clause_negative_control
        source_first_downstream_finish_clause_negative_control
        source_first_no_visible_clause_negative_control
  by simp

theorem operational_definition_strength_negative_controls:
  "(\<exists>s::(nat, nat) dw_exec_state.
      exec_status s \<noteq> Crashed ec1
    \<and> ec1 \<le> exec_finish s
    \<and> mismatch_at (proto_of_exec_at s ec1) ec1 0
    \<and> \<not> observable_mismatch s ec1 0)
   \<and> (\<exists>s::(nat, nat) dw_exec_state.
      exec_status s = Crashed ec3
    \<and> \<not> ec3 \<le> exec_finish s
    \<and> mismatch_at (proto_of_exec_at s ec3) ec3 0
    \<and> \<not> observable_mismatch s ec3 0)
   \<and> (\<exists>s::(nat, nat) dw_exec_state.
      exec_status s = Crashed ec1
    \<and> ec1 \<le> exec_finish s
    \<and> 0 \<notin> exec_scope s
    \<and> Src (exec_base s) (exec_down_hist s) ec1 0
      \<noteq> Src (exec_base s) (exec_src_hist s) ec1 0
    \<and> \<not> observable_mismatch s ec1 0)
   \<and> (\<exists>s::(nat, nat) dw_exec_state.
      exec_status s = Crashed ec1
    \<and> ec1 \<le> exec_finish s
    \<and> 0 \<in> exec_scope s
    \<and> \<not> mismatch_at (proto_of_exec_at s ec1) ec1 0
    \<and> \<not> observable_mismatch s ec1 0)
   \<and> (\<exists>I::(unit, nat, nat) dual_write_implementation.
      \<not> crash_closed_implementation I
    \<and> exec_status (dwi_state I (dwi_initial I)) = Running
    \<and> ec1 \<le> exec_finish (dwi_state I (dwi_initial I))
    \<and> \<not> (\<exists>s'. dwi_step I (dwi_initial I) (Crash ec1) s'))
   \<and> (\<exists>I::(unit, nat, nat) dual_write_implementation.
      crash_closed_implementation I
    \<and> exec_status (dwi_state I (dwi_initial I)) = Crashed ec1
    \<and> ec1 \<le> exec_finish (dwi_state I (dwi_initial I))
    \<and> \<not> (\<exists>s'. dwi_step I (dwi_initial I) (Crash ec1) s'))
   \<and> (\<exists>I::(unit, nat, nat) dual_write_implementation.
      crash_closed_implementation I
    \<and> exec_status (dwi_state I (dwi_initial I)) = Running
    \<and> \<not> ec3 \<le> exec_finish (dwi_state I (dwi_initial I))
    \<and> \<not> (\<exists>s'. dwi_step I (dwi_initial I) (Crash ec3) s'))
   \<and> source_first_separable_completion
      sf_audit_implementation sf_audit_completion
   \<and> sf_pre_running sf_audit_completion
   \<and> sf_start_running sf_audit_implementation
   \<and> sf_key_matches sf_audit_completion
   \<and> sf_source_within_finish sf_audit_implementation sf_audit_completion
   \<and> \<not> source_first_separable_completion
      sf_non_refining_implementation sf_audit_completion
   \<and> \<not> source_first_separable_completion
      sf_no_step_implementation sf_audit_completion
   \<and> \<not> source_first_separable_completion
      sf_audit_implementation sf_no_effect_completion
   \<and> \<not> source_first_separable_completion
      sf_audit_implementation sf_bad_downstream_effect_completion
   \<and> \<not> source_first_separable_completion
      sf_unscoped_implementation sf_audit_completion
   \<and> \<not> source_first_separable_completion
      sf_audit_implementation sf_bad_order_completion
   \<and> \<not> source_first_separable_completion
      sf_audit_implementation sf_down_beyond_finish_completion
   \<and> \<not> source_first_separable_completion
      sf_visible_downstream_implementation sf_audit_completion"
proof -
  have source_positive:
    "source_first_separable_completion sf_audit_implementation sf_audit_completion
   \<and> sf_pre_running sf_audit_completion
   \<and> sf_start_running sf_audit_implementation
   \<and> sf_key_matches sf_audit_completion
   \<and> sf_source_within_finish sf_audit_implementation sf_audit_completion"
    using sf_audit_completion_inhabits_source_first
    by (simp add: source_first_separable_completion_side_condition_expansion)
  show ?thesis
    using observable_mismatch_definition_conjuncts_load_bearing
          crash_closed_definition_conjuncts_load_bearing
          source_positive
          source_first_load_bearing_side_conditions_have_negative_controls
    by blast
qed

end
