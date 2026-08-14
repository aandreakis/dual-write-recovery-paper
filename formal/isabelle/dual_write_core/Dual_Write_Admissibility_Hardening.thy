(*  Title:       Dual_Write_Admissibility_Hardening.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Non-vacuity checks for the admissible execution wrapper.  The raw
    execution relation is deliberately permissive; this leaf theory proves that
    the admissible wrapper is a proper restriction and that each conjunct of
    wellformed_exec_state is load-bearing.
*)

theory Dual_Write_Admissibility_Hardening
  imports Dual_Write_Execution
begin

section \<open>Admissible-wrapper non-vacuity\<close>

definition admissibility_bad_event :: "(nat, nat) source_event"
where
  "admissibility_bad_event = Update 0 2"

definition admissibility_initial :: "(nat, nat) dw_exec_state"
where
  "admissibility_initial = initial_exec_state [0 \<mapsto> 1] {0} ec4"

definition bad_history_exec_state :: "(nat, nat) dw_exec_state"
where
  "bad_history_exec_state =
     admissibility_initial
       \<lparr>exec_src_hist := [(c0, admissibility_bad_event)]\<rparr>"

definition bad_pending_exec_state :: "(nat, nat) dw_exec_state"
where
  "bad_pending_exec_state =
     admissibility_initial
       \<lparr>exec_pending := {(ec1, admissibility_bad_event)}\<rparr>"

definition bad_acked_exec_state :: "(nat, nat) dw_exec_state"
where
  "bad_acked_exec_state =
     admissibility_initial
       \<lparr>exec_acked := [(ec1, admissibility_bad_event)]\<rparr>"

definition out_of_order_first_exec_state :: "(nat, nat) dw_exec_state"
where
  "out_of_order_first_exec_state =
     admissibility_initial
       \<lparr>exec_src_hist := [(ec2, admissibility_bad_event)]\<rparr>"

definition out_of_order_exec_state :: "(nat, nat) dw_exec_state"
where
  "out_of_order_exec_state =
     admissibility_initial
       \<lparr>exec_src_hist :=
          [(ec2, admissibility_bad_event),
           (ec1, admissibility_bad_event)]\<rparr>"

lemma admissibility_initial_wellformed:
  "wellformed_exec_state admissibility_initial"
  by (simp add: admissibility_initial_def)

lemma bad_history_exec_state_drop_one:
  "\<not> exec_histories_wellformed bad_history_exec_state
   \<and> pending_enqueued_consistent bad_history_exec_state
   \<and> acked_source_consistent bad_history_exec_state"
  by (auto simp: bad_history_exec_state_def admissibility_initial_def
                 admissibility_bad_event_def initial_exec_state_def
                 exec_histories_wellformed_def wellformed_src_history_def
                 pending_enqueued_consistent_def acked_source_consistent_def)

lemma bad_pending_exec_state_drop_one:
  "exec_histories_wellformed bad_pending_exec_state
   \<and> \<not> pending_enqueued_consistent bad_pending_exec_state
   \<and> acked_source_consistent bad_pending_exec_state"
  by (auto simp: bad_pending_exec_state_def admissibility_initial_def
                 admissibility_bad_event_def initial_exec_state_def
                 exec_histories_wellformed_def wellformed_src_history_def
                 pending_enqueued_consistent_def acked_source_consistent_def
                 ec_defs c0_def)

lemma bad_acked_exec_state_drop_one:
  "exec_histories_wellformed bad_acked_exec_state
   \<and> pending_enqueued_consistent bad_acked_exec_state
   \<and> \<not> acked_source_consistent bad_acked_exec_state"
  using c0_neq_ec1
  by (auto simp: bad_acked_exec_state_def admissibility_initial_def
                 admissibility_bad_event_def initial_exec_state_def
                 exec_histories_wellformed_def wellformed_src_history_def
                 pending_enqueued_consistent_def acked_source_consistent_def)

lemma exec_histories_wellformed_is_load_bearing:
  "\<exists>s::(nat, nat) dw_exec_state.
      \<not> exec_histories_wellformed s
    \<and> pending_enqueued_consistent s
    \<and> acked_source_consistent s"
  using bad_history_exec_state_drop_one by blast

lemma pending_enqueued_consistent_is_load_bearing:
  "\<exists>s::(nat, nat) dw_exec_state.
      exec_histories_wellformed s
    \<and> \<not> pending_enqueued_consistent s
    \<and> acked_source_consistent s"
  using bad_pending_exec_state_drop_one by blast

lemma acked_source_consistent_is_load_bearing:
  "\<exists>s::(nat, nat) dw_exec_state.
      exec_histories_wellformed s
    \<and> pending_enqueued_consistent s
    \<and> \<not> acked_source_consistent s"
  using bad_acked_exec_state_drop_one by blast

lemma bad_history_exec_state_not_wellformed:
  "\<not> wellformed_exec_state bad_history_exec_state"
  using bad_history_exec_state_drop_one
  by (simp add: wellformed_exec_state_def)

lemma bad_pending_exec_state_not_wellformed:
  "\<not> wellformed_exec_state bad_pending_exec_state"
  using bad_pending_exec_state_drop_one
  by (simp add: wellformed_exec_state_def)

lemma bad_acked_exec_state_not_wellformed:
  "\<not> wellformed_exec_state bad_acked_exec_state"
  using bad_acked_exec_state_drop_one
  by (simp add: wellformed_exec_state_def)

lemma bad_history_empty_raw_trace_not_admissible:
  "dw_exec_trace bad_history_exec_state [] bad_history_exec_state
   \<and> \<not> admissible_dw_exec_trace
        bad_history_exec_state [] bad_history_exec_state"
  using bad_history_exec_state_not_wellformed
  by (auto intro: dw_exec_trace.trace_refl
           dest: admissible_dw_exec_trace_start_wellformed)

lemma bad_pending_empty_raw_trace_not_admissible:
  "dw_exec_trace bad_pending_exec_state [] bad_pending_exec_state
   \<and> \<not> admissible_dw_exec_trace
        bad_pending_exec_state [] bad_pending_exec_state"
  using bad_pending_exec_state_not_wellformed
  by (auto intro: dw_exec_trace.trace_refl
           dest: admissible_dw_exec_trace_start_wellformed)

lemma bad_acked_empty_raw_trace_not_admissible:
  "dw_exec_trace bad_acked_exec_state [] bad_acked_exec_state
   \<and> \<not> admissible_dw_exec_trace
        bad_acked_exec_state [] bad_acked_exec_state"
  using bad_acked_exec_state_not_wellformed
  by (auto intro: dw_exec_trace.trace_refl
           dest: admissible_dw_exec_trace_start_wellformed)

lemma out_of_order_exec_state_not_wellformed:
  "\<not> wellformed_exec_state out_of_order_exec_state"
  by (auto simp: out_of_order_exec_state_def admissibility_initial_def
                 admissibility_bad_event_def initial_exec_state_def
                 wellformed_exec_state_def exec_histories_wellformed_def
                 wellformed_src_history_def ec_defs)

lemma wellformed_exec_state_conjuncts_load_bearing:
  "(\<exists>s::(nat, nat) dw_exec_state.
      \<not> exec_histories_wellformed s
    \<and> pending_enqueued_consistent s
    \<and> acked_source_consistent s)
   \<and> (\<exists>s::(nat, nat) dw_exec_state.
      exec_histories_wellformed s
    \<and> \<not> pending_enqueued_consistent s
    \<and> acked_source_consistent s)
   \<and> (\<exists>s::(nat, nat) dw_exec_state.
      exec_histories_wellformed s
    \<and> pending_enqueued_consistent s
    \<and> \<not> acked_source_consistent s)"
  using exec_histories_wellformed_is_load_bearing
        pending_enqueued_consistent_is_load_bearing
        acked_source_consistent_is_load_bearing
  by blast

lemma base_coordinate_source_label_rejected:
  "\<not> exec_label_preserves_history_wf admissibility_initial
        (DoSource c0 admissibility_bad_event)"
  by (simp add: exec_label_preserves_history_wf_def
                admissibility_initial_def initial_exec_state_def
                history_can_append_def)

lemma raw_base_coordinate_source_step:
  "dw_exec_step admissibility_initial
     (DoSource c0 admissibility_bad_event)
     bad_history_exec_state"
proof -
  have step:
    "dw_exec_step admissibility_initial
       (DoSource c0 admissibility_bad_event)
       (admissibility_initial
          \<lparr>exec_src_hist :=
             exec_src_hist admissibility_initial
             @ [(c0, admissibility_bad_event)]\<rparr>)"
    by (rule dw_exec_step.do_source)
       (simp add: admissibility_initial_def initial_exec_state_def)
  have
    "admissibility_initial
       \<lparr>exec_src_hist :=
          exec_src_hist admissibility_initial
          @ [(c0, admissibility_bad_event)]\<rparr>
     = bad_history_exec_state"
    by (simp add: bad_history_exec_state_def admissibility_initial_def
                  initial_exec_state_def)
  with step show ?thesis
    by simp
qed

lemma raw_base_coordinate_source_trace:
  "dw_exec_trace admissibility_initial
     [DoSource c0 admissibility_bad_event]
     bad_history_exec_state"
  by (meson dw_exec_trace.trace_refl dw_exec_trace.trace_step
            raw_base_coordinate_source_step)

lemma base_coordinate_source_trace_not_admissible:
  "\<not> admissible_dw_exec_trace admissibility_initial
        [DoSource c0 admissibility_bad_event]
        bad_history_exec_state"
proof
  assume adm:
    "admissible_dw_exec_trace admissibility_initial
       [DoSource c0 admissibility_bad_event]
       bad_history_exec_state"
  have "wellformed_exec_state bad_history_exec_state"
    by (rule admissible_dw_exec_trace_final_wellformed[OF adm])
  with bad_history_exec_state_not_wellformed show False
    by simp
qed

lemma out_of_order_first_raw_source_step:
  "dw_exec_step admissibility_initial
     (DoSource ec2 admissibility_bad_event)
     out_of_order_first_exec_state"
proof -
  have step:
    "dw_exec_step admissibility_initial
       (DoSource ec2 admissibility_bad_event)
       (admissibility_initial
          \<lparr>exec_src_hist :=
             exec_src_hist admissibility_initial
             @ [(ec2, admissibility_bad_event)]\<rparr>)"
    by (rule dw_exec_step.do_source)
       (simp add: admissibility_initial_def initial_exec_state_def)
  have
    "admissibility_initial
       \<lparr>exec_src_hist :=
          exec_src_hist admissibility_initial
          @ [(ec2, admissibility_bad_event)]\<rparr>
     = out_of_order_first_exec_state"
    by (simp add: out_of_order_first_exec_state_def admissibility_initial_def
                  initial_exec_state_def)
  with step show ?thesis
    by simp
qed

lemma out_of_order_second_raw_source_step:
  "dw_exec_step out_of_order_first_exec_state
     (DoSource ec1 admissibility_bad_event)
     out_of_order_exec_state"
proof -
  have step:
    "dw_exec_step out_of_order_first_exec_state
       (DoSource ec1 admissibility_bad_event)
       (out_of_order_first_exec_state
          \<lparr>exec_src_hist :=
             exec_src_hist out_of_order_first_exec_state
             @ [(ec1, admissibility_bad_event)]\<rparr>)"
    by (rule dw_exec_step.do_source)
       (simp add: out_of_order_first_exec_state_def admissibility_initial_def
                  initial_exec_state_def)
  have
    "out_of_order_first_exec_state
       \<lparr>exec_src_hist :=
          exec_src_hist out_of_order_first_exec_state
          @ [(ec1, admissibility_bad_event)]\<rparr>
     = out_of_order_exec_state"
    by (simp add: out_of_order_first_exec_state_def out_of_order_exec_state_def
                  admissibility_initial_def initial_exec_state_def)
  with step show ?thesis
    by simp
qed

lemma raw_out_of_order_source_trace:
  "dw_exec_trace admissibility_initial
     [DoSource ec2 admissibility_bad_event,
      DoSource ec1 admissibility_bad_event]
     out_of_order_exec_state"
  by (meson dw_exec_trace.trace_refl dw_exec_trace.trace_step
            out_of_order_first_raw_source_step
            out_of_order_second_raw_source_step)

lemma out_of_order_source_trace_not_admissible:
  "\<not> admissible_dw_exec_trace admissibility_initial
        [DoSource ec2 admissibility_bad_event,
         DoSource ec1 admissibility_bad_event]
        out_of_order_exec_state"
proof
  assume adm:
    "admissible_dw_exec_trace admissibility_initial
       [DoSource ec2 admissibility_bad_event,
        DoSource ec1 admissibility_bad_event]
       out_of_order_exec_state"
  have "wellformed_exec_state out_of_order_exec_state"
    by (rule admissible_dw_exec_trace_final_wellformed[OF adm])
  with out_of_order_exec_state_not_wellformed show False
    by simp
qed

lemma admissible_wrapper_accepts_some_trace:
  "\<exists>s::(nat, nat) dw_exec_state. admissible_dw_exec_trace s [] s"
proof
  show "admissible_dw_exec_trace admissibility_initial [] admissibility_initial"
    by (rule admissible_dw_exec_trace.admissible_trace_refl
        [OF admissibility_initial_wellformed])
qed

lemma admissible_wrapper_rejects_some_raw_trace:
  "\<exists>s as s'::(nat, nat) dw_exec_state.
      wellformed_exec_state s
    \<and> dw_exec_trace s as s'
    \<and> \<not> admissible_dw_exec_trace s as s'"
  using admissibility_initial_wellformed raw_base_coordinate_source_trace
        base_coordinate_source_trace_not_admissible
  by blast

lemma admissible_wrapper_rejects_out_of_order_raw_trace:
  "\<exists>s as s'::(nat, nat) dw_exec_state.
      wellformed_exec_state s
    \<and> dw_exec_trace s as s'
    \<and> \<not> admissible_dw_exec_trace s as s'
    \<and> as =
       [DoSource ec2 admissibility_bad_event,
        DoSource ec1 admissibility_bad_event]"
  using admissibility_initial_wellformed raw_out_of_order_source_trace
        out_of_order_source_trace_not_admissible
  by blast

theorem admissible_wrapper_is_nontrivial:
  "(\<exists>s::(nat, nat) dw_exec_state. admissible_dw_exec_trace s [] s)
   \<and> (\<exists>s as s'::(nat, nat) dw_exec_state.
      wellformed_exec_state s
    \<and> dw_exec_trace s as s'
    \<and> \<not> admissible_dw_exec_trace s as s')
   \<and> (\<exists>s as s'::(nat, nat) dw_exec_state.
      wellformed_exec_state s
    \<and> dw_exec_trace s as s'
    \<and> \<not> admissible_dw_exec_trace s as s'
    \<and> as =
       [DoSource ec2 admissibility_bad_event,
        DoSource ec1 admissibility_bad_event])
   \<and> (\<exists>s::(nat, nat) dw_exec_state.
      \<not> exec_histories_wellformed s
    \<and> pending_enqueued_consistent s
    \<and> acked_source_consistent s)
   \<and> (\<exists>s::(nat, nat) dw_exec_state.
      exec_histories_wellformed s
    \<and> \<not> pending_enqueued_consistent s
    \<and> acked_source_consistent s)
   \<and> (\<exists>s::(nat, nat) dw_exec_state.
      exec_histories_wellformed s
    \<and> pending_enqueued_consistent s
    \<and> \<not> acked_source_consistent s)"
  using admissible_wrapper_accepts_some_trace
        admissible_wrapper_rejects_some_raw_trace
        admissible_wrapper_rejects_out_of_order_raw_trace
        wellformed_exec_state_conjuncts_load_bearing
  by blast

end
