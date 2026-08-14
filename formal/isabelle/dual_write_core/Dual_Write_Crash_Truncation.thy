(*  Title:       Dual_Write_Crash_Truncation.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Explicit crash-truncation and durability-boundary semantics for the
    dual-write execution layer.  This theory is additive: the base execution
    relation keeps its status-flip crash rule, while this layer records the
    stronger model in which a crash first cuts durable histories and metadata
    back to their advertised crash-surviving prefixes.
*)

theory Dual_Write_Crash_Truncation
  imports Dual_Write_Delivery_Realism
begin

section \<open>Durable prefixes and truncating crashes\<close>

record dw_durable_boundary =
  db_src :: frontier
  db_down :: frontier
  db_enq :: frontier
  db_ack :: frontier

definition single_durable_boundary :: "frontier \<Rightarrow> dw_durable_boundary"
where
  "single_durable_boundary d =
     \<lparr> db_src = d, db_down = d, db_enq = d, db_ack = d \<rparr>"

definition durable_boundary_within_finish
  :: "dw_durable_boundary \<Rightarrow> ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "durable_boundary_within_finish B s \<longleftrightarrow>
     db_src B \<le> exec_finish s
   \<and> db_down B \<le> exec_finish s
   \<and> db_enq B \<le> exec_finish s
   \<and> db_ack B \<le> exec_finish s"

definition durable_history_prefix_at
  :: "frontier \<Rightarrow> ('k, 'v) src_history \<Rightarrow> ('k, 'v) src_history"
where
  "durable_history_prefix_at d H = takeWhile (\<lambda>x. fst x \<le> d) H"

definition durable_ack_frontier :: "dw_durable_boundary \<Rightarrow> frontier"
where
  "durable_ack_frontier B = min (db_ack B) (db_src B)"

definition durable_pending_at_boundary
  :: "dw_durable_boundary \<Rightarrow> ('k, 'v) dw_exec_state \<Rightarrow>
      (src_coord \<times> ('k, 'v) source_event) set"
where
  "durable_pending_at_boundary B s =
     set (durable_history_prefix_at (db_enq B) (exec_enqueued s))
   - set (durable_history_prefix_at (db_down B) (exec_down_hist s))"

definition durable_exec_state_at_boundary
  :: "('k, 'v) dw_exec_state \<Rightarrow> dw_durable_boundary \<Rightarrow>
      ('k, 'v) dw_exec_state"
where
  "durable_exec_state_at_boundary s B =
     s\<lparr> exec_src_hist := durable_history_prefix_at (db_src B) (exec_src_hist s),
        exec_down_hist := durable_history_prefix_at (db_down B) (exec_down_hist s),
        exec_enqueued := durable_history_prefix_at (db_enq B) (exec_enqueued s),
        exec_pending := durable_pending_at_boundary B s,
        exec_acked := durable_history_prefix_at (durable_ack_frontier B)
          (exec_acked s) \<rparr>"

definition durable_exec_state
  :: "('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow> ('k, 'v) dw_exec_state"
where
  "durable_exec_state s d =
     durable_exec_state_at_boundary s (single_durable_boundary d)"

definition truncating_crash_state_at_boundary
  :: "('k, 'v) dw_exec_state \<Rightarrow> dw_durable_boundary \<Rightarrow> frontier \<Rightarrow>
      ('k, 'v) dw_exec_state"
where
  "truncating_crash_state_at_boundary s B c =
     (durable_exec_state_at_boundary s B)\<lparr>exec_status := Crashed c\<rparr>"

definition truncating_crash_state
  :: "('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow> frontier \<Rightarrow>
      ('k, 'v) dw_exec_state"
where
  "truncating_crash_state s d c =
     truncating_crash_state_at_boundary s (single_durable_boundary d) c"

inductive truncating_crash_step_at_boundary
  :: "('k, 'v) dw_exec_state \<Rightarrow> dw_durable_boundary \<Rightarrow> frontier \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  truncating_crash:
    "\<lbrakk>wellformed_exec_state s; exec_status s = Running;
      durable_boundary_within_finish B s\<rbrakk> \<Longrightarrow>
     truncating_crash_step_at_boundary s B c
       (truncating_crash_state_at_boundary s B c)"

inductive truncating_crash_step
  :: "('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow> frontier \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  truncating_crash:
    "\<lbrakk>wellformed_exec_state s; exec_status s = Running;
      d \<le> exec_finish s\<rbrakk> \<Longrightarrow>
     truncating_crash_step s d c (truncating_crash_state s d c)"

lemma durable_boundary_within_single [simp]:
  "durable_boundary_within_finish (single_durable_boundary d) s \<longleftrightarrow>
   d \<le> exec_finish s"
  by (simp add: durable_boundary_within_finish_def single_durable_boundary_def)

lemma durable_history_prefix_set_subset:
  "set (durable_history_prefix_at d H) \<subseteq> set H"
  by (induction H) (auto simp: durable_history_prefix_at_def)

lemma durable_history_prefix_at_empty [simp]:
  "durable_history_prefix_at d [] = []"
  by (simp add: durable_history_prefix_at_def)

lemma source_pos_order_total:
  assumes "i \<noteq> j"
  shows "source_pos_order H i j \<or> source_pos_order H j i"
  using assms
  by (metis linorder_cases nat_le_linear source_pos_order_def
            src_lt_eq_less)

lemma wellformed_src_history_tail:
  assumes "wellformed_src_history (x # xs)"
  shows "wellformed_src_history xs"
  using assms
  by (auto simp: wellformed_src_history_def source_pos_order_total
                 nth_Cons src_le_eq_less_eq split: nat.splits)

lemma wellformed_src_history_cons_le_set:
  assumes wf: "wellformed_src_history (x # xs)"
      and y: "y \<in> set xs"
  shows "fst x \<le> fst y"
  using wf y
proof (induction xs arbitrary: x)
  case Nil
  thus ?case by simp
next
  case (Cons z zs)
  have x_le_z: "fst x \<le> fst z"
    using Cons.prems(1)
    by (auto simp: wellformed_src_history_def src_le_eq_less_eq)
  show ?case
  proof (cases "y = z")
    case True
    with x_le_z show ?thesis by simp
  next
    case False
    with Cons.prems(2) have y_zs: "y \<in> set zs" by simp
    have tail_wf: "wellformed_src_history (z # zs)"
      by (rule wellformed_src_history_tail[OF Cons.prems(1)])
    have z_le_y: "fst z \<le> fst y"
      by (rule Cons.IH[OF tail_wf y_zs])
    from x_le_z z_le_y show ?thesis by (rule order_trans)
  qed
qed

lemma durable_history_prefix_set_eq:
  assumes wf: "wellformed_src_history H"
  shows "set (durable_history_prefix_at d H) =
    {x \<in> set H. fst x \<le> d}"
  using wf
proof (induction H)
  case Nil
  show ?case by (simp add: durable_history_prefix_at_def)
next
  case (Cons x xs)
  have tail_wf: "wellformed_src_history xs"
    by (rule wellformed_src_history_tail[OF Cons.prems])
  show ?case
  proof (cases "fst x \<le> d")
    case True
    with Cons.IH[OF tail_wf] show ?thesis
      by (auto simp: durable_history_prefix_at_def)
  next
    case False
    have no_tail: "\<forall>y \<in> set xs. \<not> fst y \<le> d"
    proof
      fix y
      assume y: "y \<in> set xs"
      have "fst x \<le> fst y"
        by (rule wellformed_src_history_cons_le_set[OF Cons.prems y])
      with False show "\<not> fst y \<le> d"
        by auto
    qed
    with False show ?thesis
      by (auto simp: durable_history_prefix_at_def)
  qed
qed

definition history_within_frontier
  :: "frontier \<Rightarrow> ('k, 'v) src_history \<Rightarrow> bool"
where
  "history_within_frontier d H \<longleftrightarrow> (\<forall>x \<in> set H. fst x \<le> d)"

definition exec_within_durable_boundary
  :: "dw_durable_boundary \<Rightarrow> ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "exec_within_durable_boundary B s \<longleftrightarrow>
     history_within_frontier (db_src B) (exec_src_hist s)
   \<and> history_within_frontier (db_down B) (exec_down_hist s)
   \<and> history_within_frontier (db_enq B) (exec_enqueued s)
   \<and> history_within_frontier (durable_ack_frontier B) (exec_acked s)
   \<and> exec_pending s = durable_pending_at_boundary B s"

definition exec_within_durable_frontier
  :: "frontier \<Rightarrow> ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "exec_within_durable_frontier d s \<longleftrightarrow>
     exec_within_durable_boundary (single_durable_boundary d) s"

lemma durable_history_prefix_at_id:
  assumes "history_within_frontier d H"
  shows "durable_history_prefix_at d H = H"
  using assms
  by (induction H) (auto simp: durable_history_prefix_at_def
                               history_within_frontier_def)

lemma durable_exec_state_at_boundary_id:
  assumes "exec_within_durable_boundary B s"
  shows "durable_exec_state_at_boundary s B = s"
  using assms
  by (simp add: durable_exec_state_at_boundary_def
                exec_within_durable_boundary_def durable_history_prefix_at_id)

lemma durable_exec_state_id:
  assumes "exec_within_durable_frontier d s"
  shows "durable_exec_state s d = s"
  using assms
  by (simp add: durable_exec_state_def exec_within_durable_frontier_def
                durable_exec_state_at_boundary_id)

theorem no_truncation_crash_recovers_old_crash:
  assumes "exec_within_durable_boundary B s"
  shows "truncating_crash_state_at_boundary s B c =
         s\<lparr>exec_status := Crashed c\<rparr>"
  using assms
  by (simp add: truncating_crash_state_at_boundary_def
                durable_exec_state_at_boundary_id)

corollary no_truncation_frontier_crash_recovers_old_crash:
  assumes "exec_within_durable_frontier d s"
  shows "truncating_crash_state s d c = s\<lparr>exec_status := Crashed c\<rparr>"
  using assms
  by (simp add: truncating_crash_state_def exec_within_durable_frontier_def
                no_truncation_crash_recovers_old_crash)

theorem no_truncation_truncating_crash_refines_old_crash_step:
  assumes step: "truncating_crash_step_at_boundary s B c s'"
      and within: "exec_within_durable_boundary B s"
  shows "dw_exec_step s (Crash c) s'"
  using step
proof cases
  case truncating_crash
  from within have state:
    "truncating_crash_state_at_boundary s B c =
       s\<lparr>exec_status := Crashed c\<rparr>"
    by (rule no_truncation_crash_recovers_old_crash)
  show ?thesis
    using truncating_crash state by (simp add: dw_exec_step.crash)
qed

corollary no_truncation_frontier_crash_refines_old_crash_step:
  assumes step: "truncating_crash_step s d c s'"
      and within: "exec_within_durable_frontier d s"
  shows "dw_exec_step s (Crash c) s'"
  using step
proof cases
  case truncating_crash
  from within have state:
    "truncating_crash_state s d c = s\<lparr>exec_status := Crashed c\<rparr>"
    by (rule no_truncation_frontier_crash_recovers_old_crash)
  show ?thesis
    using truncating_crash state by (simp add: dw_exec_step.crash)
qed

lemma truncating_crash_pending_honest:
  "exec_pending (truncating_crash_state_at_boundary s B c) =
   set (exec_enqueued (truncating_crash_state_at_boundary s B c)) -
   set (exec_down_hist (truncating_crash_state_at_boundary s B c))"
  by (simp add: truncating_crash_state_at_boundary_def
                durable_exec_state_at_boundary_def
                durable_pending_at_boundary_def)

section \<open>Bad crashes with explicit durable state\<close>

definition durable_bad_crash_enabled_at_boundary
  :: "('k, 'v) dw_exec_state \<Rightarrow> dw_durable_boundary \<Rightarrow> frontier \<Rightarrow>
      'k \<Rightarrow> bool"
where
  "durable_bad_crash_enabled_at_boundary s B c k \<longleftrightarrow>
     wellformed_exec_state s
   \<and> exec_status s = Running
   \<and> durable_boundary_within_finish B s
   \<and> c \<le> exec_finish s
   \<and> mismatch_at (proto_of_exec_at (durable_exec_state_at_boundary s B) c) c k"

definition durable_bad_crash_enabled
  :: "('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> bool"
where
  "durable_bad_crash_enabled s d c k \<longleftrightarrow>
     durable_bad_crash_enabled_at_boundary s (single_durable_boundary d) c k"

definition durable_acked_source_effect_at_boundary
  :: "('k, 'v) dw_exec_state \<Rightarrow> dw_durable_boundary \<Rightarrow> frontier \<Rightarrow>
      'k \<Rightarrow> bool"
where
  "durable_acked_source_effect_at_boundary s B c k \<longleftrightarrow>
     acked_source_effect_at (durable_exec_state_at_boundary s B) c k"

definition durable_acked_source_effect_at
  :: "('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> bool"
where
  "durable_acked_source_effect_at s d c k \<longleftrightarrow>
     durable_acked_source_effect_at_boundary s (single_durable_boundary d) c k"

definition durable_acked_bad_crash_enabled_at_boundary
  :: "('k, 'v) dw_exec_state \<Rightarrow> dw_durable_boundary \<Rightarrow> frontier \<Rightarrow>
      'k \<Rightarrow> bool"
where
  "durable_acked_bad_crash_enabled_at_boundary s B c k \<longleftrightarrow>
     durable_bad_crash_enabled_at_boundary s B c k
   \<and> durable_acked_source_effect_at_boundary s B c k"

definition durable_acked_bad_crash_enabled
  :: "('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> bool"
where
  "durable_acked_bad_crash_enabled s d c k \<longleftrightarrow>
     durable_acked_bad_crash_enabled_at_boundary
       s (single_durable_boundary d) c k"

theorem durable_bad_crash_enabled_at_boundary_extend:
  assumes enabled: "durable_bad_crash_enabled_at_boundary s B c k"
  shows "\<exists>s'.
      truncating_crash_step_at_boundary s B c s'
    \<and> observable_mismatch s' c k
    \<and> diverges (proto_of_exec_at s' c) c"
proof -
  let ?s' = "truncating_crash_state_at_boundary s B c"
  from enabled have wf: "wellformed_exec_state s"
      and running: "exec_status s = Running"
      and boundary: "durable_boundary_within_finish B s"
      and le_fin: "c \<le> exec_finish s"
      and mismatch:
        "mismatch_at
          (proto_of_exec_at (durable_exec_state_at_boundary s B) c) c k"
    by (auto simp: durable_bad_crash_enabled_at_boundary_def)
  have step: "truncating_crash_step_at_boundary s B c ?s'"
    by (rule truncating_crash_step_at_boundary.truncating_crash
        [OF wf running boundary])
  have obs: "observable_mismatch ?s' c k"
    using le_fin mismatch
    by (simp add: observable_mismatch_def truncating_crash_state_at_boundary_def
                  durable_exec_state_at_boundary_def)
  hence div: "diverges (proto_of_exec_at ?s' c) c"
    by (rule observable_mismatch_imp_diverges)
  from step obs div show ?thesis by blast
qed

theorem durable_bad_crash_enabled_extend:
  assumes enabled: "durable_bad_crash_enabled s d c k"
  shows "\<exists>s'.
      truncating_crash_step s d c s'
    \<and> observable_mismatch s' c k
    \<and> diverges (proto_of_exec_at s' c) c"
proof -
  let ?B = "single_durable_boundary d"
  let ?s' = "truncating_crash_state s d c"
  from enabled have wf: "wellformed_exec_state s"
      and running: "exec_status s = Running"
      and durable: "d \<le> exec_finish s"
      and le_fin: "c \<le> exec_finish s"
      and mismatch:
        "mismatch_at (proto_of_exec_at (durable_exec_state s d) c) c k"
    by (auto simp: durable_bad_crash_enabled_def
                   durable_bad_crash_enabled_at_boundary_def
                   durable_exec_state_def)
  have step: "truncating_crash_step s d c ?s'"
    by (rule truncating_crash_step.truncating_crash[OF wf running durable])
  have obs: "observable_mismatch ?s' c k"
    using le_fin mismatch
    by (simp add: observable_mismatch_def truncating_crash_state_def
                  truncating_crash_state_at_boundary_def
                  durable_exec_state_def durable_exec_state_at_boundary_def)
  hence div: "diverges (proto_of_exec_at ?s' c) c"
    by (rule observable_mismatch_imp_diverges)
  from step obs div show ?thesis by blast
qed

theorem durable_acked_bad_crash_enabled_at_boundary_extend:
  assumes enabled: "durable_acked_bad_crash_enabled_at_boundary s B c k"
  shows "\<exists>s'.
      truncating_crash_step_at_boundary s B c s'
    \<and> acked_observable_mismatch s' c k
    \<and> diverges (proto_of_exec_at s' c) c"
proof -
  let ?s' = "truncating_crash_state_at_boundary s B c"
  from enabled have bad: "durable_bad_crash_enabled_at_boundary s B c k"
      and ack:
        "acked_source_effect_at
          (durable_exec_state_at_boundary s B) c k"
    by (auto simp: durable_acked_bad_crash_enabled_at_boundary_def
                   durable_acked_source_effect_at_boundary_def)
  then have wf: "wellformed_exec_state s"
      and running: "exec_status s = Running"
      and boundary: "durable_boundary_within_finish B s"
      and le_fin: "c \<le> exec_finish s"
      and mismatch:
        "mismatch_at
          (proto_of_exec_at (durable_exec_state_at_boundary s B) c) c k"
    by (auto simp: durable_bad_crash_enabled_at_boundary_def)
  have step: "truncating_crash_step_at_boundary s B c ?s'"
    by (rule truncating_crash_step_at_boundary.truncating_crash
        [OF wf running boundary])
  have obs: "observable_mismatch ?s' c k"
    using le_fin mismatch
    by (simp add: observable_mismatch_def truncating_crash_state_at_boundary_def
                  durable_exec_state_at_boundary_def)
  have acked: "acked_observable_mismatch ?s' c k"
    using obs ack
    by (simp add: acked_observable_mismatch_def acked_source_effect_at_def
                  truncating_crash_state_at_boundary_def
                  durable_exec_state_at_boundary_def)
  hence div: "diverges (proto_of_exec_at ?s' c) c"
    by (rule acked_observable_mismatch_imp_diverges)
  from step acked div show ?thesis by blast
qed

theorem durable_acked_bad_crash_enabled_extend:
  assumes enabled: "durable_acked_bad_crash_enabled s d c k"
  shows "\<exists>s'.
      truncating_crash_step s d c s'
    \<and> acked_observable_mismatch s' c k
    \<and> diverges (proto_of_exec_at s' c) c"
proof -
  let ?s' = "truncating_crash_state s d c"
  from enabled have bad: "durable_bad_crash_enabled s d c k"
      and ack: "acked_source_effect_at (durable_exec_state s d) c k"
    by (auto simp: durable_acked_bad_crash_enabled_def
                   durable_acked_bad_crash_enabled_at_boundary_def
                   durable_bad_crash_enabled_def
                   durable_acked_source_effect_at_boundary_def
                   durable_exec_state_def)
  then have wf: "wellformed_exec_state s"
      and running: "exec_status s = Running"
      and durable: "d \<le> exec_finish s"
      and le_fin: "c \<le> exec_finish s"
      and mismatch:
        "mismatch_at (proto_of_exec_at (durable_exec_state s d) c) c k"
    by (auto simp: durable_bad_crash_enabled_def
                   durable_bad_crash_enabled_at_boundary_def
                   durable_exec_state_def)
  have step: "truncating_crash_step s d c ?s'"
    by (rule truncating_crash_step.truncating_crash[OF wf running durable])
  have obs: "observable_mismatch ?s' c k"
    using le_fin mismatch
    by (simp add: observable_mismatch_def truncating_crash_state_def
                  truncating_crash_state_at_boundary_def
                  durable_exec_state_def durable_exec_state_at_boundary_def)
  have acked: "acked_observable_mismatch ?s' c k"
    using obs ack
    by (simp add: acked_observable_mismatch_def acked_source_effect_at_def
                  truncating_crash_state_def truncating_crash_state_at_boundary_def
                  durable_exec_state_def durable_exec_state_at_boundary_def)
  hence div: "diverges (proto_of_exec_at ?s' c) c"
    by (rule acked_observable_mismatch_imp_diverges)
  from step acked div show ?thesis by blast
qed

corollary bad_crash_enabled_no_truncation_imp_durable_bad_crash_enabled:
  assumes bad: "bad_crash_enabled s c k"
      and within: "exec_within_durable_frontier d s"
      and durable: "d \<le> exec_finish s"
      and wf: "wellformed_exec_state s"
  shows "durable_bad_crash_enabled s d c k"
proof -
  have id: "durable_exec_state s d = s"
    by (rule durable_exec_state_id[OF within])
  show ?thesis
    using bad durable wf id
    by (simp add: bad_crash_enabled_def durable_bad_crash_enabled_def
                  durable_bad_crash_enabled_at_boundary_def
                  durable_exec_state_def)
qed

corollary bad_crash_enabled_finish_no_truncation_imp_durable_bad_crash_enabled:
  assumes bad: "bad_crash_enabled s c k"
      and within: "exec_within_durable_frontier (exec_finish s) s"
      and wf: "wellformed_exec_state s"
  shows "durable_bad_crash_enabled s (exec_finish s) c k"
  by (rule bad_crash_enabled_no_truncation_imp_durable_bad_crash_enabled
      [OF bad within _ wf])
     simp

lemma truncating_crash_preserves_downstream_absence:
  assumes absent: "no_visible_key_events (exec_down_hist s) c k"
  shows "no_visible_key_events
    (exec_down_hist (truncating_crash_state_at_boundary s B f)) c k"
proof -
  have subset:
    "set (durable_history_prefix_at (db_down B) (exec_down_hist s))
      \<subseteq> set (exec_down_hist s)"
    by (rule durable_history_prefix_set_subset)
  show ?thesis
    using absent subset
    by (auto simp: truncating_crash_state_at_boundary_def
                   durable_exec_state_at_boundary_def
                   no_visible_key_events_def)
qed

section \<open>Delivery faults followed by truncating crashes\<close>

definition durable_pending_queue_at_boundary
  :: "dw_durable_boundary \<Rightarrow> ('k, 'v) dw_delivery_state \<Rightarrow>
      (src_coord \<times> ('k, 'v) source_event) list"
where
  "durable_pending_queue_at_boundary B S =
     fold remove1
       (durable_history_prefix_at (db_down B)
          (exec_down_hist (del_exec S)))
       (durable_history_prefix_at (db_enq B)
          (exec_enqueued (del_exec S)))"

definition truncating_delivery_crash_state_at_boundary
  :: "('k, 'v) dw_delivery_state \<Rightarrow> dw_durable_boundary \<Rightarrow> frontier \<Rightarrow>
      ('k, 'v) dw_delivery_state"
where
  "truncating_delivery_crash_state_at_boundary S B c =
     (let q = durable_pending_queue_at_boundary B S
      in S\<lparr> del_exec :=
           (truncating_crash_state_at_boundary (del_exec S) B c)
             \<lparr>exec_pending := set q\<rparr>,
         del_pending := q \<rparr>)"

inductive truncating_delivery_crash_step_at_boundary
  :: "('k, 'v) dw_delivery_state \<Rightarrow> dw_durable_boundary \<Rightarrow> frontier \<Rightarrow>
      ('k, 'v) dw_delivery_state \<Rightarrow> bool"
where
  truncating_delivery_crash:
    "truncating_crash_step_at_boundary (del_exec S) B c s' \<Longrightarrow>
     truncating_delivery_crash_step_at_boundary S B c
       (let q = durable_pending_queue_at_boundary B S
        in S\<lparr> del_exec := s'\<lparr>exec_pending := set q\<rparr>,
             del_pending := q \<rparr>)"

lemma truncating_delivery_crash_set_view_consistent:
  "delivery_set_view_consistent
    (truncating_delivery_crash_state_at_boundary S B c)"
  by (simp add: delivery_set_view_consistent_def
                truncating_delivery_crash_state_at_boundary_def Let_def)

lemma delivery_trace_preserves_set_view:
  assumes trace: "delivery_trace S xs S'"
      and consistent: "delivery_set_view_consistent S"
  shows "delivery_set_view_consistent S'"
  using trace consistent
proof (induction rule: delivery_trace.induct)
  case (delivery_trace_refl S)
  show ?case by (rule delivery_trace_refl.prems)
next
  case (delivery_trace_step S a S' xs S'')
  have consistent': "delivery_set_view_consistent S'"
    by (rule delivery_step_preserves_set_view
        [OF delivery_trace_step.hyps(1) delivery_trace_step.prems])
  show ?case by (rule delivery_trace_step.IH[OF consistent'])
qed

lemma delivery_fault_step_preserves_exec_histories:
  assumes step: "delivery_step S a S'"
      and fault: "delivery_fault_label a"
  shows "exec_base (del_exec S') = exec_base (del_exec S)"
        "exec_src_hist (del_exec S') = exec_src_hist (del_exec S)"
        "exec_down_hist (del_exec S') = exec_down_hist (del_exec S)"
        "exec_enqueued (del_exec S') = exec_enqueued (del_exec S)"
        "exec_scope (del_exec S') = exec_scope (del_exec S)"
        "exec_acked (del_exec S') = exec_acked (del_exec S)"
  using step fault
  by (induction rule: delivery_step.induct) auto

lemma delivery_fault_trace_preserves_exec_histories:
  assumes trace: "delivery_trace S xs S'"
      and faults: "list_all delivery_fault_label xs"
  shows "exec_base (del_exec S') = exec_base (del_exec S)"
        "exec_src_hist (del_exec S') = exec_src_hist (del_exec S)"
        "exec_down_hist (del_exec S') = exec_down_hist (del_exec S)"
        "exec_enqueued (del_exec S') = exec_enqueued (del_exec S)"
        "exec_scope (del_exec S') = exec_scope (del_exec S)"
        "exec_acked (del_exec S') = exec_acked (del_exec S)"
  using trace faults
  by (induction rule: delivery_trace.induct)
     (auto dest: delivery_fault_step_preserves_exec_histories)

lemma set_remove1_subset_local:
  "set (remove1 x xs) \<subseteq> set xs"
  by (induction xs) auto

lemma delivery_fault_step_del_pending_subset:
  assumes step: "delivery_step S a S'"
      and fault: "delivery_fault_label a"
  shows "set (del_pending S') \<subseteq> set (del_pending S)"
  using step fault
  by (induction rule: delivery_step.induct)
     (auto dest!: mset_eq_setD dest: set_remove1_subset_local[THEN subsetD])

lemma delivery_fault_trace_del_pending_subset:
  assumes trace: "delivery_trace S xs S'"
      and faults: "list_all delivery_fault_label xs"
  shows "set (del_pending S') \<subseteq> set (del_pending S)"
  using trace faults
proof (induction rule: delivery_trace.induct)
  case (delivery_trace_refl S)
  show ?case by simp
next
  case (delivery_trace_step S a S' xs S'')
  have fault_a: "delivery_fault_label a"
    using delivery_trace_step.prems by simp
  have faults_xs: "list_all delivery_fault_label xs"
    using delivery_trace_step.prems by simp
  have step_subset: "set (del_pending S') \<subseteq> set (del_pending S)"
    by (rule delivery_fault_step_del_pending_subset
        [OF delivery_trace_step.hyps(1) fault_a])
  have tail_subset: "set (del_pending S'') \<subseteq> set (del_pending S')"
    by (rule delivery_trace_step.IH[OF faults_xs])
  from tail_subset step_subset show ?case by blast
qed

lemma delivery_fault_trace_preserves_wellformed_exec_state:
  assumes wf: "wellformed_exec_state (del_exec S)"
      and consistent: "delivery_set_view_consistent S"
      and trace: "delivery_trace S xs S'"
      and faults: "list_all delivery_fault_label xs"
  shows "wellformed_exec_state (del_exec S')"
proof -
  have consistent': "delivery_set_view_consistent S'"
    by (rule delivery_trace_preserves_set_view[OF trace consistent])
  have pending_subset: "set (del_pending S') \<subseteq> set (del_pending S)"
    by (rule delivery_fault_trace_del_pending_subset[OF trace faults])
  have enq:
    "exec_enqueued (del_exec S') = exec_enqueued (del_exec S)"
    by (rule delivery_fault_trace_preserves_exec_histories[OF trace faults])
  have src:
    "exec_src_hist (del_exec S') = exec_src_hist (del_exec S)"
    by (rule delivery_fault_trace_preserves_exec_histories[OF trace faults])
  have down:
    "exec_down_hist (del_exec S') = exec_down_hist (del_exec S)"
    by (rule delivery_fault_trace_preserves_exec_histories[OF trace faults])
  have ack:
    "exec_acked (del_exec S') = exec_acked (del_exec S)"
    by (rule delivery_fault_trace_preserves_exec_histories[OF trace faults])
  have histories: "exec_histories_wellformed (del_exec S')"
    using wf src down enq ack
    by (simp add: wellformed_exec_state_def exec_histories_wellformed_def)
  have pending: "pending_enqueued_consistent (del_exec S')"
    using wf consistent consistent' pending_subset enq
    by (auto simp: wellformed_exec_state_def
                   pending_enqueued_consistent_def
                   delivery_set_view_consistent_def)
  have acked: "acked_source_consistent (del_exec S')"
    using wf src ack
    by (simp add: wellformed_exec_state_def acked_source_consistent_def)
  from histories pending acked show ?thesis
    by (simp add: wellformed_exec_state_def)
qed

lemma delivery_fault_trace_preserves_durable_exec_state_at_boundary:
  assumes trace: "delivery_trace S xs S'"
      and faults: "list_all delivery_fault_label xs"
  shows "durable_exec_state_at_boundary (del_exec S') B =
         durable_exec_state_at_boundary (del_exec S) B"
  using
    delivery_fault_trace_preserves_exec_histories[OF trace faults]
    delivery_fault_trace_preserves_status[OF trace faults]
    delivery_fault_trace_preserves_finish[OF trace faults]
  by (simp add: durable_exec_state_at_boundary_def
                durable_pending_at_boundary_def)

theorem delivery_faults_preserve_durable_bad_crash_enabled_at_boundary:
  assumes enabled:
        "durable_bad_crash_enabled_at_boundary (del_exec S) B c k"
      and consistent: "delivery_set_view_consistent S"
      and trace: "delivery_trace S xs S'"
      and faults: "list_all delivery_fault_label xs"
  shows "durable_bad_crash_enabled_at_boundary (del_exec S') B c k"
proof -
  from enabled have wf: "wellformed_exec_state (del_exec S)"
      and running: "exec_status (del_exec S) = Running"
      and boundary: "durable_boundary_within_finish B (del_exec S)"
      and le_fin: "c \<le> exec_finish (del_exec S)"
      and mismatch:
        "mismatch_at
          (proto_of_exec_at
            (durable_exec_state_at_boundary (del_exec S) B) c) c k"
    by (auto simp: durable_bad_crash_enabled_at_boundary_def)
  have wf': "wellformed_exec_state (del_exec S')"
    by (rule delivery_fault_trace_preserves_wellformed_exec_state
        [OF wf consistent trace faults])
  have running': "exec_status (del_exec S') = Running"
    using running delivery_fault_trace_preserves_status[OF trace faults]
    by simp
  have boundary': "durable_boundary_within_finish B (del_exec S')"
    using boundary delivery_fault_trace_preserves_finish[OF trace faults]
    by (simp add: durable_boundary_within_finish_def)
  have le_fin': "c \<le> exec_finish (del_exec S')"
    using le_fin delivery_fault_trace_preserves_finish[OF trace faults]
    by simp
  have durable_eq:
    "durable_exec_state_at_boundary (del_exec S') B =
     durable_exec_state_at_boundary (del_exec S) B"
    by (rule delivery_fault_trace_preserves_durable_exec_state_at_boundary
        [OF trace faults])
  show ?thesis
    using wf' running' boundary' le_fin' mismatch durable_eq
    by (simp add: durable_bad_crash_enabled_at_boundary_def)
qed

theorem delivery_faults_have_truncating_bad_crash_extension:
  assumes enabled:
        "durable_bad_crash_enabled_at_boundary (del_exec S) B c k"
      and consistent: "delivery_set_view_consistent S"
      and trace: "delivery_trace S xs S'"
      and faults: "list_all delivery_fault_label xs"
  shows "\<exists>S''.
      delivery_trace S xs S'
    \<and> truncating_delivery_crash_step_at_boundary S' B c S''
    \<and> delivery_set_view_consistent S''
    \<and> observable_mismatch (del_exec S'') c k
    \<and> diverges (proto_of_exec_at (del_exec S'') c) c"
proof -
  have enabled':
    "durable_bad_crash_enabled_at_boundary (del_exec S') B c k"
    by (rule delivery_faults_preserve_durable_bad_crash_enabled_at_boundary
        [OF enabled consistent trace faults])
  let ?S'' = "truncating_delivery_crash_state_at_boundary S' B c"
  from enabled' have wf: "wellformed_exec_state (del_exec S')"
      and running: "exec_status (del_exec S') = Running"
      and boundary: "durable_boundary_within_finish B (del_exec S')"
      and le_fin: "c \<le> exec_finish (del_exec S')"
      and mismatch:
        "mismatch_at
          (proto_of_exec_at
            (durable_exec_state_at_boundary (del_exec S') B) c) c k"
    by (auto simp: durable_bad_crash_enabled_at_boundary_def)
  have exec_step:
    "truncating_crash_step_at_boundary
      (del_exec S') B c
      (truncating_crash_state_at_boundary (del_exec S') B c)"
    by (rule truncating_crash_step_at_boundary.truncating_crash
        [OF wf running boundary])
  have crash_step_raw:
    "truncating_delivery_crash_step_at_boundary S' B c
       (let q = durable_pending_queue_at_boundary B S'
        in S'\<lparr>del_exec :=
             (truncating_crash_state_at_boundary (del_exec S') B c)
               \<lparr>exec_pending := set q\<rparr>,
           del_pending := q\<rparr>)"
    by (rule truncating_delivery_crash_step_at_boundary.truncating_delivery_crash
        [OF exec_step])
  have crash_step: "truncating_delivery_crash_step_at_boundary S' B c ?S''"
    using crash_step_raw
    by (simp add: truncating_delivery_crash_state_at_boundary_def Let_def)
  have set_view: "delivery_set_view_consistent ?S''"
    by (rule truncating_delivery_crash_set_view_consistent)
  have status:
    "exec_status (del_exec ?S'') = Crashed c"
    by (simp add: truncating_delivery_crash_state_at_boundary_def
                  truncating_crash_state_at_boundary_def Let_def)
  have finish:
    "exec_finish (del_exec ?S'') = exec_finish (del_exec S')"
    by (simp add: truncating_delivery_crash_state_at_boundary_def
                  truncating_crash_state_at_boundary_def
                  durable_exec_state_at_boundary_def Let_def)
  have proto:
    "proto_of_exec_at (del_exec ?S'') c =
     proto_of_exec_at
       (durable_exec_state_at_boundary (del_exec S') B) c"
    by (simp add: truncating_delivery_crash_state_at_boundary_def
                  truncating_crash_state_at_boundary_def
                  proto_of_exec_at_def store2_of_exec_def
                  fun_eq_iff Let_def)
  have obs: "observable_mismatch (del_exec ?S'') c k"
    using le_fin mismatch status finish proto
    by (simp add: observable_mismatch_def)
  hence div: "diverges (proto_of_exec_at (del_exec ?S'') c) c"
    by (rule observable_mismatch_imp_diverges)
  from trace crash_step set_view obs div show ?thesis by blast
qed

section \<open>Concrete load-bearing witnesses\<close>

definition durable_source_first_precrash_state
  :: "(nat, nat) dw_exec_state"
where
  "durable_source_first_precrash_state =
     after_source_ack_state [0 \<mapsto> 1] {0} ec1 ec1 (Update 0 2)"

lemma durable_source_first_within_ec1:
  "exec_within_durable_frontier ec1 durable_source_first_precrash_state"
  by (simp add: durable_source_first_precrash_state_def
                after_source_ack_state_def after_source_state_def
                initial_exec_state_def exec_within_durable_frontier_def
                exec_within_durable_boundary_def
                single_durable_boundary_def durable_ack_frontier_def
                history_within_frontier_def durable_pending_at_boundary_def
                durable_history_prefix_at_def)

lemma durable_source_first_precrash_admissible_trace:
  "admissible_dw_exec_trace
    (initial_exec_state [0 \<mapsto> 1] {0::nat} ec1)
    [DoSource ec1 (Update 0 2), Ack ec1 (Update 0 2)]
    durable_source_first_precrash_state"
proof -
  let ?e = "Update (0::nat) (2::nat)"
  let ?s0 = "initial_exec_state [0 \<mapsto> 1] {0::nat} ec1"
  let ?s1 = "after_source_state [0 \<mapsto> 1] {0::nat} ec1 ec1 ?e"
  let ?s2 = "durable_source_first_precrash_state"
  have step1: "dw_exec_step ?s0 (DoSource ec1 ?e) ?s1"
  proof -
    have "dw_exec_step ?s0 (DoSource ec1 ?e)
        (?s0\<lparr>exec_src_hist := exec_src_hist ?s0 @ [(ec1, ?e)]\<rparr>)"
      by (rule dw_exec_step.do_source) (simp add: initial_exec_state_def)
    thus ?thesis
      by (simp add: after_source_state_def initial_exec_state_def)
  qed
  have wf0: "wellformed_exec_state ?s0"
    by simp
  have preserves1: "exec_label_preserves_history_wf ?s0 (DoSource ec1 ?e)"
    by (simp add: exec_label_preserves_history_wf_def
                  history_can_append_def initial_exec_state_def ec_defs)
  have wf1: "wellformed_exec_state ?s1"
    by (rule dw_exec_step_wellformed_exec_state
        [OF step1 wf0 preserves1])
  have step2: "dw_exec_step ?s1 (Ack ec1 ?e) ?s2"
  proof -
    have "dw_exec_step ?s1 (Ack ec1 ?e)
        (?s1\<lparr>exec_acked := exec_acked ?s1 @ [(ec1, ?e)]\<rparr>)"
      by (rule dw_exec_step.ack)
         (simp_all add: after_source_state_def initial_exec_state_def)
    thus ?thesis
      by (simp add: durable_source_first_precrash_state_def
                    after_source_ack_state_def after_source_state_def
                    initial_exec_state_def)
  qed
  have preserves2: "exec_label_preserves_history_wf ?s1 (Ack ec1 ?e)"
    by (simp add: exec_label_preserves_history_wf_def
                  history_can_append_def after_source_state_def
                  initial_exec_state_def ec_defs)
  have wf2: "wellformed_exec_state ?s2"
    by (rule dw_exec_step_wellformed_exec_state
        [OF step2 wf1 preserves2])
  show ?thesis
    by (rule admissible_dw_exec_trace.admissible_trace_step
        [OF step1 wf0 preserves1])
       (rule admissible_dw_exec_trace.admissible_trace_step
        [OF step2 wf1 preserves2
            admissible_dw_exec_trace.admissible_trace_refl[OF wf2]])
qed

lemma durable_source_first_enabled:
  "durable_acked_bad_crash_enabled
    durable_source_first_precrash_state ec1 ec1 (0::nat)"
  by (simp add: durable_acked_bad_crash_enabled_def
                durable_acked_bad_crash_enabled_at_boundary_def
                durable_bad_crash_enabled_at_boundary_def
                durable_boundary_within_finish_def
                durable_acked_source_effect_at_boundary_def
                durable_source_first_precrash_state_def
                after_source_ack_state_def after_source_state_def
                initial_exec_state_def durable_exec_state_at_boundary_def
                single_durable_boundary_def durable_ack_frontier_def
                durable_history_prefix_at_def durable_pending_at_boundary_def
                acked_source_effect_at_def mismatch_at_def
                proto_of_exec_at_def store2_of_exec_def log_image_def
                Src_single_event_at_key restrict_def ec_defs
                wellformed_exec_state_def exec_histories_wellformed_def
                pending_enqueued_consistent_def acked_source_consistent_def
                wellformed_src_history_def)

corollary durable_source_first_truncating_bad_crash_witness:
  "\<exists>s.
      truncating_crash_step durable_source_first_precrash_state ec1 ec1 s
    \<and> acked_observable_mismatch s ec1 (0::nat)
    \<and> diverges (proto_of_exec_at s ec1) ec1"
  using durable_acked_bad_crash_enabled_extend[OF durable_source_first_enabled]
  by blast

corollary durable_source_first_no_truncation_recovers_old_crash:
  "truncating_crash_state durable_source_first_precrash_state ec1 ec1 =
     durable_source_first_precrash_state\<lparr>exec_status := Crashed ec1\<rparr>"
  by (rule no_truncation_frontier_crash_recovers_old_crash
      [OF durable_source_first_within_ec1])

corollary durable_source_first_truncating_step_refines_old_crash_step:
  assumes "truncating_crash_step durable_source_first_precrash_state ec1 ec1 s"
  shows "dw_exec_step durable_source_first_precrash_state (Crash ec1) s"
  by (rule no_truncation_frontier_crash_refines_old_crash_step
      [OF assms durable_source_first_within_ec1])

definition nondurable_source_suffix_precrash_state
  :: "(nat, nat) dw_exec_state"
where
  "nondurable_source_suffix_precrash_state =
     after_source_ack_state [0 \<mapsto> 1] {0} ec1 ec1 (Update 0 2)"

lemma nondurable_source_suffix_not_enabled:
  "\<not> durable_bad_crash_enabled
    nondurable_source_suffix_precrash_state c0 ec1 (0::nat)"
  by (simp add: durable_bad_crash_enabled_def
                durable_bad_crash_enabled_at_boundary_def
                nondurable_source_suffix_precrash_state_def
                after_source_ack_state_def after_source_state_def
                initial_exec_state_def durable_exec_state_at_boundary_def
                single_durable_boundary_def durable_ack_frontier_def
                durable_history_prefix_at_def durable_pending_at_boundary_def
                mismatch_at_def proto_of_exec_at_def store2_of_exec_def
                log_image_def restrict_def ec_defs c0_eq_coord_of_nat_0)

lemma nondurable_source_suffix_truncating_crash_no_mismatch:
  "\<not> mismatch_at
    (proto_of_exec_at
      (truncating_crash_state
        nondurable_source_suffix_precrash_state c0 ec1) ec1)
    ec1 (0::nat)"
  by (simp add: truncating_crash_state_def
                truncating_crash_state_at_boundary_def
                durable_exec_state_at_boundary_def
                nondurable_source_suffix_precrash_state_def
                after_source_ack_state_def after_source_state_def
                initial_exec_state_def single_durable_boundary_def
                durable_ack_frontier_def durable_history_prefix_at_def
                durable_pending_at_boundary_def mismatch_at_def
                proto_of_exec_at_def store2_of_exec_def log_image_def
                restrict_def ec_defs c0_eq_coord_of_nat_0)

lemma nondurable_source_suffix_truncating_crash_no_divergence:
  "\<not> diverges
    (proto_of_exec_at
      (truncating_crash_state
        nondurable_source_suffix_precrash_state c0 ec1) ec1)
    ec1"
  by (simp add: truncating_crash_state_def
                truncating_crash_state_at_boundary_def
                durable_exec_state_at_boundary_def
                nondurable_source_suffix_precrash_state_def
                after_source_ack_state_def after_source_state_def
                initial_exec_state_def single_durable_boundary_def
                durable_ack_frontier_def durable_history_prefix_at_def
                durable_pending_at_boundary_def diverges_def mismatch_at_def
                proto_of_exec_at_def store2_of_exec_def log_image_def
                restrict_def ec_defs c0_eq_coord_of_nat_0)

corollary nondurable_source_suffix_truncation_avoids_bad_crash_witness:
  "\<exists>s.
      truncating_crash_step nondurable_source_suffix_precrash_state c0 ec1 s
    \<and> \<not> diverges (proto_of_exec_at s ec1) ec1"
proof -
  let ?s = "truncating_crash_state nondurable_source_suffix_precrash_state c0 ec1"
  have step:
    "truncating_crash_step nondurable_source_suffix_precrash_state c0 ec1 ?s"
    by (rule truncating_crash_step.truncating_crash)
       (simp_all add: nondurable_source_suffix_precrash_state_def
                      after_source_ack_state_def after_source_state_def
                      initial_exec_state_def ec_defs c0_eq_coord_of_nat_0
                      wellformed_exec_state_def exec_histories_wellformed_def
                      pending_enqueued_consistent_def
                      acked_source_consistent_def wellformed_src_history_def)
  from step nondurable_source_suffix_truncating_crash_no_divergence
  show ?thesis by blast
qed

definition enqueue_survives_downstream_lost_boundary :: dw_durable_boundary
where
  "enqueue_survives_downstream_lost_boundary =
     \<lparr> db_src = c0, db_down = c0, db_enq = ec1, db_ack = c0 \<rparr>"

definition durable_enqueue_volatile_downstream_precrash_state
  :: "(nat, nat) dw_exec_state"
where
  "durable_enqueue_volatile_downstream_precrash_state =
     (initial_exec_state (\<lambda>(_::nat). None) {0::nat} ec1)
       \<lparr> exec_enqueued := [(ec1, Insert 0 2)],
         exec_down_hist := [(ec1, Insert 0 2)],
         exec_pending := {} \<rparr>"

lemma durable_enqueue_volatile_downstream_reappears_pending:
  "exec_pending
    (truncating_crash_state_at_boundary
      durable_enqueue_volatile_downstream_precrash_state
      enqueue_survives_downstream_lost_boundary ec1)
   = {(ec1, Insert (0::nat) (2::nat))}"
  by (simp add: truncating_crash_state_at_boundary_def
                durable_exec_state_at_boundary_def
                durable_enqueue_volatile_downstream_precrash_state_def
                enqueue_survives_downstream_lost_boundary_def
                initial_exec_state_def durable_pending_at_boundary_def
                durable_history_prefix_at_def ec_defs c0_eq_coord_of_nat_0)

corollary truncating_crash_pending_recomputed_witness:
  "exec_pending
    (truncating_crash_state_at_boundary
      durable_enqueue_volatile_downstream_precrash_state
      enqueue_survives_downstream_lost_boundary ec1)
   = set
      (exec_enqueued
        (truncating_crash_state_at_boundary
          durable_enqueue_volatile_downstream_precrash_state
          enqueue_survives_downstream_lost_boundary ec1))
     - set
      (exec_down_hist
        (truncating_crash_state_at_boundary
          durable_enqueue_volatile_downstream_precrash_state
          enqueue_survives_downstream_lost_boundary ec1))"
  by (rule truncating_crash_pending_honest)

end
