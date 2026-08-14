(*  Title:       Dual_Write_Replay_Safety.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Constructional positive safety bridge for the dual-write core.
    This theory connects the protocol-level no-divergence predicate to the
    DBLog-free replay / virtual-cut algebra. It intentionally imports the
    outbox continuation layer here, after the core protocol theory, so the
    core record remains independent of replay certificates and DBLog objects.
*)

theory Dual_Write_Replay_Safety
  imports Dual_Write_Execution Outbox_Continuation
begin

section \<open>Replay-derived downstream safety\<close>

definition replay_derived_at
  :: "('k, 'v) proto \<Rightarrow> ('k, 'v) replay_event list \<Rightarrow> frontier \<Rightarrow> bool"
where
  "replay_derived_at P \<sigma> f \<longleftrightarrow>
     virtual_cut_state (pbase P) \<sigma> (pscope P) f (psrc P)
   \<and> s2 P f = restrict (Apply \<sigma>) (pscope P)"

theorem replay_derived_at_agrees:
  assumes "replay_derived_at P \<sigma> f"
  shows "s2 P f = log_image P f"
  using assms
  by (simp add: replay_derived_at_def virtual_cut_state_def log_image_def)

theorem replay_derived_at_no_mismatch:
  assumes derived: "replay_derived_at P \<sigma> f"
  shows "\<forall>k. \<not> mismatch_at P f k"
proof
  fix k
  have agree: "s2 P f = log_image P f"
    by (rule replay_derived_at_agrees[OF derived])
  show "\<not> mismatch_at P f k"
  proof
    assume mismatch: "mismatch_at P f k"
    hence scoped: "k \<in> pscope P"
        and ne: "store2 P f k \<noteq> log_image P f k"
      by (auto simp: mismatch_at_def)
    from agree have "s2 P f k = log_image P f k" by simp
    with scoped have "store2 P f k = log_image P f k"
      by (simp add: restrict_def)
    with ne show False by simp
  qed
qed

corollary replay_derived_no_mismatch:
  assumes "replay_derived_at P \<sigma> f"
  shows "\<forall>k. \<not> mismatch_at P f k"
  by (rule replay_derived_at_no_mismatch[OF assms])

theorem replay_derived_at_no_divergence:
  assumes derived: "replay_derived_at P \<sigma> f"
      and le_fin: "f \<le> pfin P"
  shows "\<not> diverges P f"
  using replay_derived_at_agrees[OF derived] le_fin
  by (simp add: diverges_iff_s2_neq_log_image)


section \<open>Execution-observation bridge\<close>

definition execution_replay_derived_at
  :: "('k, 'v) dw_exec_state \<Rightarrow>
      ('k, 'v) replay_event list \<Rightarrow> frontier \<Rightarrow> bool"
where
  "execution_replay_derived_at s \<sigma> f \<longleftrightarrow>
     replay_derived_at (proto_of_exec_at s f) \<sigma> f"

theorem execution_replay_derived_at_no_observable_mismatch:
  assumes derived: "execution_replay_derived_at s \<sigma> f"
      and le_fin: "f \<le> exec_finish s"
  shows "\<not> observable_mismatch (s\<lparr>exec_status := Crashed f\<rparr>) f k"
proof
  assume obs: "observable_mismatch (s\<lparr>exec_status := Crashed f\<rparr>) f k"
  have no_div: "\<not> diverges (proto_of_exec_at s f) f"
    using replay_derived_at_no_divergence[of "proto_of_exec_at s f" \<sigma> f]
      derived le_fin
    by (simp add: execution_replay_derived_at_def proto_of_exec_at_def)
  have div: "diverges (proto_of_exec_at s f) f"
    using observable_mismatch_imp_diverges[OF obs] by simp
  with no_div show False by simp
qed

corollary replay_derived_no_observable_mismatch:
  assumes "execution_replay_derived_at s \<sigma> f"
      and "f \<le> exec_finish s"
  shows "\<not> observable_mismatch (s\<lparr>exec_status := Crashed f\<rparr>) f k"
  by (rule execution_replay_derived_at_no_observable_mismatch[OF assms])

theorem execution_replay_derived_at_existing_crash_no_observable_mismatch:
  assumes derived: "execution_replay_derived_at s \<sigma> f"
      and status: "exec_status s = Crashed f"
      and le_fin: "f \<le> exec_finish s"
  shows "\<not> observable_mismatch s f k"
proof
  assume obs: "observable_mismatch s f k"
  have no_div: "\<not> diverges (proto_of_exec_at s f) f"
    using replay_derived_at_no_divergence[of "proto_of_exec_at s f" \<sigma> f]
      derived le_fin
    by (simp add: execution_replay_derived_at_def proto_of_exec_at_def)
  have div: "diverges (proto_of_exec_at s f) f"
    using observable_mismatch_imp_diverges[OF obs] .
  with no_div show False by simp
qed

definition replay_derived_through
  :: "('k, 'v) proto \<Rightarrow> (frontier \<Rightarrow> ('k, 'v) replay_event list) \<Rightarrow> bool"
where
  "replay_derived_through P R \<longleftrightarrow>
     wellformed_src_history (psrc P)
   \<and> pcrash P \<le> pfin P
   \<and> (\<forall>f. f \<le> pfin P \<longrightarrow> replay_derived_at P (R f) f)"

theorem replay_derived_through_log_derived:
  assumes "replay_derived_through P R"
  shows "log_derived P"
proof -
  from assms have wf: "wellformed_src_history (psrc P)"
      and le: "pcrash P \<le> pfin P"
      and derived:
        "\<And>f. f \<le> pfin P \<Longrightarrow> replay_derived_at P (R f) f"
    by (auto simp: replay_derived_through_def)
  have agree: "\<And>f. f \<le> pfin P \<Longrightarrow> s2 P f = log_image P f"
    by (rule replay_derived_at_agrees[OF derived])
  show ?thesis
    using wf le agree by (simp add: log_derived_def)
qed

theorem replay_derived_through_no_divergence:
  assumes derived: "replay_derived_through P R"
      and le_fin: "f \<le> pfin P"
  shows "\<not> diverges P f"
proof -
  have "log_derived P"
    by (rule replay_derived_through_log_derived[OF derived])
  with le_fin show ?thesis
    by (simp add: log_derived_iff_no_divergence_before_completion)
qed

theorem replay_virtual_cuts_imp_log_derived:
  assumes wf: "wellformed_src_history (psrc P)"
      and le: "pcrash P \<le> pfin P"
      and replay_cuts:
        "\<And>f. f \<le> pfin P \<Longrightarrow>
           \<exists>\<sigma>. s2 P f = restrict (Apply \<sigma>) (pscope P)
             \<and> virtual_cut_state (pbase P) \<sigma> (pscope P) f (psrc P)"
  shows "log_derived P"
proof -
  have agree: "\<And>f. f \<le> pfin P \<Longrightarrow> s2 P f = log_image P f"
  proof -
    fix f
    assume f_le: "f \<le> pfin P"
    from replay_cuts[OF f_le] obtain \<sigma> where
        store: "s2 P f = restrict (Apply \<sigma>) (pscope P)"
        and cut: "virtual_cut_state (pbase P) \<sigma> (pscope P) f (psrc P)"
      by blast
    show "s2 P f = log_image P f"
      by (rule replay_derived_at_agrees[where \<sigma> = \<sigma>])
         (simp add: replay_derived_at_def store cut)
  qed
  show ?thesis
    using wf le agree by (simp add: log_derived_def)
qed


section \<open>Outbox / CDC replay as a replay-derived construction\<close>

definition cdc_replay_prefix
  :: "('k, 'v) proto \<Rightarrow> frontier \<Rightarrow> ('k, 'v) replay_event list"
where
  "cdc_replay_prefix P f =
     map (\<lambda>(c, e). cdc_lift c e)
       (filter (\<lambda>(c, e). c0 < c \<and> c \<le> f \<and> key_of e \<in> pscope P)
          (psrc P))"

lemma cdc_replay_prefix_segment:
  "cdc_segment_between (psrc P) (pscope P) c0 f (cdc_replay_prefix P f)"
proof -
  have "c0 \<le> f"
    by (simp add: less_eq_src_coord_def c0_least)
  thus ?thesis
    by (simp add: cdc_replay_prefix_def cdc_segment_between_def)
qed

lemma cdc_replay_prefix_cdc_only:
  "cdc_only (cdc_replay_prefix P f)"
  by (rule cdc_segment_imp_cdc_only[OF cdc_replay_prefix_segment])

theorem outbox_cdc_segment_replay_derived_at:
  assumes wf: "wellformed_src_history (psrc P)"
      and base: "pbase P = (\<lambda>_. None)"
      and seg: "cdc_segment_between (psrc P) (pscope P) c0 f \<sigma>"
      and store: "s2 P f = restrict (Apply \<sigma>) (pscope P)"
  shows "cdc_only \<sigma> \<and> replay_derived_at P \<sigma> f"
proof -
  from virtual_cut_certifies_outbox[OF wf seg]
  have cdc: "cdc_only \<sigma>"
      and cut0: "virtual_cut_state (\<lambda>_. None) \<sigma> (pscope P) f (psrc P)"
    by auto
  from cut0 have cut:
    "virtual_cut_state (pbase P) \<sigma> (pscope P) f (psrc P)"
    using base by simp
  have derived: "replay_derived_at P \<sigma> f"
    using cut store by (simp add: replay_derived_at_def)
  from cdc derived show ?thesis by blast
qed

theorem outbox_cdc_segment_no_mismatch:
  assumes wf: "wellformed_src_history (psrc P)"
      and base: "pbase P = (\<lambda>_. None)"
      and seg: "cdc_segment_between (psrc P) (pscope P) c0 f \<sigma>"
      and store: "s2 P f = restrict (Apply \<sigma>) (pscope P)"
  shows "cdc_only \<sigma> \<and> (\<forall>k. \<not> mismatch_at P f k)"
proof -
  have derived: "cdc_only \<sigma> \<and> replay_derived_at P \<sigma> f"
    by (rule outbox_cdc_segment_replay_derived_at[OF wf base seg store])
  hence cdc: "cdc_only \<sigma>"
      and replay: "replay_derived_at P \<sigma> f"
    by blast+
  have no_mismatch: "\<forall>k. \<not> mismatch_at P f k"
    by (rule replay_derived_at_no_mismatch[OF replay])
  from cdc no_mismatch show ?thesis by blast
qed

corollary outbox_cdc_segment_no_divergence:
  assumes wf: "wellformed_src_history (psrc P)"
      and base: "pbase P = (\<lambda>_. None)"
      and seg: "cdc_segment_between (psrc P) (pscope P) c0 f \<sigma>"
      and store: "s2 P f = restrict (Apply \<sigma>) (pscope P)"
      and le_fin: "f \<le> pfin P"
  shows "cdc_only \<sigma> \<and> \<not> diverges P f"
proof -
  have derived: "cdc_only \<sigma> \<and> replay_derived_at P \<sigma> f"
    by (rule outbox_cdc_segment_replay_derived_at[OF wf base seg store])
  hence replay: "replay_derived_at P \<sigma> f"
    by blast
  have "\<not> diverges P f"
    by (rule replay_derived_at_no_divergence[OF replay le_fin])
  with derived show ?thesis by blast
qed

corollary outbox_cdc_segment_no_mismatch_no_divergence:
  assumes wf: "wellformed_src_history (psrc P)"
      and base: "pbase P = (\<lambda>_. None)"
      and seg: "cdc_segment_between (psrc P) (pscope P) c0 f \<sigma>"
      and store: "s2 P f = restrict (Apply \<sigma>) (pscope P)"
      and le_fin: "f \<le> pfin P"
  shows "cdc_only \<sigma> \<and> (\<forall>k. \<not> mismatch_at P f k) \<and> \<not> diverges P f"
proof -
  have no_mismatch: "cdc_only \<sigma> \<and> (\<forall>k. \<not> mismatch_at P f k)"
    by (rule outbox_cdc_segment_no_mismatch[OF wf base seg store])
  have no_div: "cdc_only \<sigma> \<and> \<not> diverges P f"
    by (rule outbox_cdc_segment_no_divergence[OF wf base seg store le_fin])
  from no_mismatch no_div show ?thesis by blast
qed

theorem certified_cdc_tail_replay_derived_at:
  assumes wf: "wellformed_src_history (psrc P)"
      and cut: "virtual_cut_state (pbase P) \<sigma>0 (pscope P) f0 (psrc P)"
      and tail: "cdc_segment_between (psrc P) (pscope P) f0 f \<delta>"
      and store:
        "s2 P f = restrict (Apply (\<sigma>0 @ \<delta>)) (pscope P)"
  shows "replay_derived_at P (\<sigma>0 @ \<delta>) f"
proof -
  have cut_f:
    "virtual_cut_state (pbase P) (\<sigma>0 @ \<delta>) (pscope P) f (psrc P)"
    by (rule virtual_cut_state_continuation[OF wf cut tail])
  show ?thesis
    using cut_f store by (simp add: replay_derived_at_def)
qed

theorem certified_cdc_tail_no_mismatch_no_divergence:
  assumes wf: "wellformed_src_history (psrc P)"
      and cut: "virtual_cut_state (pbase P) \<sigma>0 (pscope P) f0 (psrc P)"
      and tail: "cdc_segment_between (psrc P) (pscope P) f0 f \<delta>"
      and store:
        "s2 P f = restrict (Apply (\<sigma>0 @ \<delta>)) (pscope P)"
      and le_fin: "f \<le> pfin P"
  shows "(\<forall>k. \<not> mismatch_at P f k) \<and> \<not> diverges P f"
proof -
  have derived: "replay_derived_at P (\<sigma>0 @ \<delta>) f"
    by (rule certified_cdc_tail_replay_derived_at[OF wf cut tail store])
  have no_mismatch: "\<forall>k. \<not> mismatch_at P f k"
    by (rule replay_derived_at_no_mismatch[OF derived])
  have no_div: "\<not> diverges P f"
    by (rule replay_derived_at_no_divergence[OF derived le_fin])
  from no_mismatch no_div show ?thesis by blast
qed

theorem certified_cdc_tail_no_observable_mismatch:
  assumes wf: "wellformed_src_history (exec_src_hist s)"
      and cut:
        "virtual_cut_state (exec_base s) \<sigma>0 (exec_scope s) f0
          (exec_src_hist s)"
      and tail:
        "cdc_segment_between (exec_src_hist s) (exec_scope s) f0 f \<delta>"
      and store:
        "restrict (store2_of_exec s f) (exec_scope s) =
         restrict (Apply (\<sigma>0 @ \<delta>)) (exec_scope s)"
      and le_fin: "f \<le> exec_finish s"
  shows "\<not> observable_mismatch (s\<lparr>exec_status := Crashed f\<rparr>) f k"
proof -
  have wfP:
    "wellformed_src_history (psrc (proto_of_exec_at s f))"
    using wf by (simp add: proto_of_exec_at_def)
  have cutP:
    "virtual_cut_state
      (pbase (proto_of_exec_at s f)) \<sigma>0
      (pscope (proto_of_exec_at s f)) f0
      (psrc (proto_of_exec_at s f))"
    using cut by (simp add: proto_of_exec_at_def)
  have tailP:
    "cdc_segment_between
      (psrc (proto_of_exec_at s f)) (pscope (proto_of_exec_at s f))
      f0 f \<delta>"
    using tail by (simp add: proto_of_exec_at_def)
  have storeP:
    "s2 (proto_of_exec_at s f) f =
     restrict (Apply (\<sigma>0 @ \<delta>)) (pscope (proto_of_exec_at s f))"
    using store by (simp add: proto_of_exec_at_def)
  have derived:
    "replay_derived_at (proto_of_exec_at s f) (\<sigma>0 @ \<delta>) f"
    by (rule certified_cdc_tail_replay_derived_at
        [OF wfP cutP tailP storeP])
  have exec_derived: "execution_replay_derived_at s (\<sigma>0 @ \<delta>) f"
    using derived by (simp add: execution_replay_derived_at_def)
  show ?thesis
    by (rule execution_replay_derived_at_no_observable_mismatch
        [OF exec_derived le_fin])
qed

theorem cdc_replay_prefix_replay_derived_at:
  assumes wf: "wellformed_src_history (psrc P)"
      and base: "pbase P = (\<lambda>_. None)"
      and store:
        "s2 P f = restrict (Apply (cdc_replay_prefix P f)) (pscope P)"
  shows "cdc_only (cdc_replay_prefix P f)
       \<and> replay_derived_at P (cdc_replay_prefix P f) f"
  by (rule outbox_cdc_segment_replay_derived_at
      [OF wf base cdc_replay_prefix_segment store])

theorem execution_cdc_replay_prefix_no_observable_mismatch:
  assumes wf: "wellformed_src_history (exec_src_hist s)"
      and base: "exec_base s = (\<lambda>_. None)"
      and store:
        "restrict (store2_of_exec s f) (exec_scope s) =
         restrict
          (Apply (cdc_replay_prefix (proto_of_exec_at s f) f))
          (exec_scope s)"
      and le_fin: "f \<le> exec_finish s"
  shows "\<not> observable_mismatch (s\<lparr>exec_status := Crashed f\<rparr>) f k"
proof -
  have wfP:
    "wellformed_src_history (psrc (proto_of_exec_at s f))"
    using wf by (simp add: proto_of_exec_at_def)
  have baseP:
    "pbase (proto_of_exec_at s f) = (\<lambda>_. None)"
    using base by (simp add: proto_of_exec_at_def)
  have storeP:
    "s2 (proto_of_exec_at s f) f =
     restrict
      (Apply (cdc_replay_prefix (proto_of_exec_at s f) f))
      (pscope (proto_of_exec_at s f))"
    using store by (simp add: proto_of_exec_at_def)
  have derived:
    "replay_derived_at
      (proto_of_exec_at s f)
      (cdc_replay_prefix (proto_of_exec_at s f) f) f"
    using cdc_replay_prefix_replay_derived_at[OF wfP baseP storeP]
    by blast
  have exec_derived:
    "execution_replay_derived_at s
      (cdc_replay_prefix (proto_of_exec_at s f) f) f"
    using derived by (simp add: execution_replay_derived_at_def)
  show ?thesis
    by (rule execution_replay_derived_at_no_observable_mismatch
        [OF exec_derived le_fin])
qed

subsection \<open>Closed nonempty CDC replay witness\<close>

definition cdc_replay_witness_state :: "(nat, nat) dw_exec_state" where
  "cdc_replay_witness_state =
     (initial_exec_state (\<lambda>_. None) {0} ec3)
       \<lparr> exec_src_hist := wH,
         exec_down_hist := wH,
         exec_enqueued := wH \<rparr>"

lemma cdc_replay_witness_state_wellformed:
  "wellformed_exec_state cdc_replay_witness_state"
  by (simp add: cdc_replay_witness_state_def wH_wellformed
                wellformed_exec_state_def exec_histories_wellformed_def
                pending_enqueued_consistent_def acked_source_consistent_def
                initial_exec_state_def wellformed_src_history_def wH_def
                ec_defs)

lemma cdc_replay_witness_prefix_nonempty:
  "cdc_replay_prefix
    (proto_of_exec_at cdc_replay_witness_state ec3) ec3 =
   [Cdc ec2 (Insert 0 7)]"
  by (simp add: cdc_replay_prefix_def cdc_replay_witness_state_def
                proto_of_exec_at_def initial_exec_state_def wH_def
                cdc_lift_def ec_defs)

lemma cdc_replay_witness_store_eq:
  "restrict (store2_of_exec cdc_replay_witness_state ec3)
      (exec_scope cdc_replay_witness_state) =
   restrict
    (Apply (cdc_replay_prefix
      (proto_of_exec_at cdc_replay_witness_state ec3) ec3))
    (exec_scope cdc_replay_witness_state)"
  by (simp add: cdc_replay_prefix_def cdc_replay_witness_state_def
                proto_of_exec_at_def store2_of_exec_def initial_exec_state_def
                wH_def cdc_lift_def Apply_def Src_def latest_src_event_def
                restrict_def ec_defs Let_def fun_eq_iff)

theorem cdc_replay_witness_execution_replay_derived:
  "execution_replay_derived_at cdc_replay_witness_state
    (cdc_replay_prefix
      (proto_of_exec_at cdc_replay_witness_state ec3) ec3)
    ec3"
proof -
  have wf:
    "wellformed_src_history (exec_src_hist cdc_replay_witness_state)"
    using cdc_replay_witness_state_wellformed
    by (simp add: wellformed_exec_state_def exec_histories_wellformed_def)
  have base: "exec_base cdc_replay_witness_state = (\<lambda>_. None)"
    by (simp add: cdc_replay_witness_state_def initial_exec_state_def)
  have store: "restrict (store2_of_exec cdc_replay_witness_state ec3)
      (exec_scope cdc_replay_witness_state) =
   restrict
    (Apply (cdc_replay_prefix
      (proto_of_exec_at cdc_replay_witness_state ec3) ec3))
    (exec_scope cdc_replay_witness_state)"
    by (rule cdc_replay_witness_store_eq)
  from wf base store have derived:
    "replay_derived_at
      (proto_of_exec_at cdc_replay_witness_state ec3)
      (cdc_replay_prefix
        (proto_of_exec_at cdc_replay_witness_state ec3) ec3)
      ec3"
    using cdc_replay_prefix_replay_derived_at
      [of "proto_of_exec_at cdc_replay_witness_state ec3" ec3]
    by (simp add: execution_replay_derived_at_def proto_of_exec_at_def)
  show ?thesis
    using derived by (simp add: execution_replay_derived_at_def)
qed

corollary cdc_replay_witness_no_observable_mismatch:
  "\<not> observable_mismatch
    (cdc_replay_witness_state\<lparr>exec_status := Crashed ec3\<rparr>)
    ec3 (0::nat)"
  by (rule replay_derived_no_observable_mismatch
      [OF cdc_replay_witness_execution_replay_derived])
     (simp add: cdc_replay_witness_state_def initial_exec_state_def)

theorem cdc_replay_prefix_imp_replay_derived_through:
  assumes base: "pbase P = (\<lambda>_. None)"
      and wf: "wellformed_src_history (psrc P)"
      and le: "pcrash P \<le> pfin P"
      and store:
        "\<And>f. f \<le> pfin P \<Longrightarrow>
           s2 P f = restrict (Apply (cdc_replay_prefix P f)) (pscope P)"
  shows "replay_derived_through P (cdc_replay_prefix P)"
proof -
  have derived:
    "\<And>f. f \<le> pfin P \<Longrightarrow>
       replay_derived_at P (cdc_replay_prefix P f) f"
  proof -
    fix f
    assume f_le: "f \<le> pfin P"
    from cdc_replay_prefix_replay_derived_at
          [OF wf base store[OF f_le]]
    show "replay_derived_at P (cdc_replay_prefix P f) f"
      by blast
  qed
  show ?thesis
    using wf le derived by (simp add: replay_derived_through_def)
qed

corollary cdc_replay_prefix_imp_log_derived:
  assumes base: "pbase P = (\<lambda>_. None)"
      and wf: "wellformed_src_history (psrc P)"
      and le: "pcrash P \<le> pfin P"
      and store:
        "\<And>f. f \<le> pfin P \<Longrightarrow>
           s2 P f = restrict (Apply (cdc_replay_prefix P f)) (pscope P)"
  shows "log_derived P"
  by (rule replay_derived_through_log_derived
      [OF cdc_replay_prefix_imp_replay_derived_through
          [OF base wf le store]])

theorem cdc_replay_proto_imp_log_derived:
  assumes base: "pbase P = (\<lambda>_. None)"
      and wf: "wellformed_src_history (psrc P)"
      and le: "pcrash P \<le> pfin P"
      and replay_segments:
        "\<And>f. f \<le> pfin P \<Longrightarrow>
           \<exists>\<sigma>. cdc_segment_between (psrc P) (pscope P) c0 f \<sigma>
             \<and> s2 P f = restrict (Apply \<sigma>) (pscope P)"
  shows "log_derived P"
proof (rule replay_virtual_cuts_imp_log_derived[OF wf le])
  fix f
  assume f_le: "f \<le> pfin P"
  from replay_segments[OF f_le] obtain \<sigma> where
      seg: "cdc_segment_between (psrc P) (pscope P) c0 f \<sigma>"
      and store: "s2 P f = restrict (Apply \<sigma>) (pscope P)"
    by blast
  from virtual_cut_certifies_outbox[OF wf seg]
  have cut0: "virtual_cut_state (\<lambda>_. None) \<sigma> (pscope P) f (psrc P)"
    by blast
  hence cut: "virtual_cut_state (pbase P) \<sigma> (pscope P) f (psrc P)"
    using base by simp
  show "\<exists>\<sigma>. s2 P f = restrict (Apply \<sigma>) (pscope P)
          \<and> virtual_cut_state (pbase P) \<sigma> (pscope P) f (psrc P)"
    using store cut by blast
qed

end
