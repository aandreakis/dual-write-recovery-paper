(*  Title:       Dual_Write_Store_Clocks.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Per-store observation clocks for the dual-write crash boundary.  The
    downstream clock carrier is independent of source coordinates; it is linked
    back to source coordinates only by an explicit, faithful committed-offset
    acknowledgement relation.  The older one-frontier model is recovered as the
    identity-offset special case.
*)

theory Dual_Write_Store_Clocks
  imports Dual_Write_Crash_Truncation
begin

section \<open>Per-store clocks linked by source-offset acknowledgements\<close>

text \<open>
  The source frontier remains the authority coordinate.  A downstream clock
  value \<open>q\<close>, of an arbitrary preordered carrier, becomes comparable to it only
  through an acknowledgement relation \<open>A q f\<close> saying that \<open>q\<close> advertises or
  commits source offset \<open>f\<close>.  Faithfulness requires the advertised offset to
  be total, functional, and monotone in downstream-clock order.
\<close>

definition faithful_source_offset_ack
  :: "('dc::preorder \<Rightarrow> frontier \<Rightarrow> bool) \<Rightarrow> bool"
where
  "faithful_source_offset_ack A \<longleftrightarrow>
     (\<forall>q. \<exists>f. A q f)
   \<and> (\<forall>q f f'. A q f \<longrightarrow> A q f' \<longrightarrow> f = f')
   \<and> (\<forall>q q' f f'. q \<le> q' \<longrightarrow> A q f \<longrightarrow> A q' f' \<longrightarrow> f \<le> f')"

definition acknowledged_source_lag
  :: "('dc::preorder \<Rightarrow> frontier \<Rightarrow> bool) \<Rightarrow> frontier \<Rightarrow> 'dc \<Rightarrow> bool"
where
  "acknowledged_source_lag A c_src q \<longleftrightarrow>
     (\<exists>f_ack. A q f_ack \<and> f_ack < c_src)"

definition cross_axis_mismatch_at
  :: "('dc::preorder \<Rightarrow> frontier \<Rightarrow> bool) \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow> 'dc \<Rightarrow> 'k \<Rightarrow> bool"
where
  "cross_axis_mismatch_at A s c_src q k \<longleftrightarrow>
     faithful_source_offset_ack A
   \<and> (\<exists>f_ack.
        A q f_ack
      \<and> k \<in> exec_scope s
      \<and> Src (exec_base s) (exec_down_hist s) f_ack k
          \<noteq> Src (exec_base s) (exec_src_hist s) c_src k)"

definition cross_axis_diverges_at
  :: "('dc::preorder \<Rightarrow> frontier \<Rightarrow> bool) \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow> 'dc \<Rightarrow> bool"
where
  "cross_axis_diverges_at A s c_src q \<longleftrightarrow>
     c_src \<le> exec_finish s \<and> (\<exists>k. cross_axis_mismatch_at A s c_src q k)"

definition cross_axis_observable_mismatch
  :: "('dc::preorder \<Rightarrow> frontier \<Rightarrow> bool) \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow> frontier \<Rightarrow> 'dc \<Rightarrow> 'k \<Rightarrow> bool"
where
  "cross_axis_observable_mismatch A s c_crash c_src q k \<longleftrightarrow>
     exec_status s = Crashed c_crash
   \<and> c_crash \<le> exec_finish s
   \<and> c_src \<le> exec_finish s
   \<and> cross_axis_mismatch_at A s c_src q k"

lemma cross_axis_observable_mismatch_imp_diverges:
  assumes "cross_axis_observable_mismatch A s c_crash c_src q k"
  shows "cross_axis_diverges_at A s c_src q"
  using assms
  by (auto simp: cross_axis_observable_mismatch_def
                 cross_axis_diverges_at_def)

lemma faithful_source_offset_ack_functional:
  assumes "faithful_source_offset_ack A"
      and "A q f"
      and "A q f'"
  shows "f = f'"
  using assms by (auto simp: faithful_source_offset_ack_def)

lemma faithful_source_offset_ack_monotone:
  assumes "faithful_source_offset_ack A"
      and "q \<le> q'"
      and "A q f"
      and "A q' f'"
  shows "f \<le> f'"
  using assms by (auto simp: faithful_source_offset_ack_def)

lemma acknowledged_caught_up_no_cross_axis_mismatch:
  assumes rel: "A q c_src"
      and same: "Src (exec_base s) (exec_down_hist s) c_src k =
                 Src (exec_base s) (exec_src_hist s) c_src k"
  shows "\<not> cross_axis_mismatch_at A s c_src q k"
  using assms faithful_source_offset_ack_functional
  by (fastforce simp: cross_axis_mismatch_at_def)

subsection \<open>Durable bad crashes with independent downstream clocks\<close>

definition durable_cross_axis_acked_bad_crash_enabled_at_boundary
  :: "('dc::preorder \<Rightarrow> frontier \<Rightarrow> bool) \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> dw_durable_boundary \<Rightarrow>
      frontier \<Rightarrow> frontier \<Rightarrow> 'dc \<Rightarrow> 'k \<Rightarrow> bool"
where
  "durable_cross_axis_acked_bad_crash_enabled_at_boundary
      A s B c_crash c_src q k \<longleftrightarrow>
     faithful_source_offset_ack A
   \<and> wellformed_exec_state s
   \<and> exec_status s = Running
   \<and> durable_boundary_within_finish B s
   \<and> c_crash \<le> exec_finish s
   \<and> c_src \<le> db_src B
   \<and> acked_source_effect_at (durable_exec_state_at_boundary s B) c_src k
   \<and> (\<exists>f_ack.
        A q f_ack
      \<and> f_ack \<le> db_down B
      \<and> f_ack < c_src
      \<and> cross_axis_mismatch_at A
          (durable_exec_state_at_boundary s B) c_src q k)"

definition durable_cross_axis_acked_bad_crash_enabled
  :: "('dc::preorder \<Rightarrow> frontier \<Rightarrow> bool) \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow>
      frontier \<Rightarrow> frontier \<Rightarrow> 'dc \<Rightarrow> 'k \<Rightarrow> bool"
where
  "durable_cross_axis_acked_bad_crash_enabled A s d c_crash c_src q k \<longleftrightarrow>
     durable_cross_axis_acked_bad_crash_enabled_at_boundary
       A s (single_durable_boundary d) c_crash c_src q k"

theorem durable_cross_axis_acked_bad_crash_enabled_at_boundary_extend:
  assumes enabled:
    "durable_cross_axis_acked_bad_crash_enabled_at_boundary
       A s B c_crash c_src q k"
  shows "\<exists>s'.
      truncating_crash_step_at_boundary s B c_crash s'
    \<and> cross_axis_observable_mismatch A s' c_crash c_src q k
    \<and> cross_axis_diverges_at A s' c_src q"
proof -
  let ?s' = "truncating_crash_state_at_boundary s B c_crash"
  from enabled have wf: "wellformed_exec_state s"
      and running: "exec_status s = Running"
      and boundary: "durable_boundary_within_finish B s"
      and crash_le: "c_crash \<le> exec_finish s"
      and src_le_boundary: "c_src \<le> db_src B"
      and cross:
        "cross_axis_mismatch_at A
          (durable_exec_state_at_boundary s B) c_src q k"
    by (auto simp: durable_cross_axis_acked_bad_crash_enabled_at_boundary_def)
  have step: "truncating_crash_step_at_boundary s B c_crash ?s'"
    by (rule truncating_crash_step_at_boundary.truncating_crash
        [OF wf running boundary])
  have src_le_finish: "c_src \<le> exec_finish ?s'"
    using boundary src_le_boundary
    by (auto simp: durable_boundary_within_finish_def
                  durable_exec_state_at_boundary_def
                  truncating_crash_state_at_boundary_def)
  have cross': "cross_axis_mismatch_at A ?s' c_src q k"
    using cross by (simp add: cross_axis_mismatch_at_def
                              truncating_crash_state_at_boundary_def)
  have obs: "cross_axis_observable_mismatch A ?s' c_crash c_src q k"
    using crash_le src_le_finish cross'
    by (simp add: cross_axis_observable_mismatch_def
                  durable_exec_state_at_boundary_def
                  truncating_crash_state_at_boundary_def)
  hence div: "cross_axis_diverges_at A ?s' c_src q"
    by (rule cross_axis_observable_mismatch_imp_diverges)
  from step obs div show ?thesis by blast
qed

theorem durable_cross_axis_acked_bad_crash_enabled_extend:
  assumes enabled:
    "durable_cross_axis_acked_bad_crash_enabled A s d c_crash c_src q k"
  shows "\<exists>s'.
      truncating_crash_step s d c_crash s'
    \<and> cross_axis_observable_mismatch A s' c_crash c_src q k
    \<and> cross_axis_diverges_at A s' c_src q"
proof -
  let ?s' = "truncating_crash_state s d c_crash"
  from enabled have wf: "wellformed_exec_state s"
      and running: "exec_status s = Running"
      and durable: "d \<le> exec_finish s"
      and crash_le: "c_crash \<le> exec_finish s"
      and src_le_d: "c_src \<le> d"
      and cross:
        "cross_axis_mismatch_at A (durable_exec_state s d) c_src q k"
    by (auto simp: durable_cross_axis_acked_bad_crash_enabled_def
                   durable_cross_axis_acked_bad_crash_enabled_at_boundary_def
                   durable_boundary_within_finish_def
                   durable_exec_state_def single_durable_boundary_def)
  have step: "truncating_crash_step s d c_crash ?s'"
    by (rule truncating_crash_step.truncating_crash[OF wf running durable])
  have src_le_finish: "c_src \<le> exec_finish ?s'"
    using src_le_d durable by (simp add: truncating_crash_state_def
                                        truncating_crash_state_at_boundary_def
                                        durable_exec_state_at_boundary_def)
  have cross': "cross_axis_mismatch_at A ?s' c_src q k"
    using cross by (simp add: cross_axis_mismatch_at_def
                              durable_exec_state_def truncating_crash_state_def
                              truncating_crash_state_at_boundary_def)
  have obs: "cross_axis_observable_mismatch A ?s' c_crash c_src q k"
    using crash_le src_le_finish cross'
    by (simp add: cross_axis_observable_mismatch_def
                  durable_exec_state_at_boundary_def
                  truncating_crash_state_def truncating_crash_state_at_boundary_def)
  hence div: "cross_axis_diverges_at A ?s' c_src q"
    by (rule cross_axis_observable_mismatch_imp_diverges)
  from step obs div show ?thesis by blast
qed

subsection \<open>The old single-axis model as the identity special case\<close>

definition identity_offset_ack :: "frontier \<Rightarrow> frontier \<Rightarrow> bool" where
  "identity_offset_ack q f \<longleftrightarrow> f = q"

lemma identity_offset_ack_faithful [simp]:
  "faithful_source_offset_ack identity_offset_ack"
  by (auto simp: faithful_source_offset_ack_def identity_offset_ack_def)

theorem identity_cross_axis_mismatch_at:
  "cross_axis_mismatch_at identity_offset_ack s c c k \<longleftrightarrow>
   mismatch_at (proto_of_exec_at s c) c k"
  by (simp add: cross_axis_mismatch_at_def identity_offset_ack_def
                mismatch_at_def proto_of_exec_at_def store2_of_exec_def
                log_image_def restrict_def)

theorem identity_cross_axis_diverges_at:
  "cross_axis_diverges_at identity_offset_ack s c c \<longleftrightarrow>
   diverges (proto_of_exec_at s c) c"
  by (auto simp: cross_axis_diverges_at_def diverges_iff_mismatch_at
                 proto_of_exec_at_def identity_cross_axis_mismatch_at)

theorem identity_cross_axis_observable_mismatch_iff:
  "cross_axis_observable_mismatch identity_offset_ack s c c c k \<longleftrightarrow>
   observable_mismatch s c k"
  by (simp add: cross_axis_observable_mismatch_def
                observable_mismatch_def proto_of_exec_at_def
                identity_cross_axis_mismatch_at)

theorem old_single_axis_model_is_identity_special_case:
  "(\<forall>k. cross_axis_mismatch_at identity_offset_ack s c c k
       \<longleftrightarrow> mismatch_at (proto_of_exec_at s c) c k)
   \<and> (cross_axis_diverges_at identity_offset_ack s c c
       \<longleftrightarrow> diverges (proto_of_exec_at s c) c)
   \<and> (\<forall>k. cross_axis_observable_mismatch identity_offset_ack s c c c k
       \<longleftrightarrow> observable_mismatch s c k)"
  by (simp add: identity_cross_axis_mismatch_at
                identity_cross_axis_diverges_at
                identity_cross_axis_observable_mismatch_iff)

subsection \<open>Load-bearing relation controls\<close>

definition unlinked_offset_ack :: "'dc \<Rightarrow> frontier \<Rightarrow> bool" where
  "unlinked_offset_ack q f \<longleftrightarrow> False"

lemma unlinked_offset_ack_not_faithful:
  "\<not> faithful_source_offset_ack unlinked_offset_ack"
  by (simp add: faithful_source_offset_ack_def unlinked_offset_ack_def)

lemma universal_offset_ack_not_faithful:
  "\<not> faithful_source_offset_ack (\<lambda>(_::nat) (_::frontier). True)"
proof
  assume "faithful_source_offset_ack (\<lambda>(_::nat) (_::frontier). True)"
  hence "c0 = ec1"
    by (auto simp: faithful_source_offset_ack_def)
  with c0_neq_ec1 show False by simp
qed

lemma nonmonotone_offset_ack_not_faithful:
  assumes "q1 \<le> q2"
      and "A q1 f2"
      and "A q2 f1"
      and "\<not> f2 \<le> f1"
  shows "\<not> faithful_source_offset_ack A"
  using assms by (auto simp: faithful_source_offset_ack_def)

lemma missing_faithful_relation_no_cross_axis_mismatch:
  assumes "\<not> faithful_source_offset_ack A"
  shows "\<not> cross_axis_mismatch_at A s c_src q k"
  using assms by (simp add: cross_axis_mismatch_at_def)

lemma missing_faithful_relation_no_cross_axis_observable_mismatch:
  assumes "\<not> faithful_source_offset_ack A"
  shows "\<not> cross_axis_observable_mismatch A s c_crash c_src q k"
  using assms by (simp add: cross_axis_observable_mismatch_def
                            cross_axis_mismatch_at_def)

lemma missing_faithful_relation_no_cross_axis_divergence:
  assumes "\<not> faithful_source_offset_ack A"
  shows "\<not> cross_axis_diverges_at A s c_src q"
  using assms by (simp add: cross_axis_diverges_at_def
                            cross_axis_mismatch_at_def)

lemma nondurable_source_offset_not_cross_axis_enabled:
  assumes "\<not> c_src \<le> db_src B"
  shows "\<not> durable_cross_axis_acked_bad_crash_enabled_at_boundary
     A s B c_crash c_src q k"
  using assms
  by (simp add: durable_cross_axis_acked_bad_crash_enabled_at_boundary_def)

lemma empty_durable_downstream_no_ghost_image:
  assumes "durable_history_prefix_at (db_down B) (exec_down_hist s) = []"
  shows "Src (exec_base (durable_exec_state_at_boundary s B))
             (exec_down_hist (durable_exec_state_at_boundary s B)) f k =
         exec_base s k"
  using assms by (simp add: durable_exec_state_at_boundary_def)

subsection \<open>A concrete independent-clock witness\<close>

definition saturating_nat_offset_ack :: "nat \<Rightarrow> frontier \<Rightarrow> bool" where
  "saturating_nat_offset_ack n f \<longleftrightarrow> f = coord_of_nat (min n 1)"

lemma saturating_nat_offset_ack_faithful [simp]:
  "faithful_source_offset_ack saturating_nat_offset_ack"
  by (auto simp: faithful_source_offset_ack_def saturating_nat_offset_ack_def
      intro: min.mono)

lemma saturating_nat_offset_ack_not_rename:
  "saturating_nat_offset_ack 1 ec1
   \<and> saturating_nat_offset_ack 2 ec1
   \<and> (1::nat) \<noteq> 2"
  by (simp add: saturating_nat_offset_ack_def ec_defs)

lemma durable_source_first_cross_axis_enabled:
  "durable_cross_axis_acked_bad_crash_enabled
     saturating_nat_offset_ack
     durable_source_first_precrash_state ec1 ec1 ec1 (0::nat) (0::nat)"
  by (simp add: durable_cross_axis_acked_bad_crash_enabled_def
                durable_cross_axis_acked_bad_crash_enabled_at_boundary_def
                durable_boundary_within_finish_def
                durable_source_first_precrash_state_def
                after_source_ack_state_def after_source_state_def
                initial_exec_state_def durable_exec_state_at_boundary_def
                single_durable_boundary_def durable_ack_frontier_def
                durable_history_prefix_at_def durable_pending_at_boundary_def
                acked_source_effect_at_def cross_axis_mismatch_at_def
                saturating_nat_offset_ack_def
                Src_single_event_at_key Src_single_event_before_key
                ec_defs c0_eq_coord_of_nat_0
                wellformed_exec_state_def exec_histories_wellformed_def
                pending_enqueued_consistent_def acked_source_consistent_def
                wellformed_src_history_def)

lemma durable_source_first_acknowledged_source_lag:
  "acknowledged_source_lag saturating_nat_offset_ack ec1 (0::nat)"
  by (auto simp: acknowledged_source_lag_def saturating_nat_offset_ack_def
                 ec_defs c0_eq_coord_of_nat_0)

corollary per_store_offset_source_first_truncating_bad_crash_witness:
  "\<exists>s'.
      truncating_crash_step durable_source_first_precrash_state ec1 ec1 s'
    \<and> cross_axis_observable_mismatch
        saturating_nat_offset_ack s' ec1 ec1 (0::nat) (0::nat)
    \<and> acknowledged_source_lag saturating_nat_offset_ack ec1 (0::nat)
    \<and> cross_axis_diverges_at saturating_nat_offset_ack s' ec1 (0::nat)"
proof -
  from durable_cross_axis_acked_bad_crash_enabled_extend
    [OF durable_source_first_cross_axis_enabled]
  obtain s' where
      step: "truncating_crash_step durable_source_first_precrash_state ec1 ec1 s'"
      and obs: "cross_axis_observable_mismatch
        saturating_nat_offset_ack s' ec1 ec1 (0::nat) (0::nat)"
      and div: "cross_axis_diverges_at saturating_nat_offset_ack s' ec1 (0::nat)"
    by blast
  from step obs durable_source_first_acknowledged_source_lag div show ?thesis
    by blast
qed

end
