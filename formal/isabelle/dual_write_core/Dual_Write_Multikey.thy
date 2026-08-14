(*  Title:       Dual_Write_Multikey.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Multi-key source-group divergence for the Dual-Write
    development.  This additive DBLog-free layer lifts the per-key crash
    boundary to source-side key groups, records a cross-key invariant
    violation theorem with a closed witness, recovers the per-key theorem as
    the singleton-group case, and models an independent downstream-side durable
    loss without introducing an atomic-commit or multidatabase agreement
    protocol.

    Premise re-scope (the eaf22483 D9 repair): the cross-key violation
    predicate requires k1 ~= k2, and the group theorem assumes distinct
    keys --- aliased keys are the ordinary per-key case, not a cross-key
    violation.
*)

theory Dual_Write_Multikey
  imports Dual_Write_Store_Clocks
begin

section \<open>Multi-key groups and downstream-local crash loss\<close>

text \<open>
  A source-side group is a set of keys whose authoritative values are observed
  together at a source frontier.  The group vocabulary is deliberately about
  the committed-log image and the derived downstream copy; it does not model a
  coordinator, votes, prepared states, or a multidatabase atomic-commit
  protocol.
\<close>

definition source_group_present_at
  :: "('k, 'v) proto \<Rightarrow> frontier \<Rightarrow> 'k set \<Rightarrow> bool"
where
  "source_group_present_at P f K \<longleftrightarrow>
     K \<subseteq> pscope P
   \<and> (\<forall>k \<in> K. log_image P f k \<noteq> None)"

definition group_mismatch_at
  :: "('k, 'v) proto \<Rightarrow> frontier \<Rightarrow> 'k set \<Rightarrow> bool"
where
  "group_mismatch_at P f K \<longleftrightarrow>
     K \<subseteq> pscope P
   \<and> (\<exists>k \<in> K. store2 P f k \<noteq> log_image P f k)"

definition group_diverges_at
  :: "('k, 'v) proto \<Rightarrow> frontier \<Rightarrow> 'k set \<Rightarrow> bool"
where
  "group_diverges_at P f K \<longleftrightarrow>
     f \<le> pfin P \<and> group_mismatch_at P f K"

definition partial_group_materialized_at
  :: "('k, 'v) proto \<Rightarrow> frontier \<Rightarrow> 'k set \<Rightarrow> bool"
where
  "partial_group_materialized_at P f K \<longleftrightarrow>
     f \<le> pfin P
   \<and> source_group_present_at P f K
   \<and> (\<exists>k \<in> K. store2 P f k = log_image P f k)
   \<and> (\<exists>k \<in> K. store2 P f k \<noteq> log_image P f k)"

definition relation2_holds_on
  :: "('k \<Rightarrow> 'v option) \<Rightarrow> ('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> bool"
where
  "relation2_holds_on S R k1 k2 \<longleftrightarrow>
     (\<exists>v1 v2. S k1 = Some v1 \<and> S k2 = Some v2 \<and> R v1 v2)"

definition source_relation_invariant_at
  :: "('k, 'v) proto \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow>
      ('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> bool"
where
  "source_relation_invariant_at P f k1 k2 R \<longleftrightarrow>
     relation2_holds_on (log_image P f) R k1 k2"

definition downstream_relation_invariant_at
  :: "('k, 'v) proto \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow>
      ('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> bool"
where
  "downstream_relation_invariant_at P f k1 k2 R \<longleftrightarrow>
     relation2_holds_on (store2 P f) R k1 k2"

definition cross_key_invariant_violation_at
  :: "('k, 'v) proto \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow>
      ('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> bool"
where
  "cross_key_invariant_violation_at P f k1 k2 R \<longleftrightarrow>
     f \<le> pfin P
   \<and> k1 \<noteq> k2
   \<and> k1 \<in> pscope P
   \<and> k2 \<in> pscope P
   \<and> source_relation_invariant_at P f k1 k2 R
   \<and> \<not> downstream_relation_invariant_at P f k1 k2 R"

theorem singleton_group_mismatch_at_iff_mismatch_at:
  "group_mismatch_at P f {k} \<longleftrightarrow> mismatch_at P f k"
  by (simp add: group_mismatch_at_def mismatch_at_def)

theorem singleton_group_diverges_at_iff_per_key_mismatch:
  "group_diverges_at P f {k} \<longleftrightarrow> f \<le> pfin P \<and> mismatch_at P f k"
  by (simp add: group_diverges_at_def singleton_group_mismatch_at_iff_mismatch_at)

theorem group_diverges_at_imp_diverges:
  assumes "group_diverges_at P f K"
  shows "diverges P f"
  using assms
  by (auto simp: group_diverges_at_def group_mismatch_at_def
                 diverges_iff_mismatch_at mismatch_at_def)

theorem partial_group_materialized_imp_group_diverges:
  assumes "partial_group_materialized_at P f K"
  shows "group_diverges_at P f K"
  using assms
  by (auto simp: partial_group_materialized_at_def
                 source_group_present_at_def group_diverges_at_def
                 group_mismatch_at_def)

corollary partial_group_materialized_imp_diverges:
  assumes "partial_group_materialized_at P f K"
  shows "diverges P f"
  using group_diverges_at_imp_diverges
        partial_group_materialized_imp_group_diverges assms
  by blast

theorem missing_second_key_violates_cross_key_invariant:
  assumes fin: "f \<le> pfin P"
      and distinct_keys: "k1 \<noteq> k2"
      and k1: "k1 \<in> pscope P"
      and k2: "k2 \<in> pscope P"
      and src1: "log_image P f k1 = Some v1"
      and src2: "log_image P f k2 = Some v2"
      and rel: "R v1 v2"
      and down2: "store2 P f k2 = None"
  shows "cross_key_invariant_violation_at P f k1 k2 R"
  using assms
  by (auto simp: cross_key_invariant_violation_at_def
                 source_relation_invariant_at_def
                 downstream_relation_invariant_at_def
                 relation2_holds_on_def)

theorem partial_group_materialized_cross_key_invariant_violation:
  assumes part: "partial_group_materialized_at P f {k1, k2}"
      and distinct_keys: "k1 \<noteq> k2"
      and src_rel: "source_relation_invariant_at P f k1 k2 R"
      and down2: "store2 P f k2 = None"
  shows "cross_key_invariant_violation_at P f k1 k2 R"
  using part src_rel down2
  by (auto simp: partial_group_materialized_at_def source_group_present_at_def
                 cross_key_invariant_violation_at_def
                 downstream_relation_invariant_at_def relation2_holds_on_def)

lemma complete_group_agreement_no_group_mismatch:
  assumes "\<And>k. k \<in> K \<Longrightarrow> store2 P f k = log_image P f k"
  shows "\<not> group_mismatch_at P f K"
  using assms by (auto simp: group_mismatch_at_def)

lemma downstream_invariant_no_cross_key_violation:
  assumes "downstream_relation_invariant_at P f k1 k2 R"
  shows "\<not> cross_key_invariant_violation_at P f k1 k2 R"
  using assms by (simp add: cross_key_invariant_violation_at_def)

subsection \<open>A closed source-side multi-key partial-materialization witness\<close>

definition multikey_partial_proto :: "(nat, nat) proto" where
  "multikey_partial_proto =
     \<lparr> pbase  = (\<lambda>_. None),
       psrc   = [(ec1, Insert 0 7), (ec1, Insert 1 7)],
       pscope = {0, 1},
       pcrash = ec2,
       pfin   = ec3,
       store2 =
         (\<lambda>f. if ec3 \<le> f then [0 \<mapsto> 7](1 \<mapsto> 7)
              else if ec2 \<le> f then [0 \<mapsto> 7]
              else (\<lambda>_. None)) \<rparr>"

lemma multikey_partial_source_group_present:
  "source_group_present_at multikey_partial_proto
     (pcrash multikey_partial_proto) {0, 1}"
  by (simp add: source_group_present_at_def multikey_partial_proto_def
                log_image_def Src_def latest_src_event_def restrict_def
                ec_defs Let_def)

lemma multikey_partial_group_materialized:
  "partial_group_materialized_at multikey_partial_proto
     (pcrash multikey_partial_proto) {0, 1}"
  by (auto simp: partial_group_materialized_at_def
                 source_group_present_at_def multikey_partial_proto_def
                 log_image_def Src_def latest_src_event_def restrict_def
                 ec_defs Let_def)

lemma multikey_partial_group_diverges_at_crash:
  "group_diverges_at multikey_partial_proto
     (pcrash multikey_partial_proto) {0, 1}"
  using multikey_partial_group_materialized
  by (rule partial_group_materialized_imp_group_diverges)

lemma multikey_partial_diverges_at_crash:
  "diverges multikey_partial_proto (pcrash multikey_partial_proto)"
  using multikey_partial_group_materialized
  by (rule partial_group_materialized_imp_diverges)

theorem multikey_partial_cross_key_invariant_violation:
  "cross_key_invariant_violation_at multikey_partial_proto
     (pcrash multikey_partial_proto) 0 1 (\<lambda>x y. x = y)"
  by (simp add: cross_key_invariant_violation_at_def
                source_relation_invariant_at_def
                downstream_relation_invariant_at_def relation2_holds_on_def
                multikey_partial_proto_def log_image_def Src_def
                latest_src_event_def restrict_def ec_defs Let_def)

lemma multikey_complete_no_cross_key_invariant_violation:
  "\<not> cross_key_invariant_violation_at multikey_partial_proto
        (pfin multikey_partial_proto) 0 1 (\<lambda>x y. x = y)"
  by (simp add: cross_key_invariant_violation_at_def
                downstream_relation_invariant_at_def relation2_holds_on_def
                multikey_partial_proto_def ec_defs)

subsection \<open>Independent downstream-side durable loss\<close>

definition downstream_crash_store
  :: "'k set \<Rightarrow> ('k \<rightharpoonup> 'v) \<Rightarrow> ('k \<rightharpoonup> 'v)"
where
  "downstream_crash_store Lost S = (\<lambda>k. if k \<in> Lost then None else S k)"

definition downstream_crash_proto
  :: "('k, 'v) proto \<Rightarrow> 'k set \<Rightarrow> ('k, 'v) proto"
where
  "downstream_crash_proto P Lost =
     P\<lparr>store2 := (\<lambda>f. downstream_crash_store Lost (store2 P f))\<rparr>"

lemma downstream_crash_proto_log_image [simp]:
  "log_image (downstream_crash_proto P Lost) f = log_image P f"
  by (simp add: downstream_crash_proto_def log_image_def)

definition multikey_complete_proto :: "(nat, nat) proto" where
  "multikey_complete_proto =
     \<lparr> pbase  = (\<lambda>_. None),
       psrc   = [(ec1, Insert 0 7), (ec1, Insert 1 7)],
       pscope = {0, 1},
       pcrash = ec2,
       pfin   = ec3,
       store2 = (\<lambda>f. if ec1 \<le> f then [0 \<mapsto> 7](1 \<mapsto> 7) else (\<lambda>_. None)) \<rparr>"

definition multikey_downstream_loss_proto :: "(nat, nat) proto" where
  "multikey_downstream_loss_proto =
     downstream_crash_proto multikey_complete_proto {1}"

lemma multikey_complete_no_group_mismatch_at_crash:
  "\<not> group_mismatch_at multikey_complete_proto
        (pcrash multikey_complete_proto) {0, 1}"
  by (rule complete_group_agreement_no_group_mismatch)
     (simp add: multikey_complete_proto_def log_image_def Src_def
                latest_src_event_def restrict_def ec_defs Let_def)

theorem downstream_loss_cross_key_invariant_violation:
  "cross_key_invariant_violation_at multikey_downstream_loss_proto
     (pcrash multikey_downstream_loss_proto) 0 1 (\<lambda>x y. x = y)"
  by (simp add: cross_key_invariant_violation_at_def
                source_relation_invariant_at_def
                downstream_relation_invariant_at_def relation2_holds_on_def
                multikey_downstream_loss_proto_def
                downstream_crash_proto_def downstream_crash_store_def
                multikey_complete_proto_def log_image_def Src_def
                latest_src_event_def restrict_def ec_defs Let_def)

lemma downstream_loss_group_diverges_at_crash:
  "group_diverges_at multikey_downstream_loss_proto
     (pcrash multikey_downstream_loss_proto) {0, 1}"
  by (auto simp: group_diverges_at_def group_mismatch_at_def
                 multikey_downstream_loss_proto_def downstream_crash_proto_def
                 downstream_crash_store_def multikey_complete_proto_def
                 log_image_def Src_def latest_src_event_def restrict_def
                 ec_defs Let_def)

lemma downstream_loss_singleton_recovers_per_key:
  "group_diverges_at multikey_downstream_loss_proto
      (pcrash multikey_downstream_loss_proto) {1}
   \<longleftrightarrow>
   pcrash multikey_downstream_loss_proto \<le> pfin multikey_downstream_loss_proto
   \<and> mismatch_at multikey_downstream_loss_proto
        (pcrash multikey_downstream_loss_proto) 1"
  by (rule singleton_group_diverges_at_iff_per_key_mismatch)

subsection \<open>The same downstream loss through durable-prefix truncation\<close>

text \<open>
  The previous witness isolates downstream-local loss as a store transformer. The
  next one routes the same shape through the existing durable-boundary crash
  semantics: the source durable boundary includes both source-side group events,
  while the downstream durable boundary includes only the first downstream
  application. This is independent downstream crash/truncation, not source-side
  loss.
\<close>

definition multikey_durable_precrash_state :: "(nat, nat) dw_exec_state" where
  "multikey_durable_precrash_state =
     \<lparr> exec_base = (\<lambda>_. None),
       exec_src_hist = [(ec1, Insert 0 7), (ec2, Insert 1 7)],
       exec_down_hist = [(ec1, Insert 0 7), (ec2, Insert 1 7)],
       exec_enqueued = [(ec1, Insert 0 7), (ec2, Insert 1 7)],
       exec_pending = {},
       exec_scope = {0, 1},
       exec_finish = ec3,
       exec_status = Running,
       exec_acked = [(ec1, Insert 0 7), (ec2, Insert 1 7)] \<rparr>"

definition multikey_downstream_loss_boundary :: dw_durable_boundary where
  "multikey_downstream_loss_boundary =
     \<lparr> db_src = ec2,
       db_down = ec1,
       db_enq = ec2,
       db_ack = ec2 \<rparr>"

definition multikey_durable_crashed_state :: "(nat, nat) dw_exec_state" where
  "multikey_durable_crashed_state =
     truncating_crash_state_at_boundary multikey_durable_precrash_state
       multikey_downstream_loss_boundary ec2"

lemma multikey_durable_boundary_within_finish:
  "durable_boundary_within_finish multikey_downstream_loss_boundary
     multikey_durable_precrash_state"
  by (simp add: durable_boundary_within_finish_def
                multikey_downstream_loss_boundary_def
                multikey_durable_precrash_state_def ec_defs)

lemma multikey_durable_precrash_wellformed:
  "wellformed_exec_state multikey_durable_precrash_state"
  by (auto simp: multikey_durable_precrash_state_def
                wellformed_exec_state_def exec_histories_wellformed_def
                pending_enqueued_consistent_def acked_source_consistent_def
                wellformed_src_history_def source_pos_order_total
                nth_Cons src_le_eq_less_eq c0_eq_coord_of_nat_0 ec_defs
          split: nat.splits)

lemma multikey_downstream_loss_truncates_down_not_src:
  "exec_src_hist
      (durable_exec_state_at_boundary multikey_durable_precrash_state
        multikey_downstream_loss_boundary) =
     [(ec1, Insert 0 7), (ec2, Insert 1 7)]"
  "exec_down_hist
      (durable_exec_state_at_boundary multikey_durable_precrash_state
        multikey_downstream_loss_boundary) =
     [(ec1, Insert 0 7)]"
  by (simp_all add: durable_exec_state_at_boundary_def
                    durable_history_prefix_at_def
                    multikey_downstream_loss_boundary_def
                    multikey_durable_precrash_state_def ec_defs)

lemma multikey_durable_truncating_crash_step:
  "truncating_crash_step_at_boundary multikey_durable_precrash_state
     multikey_downstream_loss_boundary ec2 multikey_durable_crashed_state"
  unfolding multikey_durable_crashed_state_def
  by (rule truncating_crash_step_at_boundary.truncating_crash)
     (rule multikey_durable_precrash_wellformed,
      simp add: multikey_durable_precrash_state_def,
      rule multikey_durable_boundary_within_finish)

lemma multikey_durable_crashed_cross_key_invariant_violation:
  "cross_key_invariant_violation_at
     (proto_of_exec_at multikey_durable_crashed_state ec2)
     ec2 0 1 (\<lambda>x y. x = y)"
  by (simp add: cross_key_invariant_violation_at_def
                source_relation_invariant_at_def
                downstream_relation_invariant_at_def relation2_holds_on_def
                multikey_durable_crashed_state_def
                truncating_crash_state_at_boundary_def
                durable_exec_state_at_boundary_def
                durable_history_prefix_at_def
                durable_pending_at_boundary_def
                durable_ack_frontier_def
                multikey_downstream_loss_boundary_def
                multikey_durable_precrash_state_def
                proto_of_exec_at_def store2_of_exec_def log_image_def
                Src_def latest_src_event_def restrict_def ec_defs Let_def)

lemma multikey_durable_crashed_group_diverges:
  "group_diverges_at (proto_of_exec_at multikey_durable_crashed_state ec2)
     ec2 {0, 1}"
  by (auto simp: group_diverges_at_def group_mismatch_at_def
                 multikey_durable_crashed_state_def
                 truncating_crash_state_at_boundary_def
                 durable_exec_state_at_boundary_def
                 durable_history_prefix_at_def
                 durable_pending_at_boundary_def
                 multikey_downstream_loss_boundary_def
                 multikey_durable_precrash_state_def
                 proto_of_exec_at_def store2_of_exec_def log_image_def
                 Src_def latest_src_event_def restrict_def ec_defs Let_def)

theorem multikey_durable_downstream_loss_closed_witness:
  "truncating_crash_step_at_boundary multikey_durable_precrash_state
      multikey_downstream_loss_boundary ec2 multikey_durable_crashed_state
   \<and> cross_key_invariant_violation_at
      (proto_of_exec_at multikey_durable_crashed_state ec2)
      ec2 0 1 (\<lambda>x y. x = y)
   \<and> group_diverges_at
      (proto_of_exec_at multikey_durable_crashed_state ec2) ec2 {0, 1}
   \<and> diverges (proto_of_exec_at multikey_durable_crashed_state ec2) ec2"
proof -
  have step: "truncating_crash_step_at_boundary multikey_durable_precrash_state
      multikey_downstream_loss_boundary ec2 multikey_durable_crashed_state"
    by (rule multikey_durable_truncating_crash_step)
  have inv: "cross_key_invariant_violation_at
      (proto_of_exec_at multikey_durable_crashed_state ec2)
      ec2 0 1 (\<lambda>x y. x = y)"
    by (rule multikey_durable_crashed_cross_key_invariant_violation)
  have group: "group_diverges_at
      (proto_of_exec_at multikey_durable_crashed_state ec2) ec2 {0, 1}"
    by (rule multikey_durable_crashed_group_diverges)
  hence div: "diverges (proto_of_exec_at multikey_durable_crashed_state ec2) ec2"
    by (rule group_diverges_at_imp_diverges)
  from step inv group div show ?thesis by blast
qed

end
