(*  Title:       DBLog_Instance.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    The subordinated DBLog instance for the decoupled Dual-Write development
    (ADR-007 decouple-and-subordinate, group 2 / increment 2). This is the
    SOLE importer of DBLog_Virtual_Cuts (Paper 1, arXiv:2605.31475). It
    exhibits a wellformed DBLog run as ONE certified inhabitant of the
    virtual-cut-state interface, via a bridge LEMMA --- not a locale
    interpretation: the abstract asymmetric_store locale (parameters P, k0) and a
    DBLog run have disjoint parameter sets, so an interpretation does not
    typecheck; the connection is the one-line citation
    virtual_cut_certifies_dblog below. Result 3's DBLog prong is demoted here
    to a worked instance, never the paper's headline.

    The abstract interface predicate virtual_cut_state now lives in the shared
    DBLog-free parent session Dual_Write_Layer0. The DBLog formalization and
    the Dual_Write_Core session both inherit that same HOL constant, while this
    companion remains the only place where the DBLog run/certificate stack is
    cited from the Dual-Write side.

    Everything below is transplanted byte-for-byte from the locked
    dual_write/Dual_Write_Unification.thy (only the imports are reparented ---
    no proof body is edited). No new axiomatization/typedecl/consts; the DBLog
    prong is by citation to wellformed_run_implies_virtual_cut, not re-derived.
*)

theory DBLog_Instance
  imports
    DBLog_Virtual_Cuts.Public_Checker_Witness
begin

subsection \<open>The event-constructor filter\<close>

definition cdc_only :: "('k, 'v) replay_event list \<Rightarrow> bool" where
  "cdc_only \<sigma> \<longleftrightarrow> (\<forall>e \<in> set \<sigma>. \<not> is_refresh e)"

subsection \<open>The bridge lemma --- a wellformed DBLog run certifies a virtual cut\<close>

text \<open>
  A wellformed DBLog run is one certified inhabitant of the virtual-cut-state
  interface. This is the imported \<open>wellformed_run_implies_virtual_cut\<close> from
  \<open>DBLog_Virtual_Cuts\<close>, applied directly (a bridge lemma, not a locale
  interpretation: disjoint parameter sets), not re-derived. Forced to
  \<open>k::linorder\<close> by \<open>wellformed_dblog_run\<close> / \<open>clean_prefix_of\<close>.
\<close>

theorem virtual_cut_certifies_dblog:
  fixes b0 :: "'k::linorder \<rightharpoonup> 'v"
  assumes "wellformed_dblog_run b0 R H"
  shows   "virtual_cut_state b0 (clean_prefix_of R) (scope_of R) (frontier_of R) H"
  by (rule Virtual_Cut.wellformed_run_implies_virtual_cut[OF assms])

subsection \<open>Adapter-level safety shape\<close>

text \<open>
  The dual-write core proves replay safety in its own DBLog-free session. This
  DBLog adapter states the same positive-safety shape locally over the shared
  @{const virtual_cut_state}. This is an adapter theorem: it does not feed DBLog
  premises back into the core negative theorem.
\<close>

definition dblog_replay_image
  :: "('k::linorder, 'v) run \<Rightarrow> ('k \<rightharpoonup> 'v)"
where
  "dblog_replay_image R =
     restrict (Apply (clean_prefix_of R)) (scope_of R)"

definition dblog_source_image
  :: "('k::linorder \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) run \<Rightarrow>
      ('k, 'v) src_history \<Rightarrow> ('k \<rightharpoonup> 'v)"
where
  "dblog_source_image b0 R H =
     restrict (Src b0 H (frontier_of R)) (scope_of R)"

definition dblog_observable_mismatch
  :: "('k::linorder \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) run \<Rightarrow>
      ('k, 'v) src_history \<Rightarrow> 'k \<Rightarrow> bool"
where
  "dblog_observable_mismatch b0 R H k \<longleftrightarrow>
     k \<in> scope_of R
   \<and> dblog_replay_image R k \<noteq> dblog_source_image b0 R H k"

theorem virtual_cut_state_no_dblog_observable_mismatch:
  assumes
    "virtual_cut_state b0 (clean_prefix_of R) (scope_of R) (frontier_of R) H"
  shows "\<not> dblog_observable_mismatch b0 R H k"
  using assms
  by (auto simp: dblog_observable_mismatch_def dblog_replay_image_def
                 dblog_source_image_def virtual_cut_state_def)

theorem wellformed_dblog_run_no_observable_mismatch:
  fixes b0 :: "'k::linorder \<rightharpoonup> 'v"
  assumes "wellformed_dblog_run b0 R H"
  shows "\<not> dblog_observable_mismatch b0 R H k"
  by (rule virtual_cut_state_no_dblog_observable_mismatch
      [OF virtual_cut_certifies_dblog[OF assms]])

subsection \<open>Distinctness --- the DBLog inhabitant is genuinely refresh-bearing\<close>

text \<open>
  The DBLog prong is not \<open>cdc_only\<close>: its exhibited witness clean prefix
  carries \<open>Refresh\<close> events. Paired with the core outbox prong (which is
  \<open>cdc_only\<close>), this shows the abstract interface has two genuinely distinct
  inhabitants. Monomorphic over \<open>nat\<close>.
\<close>

lemma dblog_prong_not_cdc_only:
  "\<not> cdc_only (clean_prefix_of ex_run)"
  by (simp add: cdc_only_def exr_clean_prefix)

end
