(*  Title:       DWU_Segments.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Road-2 increment I7 — the U16 fence factorization + fence-boundary bank.

    Most of U16 is landed at I0 in DWU_Machine and is CITED here, never re-proved:
      * the two HARD seams  u_release_hard_seam / u_trunccrash_hard_seam,
      * the three UTruncCrash frame lemmas  u_trunc_ledger_frame / u_trunc_base_frame /
        u_trunc_stamps_frame,
      * the turnover=epoch fact  u_turnover_counts_epoch,
      * S4  u_journal_stamps_bounded_invariant,
      * S6  u_gens_dom_bounded  (the dom (dwu_gens) ⊆ {0..dwu_hwm} spine).

    This increment adds the small bank AROUND that factorization:
      * u_fence_le_hwm_no_free_raise  (the U16 main theorem: fence ≤ hwm, scoped
        honestly to the UFenceRaise-free sub-grammar, machine-wide FALSE via the
        free raise),
      * u_armf_pos_fence  (field-guide §4b reader-clarity: an UArmF by g>0 leaves
        the fence positive — keeps "never claimed" a TRACE-level reading),
      * u_fence_boundary_kind  (the fence-segment classification: the only steps
        that move the fence are UArmF and UFenceRaise — the "3 boundary kinds,
        honest hard-seam count 2" enumeration, complementing the two landed seams).
*)

theory DWU_Segments
  imports DWU_Machine
begin

section \<open>U16 — the segment/stamps bank (fence factorization + fence boundaries)\<close>

text \<open>The UFenceRaise-free sub-grammar (P7: fence \<le> hwm is machine-wide FALSE via
  the free raise; the factorization is scoped honestly).  Definition copied
  byte-identically from the pinned probe seed.\<close>

definition dwu_reachable_no_free_raise
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k set \<Rightarrow> frontier \<Rightarrow> ('k, 'v) dwu_state \<Rightarrow> bool"
where
  "dwu_reachable_no_free_raise b K fin t \<longleftrightarrow>
     (\<exists>xs. dwu_temporal_trace (dwu_init b K fin) xs t
         \<and> (\<forall>n. UFenceRaise n \<notin> set xs))"


subsection \<open>Step-local bookkeeping (fresh helpers; the landed frame bank covers
  arm/lift/heal/fire/spawn/release but not UArmF)\<close>

text \<open>UArmF inversion: the sole rule producing an @{const UArmF} action sets the
  fence to @{term g}, leaves the high-water mark, and fires under the domain guard
  @{term "g \<in> dom (dwu_gens t)"} (the fact the fence factorization needs at the
  claim boundary).\<close>

lemma seg_step_armf_inv:
  assumes "dwu_step t (UArmF g f) t'"
  shows "dwu_fence t' = g \<and> dwu_hwm t' = dwu_hwm t \<and> g \<in> dom (dwu_gens t)"
  using assms by (cases rule: dwu_step.cases) auto

text \<open>The high-water mark is monotone under every step (only @{const USpawn}
  moves it, upward).\<close>

lemma seg_step_hwm_mono:
  assumes "dwu_step t \<alpha> t'"
  shows "dwu_hwm t \<le> dwu_hwm t'"
  using assms by (induction rule: dwu_step.induct) (auto intro: le_SucI)


subsection \<open>U16 SEGMENT-BOUNDARY ENUMERATION — @{text u_fence_boundary_kind}\<close>

text \<open>Only @{const UArmF} (@{text "dwu_fence := g"}) and @{const UFenceRaise}
  (@{text "dwu_fence := max (dwu_fence t) n"}) touch the fence; every other rule
  leaves it.  This is the honest fence-segment boundary enumeration (the two
  fence-changing kinds), complementing the two landed HARD seams
  (@{thm [source] u_release_hard_seam} = the Resume seam,
  @{thm [source] u_trunccrash_hard_seam} = the truncation seam): three boundary
  kinds, honest hard-seam count 2.\<close>

lemma u_fence_boundary_kind:
  assumes "dwu_step t \<alpha> t'"
      and "dwu_fence t' \<noteq> dwu_fence t"
  shows "(\<exists>g f. \<alpha> = UArmF g f) \<or> (\<exists>n. \<alpha> = UFenceRaise n)"
proof (rule ccontr)
  assume "\<not> ((\<exists>g f. \<alpha> = UArmF g f) \<or> (\<exists>n. \<alpha> = UFenceRaise n))"
  hence na: "\<forall>g f. \<alpha> \<noteq> UArmF g f" and nr: "\<forall>n. \<alpha> \<noteq> UFenceRaise n" by auto
  from assms(1) na nr have "dwu_fence t' = dwu_fence t"
    by (cases rule: dwu_step.cases) auto
  with assms(2) show False by simp
qed


subsection \<open>U16 READER-CLARITY — @{text u_armf_pos_fence}\<close>

text \<open>Field-guide §4b: after any @{const UArmF} by a positive generation the fence
  is positive.  This keeps "never claimed" a TRACE-level reading (no @{const UArmF}
  occurs), never a state-level @{term "dwu_fence t = 0"} misread.\<close>

lemma u_armf_pos_fence:
  assumes "dwu_step t (UArmF g f) t'"
      and "0 < g"
  shows "0 < dwu_fence t'"
  using seg_step_armf_inv[OF assms(1)] assms(2) by simp


subsection \<open>U16 MAIN — @{text u_fence_le_hwm_no_free_raise}\<close>

text \<open>The step invariant: every non-@{const UFenceRaise} step of a reachable state
  preserves @{term "dwu_fence \<le> dwu_hwm"}.  @{const UArmF} sets @{text "dwu_fence := g"}
  under @{term "g \<in> dom (dwu_gens t)"}, and S6 (@{thm [source] u_gens_dom_bounded})
  bounds that domain by the high-water mark, so @{term "g \<le> dwu_hwm t"}; every other
  non-raise step either leaves the fence (hwm monotone closes it) or is excluded.\<close>

lemma fence_le_hwm_step:
  assumes r: "dwu_reachable b K fin t"
      and le: "dwu_fence t \<le> dwu_hwm t"
      and st: "dwu_step t \<alpha> t'"
      and nf: "\<forall>n. \<alpha> \<noteq> UFenceRaise n"
  shows "dwu_fence t' \<le> dwu_hwm t'"
proof (cases "dwu_fence t' = dwu_fence t")
  case True
  have "dwu_fence t' \<le> dwu_hwm t" using le True by simp
  also have "\<dots> \<le> dwu_hwm t'" using seg_step_hwm_mono[OF st] .
  finally show ?thesis .
next
  case False
  from u_fence_boundary_kind[OF st False] nf
  obtain g f where af: "\<alpha> = UArmF g f" by blast
  have step_af: "dwu_step t (UArmF g f) t'" using st af by simp
  have fe: "dwu_fence t' = g" and hw: "dwu_hwm t' = dwu_hwm t"
    and gd: "g \<in> dom (dwu_gens t)"
    using seg_step_armf_inv[OF step_af] by auto
  from u_gens_dom_bounded[OF r] gd have g_le: "g \<le> dwu_hwm t" by auto
  show ?thesis using fe hw g_le by simp
qed

text \<open>Reachability is preserved along a single further step (the landed
  @{const dwu_reachable} idiom; re-derived here since the visible ancestor is only
  DWU_Machine).\<close>

lemma seg_reach_lift:
  assumes "dwu_reachable b K fin t"
      and "wellformed_exec_state (dwu_store t)"
      and "exec_label_preserves_history_wf (dwu_store t) a"
      and "dwu_step t (ULift g a) t'"
  shows "dwu_reachable b K fin t'"
proof -
  from assms(1) obtain xs where xs: "dwu_temporal_trace (dwu_init b K fin) xs t"
    unfolding dwu_reachable_def by blast
  have "dwu_temporal_trace t [ULift g a] t'"
    by (rule dwu_temporal_trace.dwu_lift_step
              [OF assms(2) assms(3) assms(4) dwu_temporal_trace.dwu_refl])
  with xs have "dwu_temporal_trace (dwu_init b K fin) (xs @ [ULift g a]) t'"
    by (rule dwu_temporal_trace_append)
  thus ?thesis unfolding dwu_reachable_def by blast
qed

lemma seg_reach_publost:
  assumes "dwu_reachable b K fin t"
      and "wellformed_exec_state (dwu_store t)"
      and "exec_label_preserves_history_wf (dwu_store t) (DoDownstream c e)"
      and "dwu_step t (UPubLost g c e) t'"
  shows "dwu_reachable b K fin t'"
proof -
  from assms(1) obtain xs where xs: "dwu_temporal_trace (dwu_init b K fin) xs t"
    unfolding dwu_reachable_def by blast
  have "dwu_temporal_trace t [UPubLost g c e] t'"
    by (rule dwu_temporal_trace.dwu_publost_step
              [OF assms(2) assms(3) assms(4) dwu_temporal_trace.dwu_refl])
  with xs have "dwu_temporal_trace (dwu_init b K fin) (xs @ [UPubLost g c e]) t'"
    by (rule dwu_temporal_trace_append)
  thus ?thesis unfolding dwu_reachable_def by blast
qed

lemma seg_reach_other:
  assumes "dwu_reachable b K fin t"
      and "\<forall>g a. \<alpha> \<noteq> ULift g a"
      and "\<forall>g c e. \<alpha> \<noteq> UPubLost g c e"
      and "dwu_step t \<alpha> t'"
  shows "dwu_reachable b K fin t'"
proof -
  from assms(1) obtain xs where xs: "dwu_temporal_trace (dwu_init b K fin) xs t"
    unfolding dwu_reachable_def by blast
  have "dwu_temporal_trace t [\<alpha>] t'"
    by (rule dwu_temporal_trace.dwu_other_step
              [OF assms(2) assms(3) assms(4) dwu_temporal_trace.dwu_refl])
  with xs have "dwu_temporal_trace (dwu_init b K fin) (xs @ [\<alpha>]) t'"
    by (rule dwu_temporal_trace_append)
  thus ?thesis unfolding dwu_reachable_def by blast
qed

text \<open>Lifting the step invariant over a UFenceRaise-free temporal trace, threading
  BOTH reachability (each prefix state is @{const dwu_reachable}, so S6 applies) and
  @{term "dwu_fence \<le> dwu_hwm"}.  Mirrors the S6 trace threading
  (@{thm [source] u_gens_dom_trace}) and the landed persistence idiom.\<close>

lemma fence_le_hwm_trace:
  assumes "dwu_temporal_trace u xs u'"
      and "dwu_reachable b K fin u"
      and "dwu_fence u \<le> dwu_hwm u"
      and "\<forall>n. UFenceRaise n \<notin> set xs"
  shows "dwu_fence u' \<le> dwu_hwm u'"
  using assms
proof (induction rule: dwu_temporal_trace.induct)
  case (dwu_refl t)
  then show ?case by simp
next
  case (dwu_lift_step t a g t' as t'')
  have nf_as: "\<forall>n. UFenceRaise n \<notin> set as" using dwu_lift_step.prems(3) by simp
  have nfh: "\<forall>n. ULift g a \<noteq> UFenceRaise n" by simp
  have le': "dwu_fence t' \<le> dwu_hwm t'"
    by (rule fence_le_hwm_step[OF dwu_lift_step.prems(1) dwu_lift_step.prems(2)
                                  dwu_lift_step.hyps(3) nfh])
  have rc': "dwu_reachable b K fin t'"
    by (rule seg_reach_lift[OF dwu_lift_step.prems(1) dwu_lift_step.hyps(1)
                               dwu_lift_step.hyps(2) dwu_lift_step.hyps(3)])
  show ?case by (rule dwu_lift_step.IH[OF rc' le' nf_as])
next
  case (dwu_publost_step t c e g t' as t'')
  have nf_as: "\<forall>n. UFenceRaise n \<notin> set as" using dwu_publost_step.prems(3) by simp
  have nfh: "\<forall>n. UPubLost g c e \<noteq> UFenceRaise n" by simp
  have le': "dwu_fence t' \<le> dwu_hwm t'"
    by (rule fence_le_hwm_step[OF dwu_publost_step.prems(1) dwu_publost_step.prems(2)
                                  dwu_publost_step.hyps(3) nfh])
  have rc': "dwu_reachable b K fin t'"
    by (rule seg_reach_publost[OF dwu_publost_step.prems(1) dwu_publost_step.hyps(1)
                                  dwu_publost_step.hyps(2) dwu_publost_step.hyps(3)])
  show ?case by (rule dwu_publost_step.IH[OF rc' le' nf_as])
next
  case (dwu_other_step \<alpha> t t' as t'')
  have nf_as: "\<forall>n. UFenceRaise n \<notin> set as" using dwu_other_step.prems(3) by simp
  have nfh: "\<forall>n. \<alpha> \<noteq> UFenceRaise n"
    using dwu_other_step.prems(3) by (metis list.set_intros(1))
  have le': "dwu_fence t' \<le> dwu_hwm t'"
    by (rule fence_le_hwm_step[OF dwu_other_step.prems(1) dwu_other_step.prems(2)
                                  dwu_other_step.hyps(3) nfh])
  have rc': "dwu_reachable b K fin t'"
    by (rule seg_reach_other[OF dwu_other_step.prems(1) dwu_other_step.hyps(1)
                                dwu_other_step.hyps(2) dwu_other_step.hyps(3)])
  show ?case by (rule dwu_other_step.IH[OF rc' le' nf_as])
qed

theorem u_fence_le_hwm_no_free_raise:   \<comment> \<open>fence \<le> hwm, scoped to the
  UFenceRaise-free sub-grammar (machine-wide FALSE via the free raise)\<close>
  assumes "dwu_reachable_no_free_raise b K fin t"
  shows "dwu_fence t \<le> dwu_hwm t"
proof -
  from assms obtain xs
    where xs: "dwu_temporal_trace (dwu_init b K fin) xs t"
      and nf: "\<forall>n. UFenceRaise n \<notin> set xs"
    unfolding dwu_reachable_no_free_raise_def by blast
  have rc0: "dwu_reachable b K fin (dwu_init b K fin)" by (rule dwu_reachable_init)
  have le0: "dwu_fence (dwu_init b K fin) \<le> dwu_hwm (dwu_init b K fin)"
    by (simp add: dwu_init_def)
  show ?thesis by (rule fence_le_hwm_trace[OF xs rc0 le0 nf])
qed

end
