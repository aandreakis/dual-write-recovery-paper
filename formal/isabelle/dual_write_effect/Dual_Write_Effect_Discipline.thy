(*  Title:       Dual_Write_Effect_Discipline.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    The GENERAL POSITIVE DISCIPLINE THEOREM (T2.8) and its per-guard
    controls on the CYCLIC effect machine (Dual_Write_Effect_Cyclic, the
    promoted primary) --- the safe half of the two-tier slogan as a
    for-all theorem.

    Source material: the S1 probe Discipline_Probe.thy (terminal machine,
    machine-checked green, independently audited).  This theory re-states
    and re-proves, on the cyclic machine with its epoch-stamped 4-tuple
    emissions and its Resume rule:

    1.  The two trace disciplines (the pinned 2-premise form and the honest
        3-guard form), each EXTENDED with a Resume case that carries NO
        GUARD: discipline imposes nothing on Resume.

    2.  resume_preserves_effect_safe -- the S1 low-risk claim as a theorem:
        a Resume step preserves the emission ledger and the committed
        source history VERBATIM, hence preserves the effect verdict
        exactly (an iff, the strongest honest form).

    3.  The three step-preservation lemmas, the glue induction, and
        general_positive_discipline in the SAME honest 3-guard form as the
        probe's (fire-time justification + publish freshness +
        reconcile-suffix fresh-and-distinct).  STATEMENT AUDIT: the cyclic
        machine forces NO additional premise -- no epoch condition, no
        advertised-frontier vocabulary, nothing.  The epoch appears in no
        discipline guard; it rides along inside the emission tuples, and
        e_payload projects it away.

    4.  disciplined_runs_are_reachable at the machine's PINNED reachability
        (dwe_init Map.empty {0, 1} ec2 -- the cyclic machine's
        dwe_reachable is monomorphic, unlike the probe's parametric one).

    5.  discipline_nonvacuous, now EXERCISING THE CYCLE: commit+publish e1,
        commit e2 with delivery in flight, crash, checkpointed genuinely
        re-driving reconcile (m = 1), RESUME into epoch 1, then a fresh
        disciplined publish of a THIRD event e3 at ec3 -- ending Running,
        epoch 1, with a three-entry ledger spanning both epochs, not
        effect-unsafe.

    6.  The four per-guard load-bearing controls, ported: dropping
        fire-time justification, publish freshness (the refire theorem +
        the 2-premise refutation), reconcile-suffix freshness, or
        reconcile-suffix internal distinctness is each witnessed unsafe.
        The distinctness route re-checks that WF-H1 non-strictness
        (history_can_append uses \<le>) carries to the cyclic machine
        identically -- the core is shared.

    Ported from the S4c prover artifact with statements unchanged; the
    scratch original's in-source ML oracle gates are STRIPPED here:
    oracle-freedom is certified by scratch-side per-slice gate sessions
    with confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Discipline
  imports Dual_Write_Effect_Cyclic
begin

section \<open>The two trace disciplines on the cyclic machine\<close>

text \<open>
  The PINNED 2-premise discipline (the plan's slogan form of T2.8), now on
  the cyclic machine: label steps carry the machine's own admissibility
  guards; publish steps must be justified at fire time (the payload sits in
  the committed source history NOW); reconcile steps must re-drive a suffix
  that is ledger-fresh and internally payload-distinct.  NO publish
  freshness guard.  Resume steps carry NO guard at all: the discipline
  imposes nothing on Resume (made honest by
  @{text resume_preserves_effect_safe} below).
\<close>

inductive semi_disciplined_trace
  :: "('k, 'v) dwe_state \<Rightarrow> ('k, 'v) dwe_action list \<Rightarrow>
      ('k, 'v) dwe_state \<Rightarrow> bool"
where
  semi_refl:
    "semi_disciplined_trace t [] t"
| semi_nonpub:
    "\<lbrakk>dwe_step t a t';
      wellformed_exec_state (dwe_core t);
      exec_label_preserves_history_wf (dwe_core t) a;
      \<forall>c e. a \<noteq> DoDownstream c e;
      semi_disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     semi_disciplined_trace t (DWE_Label a # as) t''"
| semi_publish:
    "\<lbrakk>dwe_step t (DoDownstream c e) t';
      wellformed_exec_state (dwe_core t);
      exec_label_preserves_history_wf (dwe_core t) (DoDownstream c e);
      (c, e) \<in> set (exec_src_hist (dwe_core t));
      semi_disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     semi_disciplined_trace t (DWE_Label (DoDownstream c e) # as) t''"
| semi_reconcile:
    "\<lbrakk>emitting_reconcile m t f t';
      distinct (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                          (exec_scope (dwe_core t)) f));
      set (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                     (exec_scope (dwe_core t)) f))
        \<inter> e_payload ` set (dwe_emitted t) = {};
      semi_disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     semi_disciplined_trace t (DWE_Reconcile m f # as) t''"
| semi_resume:
    "\<lbrakk>dwe_resume t t';
      semi_disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     semi_disciplined_trace t (DWE_Resume # as) t''"

text \<open>
  The HONEST discipline: identical, except publish steps additionally
  require PUBLISH FRESHNESS --- the payload is not already on the emission
  ledger.  The Resume case is again guard-free.  Every guard is
  ledger/src\_hist-local; the epoch appears in NO guard.
\<close>

inductive disciplined_trace
  :: "('k, 'v) dwe_state \<Rightarrow> ('k, 'v) dwe_action list \<Rightarrow>
      ('k, 'v) dwe_state \<Rightarrow> bool"
where
  disciplined_refl:
    "disciplined_trace t [] t"
| disciplined_nonpub:
    "\<lbrakk>dwe_step t a t';
      wellformed_exec_state (dwe_core t);
      exec_label_preserves_history_wf (dwe_core t) a;
      \<forall>c e. a \<noteq> DoDownstream c e;
      disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     disciplined_trace t (DWE_Label a # as) t''"
| disciplined_publish:
    "\<lbrakk>dwe_step t (DoDownstream c e) t';
      wellformed_exec_state (dwe_core t);
      exec_label_preserves_history_wf (dwe_core t) (DoDownstream c e);
      (c, e) \<in> set (exec_src_hist (dwe_core t));
      (c, e) \<notin> e_payload ` set (dwe_emitted t);
      disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     disciplined_trace t (DWE_Label (DoDownstream c e) # as) t''"
| disciplined_reconcile:
    "\<lbrakk>emitting_reconcile m t f t';
      distinct (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                          (exec_scope (dwe_core t)) f));
      set (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                     (exec_scope (dwe_core t)) f))
        \<inter> e_payload ` set (dwe_emitted t) = {};
      disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     disciplined_trace t (DWE_Reconcile m f # as) t''"
| disciplined_resume:
    "\<lbrakk>dwe_resume t t';
      disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     disciplined_trace t (DWE_Resume # as) t''"

text \<open>The honest form only ADDS one guard: it refines the pinned form.\<close>

lemma discipline_refines_two_premise_form:
  assumes "disciplined_trace t acts t'"
  shows "semi_disciplined_trace t acts t'"
  using assms
  by (induction rule: disciplined_trace.induct)
     (auto intro: semi_disciplined_trace.intros)

text \<open>Both disciplines restrict the SCHEDULER only: every disciplined run is
  a genuine temporal run of the cyclic machine (no new transitions).\<close>

lemma semi_disciplined_imp_temporal:
  assumes "semi_disciplined_trace t acts t'"
  shows "dwe_temporal_trace t acts t'"
  using assms
  by (induction rule: semi_disciplined_trace.induct)
     (auto intro: dwe_temporal_trace.intros)

lemma disciplined_trace_imp_temporal:
  assumes "disciplined_trace t acts t'"
  shows "dwe_temporal_trace t acts t'"
  by (rule semi_disciplined_imp_temporal
      [OF discipline_refines_two_premise_form[OF assms]])

subsection \<open>Introduction helpers\<close>

lemma semi_disciplined_trace_append:
  assumes "semi_disciplined_trace t as t'"
      and "semi_disciplined_trace t' bs t''"
  shows "semi_disciplined_trace t (as @ bs) t''"
  using assms
  by (induction rule: semi_disciplined_trace.induct)
     (auto intro: semi_disciplined_trace.intros)

lemma disciplined_trace_append:
  assumes "disciplined_trace t as t'"
      and "disciplined_trace t' bs t''"
  shows "disciplined_trace t (as @ bs) t''"
  using assms
  by (induction rule: disciplined_trace.induct)
     (auto intro: disciplined_trace.intros)

lemma semi_publish_singleI:
  assumes "dwe_step t (DoDownstream c e) t'"
      and "wellformed_exec_state (dwe_core t)"
      and "exec_label_preserves_history_wf (dwe_core t) (DoDownstream c e)"
      and "(c, e) \<in> set (exec_src_hist (dwe_core t))"
  shows "semi_disciplined_trace t [DWE_Label (DoDownstream c e)] t'"
  by (rule semi_disciplined_trace.semi_publish
      [OF assms semi_disciplined_trace.semi_refl])

lemma disciplined_nonpub_singleI:
  assumes "dwe_step t a t'"
      and "wellformed_exec_state (dwe_core t)"
      and "exec_label_preserves_history_wf (dwe_core t) a"
      and "\<forall>c e. a \<noteq> DoDownstream c e"
  shows "disciplined_trace t [DWE_Label a] t'"
  by (rule disciplined_trace.disciplined_nonpub
      [OF assms disciplined_trace.disciplined_refl])

lemma disciplined_publish_singleI:
  assumes "dwe_step t (DoDownstream c e) t'"
      and "wellformed_exec_state (dwe_core t)"
      and "exec_label_preserves_history_wf (dwe_core t) (DoDownstream c e)"
      and "(c, e) \<in> set (exec_src_hist (dwe_core t))"
      and "(c, e) \<notin> e_payload ` set (dwe_emitted t)"
  shows "disciplined_trace t [DWE_Label (DoDownstream c e)] t'"
  by (rule disciplined_trace.disciplined_publish
      [OF assms disciplined_trace.disciplined_refl])

lemma disciplined_reconcile_singleI:
  assumes "emitting_reconcile m t f t'"
      and "distinct (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                               (exec_scope (dwe_core t)) f))"
      and "set (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                          (exec_scope (dwe_core t)) f))
             \<inter> e_payload ` set (dwe_emitted t) = {}"
  shows "disciplined_trace t [DWE_Reconcile m f] t'"
  by (rule disciplined_trace.disciplined_reconcile
      [OF assms disciplined_trace.disciplined_refl])

lemma disciplined_resume_singleI:
  assumes "dwe_resume t t'"
  shows "disciplined_trace t [DWE_Resume] t'"
  by (rule disciplined_trace.disciplined_resume
      [OF assms disciplined_trace.disciplined_refl])


section \<open>Resume preserves the effect verdict verbatim (the S1 claim)\<close>

text \<open>
  The S1 evidence said the Resume rule is low-risk for T2.8 because it
  touches neither the emission ledger nor the committed source history.
  Made a theorem, in the strongest honest form: Resume preserves BOTH
  verbatim, and therefore preserves the effect verdict as an IFF (not
  merely one direction).  This is exactly why the Resume case of the
  discipline needs no guard.
\<close>

theorem resume_preserves_effect_safe:
  assumes "dwe_resume t t'"
  shows "dwe_emitted t' = dwe_emitted t
       \<and> exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t)
       \<and> (effect_unsafe t' \<longleftrightarrow> effect_unsafe t)"
proof -
  have em: "dwe_emitted t' = dwe_emitted t"
    by (rule dwe_resume_emitted_same[OF assms])
  have src: "exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t)"
    by (rule dwe_resume_src_same[OF assms])
  have "effect_unsafe t' \<longleftrightarrow> effect_unsafe t"
    by (simp add: effect_unsafe_def premature_def duplicate_def em src)
  with em src show ?thesis by blast
qed


section \<open>The general positive discipline theorem (T2.8, cyclic)\<close>

text \<open>
  The inductive invariant is LITERALLY effect safety: all emissions
  justified against the current committed source history
  (\<open>\<not> premature\<close>) and a payload-distinct ledger (\<open>\<not> duplicate\<close>).
  No strengthening, no frontier bookkeeping, and --- the cyclic audit
  point --- no epoch bookkeeping is required.
\<close>

lemma effect_safe_alt:
  "\<not> effect_unsafe t \<longleftrightarrow>
     (\<forall>x \<in> set (dwe_emitted t). justified_at (exec_src_hist (dwe_core t)) x)
   \<and> distinct (map e_payload (dwe_emitted t))"
  by (auto simp: effect_unsafe_def premature_def duplicate_def)

subsection \<open>Step-shape inversion lemmas\<close>

lemma dwe_step_nonpub_emitted:
  assumes "dwe_step t a t'"
      and "\<forall>c e. a \<noteq> DoDownstream c e"
  shows "dwe_emitted t' = dwe_emitted t"
  using assms by (cases rule: dwe_step.cases) auto

lemma dwe_step_publish_emitted:
  assumes "dwe_step t (DoDownstream c e) t'"
  shows "dwe_emitted t' =
           dwe_emitted t
             @ [(length (exec_src_hist (dwe_core t)), dwe_epoch t, c, e)]"
  using assms by (cases rule: dwe_step.cases) auto

lemma dw_exec_step_downstream_src:
  assumes "dw_exec_step s (DoDownstream c e) s'"
  shows "exec_src_hist s' = exec_src_hist s"
  using assms by (cases rule: dw_exec_step.cases) simp_all

lemma dwe_step_publish_src_hist:
  assumes "dwe_step t (DoDownstream c e) t'"
  shows "exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t)"
  by (rule dw_exec_step_downstream_src[OF dwe_step_core[OF assms]])

lemma dwe_step_src_hist_extends:
  assumes "dwe_step t a t'"
  shows "\<exists>zs. exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t) @ zs"
  by (rule dw_exec_step_src_ext[OF dwe_step_core[OF assms]])

text \<open>The 4-tuple restamp projection (the probe's 3-tuple lemma, with the
  epoch component added; @{const e_payload} projects both away).\<close>

lemma map_e_payload_restamp:
  "map e_payload (map (\<lambda>(c, e). (n, ep, c, e)) xs) = xs"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases x) simp
qed

lemma emitting_reconcile_emitted:
  assumes "emitting_reconcile m t f t'"
  shows "dwe_emitted t' =
           dwe_emitted t
             @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                              dwe_epoch t, c, e))
                 (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                            (exec_scope (dwe_core t)) f))"
  using assms by (simp add: emitting_reconcile_def)

subsection \<open>Safety preservation under each disciplined step\<close>

lemma nonpub_preserves_effect_safe:
  assumes step: "dwe_step t a t'"
      and nonpub: "\<forall>c e. a \<noteq> DoDownstream c e"
      and safe: "\<not> effect_unsafe t"
  shows "\<not> effect_unsafe t'"
proof -
  have emitted: "dwe_emitted t' = dwe_emitted t"
    by (rule dwe_step_nonpub_emitted[OF step nonpub])
  obtain zs where zs: "exec_src_hist (dwe_core t')
                       = exec_src_hist (dwe_core t) @ zs"
    using dwe_step_src_hist_extends[OF step] by blast
  have just: "\<forall>x \<in> set (dwe_emitted t).
                justified_at (exec_src_hist (dwe_core t)) x"
    and dist: "distinct (map e_payload (dwe_emitted t))"
    using safe by (auto simp: effect_safe_alt)
  have just': "\<forall>x \<in> set (dwe_emitted t').
                 justified_at (exec_src_hist (dwe_core t')) x"
  proof
    fix x assume "x \<in> set (dwe_emitted t')"
    then have x_in: "x \<in> set (dwe_emitted t)" by (simp add: emitted)
    have jx: "justified_at (exec_src_hist (dwe_core t)) x"
      using just x_in by blast
    have "e_stamp x \<le> length (exec_src_hist (dwe_core t))"
      using jx by (simp add: justified_at_def)
    then show "justified_at (exec_src_hist (dwe_core t')) x"
      using jx by (simp add: zs justified_at_append_stable)
  qed
  show ?thesis
    using just' dist by (simp add: effect_safe_alt emitted)
qed

lemma publish_preserves_effect_safe:
  assumes step: "dwe_step t (DoDownstream c e) t'"
      and fire_just: "(c, e) \<in> set (exec_src_hist (dwe_core t))"
      and fresh: "(c, e) \<notin> e_payload ` set (dwe_emitted t)"
      and safe: "\<not> effect_unsafe t"
  shows "\<not> effect_unsafe t'"
proof -
  let ?S = "exec_src_hist (dwe_core t)"
  have emitted: "dwe_emitted t'
                 = dwe_emitted t @ [(length ?S, dwe_epoch t, c, e)]"
    by (rule dwe_step_publish_emitted[OF step])
  have src: "exec_src_hist (dwe_core t') = ?S"
    by (rule dwe_step_publish_src_hist[OF step])
  have just: "\<forall>x \<in> set (dwe_emitted t). justified_at ?S x"
    and dist: "distinct (map e_payload (dwe_emitted t))"
    using safe by (auto simp: effect_safe_alt)
  have take_S: "take (length ?S) ?S = ?S" by simp
  have new_just: "justified_at ?S (length ?S, dwe_epoch t, c, e)"
    using fire_just by (simp add: justified_at_def take_S)
  have just': "\<forall>x \<in> set (dwe_emitted t').
                 justified_at (exec_src_hist (dwe_core t')) x"
    using just new_just by (auto simp: emitted src)
  have dist': "distinct (map e_payload (dwe_emitted t'))"
    using dist fresh by (auto simp: emitted)
  show ?thesis
    using just' dist' by (simp add: effect_safe_alt)
qed

text \<open>
  The reconcile preservation lemma, with the S1-probe forensics baked in:
  \<open>sfx_S\<close> is EXPLICIT RULE COMPOSITION (@{thm [source] subset_trans} over
  @{thm [source] set_drop_subset}) --- never chain the quantified library
  fact into blast; \<open>payload_eq\<close> is a LITERAL \<open>simp only:\<close> rewrite
  (the eager map-fusion of the default simpset would defeat the double-map
  shape before @{thm [source] map_e_payload_restamp} can fire).
\<close>

lemma reconcile_preserves_effect_safe:
  assumes rec: "emitting_reconcile m t f t'"
      and dist_sfx: "distinct (drop m (replay_down_hist
                       (exec_src_hist (dwe_core t))
                       (exec_scope (dwe_core t)) f))"
      and fresh_sfx: "set (drop m (replay_down_hist
                        (exec_src_hist (dwe_core t))
                        (exec_scope (dwe_core t)) f))
                        \<inter> e_payload ` set (dwe_emitted t) = {}"
      and safe: "\<not> effect_unsafe t"
  shows "\<not> effect_unsafe t'"
proof -
  let ?S = "exec_src_hist (dwe_core t)"
  let ?R = "replay_down_hist ?S (exec_scope (dwe_core t)) f"
  let ?sfx = "drop m ?R"
  have emitted: "dwe_emitted t'
                 = dwe_emitted t
                     @ map (\<lambda>(c, e). (length ?S, dwe_epoch t, c, e)) ?sfx"
    by (rule emitting_reconcile_emitted[OF rec])
  have src: "exec_src_hist (dwe_core t') = ?S"
    by (rule emitting_reconcile_src_same[OF rec])
  have just: "\<forall>x \<in> set (dwe_emitted t). justified_at ?S x"
    and dist: "distinct (map e_payload (dwe_emitted t))"
    using safe by (auto simp: effect_safe_alt)
  have R_S: "set ?R \<subseteq> set ?S"
    unfolding replay_down_hist_def by (rule filter_is_subset)
  have sfx_S: "set ?sfx \<subseteq> set ?S"
    by (rule subset_trans[OF set_drop_subset R_S])
  have take_S: "take (length ?S) ?S = ?S" by simp
  have new_just:
    "\<forall>x \<in> set (map (\<lambda>(c, e). (length ?S, dwe_epoch t, c, e)) ?sfx).
       justified_at ?S x"
  proof
    fix x assume "x \<in> set (map (\<lambda>(c, e). (length ?S, dwe_epoch t, c, e)) ?sfx)"
    then obtain y where y_in: "y \<in> set ?sfx"
        and x_eq: "x = (case y of (c, e) \<Rightarrow> (length ?S, dwe_epoch t, c, e))"
      by auto
    obtain c e where y_eq: "y = (c, e)" by (cases y)
    have "(c, e) \<in> set ?S" using y_in y_eq sfx_S by blast
    then show "justified_at ?S x"
      by (simp add: x_eq y_eq justified_at_def take_S)
  qed
  have just': "\<forall>x \<in> set (dwe_emitted t').
                 justified_at (exec_src_hist (dwe_core t')) x"
    using just new_just by (auto simp: emitted src)
  have payload_eq: "map e_payload (dwe_emitted t')
                    = map e_payload (dwe_emitted t) @ ?sfx"
    by (simp only: emitted map_append map_e_payload_restamp)
  have dist': "distinct (map e_payload (dwe_emitted t'))"
    using dist dist_sfx fresh_sfx by (auto simp: payload_eq)
  show ?thesis
    using just' dist' by (simp add: effect_safe_alt)
qed

subsection \<open>Safety is inductive along disciplined traces\<close>

lemma disciplined_trace_preserves_effect_safe:
  assumes "disciplined_trace t acts t'"
      and "\<not> effect_unsafe t"
  shows "\<not> effect_unsafe t'"
  using assms
proof (induction rule: disciplined_trace.induct)
  case (disciplined_refl t)
  then show ?case .
next
  case (disciplined_nonpub t a t' as t'')
  have "\<not> effect_unsafe t'"
    by (rule nonpub_preserves_effect_safe
        [OF disciplined_nonpub.hyps(1) disciplined_nonpub.hyps(4)
            disciplined_nonpub.prems])
  then show ?case by (rule disciplined_nonpub.IH)
next
  case (disciplined_publish t c e t' as t'')
  have "\<not> effect_unsafe t'"
    by (rule publish_preserves_effect_safe
        [OF disciplined_publish.hyps(1) disciplined_publish.hyps(4)
            disciplined_publish.hyps(5) disciplined_publish.prems])
  then show ?case by (rule disciplined_publish.IH)
next
  case (disciplined_reconcile m t f t' as t'')
  have "\<not> effect_unsafe t'"
    by (rule reconcile_preserves_effect_safe
        [OF disciplined_reconcile.hyps(1) disciplined_reconcile.hyps(2)
            disciplined_reconcile.hyps(3) disciplined_reconcile.prems])
  then show ?case by (rule disciplined_reconcile.IH)
next
  case (disciplined_resume t t' as t'')
  have "\<not> effect_unsafe t'"
    using resume_preserves_effect_safe[OF disciplined_resume.hyps(1)]
          disciplined_resume.prems
    by simp
  then show ?case by (rule disciplined_resume.IH)
qed

text \<open>
  HEADLINE (T2.8, cyclic).  Every disciplined trace from ANY initial state
  ends effect-safe: not premature and not duplicate.  All premises live in
  the discipline's rules; every one of them is ledger/src\_hist-local, and
  --- the S4c audit point --- the statement is the SAME honest 3-guard form
  as the terminal probe's: the cyclic machine forced NO additional premise
  (no epoch condition, no advertised-frontier vocabulary, no guard on
  Resume).
\<close>

theorem general_positive_discipline:
  assumes "disciplined_trace (dwe_init b K fin) acts t"
  shows "\<not> effect_unsafe t"
proof -
  have "\<not> effect_unsafe (dwe_init b K fin)"
    by (simp add: effect_unsafe_def premature_def duplicate_def dwe_init_def)
  then show ?thesis
    by (rule disciplined_trace_preserves_effect_safe[OF assms])
qed

corollary general_positive_discipline_pinned:
  assumes "disciplined_trace
             (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2) acts t"
  shows "\<not> effect_unsafe t"
  by (rule general_positive_discipline[OF assms])

text \<open>
  Disciplined runs are reachable runs, at the machine's PINNED reachability
  instantiation: the cyclic @{const dwe_reachable} is monomorphic from
  @{term "dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2"} (the probe's
  terminal counterpart was parametric in \<open>b K fin\<close>; this is the one
  statement-level adaptation the pinned reachability forces).
\<close>

corollary disciplined_runs_are_reachable:
  assumes "disciplined_trace
             (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2) acts t"
  shows "dwe_reachable t"
  using disciplined_trace_imp_temporal[OF assms]
  unfolding dwe_reachable_def by blast


section \<open>Non-vacuity: a disciplined run that EXERCISES THE CYCLE\<close>

text \<open>
  The witness run: the banked loaded window (commit+publish \<open>e1\<close>, commit
  \<open>e2\<close> with its delivery in flight, crash at @{const ec2}), the banked
  checkpointed genuinely re-driving reconcile (m = 1, fires the missing
  \<open>e2\<close> effect), then RESUME into epoch 1, and there a fresh disciplined
  publish of a THIRD business event \<open>e3\<close> at the locked-core coordinate
  @{const ec3}.  The run ends Running in epoch 1 with a three-entry ledger
  spanning both epochs, not effect-unsafe.
\<close>

definition e3 :: "(nat, nat) source_event" where "e3 = Insert 2 3"

definition d_run_w :: "(nat, nat) dwe_state" where
  "d_run_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                    [(ec1, e1), (ec2, e2)] {} Running)
                 [(1, 0, ec1, e1), (2, 0, ec2, e2)] 1"

definition d_src3_w :: "(nat, nat) dwe_state" where
  "d_src3_w = mkT (mkC [(ec1, e1), (ec2, e2), (ec3, e3)]
                     [(ec1, e1), (ec2, e2)]
                     [(ec1, e1), (ec2, e2)] {} Running)
                  [(1, 0, ec1, e1), (2, 0, ec2, e2)] 1"

definition d_enq3_w :: "(nat, nat) dwe_state" where
  "d_enq3_w = mkT (mkC [(ec1, e1), (ec2, e2), (ec3, e3)]
                     [(ec1, e1), (ec2, e2)]
                     [(ec1, e1), (ec2, e2), (ec3, e3)] {(ec3, e3)} Running)
                  [(1, 0, ec1, e1), (2, 0, ec2, e2)] 1"

definition d_pub3_w :: "(nat, nat) dwe_state" where
  "d_pub3_w = mkT (mkC [(ec1, e1), (ec2, e2), (ec3, e3)]
                     [(ec1, e1), (ec2, e2), (ec3, e3)]
                     [(ec1, e1), (ec2, e2), (ec3, e3)] {} Running)
                  [(1, 0, ec1, e1), (2, 0, ec2, e2), (3, 1, ec3, e3)] 1"

subsection \<open>Wellformedness and admissibility of the epoch-1 chain\<close>

lemma wfh_triple: "wellformed_src_history [(ec1, e1), (ec2, e2), (ec3, e3)]"
proof -
  have can: "history_can_append [(ec1, e1), (ec2, e2)] (ec3, e3)"
    by (simp add: history_can_append_def ec_defs)
  have "wellformed_src_history ([(ec1, e1), (ec2, e2)] @ [(ec3, e3)])"
    by (rule wellformed_src_history_append_one[OF wfh_pair can])
  then show ?thesis by simp
qed

lemma wf_d_run: "wellformed_exec_state (dwe_core d_run_w)"
  by (simp add: d_run_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_pair)

lemma wf_d_src3: "wellformed_exec_state (dwe_core d_src3_w)"
  by (simp add: d_src3_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_pair
                wfh_triple)

lemma wf_d_enq3: "wellformed_exec_state (dwe_core d_enq3_w)"
  by (simp add: d_enq3_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_pair
                wfh_triple)

lemma g_d_run_src3:
  "exec_label_preserves_history_wf (dwe_core d_run_w) (DoSource ec3 e3)"
  by (simp add: d_run_w_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_d_src3_enq3:
  "exec_label_preserves_history_wf (dwe_core d_src3_w)
     (EnqueueDownstream ec3 e3)"
  by (simp add: d_src3_w_def mkT_def mkC_def
                exec_label_preserves_history_wf_def history_can_append_def
                ec_defs)

lemma g_d_enq3_down3:
  "exec_label_preserves_history_wf (dwe_core d_enq3_w) (DoDownstream ec3 e3)"
  by (simp add: d_enq3_w_def mkT_def mkC_def
                exec_label_preserves_history_wf_def history_can_append_def
                ec_defs)

subsection \<open>The resume and the epoch-1 steps\<close>

lemma res_d: "dwe_resume t_safe_w d_run_w"
  by (simp add: dwe_resume_def t_safe_w_def d_run_w_def mkT_def mkC_def
                eval_nat_numeral)

lemma ws_d1: "dwe_step d_run_w (DoSource ec3 e3) d_src3_w"
proof -
  have c: "dw_exec_step (dwe_core d_run_w) (DoSource ec3 e3) (dwe_core d_src3_w)"
    by (rule do_sourceI) (simp_all add: d_run_w_def d_src3_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c])
       (simp_all add: d_run_w_def d_src3_w_def mkT_def)
qed

lemma ws_d2: "dwe_step d_src3_w (EnqueueDownstream ec3 e3) d_enq3_w"
proof -
  have c: "dw_exec_step (dwe_core d_src3_w) (EnqueueDownstream ec3 e3)
             (dwe_core d_enq3_w)"
    by (rule enqueue_downstreamI)
       (simp_all add: d_src3_w_def d_enq3_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c])
       (simp_all add: d_src3_w_def d_enq3_w_def mkT_def)
qed

lemma ws_d3: "dwe_step d_enq3_w (DoDownstream ec3 e3) d_pub3_w"
proof -
  have c: "dw_exec_step (dwe_core d_enq3_w) (DoDownstream ec3 e3)
             (dwe_core d_pub3_w)"
    by (rule do_downstreamI)
       (simp_all add: d_enq3_w_def d_pub3_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_publish_emitI[OF c])
       (simp add: d_enq3_w_def d_pub3_w_def mkT_def mkC_def eval_nat_numeral)
qed

subsection \<open>The disciplined segments\<close>

lemma dv_sg1: "disciplined_trace W0 [DWE_Label (DoSource ec1 e1)] W1"
  by (rule disciplined_nonpub_singleI[OF ws1 wf_W0 g_W0_src1]) simp

lemma dv_sg2: "disciplined_trace W1 [DWE_Label (EnqueueDownstream ec1 e1)] W2"
  by (rule disciplined_nonpub_singleI[OF ws2 wf_W1 g_W1_enq1]) simp

lemma dv_sg3: "disciplined_trace W2 [DWE_Label (DoDownstream ec1 e1)] W3"
proof (rule disciplined_publish_singleI[OF ws3 wf_W2 g_W2_down1])
  show "(ec1, e1) \<in> set (exec_src_hist (dwe_core W2))"
    by (simp add: W2_def mkT_def mkC_def)
  show "(ec1, e1) \<notin> e_payload ` set (dwe_emitted W2)"
    by (simp add: W2_def mkT_def)
qed

lemma dv_sg4: "disciplined_trace W3 [DWE_Label (DoSource ec2 e2)] W4"
  by (rule disciplined_nonpub_singleI[OF ws4 wf_W3 g_W3_src2]) simp

lemma dv_sg5: "disciplined_trace W4 [DWE_Label (EnqueueDownstream ec2 e2)] W5"
  by (rule disciplined_nonpub_singleI[OF ws5 wf_W4 g_W4_enq2]) simp

lemma dv_sg6: "disciplined_trace W5 [DWE_Label (Crash ec2)] t_mid_w"
  by (rule disciplined_nonpub_singleI[OF ws6 wf_W5 g_W5_crash]) simp

lemma dv_suffix_distinct:
  "distinct (drop 1 (replay_down_hist (exec_src_hist (dwe_core t_mid_w))
                       (exec_scope (dwe_core t_mid_w)) ec2))"
  by (simp add: t_mid_w_def mkT_def mkC_def replay_down_hist_def
                e1_def e2_def ec_defs eval_nat_numeral)

lemma dv_suffix_fresh:
  "set (drop 1 (replay_down_hist (exec_src_hist (dwe_core t_mid_w))
                  (exec_scope (dwe_core t_mid_w)) ec2))
     \<inter> e_payload ` set (dwe_emitted t_mid_w) = {}"
  by (simp add: t_mid_w_def mkT_def mkC_def replay_down_hist_def
                e1_def e2_def ec_defs eval_nat_numeral)

lemma dv_sg7: "disciplined_trace t_mid_w [DWE_Reconcile 1 ec2] t_safe_w"
  by (rule disciplined_reconcile_singleI
      [OF rec_safe dv_suffix_distinct dv_suffix_fresh])

lemma dv_sg8: "disciplined_trace t_safe_w [DWE_Resume] d_run_w"
  by (rule disciplined_resume_singleI[OF res_d])

lemma dv_sg9: "disciplined_trace d_run_w [DWE_Label (DoSource ec3 e3)] d_src3_w"
  by (rule disciplined_nonpub_singleI[OF ws_d1 wf_d_run g_d_run_src3]) simp

lemma dv_sg10:
  "disciplined_trace d_src3_w [DWE_Label (EnqueueDownstream ec3 e3)] d_enq3_w"
  by (rule disciplined_nonpub_singleI[OF ws_d2 wf_d_src3 g_d_src3_enq3]) simp

lemma dv_sg11:
  "disciplined_trace d_enq3_w [DWE_Label (DoDownstream ec3 e3)] d_pub3_w"
proof (rule disciplined_publish_singleI[OF ws_d3 wf_d_enq3 g_d_enq3_down3])
  show "(ec3, e3) \<in> set (exec_src_hist (dwe_core d_enq3_w))"
    by (simp add: d_enq3_w_def mkT_def mkC_def)
  show "(ec3, e3) \<notin> e_payload ` set (dwe_emitted d_enq3_w)"
    by (simp add: d_enq3_w_def mkT_def e1_def e2_def e3_def ec_defs)
qed

lemma dv_trace_raw:
  "disciplined_trace W0
     (map DWE_Label witness_labels
      @ [DWE_Reconcile 1 ec2, DWE_Resume,
         DWE_Label (DoSource ec3 e3), DWE_Label (EnqueueDownstream ec3 e3),
         DWE_Label (DoDownstream ec3 e3)])
     d_pub3_w"
  using disciplined_trace_append[OF dv_sg1
          disciplined_trace_append[OF dv_sg2
            disciplined_trace_append[OF dv_sg3
              disciplined_trace_append[OF dv_sg4
                disciplined_trace_append[OF dv_sg5
                  disciplined_trace_append[OF dv_sg6
                    disciplined_trace_append[OF dv_sg7
                      disciplined_trace_append[OF dv_sg8
                        disciplined_trace_append[OF dv_sg9
                          disciplined_trace_append[OF dv_sg10 dv_sg11]]]]]]]]]]
  by (simp add: witness_labels_def)

lemma dv_trace_init:
  "disciplined_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
     (map DWE_Label witness_labels
      @ [DWE_Reconcile 1 ec2, DWE_Resume,
         DWE_Label (DoSource ec3 e3), DWE_Label (EnqueueDownstream ec3 e3),
         DWE_Label (DoDownstream ec3 e3)])
     d_pub3_w"
  using dv_trace_raw unfolding W0_init .

subsection \<open>Verdicts on the final epoch-1 state\<close>

lemma d_pub3_emitting: "genuinely_emitting d_pub3_w"
  by (simp add: genuinely_emitting_def d_pub3_w_def mkT_def)

lemma d_pub3_emitted:
  "dwe_emitted d_pub3_w = [(1, 0, ec1, e1), (2, 0, ec2, e2), (3, 1, ec3, e3)]"
  by (simp add: d_pub3_w_def mkT_def)

lemma d_pub3_epoch: "dwe_epoch d_pub3_w = 1"
  by (simp add: d_pub3_w_def mkT_def)

lemma d_pub3_running: "exec_status (dwe_core d_pub3_w) = Running"
  by (simp add: d_pub3_w_def mkT_def mkC_def)

lemma d_pub3_ep0: "\<exists>x \<in> set (dwe_emitted d_pub3_w). e_epoch x = 0"
  by (simp add: d_pub3_w_def mkT_def)

lemma d_pub3_ep1: "\<exists>x \<in> set (dwe_emitted d_pub3_w). e_epoch x = 1"
  by (simp add: d_pub3_w_def mkT_def)

lemma d_pub3_safe: "\<not> effect_unsafe d_pub3_w"
  by (simp add: effect_unsafe_def premature_def duplicate_def justified_at_def
                d_pub3_w_def mkT_def mkC_def e1_def e2_def e3_def ec_defs
                eval_nat_numeral)

lemma reach_d_pub3: "dwe_reachable d_pub3_w"
  by (rule disciplined_runs_are_reachable[OF dv_trace_init])

text \<open>
  HEADLINE (non-vacuity, cycle-exercising).  The discipline is inhabited by
  a GENUINELY EMITTING run that includes a crash, a genuinely re-driving
  checkpointed reconcile (whose suffix is fresh and distinct, and which
  heals every scoped mismatch at the frontier --- @{thm [source]
  t_safe_heal}, stated at the post-reconcile state: the later epoch-1
  publish of \<open>e3\<close> lies beyond both the scope and the @{const ec2}
  frontier), a RESUME into epoch 1, and a further fresh disciplined publish
  IN epoch 1 --- ending Running, reachable, with a three-entry ledger
  spanning epochs 0 and 1, and effect-safe.  The safe half of the two-tier
  slogan is not vacuous ON THE CYCLE.
\<close>

theorem discipline_nonvacuous:
  "disciplined_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
     (map DWE_Label witness_labels
      @ [DWE_Reconcile 1 ec2, DWE_Resume,
         DWE_Label (DoSource ec3 e3), DWE_Label (EnqueueDownstream ec3 e3),
         DWE_Label (DoDownstream ec3 e3)])
     d_pub3_w
 \<and> genuinely_emitting d_pub3_w
 \<and> dwe_emitted d_pub3_w = [(1, 0, ec1, e1), (2, 0, ec2, e2), (3, 1, ec3, e3)]
 \<and> dwe_epoch d_pub3_w = 1
 \<and> exec_status (dwe_core d_pub3_w) = Running
 \<and> (\<exists>x \<in> set (dwe_emitted d_pub3_w). e_epoch x = 0)
 \<and> (\<exists>x \<in> set (dwe_emitted d_pub3_w). e_epoch x = 1)
 \<and> \<not> effect_unsafe d_pub3_w
 \<and> dwe_reachable d_pub3_w
 \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t_safe_w) ec2) ec2 k)"
  by (intro conjI dv_trace_init d_pub3_emitting d_pub3_emitted d_pub3_epoch
        d_pub3_running d_pub3_ep0 d_pub3_ep1 d_pub3_safe reach_d_pub3
        t_safe_heal)


section \<open>Per-guard tightness: each discipline premise is load-bearing\<close>

text \<open>(a) Publish fire-time justification: the banked premature chain
  (publish with NO source commit at all) satisfies publish FRESHNESS but
  not justification, and is unsafe.\<close>

lemma jb_trace_raw:
  "dwe_temporal_trace W0
     [DWE_Label (EnqueueDownstream ec1 e1), DWE_Label (DoDownstream ec1 e1)]
     t_bad_w"
proof -
  have a2: "dwe_temporal_trace b1_w [DWE_Label (DoDownstream ec1 e1)] t_bad_w"
    by (rule dwe_temporal_trace.dwe_label_step
        [OF wf_b1 g_b1_down1 wsb2 dwe_temporal_trace.dwe_refl])
  show ?thesis
    by (rule dwe_temporal_trace.dwe_label_step[OF wf_W0 g_W0_enq1 wsb1 a2])
qed

lemma jb_trace_init:
  "dwe_temporal_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
     (map DWE_Label [EnqueueDownstream ec1 e1, DoDownstream ec1 e1]) t_bad_w"
  using jb_trace_raw unfolding W0_init by simp

lemma b1_fresh: "(ec1, e1) \<notin> e_payload ` set (dwe_emitted b1_w)"
  by (simp add: b1_w_def mkT_def)

lemma b1_no_source: "(ec1, e1) \<notin> set (exec_src_hist (dwe_core b1_w))"
  by (simp add: b1_w_def mkT_def mkC_def)

lemma unsafe_t_bad: "effect_unsafe t_bad_w"
  using t_bad_premature by (simp add: effect_unsafe_def)

theorem publish_justification_guard_load_bearing:
  "dwe_temporal_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
     (map DWE_Label [EnqueueDownstream ec1 e1, DoDownstream ec1 e1]) t_bad_w
 \<and> dwe_step b1_w (DoDownstream ec1 e1) t_bad_w
 \<and> (ec1, e1) \<notin> e_payload ` set (dwe_emitted b1_w)
 \<and> (ec1, e1) \<notin> set (exec_src_hist (dwe_core b1_w))
 \<and> premature t_bad_w
 \<and> effect_unsafe t_bad_w"
  by (intro conjI jb_trace_init wsb2 b1_fresh b1_no_source t_bad_premature
        unsafe_t_bad)

text \<open>(b) Publish freshness: the Running-time publish RE-FIRE.  From the
  banked W3 (one committed, enqueued, delivered write), re-enqueue and
  re-deliver the same \<open>(ec1, e1)\<close>.  Both machine guards are the NON-STRICT
  @{const history_can_append} (equal coordinates pass \<open>\<le>\<close>), so the machine
  admits the re-fire while Running --- no crash, no reconcile, and (the
  cyclic-specific record) NO RESUME.  Every publish is fire-time justified,
  the final ledger is a payload duplicate: the pinned 2-premise discipline
  is refuted on the cyclic machine exactly as on the terminal one, and
  publish freshness is the missing third premise.\<close>

definition rf4_w :: "(nat, nat) dwe_state" where
  "rf4_w = mkT (mkC [(ec1, e1)] [(ec1, e1)] [(ec1, e1), (ec1, e1)]
                  {(ec1, e1)} Running)
               [(1, 0, ec1, e1)] 0"

definition rf5_w :: "(nat, nat) dwe_state" where
  "rf5_w = mkT (mkC [(ec1, e1)] [(ec1, e1), (ec1, e1)] [(ec1, e1), (ec1, e1)]
                  {} Running)
               [(1, 0, ec1, e1), (1, 0, ec1, e1)] 0"

definition refire_labels :: "(nat, nat) dw_exec_label list" where
  "refire_labels =
     [DoSource ec1 e1, EnqueueDownstream ec1 e1, DoDownstream ec1 e1,
      EnqueueDownstream ec1 e1, DoDownstream ec1 e1]"

lemma wfh_e1_pair_eq: "wellformed_src_history [(ec1, e1), (ec1, e1)]"
  by (rule wf_hist_pair) (simp_all add: ec_defs)

lemma wf_rf4: "wellformed_exec_state (dwe_core rf4_w)"
  by (simp add: rf4_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e1
                wfh_e1_pair_eq)

lemma g_W3_enq1_refire:
  "exec_label_preserves_history_wf (dwe_core W3) (EnqueueDownstream ec1 e1)"
  by (simp add: W3_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_rf4_down1_refire:
  "exec_label_preserves_history_wf (dwe_core rf4_w) (DoDownstream ec1 e1)"
  by (simp add: rf4_w_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma ws_rf1: "dwe_step W3 (EnqueueDownstream ec1 e1) rf4_w"
proof -
  have c: "dw_exec_step (dwe_core W3) (EnqueueDownstream ec1 e1) (dwe_core rf4_w)"
    by (rule enqueue_downstreamI) (simp_all add: W3_def rf4_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: W3_def rf4_w_def mkT_def)
qed

lemma ws_rf2: "dwe_step rf4_w (DoDownstream ec1 e1) rf5_w"
proof -
  have c: "dw_exec_step (dwe_core rf4_w) (DoDownstream ec1 e1) (dwe_core rf5_w)"
    by (rule do_downstreamI) (simp_all add: rf4_w_def rf5_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_publish_emitI[OF c])
       (simp add: rf4_w_def rf5_w_def mkT_def mkC_def eval_nat_numeral)
qed

lemma rf_sg4: "disciplined_trace W3 [DWE_Label (EnqueueDownstream ec1 e1)] rf4_w"
  by (rule disciplined_nonpub_singleI[OF ws_rf1 wf_W3 g_W3_enq1_refire]) simp

text \<open>The re-fire publish is fire-time JUSTIFIED (semi-disciplined) but NOT
  fresh --- it is exactly the step the honest discipline forbids.\<close>

lemma rf_sg5_semi:
  "semi_disciplined_trace rf4_w [DWE_Label (DoDownstream ec1 e1)] rf5_w"
proof (rule semi_publish_singleI[OF ws_rf2 wf_rf4 g_rf4_down1_refire])
  show "(ec1, e1) \<in> set (exec_src_hist (dwe_core rf4_w))"
    by (simp add: rf4_w_def mkT_def mkC_def)
qed

lemma semi_trace_raw_rf5:
  "semi_disciplined_trace W0 (map DWE_Label refire_labels) rf5_w"
  using semi_disciplined_trace_append
          [OF discipline_refines_two_premise_form[OF dv_sg1]
              semi_disciplined_trace_append
                [OF discipline_refines_two_premise_form[OF dv_sg2]
                    semi_disciplined_trace_append
                      [OF discipline_refines_two_premise_form[OF dv_sg3]
                          semi_disciplined_trace_append
                            [OF discipline_refines_two_premise_form[OF rf_sg4]
                                rf_sg5_semi]]]]
  by (simp add: refire_labels_def)

lemma semi_trace_init_rf5:
  "semi_disciplined_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
     (map DWE_Label refire_labels) rf5_w"
  using semi_trace_raw_rf5 unfolding W0_init .

subsection \<open>Verdicts on the refire run\<close>

lemma no_reconcile_in_refire:
  "\<forall>m f. DWE_Reconcile m f \<notin> set (map DWE_Label refire_labels)"
  by (simp add: refire_labels_def)

lemma no_resume_in_refire:
  "DWE_Resume \<notin> set (map DWE_Label refire_labels)"
  by (simp add: refire_labels_def)

lemma first_publish_fire_justified:
  "justified_at (exec_src_hist (dwe_core W2))
     (length (exec_src_hist (dwe_core W2)), dwe_epoch W2, ec1, e1)"
  by (simp add: justified_at_def W2_def mkT_def mkC_def)

lemma second_publish_fire_justified:
  "justified_at (exec_src_hist (dwe_core rf4_w))
     (length (exec_src_hist (dwe_core rf4_w)), dwe_epoch rf4_w, ec1, e1)"
  by (simp add: justified_at_def rf4_w_def mkT_def mkC_def)

lemma refire_violates_publish_freshness:
  "(ec1, e1) \<in> e_payload ` set (dwe_emitted rf4_w)"
  by (simp add: rf4_w_def mkT_def)

lemma justified_rf5:
  "\<forall>x \<in> set (dwe_emitted rf5_w). justified_at (exec_src_hist (dwe_core rf5_w)) x"
  by (simp add: justified_at_def rf5_w_def mkT_def mkC_def eval_nat_numeral)

lemma not_premature_rf5: "\<not> premature rf5_w"
  using justified_rf5 by (auto simp: premature_def)

lemma duplicate_rf5: "duplicate rf5_w"
  by (simp add: duplicate_def rf5_w_def mkT_def)

lemma unsafe_rf5: "effect_unsafe rf5_w"
  by (simp add: effect_unsafe_def duplicate_rf5)

lemma count_rf5: "count_list (map e_payload (dwe_emitted rf5_w)) (ec1, e1) = 2"
  by (simp add: rf5_w_def mkT_def e1_def ec_defs eval_nat_numeral)

text \<open>
  HEADLINE (freshness control / 2-premise tightness record, cyclic).  The
  pinned 2-premise discipline admits a run with NO reconcile and NO resume
  whose every publish is justified at fire time (and which is not premature
  at the end either), yet whose final ledger carries the same payload
  TWICE.  So "no premature publishes + reconcile suffixes fresh and
  distinct" does NOT imply effect safety on the cyclic machine either:
  publish freshness is a genuinely missing third premise --- stated against
  the machine's own ledger.
\<close>

theorem publish_refire_defeats_two_premise_discipline:
  "semi_disciplined_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
     (map DWE_Label refire_labels) rf5_w
 \<and> (\<forall>m f. DWE_Reconcile m f \<notin> set (map DWE_Label refire_labels))
 \<and> DWE_Resume \<notin> set (map DWE_Label refire_labels)
 \<and> justified_at (exec_src_hist (dwe_core W2))
     (length (exec_src_hist (dwe_core W2)), dwe_epoch W2, ec1, e1)
 \<and> justified_at (exec_src_hist (dwe_core rf4_w))
     (length (exec_src_hist (dwe_core rf4_w)), dwe_epoch rf4_w, ec1, e1)
 \<and> (ec1, e1) \<in> e_payload ` set (dwe_emitted rf4_w)
 \<and> (\<forall>x \<in> set (dwe_emitted rf5_w).
      justified_at (exec_src_hist (dwe_core rf5_w)) x)
 \<and> \<not> premature rf5_w
 \<and> count_list (map e_payload (dwe_emitted rf5_w)) (ec1, e1) = 2
 \<and> duplicate rf5_w
 \<and> effect_unsafe rf5_w"
  by (intro conjI semi_trace_init_rf5 no_reconcile_in_refire
        no_resume_in_refire first_publish_fire_justified
        second_publish_fire_justified refire_violates_publish_freshness
        justified_rf5 not_premature_rf5 count_rf5 duplicate_rf5 unsafe_rf5)

corollary two_premise_discipline_refuted:
  "\<not> (\<forall>acts tf.
        semi_disciplined_trace
          (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2) acts tf
        \<longrightarrow> \<not> effect_unsafe tf)"
  using publish_refire_defeats_two_premise_discipline by blast

text \<open>(c) Reconcile suffix freshness: the banked stale-cursor reconcile
  m = 0 from @{const t_mid_w} has a DISTINCT suffix that is NOT
  ledger-fresh, and is unsafe.\<close>

lemma tfin_suffix_distinct_c:
  "distinct (drop 0 (replay_down_hist (exec_src_hist (dwe_core t_mid_w))
                       (exec_scope (dwe_core t_mid_w)) ec2))"
  by (simp add: t_mid_w_def mkT_def mkC_def replay_down_hist_def
                e1_def e2_def ec_defs eval_nat_numeral)

lemma tfin_suffix_not_fresh_c:
  "(ec1, e1) \<in> set (drop 0 (replay_down_hist
                       (exec_src_hist (dwe_core t_mid_w))
                       (exec_scope (dwe_core t_mid_w)) ec2))
                \<inter> e_payload ` set (dwe_emitted t_mid_w)"
  by (simp add: t_mid_w_def mkT_def mkC_def replay_down_hist_def
                e1_def e2_def ec_defs eval_nat_numeral)

theorem reconcile_freshness_guard_load_bearing:
  "emitting_reconcile 0 t_mid_w ec2 t_fin_w
 \<and> distinct (drop 0 (replay_down_hist (exec_src_hist (dwe_core t_mid_w))
                       (exec_scope (dwe_core t_mid_w)) ec2))
 \<and> (ec1, e1) \<in> set (drop 0 (replay_down_hist
                       (exec_src_hist (dwe_core t_mid_w))
                       (exec_scope (dwe_core t_mid_w)) ec2))
                \<inter> e_payload ` set (dwe_emitted t_mid_w)
 \<and> effect_unsafe t_fin_w"
  by (intro conjI rec_fin tfin_suffix_distinct_c tfin_suffix_not_fresh_c
        t_fin_unsafe)

text \<open>(d) Reconcile suffix INTERNAL distinctness: an equal-coordinate
  re-commit (admitted by the non-strict WF-H1 guard, which the cyclic
  machine SHARES with the terminal one --- @{const history_can_append} is
  the same locked-core constant) makes the committed source history repeat
  a payload; the m = 0 reconcile then re-drives a LEDGER-FRESH but
  internally duplicated suffix --- unsafe.  This is the in-model shadow of
  the prose modelling premise strictly\_ascending\_source.\<close>

definition dd2_w :: "(nat, nat) dwe_state" where
  "dd2_w = mkT (mkC [(ec1, e1), (ec1, e1)] [] [] {} Running) [] 0"

definition dd3_w :: "(nat, nat) dwe_state" where
  "dd3_w = mkT (mkC [(ec1, e1), (ec1, e1)] [] [] {} (Crashed ec1)) [] 0"

definition dd4_w :: "(nat, nat) dwe_state" where
  "dd4_w = mkT (mkC [(ec1, e1), (ec1, e1)] [(ec1, e1), (ec1, e1)] [] {}
                  Recovered)
               [(2, 0, ec1, e1), (2, 0, ec1, e1)] 0"

text \<open>The equal-coordinate re-commit is ADMISSIBLE: WF-H1 is non-strict.\<close>

lemma g_W1_src1_again:
  "exec_label_preserves_history_wf (dwe_core W1) (DoSource ec1 e1)"
  by (simp add: W1_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_dd2_crash: "exec_label_preserves_history_wf (dwe_core dd2_w) (Crash ec1)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma wf_dd2: "wellformed_exec_state (dwe_core dd2_w)"
  by (simp add: dd2_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e1_pair_eq)

lemma ws_dd1: "dwe_step W1 (DoSource ec1 e1) dd2_w"
proof -
  have c: "dw_exec_step (dwe_core W1) (DoSource ec1 e1) (dwe_core dd2_w)"
    by (rule do_sourceI) (simp_all add: W1_def dd2_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: W1_def dd2_w_def mkT_def)
qed

lemma ws_dd2: "dwe_step dd2_w (Crash ec1) dd3_w"
proof -
  have c: "dw_exec_step (dwe_core dd2_w) (Crash ec1) (dwe_core dd3_w)"
    by (rule crashI) (simp_all add: dd2_w_def dd3_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: dd2_w_def dd3_w_def mkT_def)
qed

lemma rec_dd: "emitting_reconcile 0 dd3_w ec1 dd4_w"
  by (simp add: emitting_reconcile_def dd3_w_def dd4_w_def mkT_def mkC_def
                replay_down_hist_def e1_def ec_defs eval_nat_numeral)

lemma dd_trace_raw:
  "dwe_temporal_trace W0
     [DWE_Label (DoSource ec1 e1), DWE_Label (DoSource ec1 e1),
      DWE_Label (Crash ec1), DWE_Reconcile 0 ec1] dd4_w"
proof -
  have a4: "dwe_temporal_trace dd3_w [DWE_Reconcile 0 ec1] dd4_w"
    by (rule dwe_temporal_trace.dwe_reconcile_step
        [OF rec_dd dwe_temporal_trace.dwe_refl])
  have a3: "dwe_temporal_trace dd2_w
              [DWE_Label (Crash ec1), DWE_Reconcile 0 ec1] dd4_w"
    by (rule dwe_temporal_trace.dwe_label_step[OF wf_dd2 g_dd2_crash ws_dd2 a4])
  have a2: "dwe_temporal_trace W1
              [DWE_Label (DoSource ec1 e1), DWE_Label (Crash ec1),
               DWE_Reconcile 0 ec1] dd4_w"
    by (rule dwe_temporal_trace.dwe_label_step
        [OF wf_W1 g_W1_src1_again ws_dd1 a3])
  show ?thesis
    by (rule dwe_temporal_trace.dwe_label_step[OF wf_W0 g_W0_src1 ws1 a2])
qed

lemma dd_trace_init:
  "dwe_temporal_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
     [DWE_Label (DoSource ec1 e1), DWE_Label (DoSource ec1 e1),
      DWE_Label (Crash ec1), DWE_Reconcile 0 ec1] dd4_w"
  using dd_trace_raw unfolding W0_init .

lemma dd_suffix_fresh:
  "set (drop 0 (replay_down_hist (exec_src_hist (dwe_core dd3_w))
                  (exec_scope (dwe_core dd3_w)) ec1))
     \<inter> e_payload ` set (dwe_emitted dd3_w) = {}"
  by (simp add: dd3_w_def mkT_def)

lemma dd_suffix_not_distinct:
  "\<not> distinct (drop 0 (replay_down_hist (exec_src_hist (dwe_core dd3_w))
                         (exec_scope (dwe_core dd3_w)) ec1))"
  by (simp add: dd3_w_def mkT_def mkC_def replay_down_hist_def e1_def ec_defs)

lemma duplicate_dd4: "duplicate dd4_w"
  by (simp add: duplicate_def dd4_w_def mkT_def)

lemma unsafe_dd4: "effect_unsafe dd4_w"
  by (simp add: effect_unsafe_def duplicate_dd4)

theorem reconcile_distinctness_guard_load_bearing:
  "dwe_temporal_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
     [DWE_Label (DoSource ec1 e1), DWE_Label (DoSource ec1 e1),
      DWE_Label (Crash ec1), DWE_Reconcile 0 ec1] dd4_w
 \<and> set (drop 0 (replay_down_hist (exec_src_hist (dwe_core dd3_w))
                  (exec_scope (dwe_core dd3_w)) ec1))
     \<inter> e_payload ` set (dwe_emitted dd3_w) = {}
 \<and> \<not> distinct (drop 0 (replay_down_hist (exec_src_hist (dwe_core dd3_w))
                         (exec_scope (dwe_core dd3_w)) ec1))
 \<and> duplicate dd4_w
 \<and> effect_unsafe dd4_w"
  by (intro conjI dd_trace_init dd_suffix_fresh dd_suffix_not_distinct
        duplicate_dd4 unsafe_dd4)


section \<open>Statement audit (the S4c seam check)\<close>

text \<open>
  Checkable against this file:

  (1) STATEMENT.  The premises of @{thm [source] general_positive_discipline}
      are the guards of \<open>disciplined_trace\<close>: fire-time justification
      (payload \<open>\<in>\<close> committed source history NOW), publish freshness
      (payload \<open>\<notin>\<close> current ledger payloads), and reconcile-suffix
      distinctness + ledger-freshness.  The Resume case carries NO guard.
      No premise mentions @{const dwe_epoch}, @{const e_epoch}, an
      advertised frontier, or the \<open>adv\<close> function of Dual\_Write\_Relay;
      the only frontier-typed data are the reconcile rule's own parameters
      \<open>m\<close> and \<open>f\<close>, whose bound \<open>f \<le> exec_finish\<close> lives inside the machine
      rule @{const emitting_reconcile}, not among the discipline premises.

  (2) PROOF.  The inductive invariant is \<open>\<not> effect_unsafe\<close> itself; the
      Resume case is discharged by @{thm [source]
      resume_preserves_effect_safe} (ledger and source history preserved
      VERBATIM), the other three cases exactly as in the terminal probe.
      No epoch case-split occurs anywhere in this theory.

  VERDICT: the cyclic machine forces NO additional premise on T2.8; the
  honest 3-guard form transfers verbatim, with Resume guard-free.
\<close>

end
