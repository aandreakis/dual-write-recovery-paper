(*  Title:       Dual_Write_Effect_Segments.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE SEGMENT FACTORIZATION INTERFACE of the cyclic effect machine:
    what the machine-checked simulation seam
    (resume_breaks_core_simulation) leaves intact, packaged.  A cyclic
    trace factors into RESUME-FREE SEGMENTS separated by Resume
    transitions; within a segment every label step projects to a landed
    dw_exec_step and every reconcile to the landed
    relay_bounded_replay_reconcile, so the landed tier-1 corpus re-lands
    per segment with its landed proofs cited verbatim.  This theory is a
    RESTATEMENT CARRIER, never an upgrade: it adds decomposition surgery
    and carrier lemmas over the banked per-rule projections, plus the one
    genuinely new proof obligation (core wellformedness is a reachability
    invariant, via replay_down_hist_wellformed).

    Produced by the S4d proof-wave P1 prover per the committed design
    (paper/dual_write/phase3/s4d_design/, gate-canonicalized); the scratch
    original's in-source ML oracle gates are STRIPPED here: oracle-freedom
    is certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Segments
  imports Dual_Write_Effect_Cyclic
begin

section \<open>Segment vocabulary\<close>

text \<open>
  A SEGMENT is a Resume-free action word: the maximal fragment of a
  cyclic trace along which the epoch is constant and the core evolves by
  landed transitions only.  @{text resume_free} is an abbreviation so the
  spelled-out membership form and the named form are literally
  interchangeable in every statement downstream.
\<close>

abbreviation resume_free :: "('k, 'v) dwe_action list \<Rightarrow> bool" where
  "resume_free xs \<equiv> DWE_Resume \<notin> set xs"

definition dwe_label_only :: "('k, 'v) dwe_action list \<Rightarrow> bool" where
  "dwe_label_only xs \<longleftrightarrow> (\<forall>x \<in> set xs. \<exists>a. x = DWE_Label a)"

fun dwe_label_of :: "('k, 'v) dwe_action \<Rightarrow> ('k, 'v) dw_exec_label" where
  "dwe_label_of (DWE_Label a) = a"
| "dwe_label_of (DWE_Reconcile m f) = Observe f"  \<comment> \<open>junk, dead under \<open>dwe_label_only\<close>\<close>
| "dwe_label_of DWE_Resume = Recover"             \<comment> \<open>junk, dead under \<open>dwe_label_only\<close>\<close>

fun core_action_of
  :: "('k, 'v) dwe_action \<Rightarrow> ('k, 'v) recovery_temporal_action" where
  "core_action_of (DWE_Label a) = Recovery_Label a"
| "core_action_of (DWE_Reconcile m f) = Recovery_Reconcile f"
| "core_action_of DWE_Resume = Recovery_Reconcile c0" \<comment> \<open>junk, dead under \<open>resume_free\<close>\<close>

text \<open>
  DISCLOSED LOSSINESS: @{const core_action_of} deliberately reuses the
  LANDED action datatype @{type recovery_temporal_action} so that segment
  words are type-compatible with landed grammar words --- and it ERASES
  the reconcile's consumer cursor @{term m}.  The core projection is
  intentionally lossy; effect-level content (the ledger, the cursor, the
  epoch) must never be routed through it.  The junk clauses of both total
  functions are dead under the side predicates every consuming statement
  carries (@{text dwe_label_only} / @{text resume_free}); they exist only
  to keep the functions total in the house style.
\<close>

section \<open>The WF-H1 toolbox and replay wellformedness (front-loaded)\<close>

text \<open>
  The foundation's only genuinely new mathematics: a scoped,
  frontier-bounded filter of a wellformed source history is wellformed.
  The three conjuncts of @{const wellformed_src_history} (layer 0) are
  handled separately: WF-H1 (adjacent non-decreasing coordinates) via the
  @{const sorted_wrt} bridge and the library filter lemma; WF-H2 (no
  base-coordinate event) via set inclusion; WF-H3 (position-order
  totality) is free for EVERY list --- @{text src_le} totality plus
  antisymmetry plus @{typ nat} linearity --- proved once below and used
  to discharge the third conjunct everywhere, never re-derived from the
  input history's own H3.
\<close>

lemma source_pos_order_total:
  assumes "i < length H" and "j < length H" and "i \<noteq> j"
  shows "source_pos_order H i j \<or> source_pos_order H j i"
proof (cases "hist_coord (H ! i) = hist_coord (H ! j)")
  case True
  then show ?thesis
    unfolding source_pos_order_def using nat_le_linear by auto
next
  case False
  from src_le_total[of "hist_coord (H ! i)" "hist_coord (H ! j)"]
  have "src_lt (hist_coord (H ! i)) (hist_coord (H ! j))
      \<or> src_lt (hist_coord (H ! j)) (hist_coord (H ! i))"
    using False unfolding src_lt_def by auto
  then show ?thesis
    unfolding source_pos_order_def by blast
qed

lemma wellformed_src_history_coord_mono:
  assumes wf: "wellformed_src_history H"
      and ij: "i \<le> j" and j: "j < length H"
  shows "src_le (hist_coord (H ! i)) (hist_coord (H ! j))"
proof -
  have adj: "\<And>n. Suc n < length H
               \<Longrightarrow> src_le (hist_coord (H ! n)) (hist_coord (H ! Suc n))"
    using wf by (simp add: wellformed_src_history_def)
  show ?thesis using ij j
  proof (induction j)
    case 0
    then show ?case by (simp add: src_le_refl)
  next
    case (Suc j)
    show ?case
    proof (cases "i = Suc j")
      case True
      then show ?thesis by (simp add: src_le_refl)
    next
      case False
      with Suc.prems have le: "i \<le> j" and lt: "j < length H" by simp_all
      have "src_le (hist_coord (H ! i)) (hist_coord (H ! j))"
        by (rule Suc.IH[OF le lt])
      moreover have "src_le (hist_coord (H ! j)) (hist_coord (H ! Suc j))"
        using adj Suc.prems(2) by simp
      ultimately show ?thesis by (rule src_le_trans)
    qed
  qed
qed

lemma wellformed_src_history_last_max:
  assumes wf: "wellformed_src_history H"
      and x: "x \<in> set H"
  shows "src_le (hist_coord x) (hist_coord (last H))"
proof -
  from x obtain i where i: "i < length H" and xi: "x = H ! i"
    by (auto simp: in_set_conv_nth)
  have ne: "H \<noteq> []" using x by auto
  have last_eq: "last H = H ! (length H - 1)"
    using ne by (simp add: last_conv_nth)
  have "src_le (hist_coord (H ! i)) (hist_coord (H ! (length H - 1)))"
    using i by (intro wellformed_src_history_coord_mono[OF wf]) auto
  then show ?thesis by (simp add: xi last_eq)
qed

lemma wellformed_src_history_filter:
  assumes wf: "wellformed_src_history H"
  shows "wellformed_src_history (filter P H)"
proof -
  let ?R = "\<lambda>p q. src_le (hist_coord p) (hist_coord q)"
  have transp_R: "transp ?R"
    by (intro transpI) (rule src_le_trans)
  have sorted_H: "sorted_wrt ?R H"
    unfolding sorted_wrt_iff_nth_Suc_transp[OF transp_R]
    using wf by (simp add: wellformed_src_history_def)
  have sorted_F: "sorted_wrt ?R (filter P H)"
    by (rule sorted_wrt_filter[OF sorted_H])
  have h1: "\<forall>i. Suc i < length (filter P H)
              \<longrightarrow> src_le (hist_coord (filter P H ! i))
                         (hist_coord (filter P H ! Suc i))"
    using sorted_F unfolding sorted_wrt_iff_nth_Suc_transp[OF transp_R] .
  have h2_all: "\<forall>i. i < length H \<longrightarrow> hist_coord (H ! i) \<noteq> c0"
    using wf unfolding wellformed_src_history_def by blast
  have h2: "\<forall>i. i < length (filter P H)
              \<longrightarrow> hist_coord (filter P H ! i) \<noteq> c0"
  proof (intro allI impI)
    fix i
    assume i: "i < length (filter P H)"
    have "filter P H ! i \<in> set (filter P H)"
      by (rule nth_mem[OF i])
    then have "filter P H ! i \<in> set H" by auto
    then obtain j where j: "j < length H" and eq: "filter P H ! i = H ! j"
      by (auto simp: in_set_conv_nth)
    show "hist_coord (filter P H ! i) \<noteq> c0"
      unfolding eq using h2_all j by blast
  qed
  have h3: "\<forall>i j. i < length (filter P H) \<and> j < length (filter P H) \<and> i \<noteq> j
              \<longrightarrow> source_pos_order (filter P H) i j
                \<or> source_pos_order (filter P H) j i"
    using source_pos_order_total by blast
  from h1 h2 h3 show ?thesis
    unfolding wellformed_src_history_def by blast
qed

lemma replay_down_hist_wellformed:
  assumes "wellformed_src_history H"
  shows "wellformed_src_history (replay_down_hist H K f)"
  unfolding replay_down_hist_def
  by (rule wellformed_src_history_filter[OF assms])

section \<open>Trace-global bookkeeping\<close>

lemma dwe_trace_emitted_ext:
  assumes "dwe_temporal_trace t xs t'"
  shows "\<exists>es. dwe_emitted t' = dwe_emitted t @ es"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  show ?case by (intro exI[of _ "[]"]) simp
next
  case (dwe_label_step t a t' as t'')
  obtain es1 where 1: "dwe_emitted t' = dwe_emitted t @ es1"
    using dwe_step_emitted_ext[OF dwe_label_step.hyps(3)] by blast
  obtain es2 where 2: "dwe_emitted t'' = dwe_emitted t' @ es2"
    using dwe_label_step.IH by blast
  show ?case by (intro exI[of _ "es1 @ es2"]) (simp add: 1 2)
next
  case (dwe_reconcile_step m t f t' as t'')
  obtain es1 where 1: "dwe_emitted t' = dwe_emitted t @ es1"
    using emitting_reconcile_emitted_ext[OF dwe_reconcile_step.hyps(1)] by blast
  obtain es2 where 2: "dwe_emitted t'' = dwe_emitted t' @ es2"
    using dwe_reconcile_step.IH by blast
  show ?case by (intro exI[of _ "es1 @ es2"]) (simp add: 1 2)
next
  case (dwe_resume_step t t' as t'')
  obtain es2 where 2: "dwe_emitted t'' = dwe_emitted t' @ es2"
    using dwe_resume_step.IH by blast
  show ?case
    by (intro exI[of _ es2])
       (simp add: 2 dwe_resume_emitted_same[OF dwe_resume_step.hyps(1)])
qed

lemma dwe_trace_src_ext:
  assumes "dwe_temporal_trace t xs t'"
  shows "\<exists>ext. exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t) @ ext"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  show ?case by (intro exI[of _ "[]"]) simp
next
  case (dwe_label_step t a t' as t'')
  obtain e1 where 1: "exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t) @ e1"
    using dw_exec_step_src_ext[OF dwe_step_core[OF dwe_label_step.hyps(3)]] by blast
  obtain e2 where 2: "exec_src_hist (dwe_core t'') = exec_src_hist (dwe_core t') @ e2"
    using dwe_label_step.IH by blast
  show ?case by (intro exI[of _ "e1 @ e2"]) (simp add: 1 2)
next
  case (dwe_reconcile_step m t f t' as t'')
  obtain e2 where 2: "exec_src_hist (dwe_core t'') = exec_src_hist (dwe_core t') @ e2"
    using dwe_reconcile_step.IH by blast
  show ?case
    by (intro exI[of _ e2])
       (simp add: 2 emitting_reconcile_src_same[OF dwe_reconcile_step.hyps(1)])
next
  case (dwe_resume_step t t' as t'')
  obtain e2 where 2: "exec_src_hist (dwe_core t'') = exec_src_hist (dwe_core t') @ e2"
    using dwe_resume_step.IH by blast
  show ?case
    by (intro exI[of _ e2])
       (simp add: 2 dwe_resume_src_same[OF dwe_resume_step.hyps(1)])
qed

lemma dwe_trace_core_frame:
  assumes "dwe_temporal_trace t xs t'"
  shows "exec_base (dwe_core t') = exec_base (dwe_core t)
       \<and> exec_scope (dwe_core t') = exec_scope (dwe_core t)
       \<and> exec_finish (dwe_core t') = exec_finish (dwe_core t)"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  show ?case by simp
next
  case (dwe_label_step t a t' as t'')
  have core: "dw_exec_step (dwe_core t) a (dwe_core t')"
    by (rule dwe_step_core[OF dwe_label_step.hyps(3)])
  show ?case
    using dwe_label_step.IH dw_exec_step_base[OF core]
          dw_exec_step_scope[OF core] dw_exec_step_finish[OF core]
    by simp
next
  case (dwe_reconcile_step m t f t' as t'')
  have "exec_base (dwe_core t') = exec_base (dwe_core t)
      \<and> exec_scope (dwe_core t') = exec_scope (dwe_core t)
      \<and> exec_finish (dwe_core t') = exec_finish (dwe_core t)"
    using dwe_reconcile_step.hyps(1) by (simp add: emitting_reconcile_def)
  with dwe_reconcile_step.IH show ?case by simp
next
  case (dwe_resume_step t t' as t'')
  have "dwe_core t' = (dwe_core t)\<lparr>exec_status := Running\<rparr>"
    by (rule dwe_resume_core[OF dwe_resume_step.hyps(1)])
  with dwe_resume_step.IH show ?case by simp
qed

text \<open>
  The sharp epoch equation: the epoch counter of a trace end is the start
  epoch plus the number of Resume actions in the word.  The two banked
  primitives @{thm [source] dwe_trace_epoch_mono} and
  @{thm [source] dwe_trace_no_resume_epoch_const} are its one-line
  consequences and remain the citation surface for their consumers.
\<close>

lemma dwe_trace_epoch_count:
  assumes "dwe_temporal_trace t xs t'"
  shows "dwe_epoch t' = dwe_epoch t + count_list xs DWE_Resume"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  show ?case by simp
next
  case (dwe_label_step t a t' as t'')
  then show ?case
    using dwe_step_epoch_const[OF dwe_label_step.hyps(3)] by simp
next
  case (dwe_reconcile_step m t f t' as t'')
  then show ?case
    using emitting_reconcile_epoch_const[OF dwe_reconcile_step.hyps(1)] by simp
next
  case (dwe_resume_step t t' as t'')
  then show ?case
    using dwe_resume_epoch_Suc[OF dwe_resume_step.hyps(1)] by simp
qed

lemma dwe_init_trace_epoch0_iff_resume_free:
  assumes "dwe_temporal_trace (dwe_init b K fin) xs t"
  shows "dwe_epoch t = 0 \<longleftrightarrow> resume_free xs"
proof -
  have "dwe_epoch t = count_list xs DWE_Resume"
    using dwe_trace_epoch_count[OF assms] by (simp add: dwe_init_def)
  then show ?thesis by (simp add: count_list_0_iff)
qed

lemma dwe_trace_reachable_ext:
  assumes "dwe_reachable t"
      and "dwe_temporal_trace t xs t'"
  shows "dwe_reachable t'"
proof -
  obtain ys where ys: "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2) ys t"
    using assms(1) unfolding dwe_reachable_def by blast
  show ?thesis
    unfolding dwe_reachable_def
    using dwe_temporal_trace_append[OF ys assms(2)] by blast
qed

section \<open>Head eliminations and append decomposition\<close>

lemma dwe_trace_label_headE:
  assumes "dwe_temporal_trace t (DWE_Label a # xs) t'"
  obtains u where "wellformed_exec_state (dwe_core t)"
              and "exec_label_preserves_history_wf (dwe_core t) a"
              and "dwe_step t a u"
              and "dwe_temporal_trace u xs t'"
  using assms by (cases rule: dwe_temporal_trace.cases) auto

lemma dwe_trace_reconcile_headE:
  assumes "dwe_temporal_trace t (DWE_Reconcile m f # xs) t'"
  obtains u where "emitting_reconcile m t f u"
              and "dwe_temporal_trace u xs t'"
  using assms by (cases rule: dwe_temporal_trace.cases) auto

lemma dwe_trace_resume_headE:
  assumes "dwe_temporal_trace t (DWE_Resume # xs) t'"
  obtains u where "dwe_resume t u"
              and "dwe_temporal_trace u xs t'"
  using assms by (cases rule: dwe_temporal_trace.cases) auto

lemma dwe_temporal_trace_appendD:
  assumes "dwe_temporal_trace t (xs @ ys) t'"
  shows "\<exists>u. dwe_temporal_trace t xs u \<and> dwe_temporal_trace u ys t'"
  using assms
proof (induction xs arbitrary: t)
  case Nil
  then show ?case by (auto intro: dwe_temporal_trace.dwe_refl)
next
  case (Cons x xs)
  show ?case
  proof (cases x)
    case (DWE_Label a)
    with Cons.prems have "dwe_temporal_trace t (DWE_Label a # (xs @ ys)) t'"
      by simp
    then obtain u1 where g1: "wellformed_exec_state (dwe_core t)"
        and g2: "exec_label_preserves_history_wf (dwe_core t) a"
        and st: "dwe_step t a u1"
        and tr: "dwe_temporal_trace u1 (xs @ ys) t'"
      by (rule dwe_trace_label_headE)
    from Cons.IH[OF tr] obtain u where
      "dwe_temporal_trace u1 xs u" and "dwe_temporal_trace u ys t'" by blast
    then show ?thesis
      using DWE_Label g1 g2 st
      by (auto intro: dwe_temporal_trace.dwe_label_step)
  next
    case (DWE_Reconcile m f)
    with Cons.prems have "dwe_temporal_trace t (DWE_Reconcile m f # (xs @ ys)) t'"
      by simp
    then obtain u1 where st: "emitting_reconcile m t f u1"
        and tr: "dwe_temporal_trace u1 (xs @ ys) t'"
      by (rule dwe_trace_reconcile_headE)
    from Cons.IH[OF tr] obtain u where
      "dwe_temporal_trace u1 xs u" and "dwe_temporal_trace u ys t'" by blast
    then show ?thesis
      using DWE_Reconcile st
      by (auto intro: dwe_temporal_trace.dwe_reconcile_step)
  next
    case DWE_Resume
    with Cons.prems have "dwe_temporal_trace t (DWE_Resume # (xs @ ys)) t'"
      by simp
    then obtain u1 where st: "dwe_resume t u1"
        and tr: "dwe_temporal_trace u1 (xs @ ys) t'"
      by (rule dwe_trace_resume_headE)
    from Cons.IH[OF tr] obtain u where
      "dwe_temporal_trace u1 xs u" and "dwe_temporal_trace u ys t'" by blast
    then show ?thesis
      using DWE_Resume st
      by (auto intro: dwe_temporal_trace.dwe_resume_step)
  qed
qed

section \<open>The decomposition theorems: segment extraction\<close>

lemma dwe_trace_resume_split_first:
  assumes "dwe_temporal_trace t xs t'"
      and "DWE_Resume \<in> set xs"
  shows "\<exists>pre post u u'.
           xs = pre @ DWE_Resume # post
         \<and> resume_free pre
         \<and> dwe_temporal_trace t pre u
         \<and> dwe_resume u u'
         \<and> dwe_temporal_trace u' post t'"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  then show ?case by simp
next
  case (dwe_label_step t a t' as t'')
  then have mem: "DWE_Resume \<in> set as" by simp
  from dwe_label_step.IH[OF mem] obtain pre post u u' where
    eq: "as = pre @ DWE_Resume # post" and rf: "resume_free pre"
    and tr1: "dwe_temporal_trace t' pre u" and res: "dwe_resume u u'"
    and tr2: "dwe_temporal_trace u' post t''" by blast
  have tr1': "dwe_temporal_trace t (DWE_Label a # pre) u"
    by (rule dwe_temporal_trace.dwe_label_step[OF dwe_label_step.hyps(1)
          dwe_label_step.hyps(2) dwe_label_step.hyps(3) tr1])
  have "DWE_Label a # as = (DWE_Label a # pre) @ DWE_Resume # post"
    using eq by simp
  moreover have "resume_free (DWE_Label a # pre)" using rf by simp
  ultimately show ?case using tr1' res tr2 by blast
next
  case (dwe_reconcile_step m t f t' as t'')
  then have mem: "DWE_Resume \<in> set as" by simp
  from dwe_reconcile_step.IH[OF mem] obtain pre post u u' where
    eq: "as = pre @ DWE_Resume # post" and rf: "resume_free pre"
    and tr1: "dwe_temporal_trace t' pre u" and res: "dwe_resume u u'"
    and tr2: "dwe_temporal_trace u' post t''" by blast
  have tr1': "dwe_temporal_trace t (DWE_Reconcile m f # pre) u"
    by (rule dwe_temporal_trace.dwe_reconcile_step[OF dwe_reconcile_step.hyps(1) tr1])
  have "DWE_Reconcile m f # as = (DWE_Reconcile m f # pre) @ DWE_Resume # post"
    using eq by simp
  moreover have "resume_free (DWE_Reconcile m f # pre)" using rf by simp
  ultimately show ?case using tr1' res tr2 by blast
next
  case (dwe_resume_step t t' as t'')
  show ?case
  proof (intro exI conjI)
    show "DWE_Resume # as = [] @ DWE_Resume # as" by simp
    show "resume_free []" by simp
    show "dwe_temporal_trace t [] t" by (rule dwe_temporal_trace.dwe_refl)
    show "dwe_resume t t'" by (rule dwe_resume_step.hyps(1))
    show "dwe_temporal_trace t' as t''" by (rule dwe_resume_step.hyps(2))
  qed
qed

lemma dwe_trace_resume_split_last:
  assumes "dwe_temporal_trace t xs t'"
      and "DWE_Resume \<in> set xs"
  shows "\<exists>pre post u u'.
           xs = pre @ DWE_Resume # post
         \<and> resume_free post
         \<and> dwe_temporal_trace t pre u
         \<and> dwe_resume u u'
         \<and> dwe_temporal_trace u' post t'"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  then show ?case by simp
next
  case (dwe_label_step t a t' as t'')
  then have mem: "DWE_Resume \<in> set as" by simp
  from dwe_label_step.IH[OF mem] obtain pre post u u' where
    eq: "as = pre @ DWE_Resume # post" and rf: "resume_free post"
    and tr1: "dwe_temporal_trace t' pre u" and res: "dwe_resume u u'"
    and tr2: "dwe_temporal_trace u' post t''" by blast
  have tr1': "dwe_temporal_trace t (DWE_Label a # pre) u"
    by (rule dwe_temporal_trace.dwe_label_step[OF dwe_label_step.hyps(1)
          dwe_label_step.hyps(2) dwe_label_step.hyps(3) tr1])
  have "DWE_Label a # as = (DWE_Label a # pre) @ DWE_Resume # post"
    using eq by simp
  then show ?case using rf tr1' res tr2 by blast
next
  case (dwe_reconcile_step m t f t' as t'')
  then have mem: "DWE_Resume \<in> set as" by simp
  from dwe_reconcile_step.IH[OF mem] obtain pre post u u' where
    eq: "as = pre @ DWE_Resume # post" and rf: "resume_free post"
    and tr1: "dwe_temporal_trace t' pre u" and res: "dwe_resume u u'"
    and tr2: "dwe_temporal_trace u' post t''" by blast
  have tr1': "dwe_temporal_trace t (DWE_Reconcile m f # pre) u"
    by (rule dwe_temporal_trace.dwe_reconcile_step[OF dwe_reconcile_step.hyps(1) tr1])
  have "DWE_Reconcile m f # as = (DWE_Reconcile m f # pre) @ DWE_Resume # post"
    using eq by simp
  then show ?case using rf tr1' res tr2 by blast
next
  case (dwe_resume_step t t' as t'')
  show ?case
  proof (cases "DWE_Resume \<in> set as")
    case True
    from dwe_resume_step.IH[OF True] obtain pre post u u' where
      eq: "as = pre @ DWE_Resume # post" and rf: "resume_free post"
      and tr1: "dwe_temporal_trace t' pre u" and res: "dwe_resume u u'"
      and tr2: "dwe_temporal_trace u' post t''" by blast
    have tr1': "dwe_temporal_trace t (DWE_Resume # pre) u"
      by (rule dwe_temporal_trace.dwe_resume_step[OF dwe_resume_step.hyps(1) tr1])
    have "DWE_Resume # as = (DWE_Resume # pre) @ DWE_Resume # post"
      using eq by simp
    then show ?thesis using rf tr1' res tr2 by blast
  next
    case False
    show ?thesis
    proof (intro exI conjI)
      show "DWE_Resume # as = [] @ DWE_Resume # as" by simp
      show "resume_free as" using False .
      show "dwe_temporal_trace t [] t" by (rule dwe_temporal_trace.dwe_refl)
      show "dwe_resume t t'" by (rule dwe_resume_step.hyps(1))
      show "dwe_temporal_trace t' as t''" by (rule dwe_resume_step.hyps(2))
    qed
  qed
qed

subsection \<open>The whole-trace segmented-run predicate\<close>

inductive dwe_segmented_run
  :: "('k, 'v) dwe_state \<Rightarrow> ('k, 'v) dwe_action list list \<Rightarrow> ('k, 'v) dwe_state \<Rightarrow> bool"
where
  seg_last:
    "\<lbrakk>dwe_temporal_trace t seg t'; resume_free seg\<rbrakk> \<Longrightarrow>
     dwe_segmented_run t [seg] t'"
| seg_cons:
    "\<lbrakk>dwe_temporal_trace t seg u; resume_free seg;
      dwe_resume u u'; dwe_segmented_run u' segs t'\<rbrakk> \<Longrightarrow>
     dwe_segmented_run t (seg # segs) t'"

lemma dwe_segmented_run_nonempty:
  assumes "dwe_segmented_run t segs t'"
  shows "segs \<noteq> []"
  using assms by (cases rule: dwe_segmented_run.cases) auto

lemma dwe_segmented_run_consE:
  assumes "dwe_segmented_run t (seg # rest) t'"
  obtains (seg_only) "rest = []" "dwe_temporal_trace t seg t'" "resume_free seg"
        | (seg_more) u u' where "dwe_temporal_trace t seg u" "resume_free seg"
                                "dwe_resume u u'" "dwe_segmented_run u' rest t'"
  using assms by (cases rule: dwe_segmented_run.cases) auto

lemma dwe_segmented_run_label_prepend:
  assumes wf: "wellformed_exec_state (dwe_core t)"
      and pres: "exec_label_preserves_history_wf (dwe_core t) a"
      and step: "dwe_step t a t'"
      and run: "dwe_segmented_run t' (seg # rest) t''"
  shows "dwe_segmented_run t ((DWE_Label a # seg) # rest) t''"
proof (rule dwe_segmented_run_consE[OF run])
  assume r0: "rest = []" and tr: "dwe_temporal_trace t' seg t''"
     and rf: "resume_free seg"
  have "dwe_temporal_trace t (DWE_Label a # seg) t''"
    by (rule dwe_temporal_trace.dwe_label_step[OF wf pres step tr])
  moreover have "resume_free (DWE_Label a # seg)" using rf by simp
  ultimately show ?thesis
    using r0 by (auto intro: dwe_segmented_run.seg_last)
next
  fix u u'
  assume tr: "dwe_temporal_trace t' seg u" and rf: "resume_free seg"
     and res: "dwe_resume u u'" and run': "dwe_segmented_run u' rest t''"
  have "dwe_temporal_trace t (DWE_Label a # seg) u"
    by (rule dwe_temporal_trace.dwe_label_step[OF wf pres step tr])
  moreover have "resume_free (DWE_Label a # seg)" using rf by simp
  ultimately show ?thesis
    using res run' by (auto intro: dwe_segmented_run.seg_cons)
qed

lemma dwe_segmented_run_reconcile_prepend:
  assumes step: "emitting_reconcile m t f t'"
      and run: "dwe_segmented_run t' (seg # rest) t''"
  shows "dwe_segmented_run t ((DWE_Reconcile m f # seg) # rest) t''"
proof (rule dwe_segmented_run_consE[OF run])
  assume r0: "rest = []" and tr: "dwe_temporal_trace t' seg t''"
     and rf: "resume_free seg"
  have "dwe_temporal_trace t (DWE_Reconcile m f # seg) t''"
    by (rule dwe_temporal_trace.dwe_reconcile_step[OF step tr])
  moreover have "resume_free (DWE_Reconcile m f # seg)" using rf by simp
  ultimately show ?thesis
    using r0 by (auto intro: dwe_segmented_run.seg_last)
next
  fix u u'
  assume tr: "dwe_temporal_trace t' seg u" and rf: "resume_free seg"
     and res: "dwe_resume u u'" and run': "dwe_segmented_run u' rest t''"
  have "dwe_temporal_trace t (DWE_Reconcile m f # seg) u"
    by (rule dwe_temporal_trace.dwe_reconcile_step[OF step tr])
  moreover have "resume_free (DWE_Reconcile m f # seg)" using rf by simp
  ultimately show ?thesis
    using res run' by (auto intro: dwe_segmented_run.seg_cons)
qed

theorem dwe_trace_imp_segmented_run:
  assumes "dwe_temporal_trace t xs t'"
  shows "\<exists>segs. dwe_segmented_run t segs t'
              \<and> length segs = Suc (count_list xs DWE_Resume)"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  have "dwe_segmented_run t [[]] t"
    by (intro dwe_segmented_run.seg_last dwe_temporal_trace.dwe_refl) simp
  then show ?case by auto
next
  case (dwe_label_step t a t' as t'')
  from dwe_label_step.IH obtain segs where
    run: "dwe_segmented_run t' segs t''"
    and len: "length segs = Suc (count_list as DWE_Resume)" by blast
  obtain seg rest where segs_eq: "segs = seg # rest"
    using dwe_segmented_run_nonempty[OF run] by (cases segs) auto
  have "dwe_segmented_run t ((DWE_Label a # seg) # rest) t''"
    by (rule dwe_segmented_run_label_prepend[OF dwe_label_step.hyps(1)
          dwe_label_step.hyps(2) dwe_label_step.hyps(3) run[unfolded segs_eq]])
  moreover have "length ((DWE_Label a # seg) # rest)
                   = Suc (count_list (DWE_Label a # as) DWE_Resume)"
    using len segs_eq by simp
  ultimately show ?case by blast
next
  case (dwe_reconcile_step m t f t' as t'')
  from dwe_reconcile_step.IH obtain segs where
    run: "dwe_segmented_run t' segs t''"
    and len: "length segs = Suc (count_list as DWE_Resume)" by blast
  obtain seg rest where segs_eq: "segs = seg # rest"
    using dwe_segmented_run_nonempty[OF run] by (cases segs) auto
  have "dwe_segmented_run t ((DWE_Reconcile m f # seg) # rest) t''"
    by (rule dwe_segmented_run_reconcile_prepend[OF dwe_reconcile_step.hyps(1)
          run[unfolded segs_eq]])
  moreover have "length ((DWE_Reconcile m f # seg) # rest)
                   = Suc (count_list (DWE_Reconcile m f # as) DWE_Resume)"
    using len segs_eq by simp
  ultimately show ?case by blast
next
  case (dwe_resume_step t t' as t'')
  from dwe_resume_step.IH obtain segs where
    run: "dwe_segmented_run t' segs t''"
    and len: "length segs = Suc (count_list as DWE_Resume)" by blast
  have "dwe_segmented_run t ([] # segs) t''"
    by (rule dwe_segmented_run.seg_cons[OF dwe_temporal_trace.dwe_refl _
          dwe_resume_step.hyps(1) run]) simp
  moreover have "length ([] # segs)
                   = Suc (count_list (DWE_Resume # as) DWE_Resume)"
    using len by simp
  ultimately show ?case by blast
qed

theorem dwe_segmented_run_imp_trace:
  assumes "dwe_segmented_run t segs t'"
  shows "\<exists>xs. dwe_temporal_trace t xs t'
             \<and> count_list xs DWE_Resume = length segs - 1"
  using assms
proof (induction rule: dwe_segmented_run.induct)
  case (seg_last t seg t')
  then show ?case by (intro exI[of _ seg]) simp
next
  case (seg_cons t seg u u' segs t')
  from seg_cons.IH obtain xs where
    tr: "dwe_temporal_trace u' xs t'"
    and cnt: "count_list xs DWE_Resume = length segs - 1" by blast
  have tail: "dwe_temporal_trace u (DWE_Resume # xs) t'"
    by (rule dwe_temporal_trace.dwe_resume_step[OF seg_cons.hyps(3) tr])
  have whole: "dwe_temporal_trace t (seg @ DWE_Resume # xs) t'"
    by (rule dwe_temporal_trace_append[OF seg_cons.hyps(1) tail])
  have nonempty: "segs \<noteq> []"
    by (rule dwe_segmented_run_nonempty[OF seg_cons.hyps(4)])
  have "count_list (seg @ DWE_Resume # xs) DWE_Resume
          = length (seg # segs) - 1"
    using seg_cons.hyps(2) cnt nonempty by simp
  with whole show ?case by blast
qed

text \<open>
  DELIBERATE OMISSION (disclosed): the exact word-reconstruction equation
  (the trace word as a concat of the segments interleaved with
  @{const DWE_Resume}) is not proved --- no consumer uses the word
  equation, only the run predicate; it is a self-contained additive
  extension if a later site needs it.
\<close>

section \<open>Segment starts\<close>

text \<open>
  A segment start is either THE pinned initial state or the target of a
  Resume from a reachable state.  Monomorphic on purpose: this is one of
  the few places the pinned @{const dwe_reachable} is the honest scope
  (the framework's trace lemmas above stay polymorphic in both the type
  parameters and the start state).
\<close>

definition dwe_segment_start :: "(nat, nat) dwe_state \<Rightarrow> bool" where
  "dwe_segment_start s \<longleftrightarrow>
     s = dwe_init Map.empty {0, 1} ec2
   \<or> (\<exists>p. dwe_reachable p \<and> dwe_resume p s)"

theorem dwe_reachable_current_segment:
  assumes "dwe_reachable t"
  shows "\<exists>s seg. dwe_segment_start s \<and> dwe_reachable s
               \<and> dwe_temporal_trace s seg t \<and> resume_free seg
               \<and> dwe_epoch s = dwe_epoch t"
proof -
  obtain xs where xs: "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2) xs t"
    using assms unfolding dwe_reachable_def by blast
  show ?thesis
  proof (cases "DWE_Resume \<in> set xs")
    case True
    from dwe_trace_resume_split_last[OF xs True] obtain pre post u u' where
      eq: "xs = pre @ DWE_Resume # post" and rf: "resume_free post"
      and tr1: "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2) pre u"
      and res: "dwe_resume u u'"
      and tr2: "dwe_temporal_trace u' post t" by blast
    have reach_u: "dwe_reachable u"
      unfolding dwe_reachable_def using tr1 by blast
    have start: "dwe_segment_start u'"
      unfolding dwe_segment_start_def using reach_u res by blast
    have reach_u': "dwe_reachable u'"
      by (rule dwe_reachable_resume_ext[OF reach_u res])
    have ep: "dwe_epoch u' = dwe_epoch t"
      using dwe_trace_no_resume_epoch_const[OF tr2 rf] by simp
    from start reach_u' tr2 rf ep show ?thesis by blast
  next
    case False
    then have nomem: "DWE_Resume \<notin> set xs" by simp
    have start: "dwe_segment_start (dwe_init Map.empty {0, 1} ec2)"
      unfolding dwe_segment_start_def by blast
    have cnt: "count_list xs DWE_Resume = 0"
      using nomem by (rule count_notin)
    have ep0: "dwe_epoch t = dwe_epoch (dwe_init Map.empty {0, 1} ec2)"
      using dwe_trace_epoch_count[OF xs] cnt by (simp add: dwe_init_def)
    from start dwe_reachable_init xs nomem ep0 ep0[symmetric]
    show ?thesis by blast
  qed
qed

lemma dwe_init_core_running:
  "exec_status (dwe_core (dwe_init b K fin)) = Running"
  by (simp add: dwe_init_def initial_exec_state_def)

lemma post_resume_core_running:
  assumes "dwe_resume u u'"
  shows "exec_status (dwe_core u') = Running"
  unfolding dwe_resume_core[OF assms] by simp

lemma dwe_segment_start_running:
  assumes "dwe_segment_start s"
  shows "exec_status (dwe_core s) = Running"
  using assms unfolding dwe_segment_start_def
  using dwe_init_core_running post_resume_core_running by blast

section \<open>Core wellformedness is a reachability invariant\<close>

text \<open>
  Needed because segment starts (post-reconcile, post-Resume states) must
  hand a wellformed core to re-founded inductions and to the admissible
  projection below.  The reconcile case is where
  @{thm [source] replay_down_hist_wellformed} earns its keep; Resume is
  status-only; label steps carry their own guards inside the trace rule.
\<close>

lemma emitting_reconcile_core_wellformed:
  assumes rec: "emitting_reconcile m t f t'"
      and wf: "wellformed_exec_state (dwe_core t)"
  shows "wellformed_exec_state (dwe_core t')"
proof -
  have core_eq: "dwe_core t' =
    (dwe_core t)\<lparr>exec_down_hist :=
        replay_down_hist (exec_src_hist (dwe_core t)) (exec_scope (dwe_core t)) f,
      exec_pending := {}, exec_status := Recovered\<rparr>"
    using rec by (simp add: emitting_reconcile_def)
  have wf_src: "wellformed_src_history (exec_src_hist (dwe_core t))"
    using wf by (simp add: ws_defs)
  show ?thesis
    using wf replay_down_hist_wellformed[OF wf_src]
    unfolding core_eq ws_defs by simp
qed

lemma dwe_resume_core_wellformed:
  assumes "dwe_resume t t'"
      and "wellformed_exec_state (dwe_core t)"
  shows "wellformed_exec_state (dwe_core t')"
  using assms(2) unfolding dwe_resume_core[OF assms(1)] ws_defs by simp

lemma dwe_trace_core_wellformed:
  assumes "dwe_temporal_trace t xs t'"
      and "wellformed_exec_state (dwe_core t)"
  shows "wellformed_exec_state (dwe_core t')"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  then show ?case by simp
next
  case (dwe_label_step t a t' as t'')
  have "wellformed_exec_state (dwe_core t')"
    by (rule dw_exec_step_wellformed_exec_state[OF
          dwe_step_core[OF dwe_label_step.hyps(3)]
          dwe_label_step.hyps(1) dwe_label_step.hyps(2)])
  then show ?case by (rule dwe_label_step.IH)
next
  case (dwe_reconcile_step m t f t' as t'')
  have "wellformed_exec_state (dwe_core t')"
    by (rule emitting_reconcile_core_wellformed[OF dwe_reconcile_step.hyps(1)
          dwe_reconcile_step.prems])
  then show ?case by (rule dwe_reconcile_step.IH)
next
  case (dwe_resume_step t t' as t'')
  have "wellformed_exec_state (dwe_core t')"
    by (rule dwe_resume_core_wellformed[OF dwe_resume_step.hyps(1)
          dwe_resume_step.prems])
  then show ?case by (rule dwe_resume_step.IH)
qed

theorem dwe_reachable_core_wellformed:
  assumes "dwe_reachable t"
  shows "wellformed_exec_state (dwe_core t)"
proof -
  obtain xs where xs: "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2) xs t"
    using assms unfolding dwe_reachable_def by blast
  have "wellformed_exec_state (dwe_core (dwe_init Map.empty {0, 1} ec2))"
    by (simp add: dwe_init_def)
  from dwe_trace_core_wellformed[OF xs this] show ?thesis .
qed

corollary dwe_segment_start_core_wellformed:
  assumes "dwe_segment_start s" and "dwe_reachable s"
  shows "wellformed_exec_state (dwe_core s)"
  by (rule dwe_reachable_core_wellformed[OF assms(2)])

section \<open>The per-segment core-trace correspondence\<close>

text \<open>
  The landed core offers no star relation combining label steps with the
  RELAY reconcile: the landed grammar's reconcile constructor denotes the
  WHOLESALE @{const recovery_reconcile_step} (a different transformer,
  landed distinct: @{thm [source] anti_atomic_down_neq_src}).  So the
  segment target is a NEW core-side grammar, defined here, whose
  reconcile is exactly the landed relay re-drive and whose label guards
  mirror the cyclic machine's own trace rule.  It is a core-side notion
  living in the effect session, named to say what its reconcile is; it
  does not upgrade the landed grammar.
\<close>

inductive core_relay_temporal_trace
  :: "('k, 'v) dw_exec_state \<Rightarrow> ('k, 'v) recovery_temporal_action list
      \<Rightarrow> ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  crt_refl:
    "core_relay_temporal_trace s [] s"
| crt_label_step:
    "\<lbrakk>wellformed_exec_state s;
      exec_label_preserves_history_wf s a;
      dw_exec_step s a s';
      core_relay_temporal_trace s' as s''\<rbrakk> \<Longrightarrow>
     core_relay_temporal_trace s (Recovery_Label a # as) s''"
| crt_reconcile_step:
    "\<lbrakk>relay_bounded_replay_reconcile s f s';
      core_relay_temporal_trace s' as s''\<rbrakk> \<Longrightarrow>
     core_relay_temporal_trace s (Recovery_Reconcile f # as) s''"

theorem dwe_segment_core_trace:
  assumes "dwe_temporal_trace t xs t'"
      and "resume_free xs"
  shows "core_relay_temporal_trace (dwe_core t) (map core_action_of xs) (dwe_core t')"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  show ?case by (simp add: core_relay_temporal_trace.crt_refl)
next
  case (dwe_label_step t a t' as t'')
  have core: "dw_exec_step (dwe_core t) a (dwe_core t')"
    by (rule dwe_step_core[OF dwe_label_step.hyps(3)])
  have tail: "core_relay_temporal_trace (dwe_core t') (map core_action_of as) (dwe_core t'')"
    using dwe_label_step.IH dwe_label_step.prems by simp
  show ?case
    using core_relay_temporal_trace.crt_label_step[OF dwe_label_step.hyps(1)
            dwe_label_step.hyps(2) core tail]
    by simp
next
  case (dwe_reconcile_step m t f t' as t'')
  have core: "relay_bounded_replay_reconcile (dwe_core t) f (dwe_core t')"
    by (rule emitting_reconcile_core[OF dwe_reconcile_step.hyps(1)])
  have tail: "core_relay_temporal_trace (dwe_core t') (map core_action_of as) (dwe_core t'')"
    using dwe_reconcile_step.IH dwe_reconcile_step.prems by simp
  show ?case
    using core_relay_temporal_trace.crt_reconcile_step[OF core tail] by simp
next
  case (dwe_resume_step t t' as t'')
  then show ?case by simp
qed

subsection \<open>Label-only specializations\<close>

text \<open>
  The forms the landed tier-1 theorems actually consume: their wait /
  continuation hypotheses are stated over @{const dw_exec_trace} and
  @{const admissible_dw_exec_trace}.  GUARD-PLACEMENT SUBTLETY (the
  empty-segment caveat): the landed @{thm [source]
  admissible_dw_exec_trace.admissible_trace_refl} demands start
  wellformedness while the cyclic @{thm [source]
  dwe_temporal_trace.dwe_refl} has no guard --- so the admissible
  projection carries an explicit start-wellformedness hypothesis (for
  nonempty runs it is derivable from the first label step's own guard;
  the uniform hypothesis keeps one statement).  At reachable states it
  discharges via the invariant above.  This is a guard relocation, not a
  weakening.
\<close>

theorem dwe_label_run_core_trace:
  assumes "dwe_temporal_trace t xs t'"
      and "dwe_label_only xs"
  shows "dw_exec_trace (dwe_core t) (map dwe_label_of xs) (dwe_core t')"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  show ?case by (simp add: dw_exec_trace.trace_refl)
next
  case (dwe_label_step t a t' as t'')
  have core: "dw_exec_step (dwe_core t) a (dwe_core t')"
    by (rule dwe_step_core[OF dwe_label_step.hyps(3)])
  have tail: "dw_exec_trace (dwe_core t') (map dwe_label_of as) (dwe_core t'')"
    using dwe_label_step.IH dwe_label_step.prems
    by (simp add: dwe_label_only_def)
  show ?case
    using dw_exec_trace.trace_step[OF core tail] by simp
next
  case (dwe_reconcile_step m t f t' as t'')
  then show ?case by (simp add: dwe_label_only_def)
next
  case (dwe_resume_step t t' as t'')
  then show ?case by (simp add: dwe_label_only_def)
qed

theorem dwe_label_run_admissible_core_trace:
  assumes "dwe_temporal_trace t xs t'"
      and "dwe_label_only xs"
      and "wellformed_exec_state (dwe_core t)"
  shows "admissible_dw_exec_trace (dwe_core t) (map dwe_label_of xs) (dwe_core t')"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  then show ?case
    by (simp add: admissible_dw_exec_trace.admissible_trace_refl)
next
  case (dwe_label_step t a t' as t'')
  have core: "dw_exec_step (dwe_core t) a (dwe_core t')"
    by (rule dwe_step_core[OF dwe_label_step.hyps(3)])
  have wf': "wellformed_exec_state (dwe_core t')"
    by (rule dw_exec_step_wellformed_exec_state[OF core
          dwe_label_step.hyps(1) dwe_label_step.hyps(2)])
  have tail: "admissible_dw_exec_trace (dwe_core t') (map dwe_label_of as) (dwe_core t'')"
    using dwe_label_step.IH dwe_label_step.prems wf'
    by (simp add: dwe_label_only_def)
  show ?case
    using admissible_dw_exec_trace.admissible_trace_step[OF core
            dwe_label_step.hyps(1) dwe_label_step.hyps(2) tail]
    by simp
next
  case (dwe_reconcile_step m t f t' as t'')
  then show ?case by (simp add: dwe_label_only_def)
next
  case (dwe_resume_step t t' as t'')
  then show ?case by (simp add: dwe_label_only_def)
qed

corollary dwe_reachable_label_run_admissible:
  assumes "dwe_reachable t"
      and "dwe_temporal_trace t xs t'"
      and "dwe_label_only xs"
  shows "admissible_dw_exec_trace (dwe_core t) (map dwe_label_of xs) (dwe_core t')"
  by (rule dwe_label_run_admissible_core_trace[OF assms(2) assms(3)
        dwe_reachable_core_wellformed[OF assms(1)]])

section \<open>Epoch tagging of emissions: the ledger-side segment interface\<close>

text \<open>
  Both emitting rules stamp the CURRENT epoch, which is segment-constant;
  Resume raises the bound and emits nothing.  This is what makes
  "per-epoch" mean something on the ledger.  The proof skeleton mirrors
  the banked stamps-bounded invariant.  Non-vacuity of the cross-epoch
  reading is the banked amplification witness @{const f_amp_w} (ledger
  entries with epoch 0 AND epoch 1 coexist,
  @{thm [source] resume_cycle_amplification}).
\<close>

lemma dwe_step_new_epochs:
  assumes "dwe_step t a t'"
  shows "\<exists>es. dwe_emitted t' = dwe_emitted t @ es
            \<and> (\<forall>x \<in> set es. e_epoch x = dwe_epoch t)"
  using assms
proof (induction rule: dwe_step.induct)
  case (lift_nonpub t a c')
  show ?case by (intro exI[of _ "[]"]) simp
next
  case (publish_emit t c e c')
  show ?case
    by (intro exI[of _ "[(length (exec_src_hist (dwe_core t)), dwe_epoch t, c, e)]"])
       simp
qed

lemma emitting_reconcile_new_epochs:
  assumes "emitting_reconcile m t f t'"
  shows "\<exists>es. dwe_emitted t' = dwe_emitted t @ es
            \<and> (\<forall>x \<in> set es. e_epoch x = dwe_epoch t)"
proof -
  have em: "dwe_emitted t' = dwe_emitted t
              @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                               dwe_epoch t, c, e))
                  (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                             (exec_scope (dwe_core t)) f))"
    using assms by (simp add: emitting_reconcile_def)
  show ?thesis
    unfolding em by (intro exI conjI) (auto simp: e_epoch_def)
qed

lemma dwe_segment_emissions_current_epoch:
  assumes "dwe_temporal_trace t xs t'"
      and "resume_free xs"
  shows "\<exists>es. dwe_emitted t' = dwe_emitted t @ es
            \<and> (\<forall>x \<in> set es. e_epoch x = dwe_epoch t)"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  show ?case by (intro exI[of _ "[]"]) simp
next
  case (dwe_label_step t a t' as t'')
  obtain es1 where 1: "dwe_emitted t' = dwe_emitted t @ es1"
      and ep1: "\<forall>x \<in> set es1. e_epoch x = dwe_epoch t"
    using dwe_step_new_epochs[OF dwe_label_step.hyps(3)] by blast
  obtain es2 where 2: "dwe_emitted t'' = dwe_emitted t' @ es2"
      and ep2: "\<forall>x \<in> set es2. e_epoch x = dwe_epoch t'"
    using dwe_label_step.IH dwe_label_step.prems by auto
  have ep_eq: "dwe_epoch t' = dwe_epoch t"
    by (rule dwe_step_epoch_const[OF dwe_label_step.hyps(3)])
  show ?case
  proof (intro exI[of _ "es1 @ es2"] conjI)
    show "dwe_emitted t'' = dwe_emitted t @ (es1 @ es2)" by (simp add: 1 2)
    show "\<forall>x \<in> set (es1 @ es2). e_epoch x = dwe_epoch t"
      using ep1 ep2 ep_eq by auto
  qed
next
  case (dwe_reconcile_step m t f t' as t'')
  obtain es1 where 1: "dwe_emitted t' = dwe_emitted t @ es1"
      and ep1: "\<forall>x \<in> set es1. e_epoch x = dwe_epoch t"
    using emitting_reconcile_new_epochs[OF dwe_reconcile_step.hyps(1)] by blast
  obtain es2 where 2: "dwe_emitted t'' = dwe_emitted t' @ es2"
      and ep2: "\<forall>x \<in> set es2. e_epoch x = dwe_epoch t'"
    using dwe_reconcile_step.IH dwe_reconcile_step.prems by auto
  have ep_eq: "dwe_epoch t' = dwe_epoch t"
    by (rule emitting_reconcile_epoch_const[OF dwe_reconcile_step.hyps(1)])
  show ?case
  proof (intro exI[of _ "es1 @ es2"] conjI)
    show "dwe_emitted t'' = dwe_emitted t @ (es1 @ es2)" by (simp add: 1 2)
    show "\<forall>x \<in> set (es1 @ es2). e_epoch x = dwe_epoch t"
      using ep1 ep2 ep_eq by auto
  qed
next
  case (dwe_resume_step t t' as t'')
  then show ?case by simp
qed

definition epochs_bounded :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "epochs_bounded t \<longleftrightarrow> (\<forall>x \<in> set (dwe_emitted t). e_epoch x \<le> dwe_epoch t)"

lemma dwe_step_epochs_bounded:
  assumes step: "dwe_step t a t'"
      and eb: "epochs_bounded t"
  shows "epochs_bounded t'"
proof -
  obtain es where es: "dwe_emitted t' = dwe_emitted t @ es"
      and new: "\<forall>x \<in> set es. e_epoch x = dwe_epoch t"
    using dwe_step_new_epochs[OF step] by blast
  show ?thesis
    unfolding epochs_bounded_def es
    using eb new dwe_step_epoch_const[OF step]
    unfolding epochs_bounded_def by auto
qed

lemma emitting_reconcile_epochs_bounded:
  assumes rec: "emitting_reconcile m t f t'"
      and eb: "epochs_bounded t"
  shows "epochs_bounded t'"
proof -
  obtain es where es: "dwe_emitted t' = dwe_emitted t @ es"
      and new: "\<forall>x \<in> set es. e_epoch x = dwe_epoch t"
    using emitting_reconcile_new_epochs[OF rec] by blast
  show ?thesis
    unfolding epochs_bounded_def es
    using eb new emitting_reconcile_epoch_const[OF rec]
    unfolding epochs_bounded_def by auto
qed

lemma dwe_resume_epochs_bounded:
  assumes res: "dwe_resume t t'"
      and eb: "epochs_bounded t"
  shows "epochs_bounded t'"
  using eb
  unfolding epochs_bounded_def dwe_resume_emitted_same[OF res]
            dwe_resume_epoch_Suc[OF res]
  by (auto intro: le_SucI)

lemma dwe_trace_epochs_bounded:
  assumes "dwe_temporal_trace t xs t'"
      and "epochs_bounded t"
  shows "epochs_bounded t'"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  then show ?case by simp
next
  case (dwe_label_step t a t' as t'')
  then show ?case using dwe_step_epochs_bounded by blast
next
  case (dwe_reconcile_step m t f t' as t'')
  then show ?case using emitting_reconcile_epochs_bounded by blast
next
  case (dwe_resume_step t t' as t'')
  then show ?case using dwe_resume_epochs_bounded by blast
qed

lemma dwe_init_epochs_bounded: "epochs_bounded (dwe_init b K fin)"
  by (simp add: epochs_bounded_def dwe_init_def)

theorem dwe_reachable_epochs_bounded:
  assumes "dwe_reachable t"
  shows "epochs_bounded t"
proof -
  obtain xs where "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2) xs t"
    using assms unfolding dwe_reachable_def by blast
  from dwe_trace_epochs_bounded[OF this dwe_init_epochs_bounded]
  show ?thesis .
qed

section \<open>THE HONEST DATUM: segment starts are NOT init-like\<close>

text \<open>
  Witness chain (three fresh states extending the banked W-chain):
  commit event 1, crash, recover BY THE LIFTED @{const Recover} LABEL
  (a status-only recovery --- not a reconcile!), then Resume.  Epoch 1
  opens with the image STILL diverging: the downstream history is empty
  against a committed source event in scope.  Consequence for the
  program: an epoch-k segment start is an ARBITRARY carried state with
  Running status --- nothing more.  Converse families and invariant
  re-foundings must take the segment-start state as a parameter, never
  assume initial-state properties.  This is the framework's central
  honest handoff.

  Three distinct epoch-1-mismatch witnesses coexist across the wave, with
  distinct consumers: THIS chain's @{text r_run1_w} (a diverging segment
  start --- no reconcile ever ran); the converse theory's
  @{text stale_run1_w} (a stale heal: store-bad yet effect-clean); and
  the tightness theory's @{text f_mis_w} (in-segment mismatch recurrence
  via a WF-H1-legal equal-coordinate re-commit, genuinely emitting).
\<close>

definition r_crash_w :: "(nat, nat) dwe_state" where
  "r_crash_w = mkT (mkC [(ec1, e1)] [] [] {} (Crashed ec1)) [] 0"

definition r_rec_w :: "(nat, nat) dwe_state" where
  "r_rec_w = mkT (mkC [(ec1, e1)] [] [] {} Recovered) [] 0"

definition r_run1_w :: "(nat, nat) dwe_state" where
  "r_run1_w = mkT (mkC [(ec1, e1)] [] [] {} Running) [] 1"

lemmas r_state_defs = r_crash_w_def r_rec_w_def r_run1_w_def

lemma recoverI:
  assumes "exec_status s = Crashed c"
      and "s' = s\<lparr>exec_status := Recovered\<rparr>"
  shows "dw_exec_step s Recover s'"
  unfolding assms(2) by (rule dw_exec_step.recover[OF assms(1)])

lemma wf_r_crash: "wellformed_exec_state (dwe_core r_crash_w)"
  by (simp add: r_crash_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e1)

lemma wf_r_rec: "wellformed_exec_state (dwe_core r_rec_w)"
  by (simp add: r_rec_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e1)

lemma wf_r_run1: "wellformed_exec_state (dwe_core r_run1_w)"
  by (simp add: r_run1_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e1)

lemma g_W1_crash: "exec_label_preserves_history_wf (dwe_core W1) (Crash ec1)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma g_r_crash_recover: "exec_label_preserves_history_wf (dwe_core r_crash_w) Recover"
  by (simp add: exec_label_preserves_history_wf_def)

lemma ws_r1: "dwe_step W1 (Crash ec1) r_crash_w"
proof -
  have c: "dw_exec_step (dwe_core W1) (Crash ec1) (dwe_core r_crash_w)"
    by (rule crashI) (simp_all add: W1_def r_crash_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: W1_def r_crash_w_def mkT_def)
qed

lemma ws_r2: "dwe_step r_crash_w Recover r_rec_w"
proof -
  have c: "dw_exec_step (dwe_core r_crash_w) Recover (dwe_core r_rec_w)"
    by (rule recoverI) (simp_all add: r_crash_w_def r_rec_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: r_crash_w_def r_rec_w_def mkT_def)
qed

lemma res_r: "dwe_resume r_rec_w r_run1_w"
  by (simp add: dwe_resume_def r_rec_w_def r_run1_w_def mkT_def mkC_def)

lemma reach_r_crash: "dwe_reachable r_crash_w"
  by (rule dwe_reachable_label_ext[OF reach_W1 wf_W1 g_W1_crash ws_r1])

lemma reach_r_rec: "dwe_reachable r_rec_w"
  by (rule dwe_reachable_label_ext[OF reach_r_crash wf_r_crash g_r_crash_recover ws_r2])

lemma reach_r_run1: "dwe_reachable r_run1_w"
  by (rule dwe_reachable_resume_ext[OF reach_r_rec res_r])

lemma r_run1_mismatch:
  "mismatch_at (proto_of_exec_at (dwe_core r_run1_w) ec1) ec1 0"
  by (simp add: r_run1_w_def eval_defs eval_nat_numeral)

lemma r_run1_segment_start: "dwe_segment_start r_run1_w"
  unfolding dwe_segment_start_def using reach_r_rec res_r by blast

theorem epoch1_segment_start_with_mismatch:
  "dwe_segment_start r_run1_w \<and> dwe_reachable r_run1_w
 \<and> dwe_epoch r_run1_w = 1
 \<and> exec_status (dwe_core r_run1_w) = Running
 \<and> mismatch_at (proto_of_exec_at (dwe_core r_run1_w) ec1) ec1 0"
  by (intro conjI r_run1_segment_start reach_r_run1 r_run1_mismatch)
     (simp_all add: r_run1_w_def mkT_def mkC_def)

end
