(*  Title:       Dual_Write_Effect_Converse.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    The per-epoch re-landing of the tier-1 converse / optimality family
    (safe_iff_running_image_faithful, Dual_Write_Converse) on the promoted
    CYCLIC effect machine: a RESTATEMENT WITH DISCLOSED SCOPE, never a
    citation and never an upgrade.

    Why it cannot be a citation: the landed family is quantified over
    dual_write_implementation records whose step relation is typed over
    dw_exec_label only, and a resume-using step relation admits NO such
    packaging that dwi_refines_exec --- a Resume step has no dw_exec_step
    image (resume_breaks_core_simulation).  So this theory re-founds the
    implementation quantification on a NEW record over the cyclic action
    grammar (labels + emitting reconcile + Resume) and re-runs the landed
    proofs' ingredients on it: the same premise triple (crash-closure,
    refinement, Running start), the same two sides (store-image
    faithfulness at reachable Running frontiers vs a reachable observable
    bad crash), the same structural predecessor argument --- with two new
    one-line predecessor cases for the two cyclic rules, both closing by
    status contradiction.

    Why the pinned machine alone cannot carry the statement: over the
    pinned dwe_reachable both sides of the iff are concretely FALSE
    (t_mid_w is a reachable observable bad crash; W4 is reachable Running
    with a scoped mismatch, W4_running_mismatch below), so a
    machine-level-only "iff" degenerates to False <-> False and is
    rejected as contentless.  The implementation quantification IS the
    content, exactly as in the landed tier.

    Produced by the S4d proof-wave P3 prover per the committed design
    (paper/dual_write/phase3/s4d_design/site_3_6_safety_family.md, SITE 3,
    as amended by the gate report's canonicalizations F1/F5/F6): the
    stale-heal witness chain lands under the gate-canonical names
    stale_heal_w / stale_run1_w / stale_crash1_w, and the new premise
    triple carries three mirrored tightness controls at the new record
    type.  The scratch original's in-source ML oracle gates are STRIPPED here:
    oracle-freedom is certified by scratch-side per-slice gate sessions
    with confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Converse
  imports Dual_Write_Effect_Segments
begin

section \<open>The cyclic implementation carrier\<close>

text \<open>
  Mirror of the landed implementation interface
  (@{type dual_write_implementation}, @{const dwi_trace},
  @{const dwi_refines_exec}, @{const crash_closed_implementation},
  @{const canonical_dw_implementation}) with the action type widened from
  @{type dw_exec_label} to @{type dwe_action}.  The crash-closure mirror
  keeps the landed definition's unrestricted quantification over ALL
  @{typ 's} states (not just reachable ones) --- that is what makes
  post-Resume states automatically covered, the exact point where the
  cyclic machine's seam state family lands on both sides of the
  biconditional at once (see the stale-heal witnesses below).
\<close>

record ('s, 'k, 'v) dwe_implementation =
  dwei_initial :: "'s"
  dwei_step    :: "'s \<Rightarrow> ('k, 'v) dwe_action \<Rightarrow> 's \<Rightarrow> bool"
  dwei_state   :: "'s \<Rightarrow> ('k, 'v) dwe_state"

inductive dwei_trace
  :: "('s, 'k, 'v) dwe_implementation \<Rightarrow> 's \<Rightarrow> ('k, 'v) dwe_action list
      \<Rightarrow> 's \<Rightarrow> bool"
where
  dwei_trace_refl:
    "dwei_trace I s [] s"
| dwei_trace_step:
    "\<lbrakk>dwei_step I s a s'; dwei_trace I s' as s''\<rbrakk> \<Longrightarrow>
     dwei_trace I s (a # as) s''"

lemma dwei_trace_append:
  assumes "dwei_trace I s as s'"
      and "dwei_trace I s' bs s''"
  shows "dwei_trace I s (as @ bs) s''"
  using assms
  by (induction arbitrary: bs s'' rule: dwei_trace.induct)
     (auto intro: dwei_trace.intros)

definition dwei_refines_cyclic :: "('s, 'k, 'v) dwe_implementation \<Rightarrow> bool" where
  "dwei_refines_cyclic I \<longleftrightarrow>
     (\<forall>s a s'. dwei_step I s a s' \<longrightarrow>
        (case a of
           DWE_Label l \<Rightarrow> dwe_step (dwei_state I s) l (dwei_state I s')
         | DWE_Reconcile m f \<Rightarrow>
             emitting_reconcile m (dwei_state I s) f (dwei_state I s')
         | DWE_Resume \<Rightarrow> dwe_resume (dwei_state I s) (dwei_state I s')))"

lemma dwei_refines_cyclicD_label:
  assumes "dwei_refines_cyclic I"
      and "dwei_step I s (DWE_Label l) s'"
  shows "dwe_step (dwei_state I s) l (dwei_state I s')"
proof -
  have "case DWE_Label l of
          DWE_Label l \<Rightarrow> dwe_step (dwei_state I s) l (dwei_state I s')
        | DWE_Reconcile m f \<Rightarrow>
            emitting_reconcile m (dwei_state I s) f (dwei_state I s')
        | DWE_Resume \<Rightarrow> dwe_resume (dwei_state I s) (dwei_state I s')"
    using assms unfolding dwei_refines_cyclic_def by blast
  then show ?thesis by simp
qed

lemma dwei_refines_cyclicD_reconcile:
  assumes "dwei_refines_cyclic I"
      and "dwei_step I s (DWE_Reconcile m f) s'"
  shows "emitting_reconcile m (dwei_state I s) f (dwei_state I s')"
proof -
  have "case DWE_Reconcile m f of
          DWE_Label l \<Rightarrow> dwe_step (dwei_state I s) l (dwei_state I s')
        | DWE_Reconcile m f \<Rightarrow>
            emitting_reconcile m (dwei_state I s) f (dwei_state I s')
        | DWE_Resume \<Rightarrow> dwe_resume (dwei_state I s) (dwei_state I s')"
    using assms unfolding dwei_refines_cyclic_def by blast
  then show ?thesis by simp
qed

lemma dwei_refines_cyclicD_resume:
  assumes "dwei_refines_cyclic I"
      and "dwei_step I s DWE_Resume s'"
  shows "dwe_resume (dwei_state I s) (dwei_state I s')"
proof -
  have "case DWE_Resume of
          DWE_Label l \<Rightarrow> dwe_step (dwei_state I s) l (dwei_state I s')
        | DWE_Reconcile m f \<Rightarrow>
            emitting_reconcile m (dwei_state I s) f (dwei_state I s')
        | DWE_Resume \<Rightarrow> dwe_resume (dwei_state I s) (dwei_state I s')"
    using assms unfolding dwei_refines_cyclic_def by blast
  then show ?thesis by simp
qed

definition dwei_crash_closed :: "('s, 'k, 'v) dwe_implementation \<Rightarrow> bool" where
  "dwei_crash_closed I \<longleftrightarrow>
     (\<forall>s c. exec_status (dwe_core (dwei_state I s)) = Running
          \<and> c \<le> exec_finish (dwe_core (dwei_state I s))
        \<longrightarrow> (\<exists>s'. dwei_step I s (DWE_Label (Crash c)) s'))"

definition canonical_dwe_implementation
  :: "('k, 'v) dwe_state \<Rightarrow> (('k, 'v) dwe_state, 'k, 'v) dwe_implementation"
where
  "canonical_dwe_implementation t =
     \<lparr> dwei_initial = t,
       dwei_step = (\<lambda>t a t'.
          case a of
            DWE_Label l \<Rightarrow>
              exec_label_preserves_history_wf (dwe_core t) l
              \<and> dwe_step t l t'
          | DWE_Reconcile m f \<Rightarrow> emitting_reconcile m t f t'
          | DWE_Resume \<Rightarrow> dwe_resume t t'),
       dwei_state = (\<lambda>t. t) \<rparr>"

lemma canonical_dwe_implementation_refines_cyclic [simp]:
  "dwei_refines_cyclic (canonical_dwe_implementation t)"
  by (simp add: dwei_refines_cyclic_def canonical_dwe_implementation_def
           split: dwe_action.split)

text \<open>The free machine's crash is always enabled from a Running core, so
  the canonical packaging is crash-closed.\<close>

lemma canonical_dwe_implementation_crash_closed:
  "dwei_crash_closed (canonical_dwe_implementation t)"
  unfolding dwei_crash_closed_def
proof (intro allI impI, elim conjE)
  fix s c
  assume run: "exec_status (dwe_core
                 (dwei_state (canonical_dwe_implementation t) s)) = Running"
  have run': "exec_status (dwe_core s) = Running"
    using run by (simp add: canonical_dwe_implementation_def)
  have core: "dw_exec_step (dwe_core s) (Crash c)
                ((dwe_core s)\<lparr>exec_status := Crashed c\<rparr>)"
    by (rule crashI[OF run' refl])
  have step: "dwe_step s (Crash c)
                (s\<lparr>dwe_core := (dwe_core s)\<lparr>exec_status := Crashed c\<rparr>\<rparr>)"
    by (rule dwe_lift_nonpubI[OF core]) simp_all
  show "\<exists>s'. dwei_step (canonical_dwe_implementation t) s
               (DWE_Label (Crash c)) s'"
    by (intro exI[of _ "s\<lparr>dwe_core := (dwe_core s)\<lparr>exec_status := Crashed c\<rparr>\<rparr>"])
       (simp add: canonical_dwe_implementation_def
                  exec_label_preserves_history_wf_def step)
qed

subsection \<open>Crash-step and per-rule frame helpers\<close>

text \<open>
  Mirrors of the landed @{thm [source] dwi_crash_step_state} shape (the
  partition layer's crash inversion), lifted through @{thm [source]
  dwe_step_core}, plus three per-rule one-liners the dwei-level trace
  lemmas below consume.  The machine-trace-level twins of the frame facts
  are banked in the Segments foundation
  (@{thm [source] dwe_trace_core_frame}); these are their per-rule
  ingredients restated for the implementation carrier, not new content.
\<close>

lemma dw_exec_crash_step_state:
  assumes "dw_exec_step s (Crash c) s'"
  shows "s' = s\<lparr>exec_status := Crashed c\<rparr>"
  using assms by (cases rule: dw_exec_step.cases) auto

lemma dw_exec_crash_step_status:
  assumes "dw_exec_step s (Crash c) s'"
  shows "exec_status s' = Crashed c"
  using assms by (cases rule: dw_exec_step.cases) auto

lemma dwei_crash_step_core_state:
  assumes refines: "dwei_refines_cyclic I"
      and step: "dwei_step I s (DWE_Label (Crash c)) s'"
  shows "dwe_core (dwei_state I s')
           = (dwe_core (dwei_state I s))\<lparr>exec_status := Crashed c\<rparr>"
proof -
  have "dwe_step (dwei_state I s) (Crash c) (dwei_state I s')"
    by (rule dwei_refines_cyclicD_label[OF refines step])
  then have "dw_exec_step (dwe_core (dwei_state I s)) (Crash c)
               (dwe_core (dwei_state I s'))"
    by (rule dwe_step_core)
  then show ?thesis by (rule dw_exec_crash_step_state)
qed

lemma emitting_reconcile_core_status:
  assumes "emitting_reconcile m t f t'"
  shows "exec_status (dwe_core t') = Recovered"
  using assms by (auto simp: emitting_reconcile_def)

lemma emitting_reconcile_scope_same:
  assumes "emitting_reconcile m t f t'"
  shows "exec_scope (dwe_core t') = exec_scope (dwe_core t)"
  using assms by (auto simp: emitting_reconcile_def)

lemma dwe_resume_scope_same:
  assumes "dwe_resume t t'"
  shows "exec_scope (dwe_core t') = exec_scope (dwe_core t)"
  using assms by (simp add: dwe_resume_def)

section \<open>The two sides of the characterization\<close>

text \<open>
  Both sides mirror their landed originals shape-for-shape at
  @{term "dwe_core (dwei_state I s)"}: the faithfulness side is the body
  of the landed @{text running_image_faithful} (Dual\_Write\_Converse,
  outside this theory's import slice by the wave's dependency mandate),
  the bad-crash side is @{thm [source]
  reachable_observable_bad_crash_def}'s (including the @{const diverges}
  conjunct, discharged as landed via
  @{thm [source] observable_mismatch_imp_diverges}).  The @{text store_}
  reading is part of the names: "safe" here is STORE-image crash-safety,
  the tier-1 notion --- see the mandatory disclosure block at the
  biconditional below.
\<close>

definition cyclic_running_image_faithful
  :: "('s, 'k, 'v) dwe_implementation \<Rightarrow> bool"
where
  "cyclic_running_image_faithful I \<longleftrightarrow>
     (\<forall>xs s c k.
        dwei_trace I (dwei_initial I) xs s
      \<and> exec_status (dwe_core (dwei_state I s)) = Running
      \<and> c \<le> exec_finish (dwe_core (dwei_state I s))
      \<longrightarrow> \<not> mismatch_at (proto_of_exec_at (dwe_core (dwei_state I s)) c) c k)"

definition cyclic_reachable_observable_bad_crash
  :: "('s, 'k, 'v) dwe_implementation \<Rightarrow> ('k, 'v) dwe_action list
      \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> 's \<Rightarrow> bool"
where
  "cyclic_reachable_observable_bad_crash I xs c k s \<longleftrightarrow>
     dwei_trace I (dwei_initial I) xs s
   \<and> observable_mismatch (dwe_core (dwei_state I s)) c k
   \<and> diverges (proto_of_exec_at (dwe_core (dwei_state I s)) c) c"

definition cyclic_has_reachable_observable_bad_crash
  :: "('s, 'k, 'v) dwe_implementation \<Rightarrow> bool"
where
  "cyclic_has_reachable_observable_bad_crash I \<longleftrightarrow>
     (\<exists>xs c k s. cyclic_reachable_observable_bad_crash I xs c k s)"

section \<open>Forward: store-safe implies running-image-faithful\<close>

text \<open>
  Transliteration of the landed partition-layer engine
  (@{thm [source]
  crash_closed_running_bad_crash_enabled_imp_reachable_observable_bad_crash})
  followed by the landed forward direction
  (@{text safe_imp_running_image_faithful}): crash-closure turns
  a Running scoped mismatch into an observable bad crash one
  @{term "DWE_Label (Crash c)"} step later; the appended action is a
  label, so this argument survives unchanged inside Resume-free segment
  scopes as well (used again for the segment-scoped form below).
\<close>

lemma dwei_crash_closed_running_mismatch_imp_bad_crash:
  assumes closed: "dwei_crash_closed I"
      and refines: "dwei_refines_cyclic I"
      and tr: "dwei_trace I (dwei_initial I) xs s"
      and run: "exec_status (dwe_core (dwei_state I s)) = Running"
      and le_fin: "c \<le> exec_finish (dwe_core (dwei_state I s))"
      and mis: "mismatch_at (proto_of_exec_at (dwe_core (dwei_state I s)) c) c k"
  shows "cyclic_has_reachable_observable_bad_crash I"
proof -
  from closed run le_fin obtain s' where
    step: "dwei_step I s (DWE_Label (Crash c)) s'"
    by (auto simp: dwei_crash_closed_def)
  have st: "dwe_core (dwei_state I s')
              = (dwe_core (dwei_state I s))\<lparr>exec_status := Crashed c\<rparr>"
    by (rule dwei_crash_step_core_state[OF refines step])
  have tr': "dwei_trace I (dwei_initial I) (xs @ [DWE_Label (Crash c)]) s'"
    using tr
    by (rule dwei_trace_append[OF _ dwei_trace.dwei_trace_step
          [OF step dwei_trace.dwei_trace_refl]])
  have obs: "observable_mismatch (dwe_core (dwei_state I s')) c k"
    using le_fin mis by (simp add: st observable_mismatch_def)
  have div: "diverges (proto_of_exec_at (dwe_core (dwei_state I s')) c) c"
    by (rule observable_mismatch_imp_diverges[OF obs])
  from tr' obs div
  have "cyclic_reachable_observable_bad_crash I (xs @ [DWE_Label (Crash c)]) c k s'"
    by (simp add: cyclic_reachable_observable_bad_crash_def)
  then show ?thesis
    by (auto simp: cyclic_has_reachable_observable_bad_crash_def)
qed

theorem cyclic_store_safe_imp_running_image_faithful:
  assumes closed:  "dwei_crash_closed I"
      and refines: "dwei_refines_cyclic I"
      and safe:    "\<not> cyclic_has_reachable_observable_bad_crash I"
  shows "cyclic_running_image_faithful I"
  unfolding cyclic_running_image_faithful_def
proof (intro allI impI, elim conjE)
  fix xs s c k
  assume tr:  "dwei_trace I (dwei_initial I) xs s"
     and run: "exec_status (dwe_core (dwei_state I s)) = Running"
     and le:  "c \<le> exec_finish (dwe_core (dwei_state I s))"
  show "\<not> mismatch_at (proto_of_exec_at (dwe_core (dwei_state I s)) c) c k"
  proof
    assume mis: "mismatch_at (proto_of_exec_at (dwe_core (dwei_state I s)) c) c k"
    have "cyclic_has_reachable_observable_bad_crash I"
      by (rule dwei_crash_closed_running_mismatch_imp_bad_crash
            [OF closed refines tr run le mis])
    with safe show False ..
  qed
qed

section \<open>The structural predecessor lemma\<close>

text \<open>
  Transliteration of the landed
  @{text crashed_has_running_predecessor_or_crashed_start}
  (Dual\_Write\_Converse), the family's one structural ingredient, with
  two changes.  (i) The SAME seven landed core cases go through verbatim
  on @{text "dwe_core (dwei_state I s)"} --- the wrapper's ledger and
  epoch fields are invisible to the argument because both @{const
  dwe_step} constructors set the core to the projected core step's target
  (@{thm [source] dwe_step_core}).  TWO NEW CASES appear for the two
  cyclic rules and both close by status contradiction: an emitting
  reconcile leaves the core @{const Recovered}
  (@{thm [source] emitting_reconcile_core_status}) and a Resume leaves it
  @{const Running} (@{thm [source] dwe_resume_core}), so neither can be
  the step INTO a @{term "Crashed c"} state.  (ii) The constructed
  predecessor trace is assembled from the original trace's own heads, so
  the conclusion carries the @{term "set ys \<subseteq> set xs"} strengthening for
  free --- the segment-scoped biconditional below consumes it to keep the
  predecessor inside the Resume-free scope.
\<close>

lemma cyclic_crashed_has_running_predecessor_or_crashed_start:
  assumes tr: "dwei_trace I s0 xs s"
  shows "dwei_refines_cyclic I
         \<and> exec_status (dwe_core (dwei_state I s)) = Crashed c \<longrightarrow>
           (\<exists>ys s_pre. dwei_trace I s0 ys s_pre
               \<and> set ys \<subseteq> set xs
               \<and> exec_status (dwe_core (dwei_state I s_pre)) = Running
               \<and> proto_of_exec_at (dwe_core (dwei_state I s_pre)) c
                   = proto_of_exec_at (dwe_core (dwei_state I s)) c)
         \<or> (exec_status (dwe_core (dwei_state I s0)) = Crashed c
               \<and> proto_of_exec_at (dwe_core (dwei_state I s0)) c
                   = proto_of_exec_at (dwe_core (dwei_state I s)) c)"
  using tr
proof (induction rule: dwei_trace.induct)
  case (dwei_trace_refl I s0)
  show ?case
  proof (intro impI, elim conjE)
    assume "exec_status (dwe_core (dwei_state I s0)) = Crashed c"
    then show "(\<exists>ys s_pre. dwei_trace I s0 ys s_pre
                 \<and> set ys \<subseteq> set []
                 \<and> exec_status (dwe_core (dwei_state I s_pre)) = Running
                 \<and> proto_of_exec_at (dwe_core (dwei_state I s_pre)) c
                     = proto_of_exec_at (dwe_core (dwei_state I s0)) c)
            \<or> (exec_status (dwe_core (dwei_state I s0)) = Crashed c
                 \<and> proto_of_exec_at (dwe_core (dwei_state I s0)) c
                     = proto_of_exec_at (dwe_core (dwei_state I s0)) c)"
      by simp
  qed
next
  case (dwei_trace_step I s0 a s1 as s)
  show ?case
  proof (intro impI, elim conjE)
    assume refines: "dwei_refines_cyclic I"
       and cr: "exec_status (dwe_core (dwei_state I s)) = Crashed c"
    have IHdisj:
      "(\<exists>ys s_pre. dwei_trace I s1 ys s_pre
           \<and> set ys \<subseteq> set as
           \<and> exec_status (dwe_core (dwei_state I s_pre)) = Running
           \<and> proto_of_exec_at (dwe_core (dwei_state I s_pre)) c
               = proto_of_exec_at (dwe_core (dwei_state I s)) c)
     \<or> (exec_status (dwe_core (dwei_state I s1)) = Crashed c
           \<and> proto_of_exec_at (dwe_core (dwei_state I s1)) c
               = proto_of_exec_at (dwe_core (dwei_state I s)) c)"
      using dwei_trace_step.IH refines cr by blast
    from IHdisj show
      "(\<exists>ys s_pre. dwei_trace I s0 ys s_pre
           \<and> set ys \<subseteq> set (a # as)
           \<and> exec_status (dwe_core (dwei_state I s_pre)) = Running
           \<and> proto_of_exec_at (dwe_core (dwei_state I s_pre)) c
               = proto_of_exec_at (dwe_core (dwei_state I s)) c)
     \<or> (exec_status (dwe_core (dwei_state I s0)) = Crashed c
           \<and> proto_of_exec_at (dwe_core (dwei_state I s0)) c
               = proto_of_exec_at (dwe_core (dwei_state I s)) c)"
    proof
      assume "\<exists>ys s_pre. dwei_trace I s1 ys s_pre
               \<and> set ys \<subseteq> set as
               \<and> exec_status (dwe_core (dwei_state I s_pre)) = Running
               \<and> proto_of_exec_at (dwe_core (dwei_state I s_pre)) c
                   = proto_of_exec_at (dwe_core (dwei_state I s)) c"
      then obtain ys s_pre where
          y_tr: "dwei_trace I s1 ys s_pre"
        and y_sub: "set ys \<subseteq> set as"
        and y_run: "exec_status (dwe_core (dwei_state I s_pre)) = Running"
        and y_proto: "proto_of_exec_at (dwe_core (dwei_state I s_pre)) c
                        = proto_of_exec_at (dwe_core (dwei_state I s)) c"
        by blast
      have "dwei_trace I s0 (a # ys) s_pre"
        by (rule dwei_trace.dwei_trace_step[OF dwei_trace_step.hyps(1) y_tr])
      moreover have "set (a # ys) \<subseteq> set (a # as)"
        using y_sub by auto
      ultimately show ?thesis using y_run y_proto by blast
    next
      assume r: "exec_status (dwe_core (dwei_state I s1)) = Crashed c
                   \<and> proto_of_exec_at (dwe_core (dwei_state I s1)) c
                       = proto_of_exec_at (dwe_core (dwei_state I s)) c"
      then have r_st: "exec_status (dwe_core (dwei_state I s1)) = Crashed c"
        and r_pr: "proto_of_exec_at (dwe_core (dwei_state I s1)) c
                     = proto_of_exec_at (dwe_core (dwei_state I s)) c"
        by simp_all
      show ?thesis
      proof (cases a)
        case (DWE_Label l)
        with dwei_trace_step.hyps(1)
        have "dwei_step I s0 (DWE_Label l) s1" by simp
        then have lstep: "dwe_step (dwei_state I s0) l (dwei_state I s1)"
          by (rule dwei_refines_cyclicD_label[OF refines])
        have estep: "dw_exec_step (dwe_core (dwei_state I s0)) l
                       (dwe_core (dwei_state I s1))"
          by (rule dwe_step_core[OF lstep])
        from estep show ?thesis
        proof (cases rule: dw_exec_step.cases)
          case (do_source cc e)      \<comment> \<open>status unchanged = Running, contra Crashed\<close>
          from do_source r_st show ?thesis by simp
        next
          case (enqueue_downstream cc e)
          from enqueue_downstream r_st show ?thesis by simp
        next
          case (do_downstream cc e)
          from do_downstream r_st show ?thesis by simp
        next
          case (ack cc e)
          from ack r_st show ?thesis by simp
        next
          case (crash cc)
          \<comment> \<open>s0's core Running; s1's core = s0's with status Crashed cc;
              proto ignores status.  Predecessor found: s0 itself, empty trace.\<close>
          from crash have run0: "exec_status (dwe_core (dwei_state I s0)) = Running"
            and s1eq: "dwe_core (dwei_state I s1)
                         = (dwe_core (dwei_state I s0))\<lparr>exec_status := Crashed cc\<rparr>"
            by auto
          have "proto_of_exec_at (dwe_core (dwei_state I s0)) c
                  = proto_of_exec_at (dwe_core (dwei_state I s)) c"
            using r_pr by (simp add: s1eq)
          moreover have "dwei_trace I s0 [] s0"
            by (rule dwei_trace.dwei_trace_refl)
          moreover have "set [] \<subseteq> set (a # as)"
            by simp
          ultimately show ?thesis using run0 by blast
        next
          case (recover cc)          \<comment> \<open>status becomes Recovered, contra Crashed\<close>
          from recover r_st show ?thesis by simp
        next
          case (observe ff)
          \<comment> \<open>identity step on the core: crashed-start disjunct persists\<close>
          from observe have eq: "dwe_core (dwei_state I s1)
                                   = dwe_core (dwei_state I s0)" by simp
          from r_st eq have "exec_status (dwe_core (dwei_state I s0)) = Crashed c"
            by simp
          moreover from r_pr eq
          have "proto_of_exec_at (dwe_core (dwei_state I s0)) c
                  = proto_of_exec_at (dwe_core (dwei_state I s)) c" by simp
          ultimately show ?thesis by blast
        qed
      next
        case (DWE_Reconcile m f)
        \<comment> \<open>NEW CASE: the reconcile's target core is Recovered, contra Crashed\<close>
        with dwei_trace_step.hyps(1)
        have "dwei_step I s0 (DWE_Reconcile m f) s1" by simp
        then have "emitting_reconcile m (dwei_state I s0) f (dwei_state I s1)"
          by (rule dwei_refines_cyclicD_reconcile[OF refines])
        then have "exec_status (dwe_core (dwei_state I s1)) = Recovered"
          by (rule emitting_reconcile_core_status)
        with r_st show ?thesis by simp
      next
        case DWE_Resume
        \<comment> \<open>NEW CASE: the Resume's target core is Running, contra Crashed\<close>
        with dwei_trace_step.hyps(1)
        have "dwei_step I s0 DWE_Resume s1" by simp
        then have "dwe_resume (dwei_state I s0) (dwei_state I s1)"
          by (rule dwei_refines_cyclicD_resume[OF refines])
        then have "exec_status (dwe_core (dwei_state I s1)) = Running"
          by (simp add: dwe_resume_core)
        with r_st show ?thesis by simp
      qed
    qed
  qed
qed

section \<open>Backward: running-image-faithful plus Running start implies store-safe\<close>

theorem cyclic_running_image_faithful_running_start_imp_store_safe:
  assumes refines:   "dwei_refines_cyclic I"
      and start_run: "exec_status (dwe_core (dwei_state I (dwei_initial I)))
                        = Running"
      and faithful:  "cyclic_running_image_faithful I"
  shows "\<not> cyclic_has_reachable_observable_bad_crash I"
proof
  assume "cyclic_has_reachable_observable_bad_crash I"
  then obtain xs c k s where
      bad: "cyclic_reachable_observable_bad_crash I xs c k s"
    by (auto simp: cyclic_has_reachable_observable_bad_crash_def)
  then have tr: "dwei_trace I (dwei_initial I) xs s"
    and obs: "observable_mismatch (dwe_core (dwei_state I s)) c k"
    by (auto simp: cyclic_reachable_observable_bad_crash_def)
  from obs have crashed: "exec_status (dwe_core (dwei_state I s)) = Crashed c"
    and le_fin: "c \<le> exec_finish (dwe_core (dwei_state I s))"
    and mis: "mismatch_at (proto_of_exec_at (dwe_core (dwei_state I s)) c) c k"
    by (auto simp: observable_mismatch_def)
  have disj:
    "(\<exists>ys s_pre. dwei_trace I (dwei_initial I) ys s_pre
         \<and> set ys \<subseteq> set xs
         \<and> exec_status (dwe_core (dwei_state I s_pre)) = Running
         \<and> proto_of_exec_at (dwe_core (dwei_state I s_pre)) c
             = proto_of_exec_at (dwe_core (dwei_state I s)) c)
   \<or> (exec_status (dwe_core (dwei_state I (dwei_initial I))) = Crashed c
         \<and> proto_of_exec_at (dwe_core (dwei_state I (dwei_initial I))) c
             = proto_of_exec_at (dwe_core (dwei_state I s)) c)"
    using cyclic_crashed_has_running_predecessor_or_crashed_start[OF tr]
          refines crashed
    by blast
  from disj show False
  proof
    assume "\<exists>ys s_pre. dwei_trace I (dwei_initial I) ys s_pre
              \<and> set ys \<subseteq> set xs
              \<and> exec_status (dwe_core (dwei_state I s_pre)) = Running
              \<and> proto_of_exec_at (dwe_core (dwei_state I s_pre)) c
                  = proto_of_exec_at (dwe_core (dwei_state I s)) c"
    then obtain ys s_pre where
        p_tr: "dwei_trace I (dwei_initial I) ys s_pre"
      and p_run: "exec_status (dwe_core (dwei_state I s_pre)) = Running"
      and p_proto: "proto_of_exec_at (dwe_core (dwei_state I s_pre)) c
                      = proto_of_exec_at (dwe_core (dwei_state I s)) c"
      by blast
    have p_mis: "mismatch_at (proto_of_exec_at (dwe_core (dwei_state I s_pre)) c) c k"
      using mis p_proto by simp
    have p_fin: "exec_finish (dwe_core (dwei_state I s_pre))
                   = exec_finish (dwe_core (dwei_state I s))"
      using p_proto by (simp add: proto_of_exec_at_def)
    have p_le: "c \<le> exec_finish (dwe_core (dwei_state I s_pre))"
      using le_fin p_fin by simp
    from faithful p_tr p_run p_le
    have "\<not> mismatch_at (proto_of_exec_at (dwe_core (dwei_state I s_pre)) c) c k"
      by (simp add: cyclic_running_image_faithful_def)
    with p_mis show False by simp
  next
    assume "exec_status (dwe_core (dwei_state I (dwei_initial I))) = Crashed c
              \<and> proto_of_exec_at (dwe_core (dwei_state I (dwei_initial I))) c
                  = proto_of_exec_at (dwe_core (dwei_state I s)) c"
    then have "exec_status (dwe_core (dwei_state I (dwei_initial I))) = Crashed c"
      by simp
    with start_run show False by simp
  qed
qed

section \<open>The biconditional\<close>

theorem cyclic_store_safe_iff_running_image_faithful:
  assumes closed:    "dwei_crash_closed I"
      and refines:   "dwei_refines_cyclic I"
      and start_run: "exec_status (dwe_core (dwei_state I (dwei_initial I)))
                        = Running"
  shows "(\<not> cyclic_has_reachable_observable_bad_crash I)
         \<longleftrightarrow> cyclic_running_image_faithful I"
proof
  assume "\<not> cyclic_has_reachable_observable_bad_crash I"
  then show "cyclic_running_image_faithful I"
    by (rule cyclic_store_safe_imp_running_image_faithful[OF closed refines])
next
  assume "cyclic_running_image_faithful I"
  then show "\<not> cyclic_has_reachable_observable_bad_crash I"
    by (rule cyclic_running_image_faithful_running_start_imp_store_safe
          [OF refines start_run])
qed

text \<open>
  MANDATORY DISCLOSURE (part of the statement, not decoration).

  (1) TIER SCOPE.  "Safe" in this biconditional is STORE-image
  crash-safety --- no reachable observable scoped mismatch at a crashed
  frontier --- i.e. the tier-1 notion re-landed on the cyclic machine.
  It does NOT characterize effect safety: the effect verdict is not a
  function of the store (@{thm [source] dwe_duplicate_separation}), and
  post-Resume the two tiers point OPPOSITE ways --- the stale-heal
  witness below (@{text post_resume_observable_bad_crash}) is store-BAD
  yet effect-CLEAN, while the banked @{thm [source] t_fin_unsafe} /
  @{thm [source] resume_cycle_amplification} states are store-HEALED yet
  effect-BAD.  Nothing in this theory constrains the ledger.

  (2) NOT A CITATION.  The landed theorem family
  (@{text safe_iff_running_image_faithful} and companions,
  Dual\_Write\_Converse) is not being cited: a resume-using cyclic step
  relation admits no @{type dual_write_implementation} packaging that
  satisfies @{const dwi_refines_exec} --- the landed record's step type
  has no Reconcile/Resume actions, and any core-projected packaging of a
  Resume step is refuted by
  @{thm [source] resume_breaks_core_simulation}.  Within a Resume-free
  segment the landed family's INGREDIENTS re-derive through the label
  projection @{thm [source] dwe_step_core}; that is what this theory
  does, on a new carrier.  Restatement with disclosed scope, not
  transfer.

  (3) NOT A MACHINE-LEVEL FACT.  Instantiated at the pinned free machine
  (@{const dwe_reachable}) alone, BOTH sides of the biconditional are
  concretely false --- @{const t_mid_w} is a reachable observable bad
  crash (@{thm [source] reach_t_mid}, @{thm [source] t_mid_mismatch}) and
  @{const W4} is reachable Running with a scoped mismatch
  (@{thm [source] reach_W4}, @{text W4_running_mismatch} below) --- so a
  machine-level-only "iff" would degenerate to @{term "False \<longleftrightarrow> False"}
  and is rejected as contentless.  The implementation quantification over
  the cyclic action grammar is the content.

  (4) STRONGER RHS, PRICED HONESTLY.  Over the full cyclic reachability
  of an implementation, faithfulness now constrains post-Resume Running
  states, i.e. recovery quality: a stale heal that resumes is
  store-unsafe (the witness chain below).  This is genuinely more than
  the landed RHS ever expressed and is presented as a NEW cyclic-machine
  theorem, never as an upgrade of the landed one.

  CROSS-REFERENCE (the complementary landed-record form).  The sibling
  theory @{text Dual_Write_Effect_Segment_Boundaries} re-founds the
  LANDED @{type dual_write_implementation} biconditional verbatim at
  segment-start cores over label-fragment continuations --- the tier-1
  theorem re-landed through the landed framework's own parametric slot.
  The present theory is the new-carrier restatement over the full cyclic
  action grammar (labels + reconcile + Resume) that the landed record
  cannot express.  The two forms are complements, not duplicates.
  Likewise, the tightness theory's @{text I_cyclic_lr} /
  @{text I_cyclic_labels} packagings live at the LANDED record type and
  FAIL @{const dwi_refines_exec} there, while the native
  @{const canonical_dwe_implementation} here refines --- the same
  type-level-escape story one tier up, closed from both sides.
\<close>

section \<open>Re-founding at segment starts\<close>

text \<open>
  (i) Re-founding at ANY reachable Running start: post-Resume segment
  starts are Running by @{thm [source] post_resume_core_running}, so this
  covers every epoch's segment start.  It is an instance of the top
  biconditional at @{term "I\<lparr>dwei_initial := s0\<rparr>"} --- both premise
  definitions quantify over ALL states and never mention
  @{const dwei_initial}, so they survive the record update verbatim.
\<close>

lemma dwei_crash_closed_initial_update [simp]:
  "dwei_crash_closed (I\<lparr>dwei_initial := s0\<rparr>) \<longleftrightarrow> dwei_crash_closed I"
  by (simp add: dwei_crash_closed_def)

lemma dwei_refines_cyclic_initial_update [simp]:
  "dwei_refines_cyclic (I\<lparr>dwei_initial := s0\<rparr>) \<longleftrightarrow> dwei_refines_cyclic I"
  by (simp add: dwei_refines_cyclic_def split: dwe_action.split)

corollary cyclic_iff_refounded_at_running_start:
  assumes closed:  "dwei_crash_closed I"
      and refines: "dwei_refines_cyclic I"
      and reach:   "dwei_trace I (dwei_initial I) ys s0"
      and run0:    "exec_status (dwe_core (dwei_state I s0)) = Running"
  shows "(\<not> cyclic_has_reachable_observable_bad_crash (I\<lparr>dwei_initial := s0\<rparr>))
         \<longleftrightarrow> cyclic_running_image_faithful (I\<lparr>dwei_initial := s0\<rparr>)"
proof (rule cyclic_store_safe_iff_running_image_faithful)
  show "dwei_crash_closed (I\<lparr>dwei_initial := s0\<rparr>)"
    using closed by simp
  show "dwei_refines_cyclic (I\<lparr>dwei_initial := s0\<rparr>)"
    using refines by simp
  show "exec_status (dwe_core (dwei_state (I\<lparr>dwei_initial := s0\<rparr>)
          (dwei_initial (I\<lparr>dwei_initial := s0\<rparr>)))) = Running"
    using run0 by simp
qed

text \<open>
  (ii) The EPOCH-SCOPED form proper: both sides restricted to the
  Resume-free continuation of a Running segment start.  RESTATEMENT WITH
  DISCLOSED SCOPE: segment-scoped store safety (the left side) is NOT
  full-trace store safety --- it says nothing about states reached after
  the next Resume; it is strictly implied by (and does not upgrade) the
  full-trace form at the same start.  The forward direction appends a
  @{term "DWE_Label (Crash c)"} --- not a Resume, so the scope is
  preserved; the backward direction keeps the predecessor inside the
  scope via the predecessor lemma's @{term "set ys \<subseteq> set xs"}
  strengthening.
\<close>

theorem cyclic_segment_store_safe_iff_running_image_faithful:
  assumes closed:  "dwei_crash_closed I"
      and refines: "dwei_refines_cyclic I"
      and run0:    "exec_status (dwe_core (dwei_state I s0)) = Running"
  shows "(\<not> (\<exists>xs s c k. dwei_trace I s0 xs s \<and> DWE_Resume \<notin> set xs
               \<and> observable_mismatch (dwe_core (dwei_state I s)) c k))
         \<longleftrightarrow> (\<forall>xs s c k. dwei_trace I s0 xs s \<and> DWE_Resume \<notin> set xs
               \<and> exec_status (dwe_core (dwei_state I s)) = Running
               \<and> c \<le> exec_finish (dwe_core (dwei_state I s))
               \<longrightarrow> \<not> mismatch_at (proto_of_exec_at (dwe_core (dwei_state I s)) c) c k)"
proof
  assume safe: "\<not> (\<exists>xs s c k. dwei_trace I s0 xs s \<and> DWE_Resume \<notin> set xs
                     \<and> observable_mismatch (dwe_core (dwei_state I s)) c k)"
  show "\<forall>xs s c k. dwei_trace I s0 xs s \<and> DWE_Resume \<notin> set xs
          \<and> exec_status (dwe_core (dwei_state I s)) = Running
          \<and> c \<le> exec_finish (dwe_core (dwei_state I s))
          \<longrightarrow> \<not> mismatch_at (proto_of_exec_at (dwe_core (dwei_state I s)) c) c k"
  proof (intro allI impI, elim conjE)
    fix xs s c k
    assume tr: "dwei_trace I s0 xs s"
       and rf: "DWE_Resume \<notin> set xs"
       and run: "exec_status (dwe_core (dwei_state I s)) = Running"
       and le: "c \<le> exec_finish (dwe_core (dwei_state I s))"
    show "\<not> mismatch_at (proto_of_exec_at (dwe_core (dwei_state I s)) c) c k"
    proof
      assume mis: "mismatch_at (proto_of_exec_at (dwe_core (dwei_state I s)) c) c k"
      from closed run le obtain s' where
        step: "dwei_step I s (DWE_Label (Crash c)) s'"
        by (auto simp: dwei_crash_closed_def)
      have st: "dwe_core (dwei_state I s')
                  = (dwe_core (dwei_state I s))\<lparr>exec_status := Crashed c\<rparr>"
        by (rule dwei_crash_step_core_state[OF refines step])
      have tr': "dwei_trace I s0 (xs @ [DWE_Label (Crash c)]) s'"
        by (rule dwei_trace_append[OF tr dwei_trace.dwei_trace_step
              [OF step dwei_trace.dwei_trace_refl]])
      have rf': "DWE_Resume \<notin> set (xs @ [DWE_Label (Crash c)])"
        using rf by simp
      have obs: "observable_mismatch (dwe_core (dwei_state I s')) c k"
        using le mis by (simp add: st observable_mismatch_def)
      from tr' rf' obs safe show False by blast
    qed
  qed
next
  assume faithful:
    "\<forall>xs s c k. dwei_trace I s0 xs s \<and> DWE_Resume \<notin> set xs
       \<and> exec_status (dwe_core (dwei_state I s)) = Running
       \<and> c \<le> exec_finish (dwe_core (dwei_state I s))
       \<longrightarrow> \<not> mismatch_at (proto_of_exec_at (dwe_core (dwei_state I s)) c) c k"
  show "\<not> (\<exists>xs s c k. dwei_trace I s0 xs s \<and> DWE_Resume \<notin> set xs
             \<and> observable_mismatch (dwe_core (dwei_state I s)) c k)"
  proof
    assume "\<exists>xs s c k. dwei_trace I s0 xs s \<and> DWE_Resume \<notin> set xs
              \<and> observable_mismatch (dwe_core (dwei_state I s)) c k"
    then obtain xs s c k where
        tr: "dwei_trace I s0 xs s"
      and rf: "DWE_Resume \<notin> set xs"
      and obs: "observable_mismatch (dwe_core (dwei_state I s)) c k"
      by blast
    from obs have crashed: "exec_status (dwe_core (dwei_state I s)) = Crashed c"
      and le_fin: "c \<le> exec_finish (dwe_core (dwei_state I s))"
      and mis: "mismatch_at (proto_of_exec_at (dwe_core (dwei_state I s)) c) c k"
      by (auto simp: observable_mismatch_def)
    have disj:
      "(\<exists>ys s_pre. dwei_trace I s0 ys s_pre
           \<and> set ys \<subseteq> set xs
           \<and> exec_status (dwe_core (dwei_state I s_pre)) = Running
           \<and> proto_of_exec_at (dwe_core (dwei_state I s_pre)) c
               = proto_of_exec_at (dwe_core (dwei_state I s)) c)
     \<or> (exec_status (dwe_core (dwei_state I s0)) = Crashed c
           \<and> proto_of_exec_at (dwe_core (dwei_state I s0)) c
               = proto_of_exec_at (dwe_core (dwei_state I s)) c)"
      using cyclic_crashed_has_running_predecessor_or_crashed_start[OF tr]
            refines crashed
      by blast
    from disj show False
    proof
      assume "\<exists>ys s_pre. dwei_trace I s0 ys s_pre
                \<and> set ys \<subseteq> set xs
                \<and> exec_status (dwe_core (dwei_state I s_pre)) = Running
                \<and> proto_of_exec_at (dwe_core (dwei_state I s_pre)) c
                    = proto_of_exec_at (dwe_core (dwei_state I s)) c"
      then obtain ys s_pre where
          p_tr: "dwei_trace I s0 ys s_pre"
        and p_sub: "set ys \<subseteq> set xs"
        and p_run: "exec_status (dwe_core (dwei_state I s_pre)) = Running"
        and p_proto: "proto_of_exec_at (dwe_core (dwei_state I s_pre)) c
                        = proto_of_exec_at (dwe_core (dwei_state I s)) c"
        by blast
      have p_rf: "DWE_Resume \<notin> set ys"
        using rf p_sub by blast
      have p_mis: "mismatch_at (proto_of_exec_at (dwe_core (dwei_state I s_pre)) c) c k"
        using mis p_proto by simp
      have p_fin: "exec_finish (dwe_core (dwei_state I s_pre))
                     = exec_finish (dwe_core (dwei_state I s))"
        using p_proto by (simp add: proto_of_exec_at_def)
      have p_le: "c \<le> exec_finish (dwe_core (dwei_state I s_pre))"
        using le_fin p_fin by simp
      have "dwei_trace I s0 ys s_pre \<and> DWE_Resume \<notin> set ys
              \<and> exec_status (dwe_core (dwei_state I s_pre)) = Running
              \<and> c \<le> exec_finish (dwe_core (dwei_state I s_pre))"
        using p_tr p_rf p_run p_le by blast
      then have "\<not> mismatch_at (proto_of_exec_at (dwe_core (dwei_state I s_pre)) c) c k"
        by (rule faithful[rule_format])
      with p_mis show False by simp
    next
      assume "exec_status (dwe_core (dwei_state I s0)) = Crashed c
                \<and> proto_of_exec_at (dwe_core (dwei_state I s0)) c
                    = proto_of_exec_at (dwe_core (dwei_state I s)) c"
      then have "exec_status (dwe_core (dwei_state I s0)) = Crashed c" by simp
      with run0 show False by simp
    qed
  qed
qed

section \<open>Epoch and scope bookkeeping at the implementation level\<close>

text \<open>
  The implementation-level consumption of the banked epoch-factorization
  interface: along a Resume-free implementation trace the epoch is
  constant, by the banked per-rule facts
  @{thm [source] dwe_step_epoch_const} /
  @{thm [source] emitting_reconcile_epoch_const}.  The scope-constancy
  twin feeds the empty-scope safe-side inhabitant below; its
  machine-trace-level counterpart is one conjunct of the banked
  @{thm [source] dwe_trace_core_frame} (cited, not restated --- this is
  the dwei-level lift only).
\<close>

lemma dwei_no_resume_epoch_const:
  assumes refines: "dwei_refines_cyclic I"
      and tr: "dwei_trace I s xs s'"
      and rf: "DWE_Resume \<notin> set xs"
  shows "dwe_epoch (dwei_state I s') = dwe_epoch (dwei_state I s)"
  using tr rf refines
proof (induction rule: dwei_trace.induct)
  case (dwei_trace_refl I s)
  show ?case by simp
next
  case (dwei_trace_step I s a s' as s'')
  have refines': "dwei_refines_cyclic I"
    using dwei_trace_step.prems(2) .
  have rf_a: "a \<noteq> DWE_Resume" and rf_as: "DWE_Resume \<notin> set as"
    using dwei_trace_step.prems(1) by auto
  have step_const: "dwe_epoch (dwei_state I s') = dwe_epoch (dwei_state I s)"
  proof (cases a)
    case (DWE_Label l)
    with dwei_trace_step.hyps(1) have "dwei_step I s (DWE_Label l) s'" by simp
    then have "dwe_step (dwei_state I s) l (dwei_state I s')"
      by (rule dwei_refines_cyclicD_label[OF refines'])
    then show ?thesis by (rule dwe_step_epoch_const)
  next
    case (DWE_Reconcile m f)
    with dwei_trace_step.hyps(1) have "dwei_step I s (DWE_Reconcile m f) s'" by simp
    then have "emitting_reconcile m (dwei_state I s) f (dwei_state I s')"
      by (rule dwei_refines_cyclicD_reconcile[OF refines'])
    then show ?thesis by (rule emitting_reconcile_epoch_const)
  next
    case DWE_Resume
    with rf_a show ?thesis by simp
  qed
  from dwei_trace_step.IH[OF rf_as refines'] step_const show ?case by simp
qed

lemma dwei_trace_scope_const:
  assumes refines: "dwei_refines_cyclic I"
      and tr: "dwei_trace I s xs s'"
  shows "exec_scope (dwe_core (dwei_state I s'))
           = exec_scope (dwe_core (dwei_state I s))"
  using tr refines
proof (induction rule: dwei_trace.induct)
  case (dwei_trace_refl I s)
  show ?case by simp
next
  case (dwei_trace_step I s a s' as s'')
  have refines': "dwei_refines_cyclic I"
    using dwei_trace_step.prems .
  have step_const: "exec_scope (dwe_core (dwei_state I s'))
                      = exec_scope (dwe_core (dwei_state I s))"
  proof (cases a)
    case (DWE_Label l)
    with dwei_trace_step.hyps(1) have "dwei_step I s (DWE_Label l) s'" by simp
    then have "dwe_step (dwei_state I s) l (dwei_state I s')"
      by (rule dwei_refines_cyclicD_label[OF refines'])
    then show ?thesis
      by (rule dw_exec_step_scope[OF dwe_step_core])
  next
    case (DWE_Reconcile m f)
    with dwei_trace_step.hyps(1) have "dwei_step I s (DWE_Reconcile m f) s'" by simp
    then have "emitting_reconcile m (dwei_state I s) f (dwei_state I s')"
      by (rule dwei_refines_cyclicD_reconcile[OF refines'])
    then show ?thesis by (rule emitting_reconcile_scope_same)
  next
    case DWE_Resume
    with dwei_trace_step.hyps(1) have "dwei_step I s DWE_Resume s'" by simp
    then have "dwe_resume (dwei_state I s) (dwei_state I s')"
      by (rule dwei_refines_cyclicD_resume[OF refines'])
    then show ?thesis by (rule dwe_resume_scope_same)
  qed
  from dwei_trace_step.IH[OF refines'] step_const show ?case by simp
qed

section \<open>Non-vacuity: the stale-heal witness chain\<close>

text \<open>
  The pinned machine's own realization of the seam family, and the
  UNSAFE-side inhabitant of the biconditional: reconcile the banked
  loaded-window crash state @{const t_mid_w} at the STALE frontier
  @{const ec1} with the warm cursor @{term "m = (1::nat)"} (appends
  nothing --- effect-SAFE), Resume into epoch 1, crash at @{const ec2}.
  The resulting Running state @{text stale_run1_w} is reachable, epoch 1,
  and carries a genuine scoped mismatch at @{const ec2} (the un-replayed
  committed event 2) --- the state family one might expect to break the
  forward direction.  It does NOT: under the unrestricted-\<open>\<forall>\<close>
  crash-closure mirror, @{term "Crash ec2"} is enabled there, and
  @{text stale_crash1_w} is an observable bad crash --- both sides of
  the biconditional go false TOGETHER.  The premise excludes only
  implementations that forbid crashing post-Resume, exactly as in the
  landed theorem (a premise, not a defect).

  Naming per the wave gate (finding F1): the Segments foundation's
  @{const r_run1_w} is a DIFFERENT epoch-1 witness (a diverging segment
  start where no reconcile ever ran); this chain is the stale HEAL
  (store-bad yet effect-clean), landed as @{text stale_heal_w} /
  @{text stale_run1_w} / @{text stale_crash1_w}.  The third member of the
  trio, the tightness theory's in-segment recurrence witness
  @{text f_mis_w}, lives with its consumers.
\<close>

definition stale_heal_w :: "(nat, nat) dwe_state" where
  "stale_heal_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1)]
                         [(ec1, e1), (ec2, e2)] {} Recovered)
                      [(1, 0, ec1, e1)] 0"

definition stale_run1_w :: "(nat, nat) dwe_state" where
  "stale_run1_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1)]
                         [(ec1, e1), (ec2, e2)] {} Running)
                      [(1, 0, ec1, e1)] 1"

definition stale_crash1_w :: "(nat, nat) dwe_state" where
  "stale_crash1_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1)]
                           [(ec1, e1), (ec2, e2)] {} (Crashed ec2))
                        [(1, 0, ec1, e1)] 1"

lemmas stale_state_defs = stale_heal_w_def stale_run1_w_def stale_crash1_w_def

lemma rec_stale: "emitting_reconcile 1 t_mid_w ec1 stale_heal_w"
  by (simp add: emitting_reconcile_def t_mid_w_def stale_heal_w_def
                mkT_def mkC_def replay_down_hist_def e1_def e2_def ec_defs
                eval_nat_numeral)

lemma res_stale: "dwe_resume stale_heal_w stale_run1_w"
  by (simp add: dwe_resume_def stale_heal_w_def stale_run1_w_def
                mkT_def mkC_def eval_nat_numeral)

lemma wf_stale_run1: "wellformed_exec_state (dwe_core stale_run1_w)"
  by (simp add: stale_run1_w_def mkT_def mkC_def ws_defs wf_hist_Nil
                wfh_e1 wfh_pair)

lemma g_stale_run1_crash:
  "exec_label_preserves_history_wf (dwe_core stale_run1_w) (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma wsr1: "dwe_step stale_run1_w (Crash ec2) stale_crash1_w"
proof -
  have c: "dw_exec_step (dwe_core stale_run1_w) (Crash ec2)
             (dwe_core stale_crash1_w)"
    by (rule crashI) (simp_all add: stale_run1_w_def stale_crash1_w_def
                                    mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c])
       (simp_all add: stale_run1_w_def stale_crash1_w_def mkT_def)
qed

lemma reach_stale_heal: "dwe_reachable stale_heal_w"
  by (rule dwe_reachable_reconcile_ext[OF reach_t_mid rec_stale])

lemma reach_stale_run1: "dwe_reachable stale_run1_w"
  by (rule dwe_reachable_resume_ext[OF reach_stale_heal res_stale])

lemma reach_stale_crash1: "dwe_reachable stale_crash1_w"
  by (rule dwe_reachable_label_ext[OF reach_stale_run1 wf_stale_run1
        g_stale_run1_crash wsr1])

lemma stale_run1_mismatch:
  "mismatch_at (proto_of_exec_at (dwe_core stale_run1_w) ec2) ec2 1"
  by (simp add: stale_run1_w_def eval_defs eval_nat_numeral)

lemma stale_crash1_obs:
  "observable_mismatch (dwe_core stale_crash1_w) ec2 1"
  by (simp add: observable_mismatch_def stale_crash1_w_def eval_defs
                eval_nat_numeral)

lemma stale_run1_not_unsafe: "\<not> effect_unsafe stale_run1_w"
  by (simp add: effect_unsafe_def premature_def duplicate_def justified_at_def
                stale_run1_w_def mkT_def mkC_def e1_def e2_def ec_defs
                eval_nat_numeral)

lemma stale_crash1_not_unsafe: "\<not> effect_unsafe stale_crash1_w"
  by (simp add: effect_unsafe_def premature_def duplicate_def justified_at_def
                stale_crash1_w_def mkT_def mkC_def e1_def e2_def ec_defs
                eval_nat_numeral)

theorem post_resume_running_unfaithful:
  "dwe_reachable stale_run1_w
 \<and> exec_status (dwe_core stale_run1_w) = Running
 \<and> dwe_epoch stale_run1_w = 1
 \<and> mismatch_at (proto_of_exec_at (dwe_core stale_run1_w) ec2) ec2 1
 \<and> \<not> effect_unsafe stale_run1_w"
  by (intro conjI reach_stale_run1 stale_run1_mismatch stale_run1_not_unsafe)
     (simp_all add: stale_run1_w_def mkT_def mkC_def)

theorem post_resume_observable_bad_crash:
  "dwe_reachable stale_crash1_w
 \<and> observable_mismatch (dwe_core stale_crash1_w) ec2 1
 \<and> dwe_epoch stale_crash1_w = 1
 \<and> \<not> effect_unsafe stale_crash1_w"
  by (intro conjI reach_stale_crash1 stale_crash1_obs stale_crash1_not_unsafe)
     (simp_all add: stale_crash1_w_def mkT_def)

section \<open>Non-vacuity: the empty-scope safe-side inhabitant\<close>

text \<open>
  A crash-closed, refining, Running-start, store-SAFE inhabitant ---
  THROUGH the full cyclic grammar (its traces may reconcile and Resume
  at will): with an empty monitored scope no key is ever in scope, scope
  is constant along every cyclic implementation trace
  (@{thm [source] dwei_trace_scope_const}), so faithfulness is trivial
  and the backward direction yields store-safety.  This also exercises
  the backward theorem.
\<close>

lemma cyclic_empty_scope_running_image_faithful:
  "cyclic_running_image_faithful
     (canonical_dwe_implementation (dwe_init (\<lambda>_. None) ({}::nat set) fin))"
  unfolding cyclic_running_image_faithful_def
proof (intro allI impI, elim conjE)
  fix xs s c k
  let ?I = "canonical_dwe_implementation (dwe_init (\<lambda>_. None) ({}::nat set) fin)"
  assume tr: "dwei_trace ?I (dwei_initial ?I) xs s"
  from dwei_trace_scope_const[OF canonical_dwe_implementation_refines_cyclic tr]
  have sc: "exec_scope (dwe_core (dwei_state ?I s)) = {}"
    by (simp add: canonical_dwe_implementation_def dwe_init_def
                  initial_exec_state_def)
  show "\<not> mismatch_at (proto_of_exec_at (dwe_core (dwei_state ?I s)) c) c k"
    by (simp add: mismatch_at_def proto_of_exec_at_def sc)
qed

theorem cyclic_empty_scope_inhabits_safe_side:
  "dwei_crash_closed
     (canonical_dwe_implementation (dwe_init (\<lambda>_. None) ({}::nat set) fin))
 \<and> dwei_refines_cyclic
     (canonical_dwe_implementation (dwe_init (\<lambda>_. None) ({}::nat set) fin))
 \<and> exec_status (dwe_core (dwei_state
       (canonical_dwe_implementation (dwe_init (\<lambda>_. None) ({}::nat set) fin))
       (dwei_initial
         (canonical_dwe_implementation (dwe_init (\<lambda>_. None) ({}::nat set) fin)))))
     = Running
 \<and> \<not> cyclic_has_reachable_observable_bad_crash
       (canonical_dwe_implementation (dwe_init (\<lambda>_. None) ({}::nat set) fin))"
proof (intro conjI)
  show "dwei_crash_closed
          (canonical_dwe_implementation (dwe_init (\<lambda>_. None) ({}::nat set) fin))"
    by (rule canonical_dwe_implementation_crash_closed)
  show "dwei_refines_cyclic
          (canonical_dwe_implementation (dwe_init (\<lambda>_. None) ({}::nat set) fin))"
    by (rule canonical_dwe_implementation_refines_cyclic)
  show "exec_status (dwe_core (dwei_state
          (canonical_dwe_implementation (dwe_init (\<lambda>_. None) ({}::nat set) fin))
          (dwei_initial
            (canonical_dwe_implementation (dwe_init (\<lambda>_. None) ({}::nat set) fin)))))
        = Running"
    by (simp add: canonical_dwe_implementation_def dwe_init_core_running)
  show "\<not> cyclic_has_reachable_observable_bad_crash
          (canonical_dwe_implementation (dwe_init (\<lambda>_. None) ({}::nat set) fin))"
    by (rule cyclic_running_image_faithful_running_start_imp_store_safe
          [OF canonical_dwe_implementation_refines_cyclic _
              cyclic_empty_scope_running_image_faithful])
       (simp add: canonical_dwe_implementation_def dwe_init_core_running)
qed

section \<open>Tightness controls for the new premise triple (gate addendum)\<close>

text \<open>
  The biconditional's premise triple (@{const dwei_crash_closed},
  @{const dwei_refines_cyclic}, start-Running) is NEW --- it lives at the
  @{type dwe_implementation} record type, where the landed tier-1
  tightness controls cannot see it (the type-level-escape lesson).  Per
  the wave gate's mandate, each of the three premises is witnessed
  load-bearing HERE, at this record type, by a mirrored control: the
  landed @{text running_start_is_load_bearing} /
  @{text crash_closed_is_load_bearing} /
  @{text refinement_drop_falsifies_forward} shapes one type up.  All
  witness ingredients are banked machine states; no control claims more
  than the five-conjunct cell it inhabits.
\<close>

text \<open>@{const W4} is the machine's own Running loaded-window state: the
  in-flight second commit gives a scoped mismatch at @{const ec2} with
  status still Running.  (Together with the banked
  @{thm [source] t_mid_mismatch} this is also the machine-level
  degeneracy datum quoted in the disclosure block above.)\<close>

lemma W4_running_mismatch:
  "mismatch_at (proto_of_exec_at (dwe_core W4) ec2) ec2 1"
  by (simp add: W4_def eval_defs eval_nat_numeral)

subsection \<open>Control 1: Running-start is load-bearing\<close>

text \<open>
  Unit-typed implementation pinned at the banked crashed state
  @{const t_mid_w} with an EMPTY step relation: crash-closure and
  refinement hold vacuously, faithfulness holds vacuously (no reachable
  Running state), yet the refl trace already sits at an observable bad
  crash --- so the backward direction would FAIL without the
  Running-start premise.  Five-conjunct mirror of the landed
  @{text running_start_is_load_bearing}.
\<close>

definition I_dwei_crashed_start :: "(unit, nat, nat) dwe_implementation" where
  "I_dwei_crashed_start =
     \<lparr> dwei_initial = (),
       dwei_step = (\<lambda>s a s'. False),
       dwei_state = (\<lambda>_. t_mid_w) \<rparr>"

lemma I_dwei_crashed_start_state [simp]:
  "dwei_state I_dwei_crashed_start s = t_mid_w"
  by (simp add: I_dwei_crashed_start_def)

lemma I_dwei_crashed_start_crash_closed:
  "dwei_crash_closed I_dwei_crashed_start"
  by (simp add: dwei_crash_closed_def t_mid_w_def mkT_def mkC_def)

lemma I_dwei_crashed_start_refines:
  "dwei_refines_cyclic I_dwei_crashed_start"
  by (simp add: dwei_refines_cyclic_def I_dwei_crashed_start_def)

lemma I_dwei_crashed_start_faithful:
  "cyclic_running_image_faithful I_dwei_crashed_start"
  unfolding cyclic_running_image_faithful_def
  by (simp add: t_mid_w_def mkT_def mkC_def)

lemma I_dwei_crashed_start_unsafe:
  "cyclic_has_reachable_observable_bad_crash I_dwei_crashed_start"
proof -
  have tr: "dwei_trace I_dwei_crashed_start (dwei_initial I_dwei_crashed_start)
              [] (dwei_initial I_dwei_crashed_start)"
    by (rule dwei_trace.dwei_trace_refl)
  have obs: "observable_mismatch (dwe_core (dwei_state I_dwei_crashed_start
               (dwei_initial I_dwei_crashed_start))) ec2 1"
    using t_mid_mismatch by simp
  have div: "diverges (proto_of_exec_at (dwe_core (dwei_state I_dwei_crashed_start
               (dwei_initial I_dwei_crashed_start))) ec2) ec2"
    by (rule observable_mismatch_imp_diverges[OF obs])
  from tr obs div show ?thesis
    unfolding cyclic_has_reachable_observable_bad_crash_def
              cyclic_reachable_observable_bad_crash_def
    by blast
qed

lemma I_dwei_crashed_start_not_running:
  "exec_status (dwe_core (dwei_state I_dwei_crashed_start
     (dwei_initial I_dwei_crashed_start))) \<noteq> Running"
  by (simp add: t_mid_w_def mkT_def mkC_def)

theorem dwei_running_start_is_load_bearing:
  "dwei_crash_closed I_dwei_crashed_start
 \<and> dwei_refines_cyclic I_dwei_crashed_start
 \<and> cyclic_running_image_faithful I_dwei_crashed_start
 \<and> cyclic_has_reachable_observable_bad_crash I_dwei_crashed_start
 \<and> exec_status (dwe_core (dwei_state I_dwei_crashed_start
       (dwei_initial I_dwei_crashed_start))) \<noteq> Running"
  by (intro conjI I_dwei_crashed_start_crash_closed I_dwei_crashed_start_refines
        I_dwei_crashed_start_faithful I_dwei_crashed_start_unsafe
        I_dwei_crashed_start_not_running)

subsection \<open>Control 2: crash-closure is load-bearing\<close>

text \<open>
  The W-chain implementation STOPPED at @{const W4}: its step relation is
  exactly the four banked label steps @{thm [source] ws1} --
  @{thm [source] ws4} and admits no Crash at all.  Refining and
  Running-start; no crashed state is reachable, hence store-SAFE; yet
  @{const W4} is a reachable Running scoped mismatch, hence NOT faithful
  --- so the forward direction would FAIL without crash-closure, which
  fails at @{const W4}.  Mirror of the landed
  @{text crash_closed_is_load_bearing}.
\<close>

definition I_dwei_w4_stop
  :: "((nat, nat) dwe_state, nat, nat) dwe_implementation"
where
  "I_dwei_w4_stop =
     \<lparr> dwei_initial = W0,
       dwei_step = (\<lambda>t a t'.
            (t = W0 \<and> a = DWE_Label (DoSource ec1 e1) \<and> t' = W1)
          \<or> (t = W1 \<and> a = DWE_Label (EnqueueDownstream ec1 e1) \<and> t' = W2)
          \<or> (t = W2 \<and> a = DWE_Label (DoDownstream ec1 e1) \<and> t' = W3)
          \<or> (t = W3 \<and> a = DWE_Label (DoSource ec2 e2) \<and> t' = W4)),
       dwei_state = (\<lambda>t. t) \<rparr>"

lemma I_dwei_w4_stop_refines: "dwei_refines_cyclic I_dwei_w4_stop"
  unfolding dwei_refines_cyclic_def
proof (intro allI impI)
  fix s a s'
  assume "dwei_step I_dwei_w4_stop s a s'"
  then show "case a of
        DWE_Label l \<Rightarrow>
          dwe_step (dwei_state I_dwei_w4_stop s) l (dwei_state I_dwei_w4_stop s')
      | DWE_Reconcile m f \<Rightarrow>
          emitting_reconcile m (dwei_state I_dwei_w4_stop s) f
            (dwei_state I_dwei_w4_stop s')
      | DWE_Resume \<Rightarrow>
          dwe_resume (dwei_state I_dwei_w4_stop s) (dwei_state I_dwei_w4_stop s')"
    using ws1 ws2 ws3 ws4 by (auto simp: I_dwei_w4_stop_def)
qed

lemma I_dwei_w4_stop_start_running:
  "exec_status (dwe_core (dwei_state I_dwei_w4_stop
     (dwei_initial I_dwei_w4_stop))) = Running"
  by (simp add: I_dwei_w4_stop_def W0_def mkT_def mkC_def)

lemma I_dwei_w4_stop_running_preserved_gen:
  assumes "dwei_trace I s xs u"
  shows "I = I_dwei_w4_stop \<longrightarrow>
           exec_status (dwe_core (dwei_state I s)) = Running \<longrightarrow>
           exec_status (dwe_core (dwei_state I u)) = Running"
  using assms
proof (induction rule: dwei_trace.induct)
  case (dwei_trace_refl I s)
  show ?case by simp
next
  case (dwei_trace_step I s a s' as s'')
  show ?case
  proof (intro impI)
    assume Ieq: "I = I_dwei_w4_stop"
       and run_s: "exec_status (dwe_core (dwei_state I s)) = Running"
    have "exec_status (dwe_core (dwei_state I s')) = Running"
      using dwei_trace_step.hyps(1) Ieq
      by (auto simp: I_dwei_w4_stop_def W1_def W2_def W3_def W4_def
                     mkT_def mkC_def)
    with dwei_trace_step.IH Ieq
    show "exec_status (dwe_core (dwei_state I s'')) = Running" by blast
  qed
qed

lemma I_dwei_w4_stop_safe:
  "\<not> cyclic_has_reachable_observable_bad_crash I_dwei_w4_stop"
proof
  assume "cyclic_has_reachable_observable_bad_crash I_dwei_w4_stop"
  then obtain xs c k s where
    "cyclic_reachable_observable_bad_crash I_dwei_w4_stop xs c k s"
    by (auto simp: cyclic_has_reachable_observable_bad_crash_def)
  then have tr: "dwei_trace I_dwei_w4_stop (dwei_initial I_dwei_w4_stop) xs s"
    and obs: "observable_mismatch (dwe_core (dwei_state I_dwei_w4_stop s)) c k"
    by (auto simp: cyclic_reachable_observable_bad_crash_def)
  have "exec_status (dwe_core (dwei_state I_dwei_w4_stop s)) = Running"
    using I_dwei_w4_stop_running_preserved_gen[OF tr]
          I_dwei_w4_stop_start_running
    by blast
  moreover from obs
  have "exec_status (dwe_core (dwei_state I_dwei_w4_stop s)) = Crashed c"
    by (simp add: observable_mismatch_def)
  ultimately show False by simp
qed

lemma I_dwei_w4_stop_trace_to_W4:
  "dwei_trace I_dwei_w4_stop W0
     [DWE_Label (DoSource ec1 e1), DWE_Label (EnqueueDownstream ec1 e1),
      DWE_Label (DoDownstream ec1 e1), DWE_Label (DoSource ec2 e2)] W4"
proof -
  have s1: "dwei_step I_dwei_w4_stop W0 (DWE_Label (DoSource ec1 e1)) W1"
    by (simp add: I_dwei_w4_stop_def)
  have s2: "dwei_step I_dwei_w4_stop W1 (DWE_Label (EnqueueDownstream ec1 e1)) W2"
    by (simp add: I_dwei_w4_stop_def)
  have s3: "dwei_step I_dwei_w4_stop W2 (DWE_Label (DoDownstream ec1 e1)) W3"
    by (simp add: I_dwei_w4_stop_def)
  have s4: "dwei_step I_dwei_w4_stop W3 (DWE_Label (DoSource ec2 e2)) W4"
    by (simp add: I_dwei_w4_stop_def)
  show ?thesis
    by (rule dwei_trace.dwei_trace_step[OF s1
          dwei_trace.dwei_trace_step[OF s2
            dwei_trace.dwei_trace_step[OF s3
              dwei_trace.dwei_trace_step[OF s4 dwei_trace.dwei_trace_refl]]]])
qed

lemma I_dwei_w4_stop_not_faithful:
  "\<not> cyclic_running_image_faithful I_dwei_w4_stop"
proof
  assume rif: "cyclic_running_image_faithful I_dwei_w4_stop"
  have tr: "dwei_trace I_dwei_w4_stop (dwei_initial I_dwei_w4_stop)
              [DWE_Label (DoSource ec1 e1), DWE_Label (EnqueueDownstream ec1 e1),
               DWE_Label (DoDownstream ec1 e1), DWE_Label (DoSource ec2 e2)] W4"
    using I_dwei_w4_stop_trace_to_W4 by (simp add: I_dwei_w4_stop_def)
  have run: "exec_status (dwe_core (dwei_state I_dwei_w4_stop W4)) = Running"
    by (simp add: I_dwei_w4_stop_def W4_def mkT_def mkC_def)
  have le: "ec2 \<le> exec_finish (dwe_core (dwei_state I_dwei_w4_stop W4))"
    by (simp add: I_dwei_w4_stop_def W4_def mkT_def mkC_def)
  from rif tr run le
  have "\<not> mismatch_at (proto_of_exec_at
          (dwe_core (dwei_state I_dwei_w4_stop W4)) ec2) ec2 1"
    by (simp add: cyclic_running_image_faithful_def)
  moreover have "mismatch_at (proto_of_exec_at
          (dwe_core (dwei_state I_dwei_w4_stop W4)) ec2) ec2 1"
    using W4_running_mismatch by (simp add: I_dwei_w4_stop_def)
  ultimately show False by simp
qed

lemma I_dwei_w4_stop_not_crash_closed:
  "\<not> dwei_crash_closed I_dwei_w4_stop"
proof
  assume cc: "dwei_crash_closed I_dwei_w4_stop"
  have run: "exec_status (dwe_core (dwei_state I_dwei_w4_stop W4)) = Running"
    by (simp add: I_dwei_w4_stop_def W4_def mkT_def mkC_def)
  have le: "ec2 \<le> exec_finish (dwe_core (dwei_state I_dwei_w4_stop W4))"
    by (simp add: I_dwei_w4_stop_def W4_def mkT_def mkC_def)
  from cc run le obtain s' where
    "dwei_step I_dwei_w4_stop W4 (DWE_Label (Crash ec2)) s'"
    by (auto simp: dwei_crash_closed_def)
  then show False
    by (simp add: I_dwei_w4_stop_def)
qed

theorem dwei_crash_closed_is_load_bearing:
  "dwei_refines_cyclic I_dwei_w4_stop
 \<and> exec_status (dwe_core (dwei_state I_dwei_w4_stop
       (dwei_initial I_dwei_w4_stop))) = Running
 \<and> \<not> dwei_crash_closed I_dwei_w4_stop
 \<and> \<not> cyclic_has_reachable_observable_bad_crash I_dwei_w4_stop
 \<and> \<not> cyclic_running_image_faithful I_dwei_w4_stop"
  by (intro conjI I_dwei_w4_stop_refines I_dwei_w4_stop_start_running
        I_dwei_w4_stop_not_crash_closed I_dwei_w4_stop_safe
        I_dwei_w4_stop_not_faithful)

corollary dwei_crash_closed_drop_breaks_forward:
  "\<not> (\<forall>I :: ((nat, nat) dwe_state, nat, nat) dwe_implementation.
        dwei_refines_cyclic I
      \<and> exec_status (dwe_core (dwei_state I (dwei_initial I))) = Running
      \<and> \<not> cyclic_has_reachable_observable_bad_crash I
      \<longrightarrow> cyclic_running_image_faithful I)"
  using dwei_crash_closed_is_load_bearing by blast

subsection \<open>Control 3: refinement is load-bearing\<close>

text \<open>
  Unit-typed implementation whose state map is constantly the Running
  mismatch state @{const W4} and whose step relation admits exactly the
  Crash labels --- each such step "teleports" back to @{const W4}, which
  is no cyclic machine transition (a crash step's target core has status
  @{term "Crashed c"}, @{thm [source] dw_exec_crash_step_status}).
  Crash-closed and Running-start; store-safe (no state is ever Crashed);
  not faithful (the refl trace sits at the mismatch) --- so the forward
  direction would FAIL with only refinement dropped.  Mirror of the
  landed @{text refinement_drop_falsifies_forward}.
\<close>

definition I_dwei_unit_crash :: "(unit, nat, nat) dwe_implementation" where
  "I_dwei_unit_crash =
     \<lparr> dwei_initial = (),
       dwei_step = (\<lambda>s a s'. \<exists>c. a = DWE_Label (Crash c)),
       dwei_state = (\<lambda>_. W4) \<rparr>"

lemma I_dwei_unit_crash_state [simp]:
  "dwei_state I_dwei_unit_crash s = W4"
  by (simp add: I_dwei_unit_crash_def)

lemma I_dwei_unit_crash_crash_closed:
  "dwei_crash_closed I_dwei_unit_crash"
  by (auto simp: dwei_crash_closed_def I_dwei_unit_crash_def)

lemma I_dwei_unit_crash_start_running:
  "exec_status (dwe_core (dwei_state I_dwei_unit_crash
     (dwei_initial I_dwei_unit_crash))) = Running"
  by (simp add: W4_def mkT_def mkC_def)

lemma I_dwei_unit_crash_step:
  "dwei_step I_dwei_unit_crash () (DWE_Label (Crash ec2)) ()"
  by (simp add: I_dwei_unit_crash_def)

lemma I_dwei_unit_crash_not_refines:
  "\<not> dwei_refines_cyclic I_dwei_unit_crash"
proof
  assume "dwei_refines_cyclic I_dwei_unit_crash"
  then have "dwe_step (dwei_state I_dwei_unit_crash ()) (Crash ec2)
               (dwei_state I_dwei_unit_crash ())"
    using I_dwei_unit_crash_step by (rule dwei_refines_cyclicD_label)
  then have "dwe_step W4 (Crash ec2) W4" by simp
  then have "dw_exec_step (dwe_core W4) (Crash ec2) (dwe_core W4)"
    by (rule dwe_step_core)
  then have "exec_status (dwe_core W4) = Crashed ec2"
    by (rule dw_exec_crash_step_status)
  then show False by (simp add: W4_def mkT_def mkC_def)
qed

lemma I_dwei_unit_crash_safe:
  "\<not> cyclic_has_reachable_observable_bad_crash I_dwei_unit_crash"
proof
  assume "cyclic_has_reachable_observable_bad_crash I_dwei_unit_crash"
  then obtain xs c k s where
    "cyclic_reachable_observable_bad_crash I_dwei_unit_crash xs c k s"
    by (auto simp: cyclic_has_reachable_observable_bad_crash_def)
  then have "observable_mismatch (dwe_core (dwei_state I_dwei_unit_crash s)) c k"
    by (simp add: cyclic_reachable_observable_bad_crash_def)
  then have "exec_status (dwe_core W4) = Crashed c"
    by (simp add: observable_mismatch_def)
  then show False by (simp add: W4_def mkT_def mkC_def)
qed

lemma I_dwei_unit_crash_not_faithful:
  "\<not> cyclic_running_image_faithful I_dwei_unit_crash"
proof
  assume rif: "cyclic_running_image_faithful I_dwei_unit_crash"
  have tr: "dwei_trace I_dwei_unit_crash (dwei_initial I_dwei_unit_crash) []
              (dwei_initial I_dwei_unit_crash)"
    by (rule dwei_trace.dwei_trace_refl)
  have le: "ec2 \<le> exec_finish (dwe_core (dwei_state I_dwei_unit_crash
              (dwei_initial I_dwei_unit_crash)))"
    by (simp add: W4_def mkT_def mkC_def)
  from rif tr I_dwei_unit_crash_start_running le
  have "\<not> mismatch_at (proto_of_exec_at (dwe_core (dwei_state I_dwei_unit_crash
           (dwei_initial I_dwei_unit_crash))) ec2) ec2 1"
    by (simp add: cyclic_running_image_faithful_def)
  moreover have "mismatch_at (proto_of_exec_at (dwe_core (dwei_state I_dwei_unit_crash
           (dwei_initial I_dwei_unit_crash))) ec2) ec2 1"
    using W4_running_mismatch by simp
  ultimately show False by simp
qed

theorem dwei_refinement_drop_falsifies_forward:
  "dwei_crash_closed I_dwei_unit_crash
 \<and> exec_status (dwe_core (dwei_state I_dwei_unit_crash
       (dwei_initial I_dwei_unit_crash))) = Running
 \<and> \<not> dwei_refines_cyclic I_dwei_unit_crash
 \<and> \<not> cyclic_has_reachable_observable_bad_crash I_dwei_unit_crash
 \<and> \<not> cyclic_running_image_faithful I_dwei_unit_crash"
  by (intro conjI I_dwei_unit_crash_crash_closed I_dwei_unit_crash_start_running
        I_dwei_unit_crash_not_refines I_dwei_unit_crash_safe
        I_dwei_unit_crash_not_faithful)

corollary dwei_refinement_drop_breaks_forward:
  "\<not> (\<forall>I :: (unit, nat, nat) dwe_implementation.
        dwei_crash_closed I
      \<and> exec_status (dwe_core (dwei_state I (dwei_initial I))) = Running
      \<and> \<not> cyclic_has_reachable_observable_bad_crash I
      \<longrightarrow> cyclic_running_image_faithful I)"
  using dwei_refinement_drop_falsifies_forward by blast

corollary dwei_refinement_drop_falsifies_biconditional:
  "\<not> ((\<not> cyclic_has_reachable_observable_bad_crash I_dwei_unit_crash)
        \<longleftrightarrow> cyclic_running_image_faithful I_dwei_unit_crash)"
  using dwei_refinement_drop_falsifies_forward by blast

end
