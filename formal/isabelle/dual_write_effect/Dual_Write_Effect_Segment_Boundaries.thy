(*  Title:       Dual_Write_Effect_Segment_Boundaries.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE TWO EDGES OF AN EPOCH SEGMENT (S4d sites 2 + 4): how a segment
    ENDS at a Recovered state --- the landed recovered_cannot_do_* pair
    holds VERBATIM at every Recovered cyclic state in every epoch, and
    within a resume-free segment a Recovered state is literally
    IDENTITY-TERMINAL (t' = t, stronger than the landed reading) --- and
    how the next segment STARTS Running: the landed converse framework's
    Running-start premise is dischargeable BY CONSTRUCTION at every
    segment start, so the tier-1 two-sided characterization re-founds at
    each epoch through the landed framework's own parametric start slot,
    while its load-bearing control (rebuilt on a REACHABLE cyclic core)
    and the honest not-clean boundary certificate price exactly what
    that premise does and does not buy.

    RESTATEMENT CARRIER, never an upgrade: every trace-level statement
    carries its scope in the name (the recovered_segment_ and
    post_resume_segment_ prefixes); segment-scoped facts are
    restatements with disclosed scope, and segment-scoped safety is
    never full-trace safety.  The designed negative control recovered_not_absorbing_cyclic
    is G5 content restated as a boundary certificate for this theory's
    scoping --- the machine's designed purpose, never a discovered
    surprise and never a defect of the landed tier.

    Produced by the S4d proof-wave P2 prover per the committed design
    (paper/dual_write/phase3/s4d_design/site_2_4_boundaries.md), with
    the coherence gate's canonicalizations applied: F4 --- the
    segment-start definition lives in Dual_Write_Effect_Segments and is
    cited, not redefined; F5 --- the converse theory's characterization
    form is a COMPLEMENT, cross-referenced in text, neither form
    consumes the other; gate section 2.6 --- the shared-wave copies of
    resume_crossing_inventory and effect_unsafe_trace_monotone land
    HERE, single-owner, because this lane's design file holds their
    pinned shapes.  The scratch original's in-source ML oracle gates are STRIPPED here:
    oracle-freedom is certified by scratch-side per-slice gate sessions
    with confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Segment_Boundaries
  imports Dual_Write_Effect_Segments "Dual_Write_Core.Dual_Write_Converse"
begin

section \<open>SITE 2 --- per-segment terminality at Recovered\<close>

text \<open>
  CROSS-MACHINE CAVEAT (disclosed; flagged for the grammar site): the
  LANDED core reconcile @{const recovery_reconcile_step} also fires from
  Recovered (rule @{text reconcile_from_recovered} --- the landed
  Recovered-heal path), while the cyclic wrapper's
  @{const emitting_reconcile} is Crashed-only by the pinned phase-2
  spec.  Every ``reconcile is disabled from Recovered'' fact below is
  therefore a fact about the CYCLIC WRAPPER rule --- new machine
  content --- and must never be presented as a transferred tier-1 fact.
  The tier-1 content that DOES transfer verbatim here is exactly the
  label-step pair @{thm [source] recovered_cannot_do_downstream} /
  @{thm [source] recovered_cannot_do_source}: @{const dwe_step} only
  lifts @{const dw_exec_step} labels (Resume is a separate transition
  relation, not a label step), so the landed pair applies through the
  projection at every Recovered wrapper state, in every epoch, with no
  trace hypothesis.
\<close>

subsection \<open>The landed terminality pair, verbatim through the projection\<close>

lemma recovered_cannot_publish_cyclic:
  assumes "exec_status (dwe_core t) = Recovered"
  shows "\<not> dwe_step t (DoDownstream c e) t'"
proof
  assume "dwe_step t (DoDownstream c e) t'"
  then have "dw_exec_step (dwe_core t) (DoDownstream c e) (dwe_core t')"
    by (rule dwe_step_core)
  with recovered_cannot_do_downstream[OF assms] show False by blast
qed

lemma recovered_cannot_source_cyclic:
  assumes "exec_status (dwe_core t) = Recovered"
  shows "\<not> dwe_step t (DoSource c e) t'"
proof
  assume "dwe_step t (DoSource c e) t'"
  then have "dw_exec_step (dwe_core t) (DoSource c e) (dwe_core t')"
    by (rule dwe_step_core)
  with recovered_cannot_do_source[OF assms] show False by blast
qed

subsection \<open>Per-step absorption and its maximal sharpening\<close>

lemma dwe_step_recovered_stays:
  assumes "dwe_step t a t'"
      and "exec_status (dwe_core t) = Recovered"
  shows "exec_status (dwe_core t') = Recovered"
  by (rule recovered_stays_recovered[OF dwe_step_core[OF assms(1)] assms(2)])

text \<open>
  The core-level sharpening behind the wrapper identity: from Recovered,
  the ONLY enabled landed core step is the identity observe --- every
  other rule of @{const dw_exec_step} requires status Running or
  @{term "Crashed c"}.
\<close>

lemma recovered_core_label_step_identity:
  assumes "dw_exec_step s a s'"
      and "exec_status s = Recovered"
  shows "s' = s \<and> (\<exists>f. a = Observe f)"
  using assms by (cases rule: dw_exec_step.cases) auto

text \<open>
  The honest sharpest per-step form: from Recovered, wrapper label steps
  can only STUTTER (identity observe).  This extends
  @{thm [source] recovered_stays_recovered} from status preservation to
  whole-state preservation at the wrapper level.
\<close>

lemma recovered_label_step_identity:
  assumes step: "dwe_step t a t'"
      and rec: "exec_status (dwe_core t) = Recovered"
  shows "t' = t \<and> (\<exists>f. a = Observe f)"
  using step
proof (cases rule: dwe_step.cases)
  case (lift_nonpub c')
  have core: "dw_exec_step (dwe_core t) a c'" by fact
  have t'_eq: "t' = t\<lparr>dwe_core := c'\<rparr>" by fact
  from recovered_core_label_step_identity[OF core rec]
  have c'_eq: "c' = dwe_core t" and obs: "\<exists>f. a = Observe f" by blast+
  have "t' = t" unfolding t'_eq c'_eq by simp
  with obs show ?thesis by blast
next
  case (publish_emit c e c')
  have "dw_exec_step (dwe_core t) (DoDownstream c e) c'" by fact
  with recovered_cannot_do_downstream[OF rec] show ?thesis by blast
qed

subsection \<open>Rule-enabledness at Recovered\<close>

lemma emitting_reconcile_requires_crashed:
  assumes "emitting_reconcile m t f t'"
  shows "\<exists>c. exec_status (dwe_core t) = Crashed c"
  using assms by (auto simp: emitting_reconcile_def)

corollary recovered_cannot_reconcile_cyclic:
  assumes "exec_status (dwe_core t) = Recovered"
  shows "\<not> emitting_reconcile m t f t'"
proof
  assume "emitting_reconcile m t f t'"
  from emitting_reconcile_requires_crashed[OF this] obtain c
    where "exec_status (dwe_core t) = Crashed c" by blast
  with assms show False by simp
qed

lemma dwe_resume_requires_recovered:
  assumes "dwe_resume t t'"
  shows "exec_status (dwe_core t) = Recovered"
  using assms by (simp add: dwe_resume_def)

subsection \<open>The Resume crossing inventory (shared with site 4)\<close>

text \<open>
  Resume changes EXACTLY the status field and the epoch counter: every
  durable core field and the whole emission ledger cross the segment
  boundary unchanged --- the record equation below is the complete
  inventory, nothing else moves.  This is the shared-wave copy mandated
  by the gate (section 2.6): sites 2 and 4 and the prose surfaces all
  cite it from here.
\<close>

theorem resume_crossing_inventory:
  assumes "dwe_resume t t'"
  shows "exec_status (dwe_core t) = Recovered
       \<and> dwe_core t' = (dwe_core t)\<lparr>exec_status := Running\<rparr>
       \<and> dwe_epoch t' = Suc (dwe_epoch t)
       \<and> dwe_emitted t' = dwe_emitted t"
  using assms by (simp add: dwe_resume_def)

subsection \<open>The single-transition exit classification\<close>

text \<open>From Recovered, every transition of the machine either stutters
  or IS the Resume.\<close>

theorem recovered_exit_classification:
  assumes rec: "exec_status (dwe_core t) = Recovered"
      and tr: "dwe_step t a t' \<or> emitting_reconcile m t f t' \<or> dwe_resume t t'"
  shows "t' = t
       \<or> (dwe_resume t t'
            \<and> exec_status (dwe_core t') = Running
            \<and> dwe_epoch t' = Suc (dwe_epoch t)
            \<and> dwe_emitted t' = dwe_emitted t)"
  using tr
proof (elim disjE)
  assume "dwe_step t a t'"
  from recovered_label_step_identity[OF this rec] show ?thesis by blast
next
  assume "emitting_reconcile m t f t'"
  with recovered_cannot_reconcile_cyclic[OF rec] show ?thesis by blast
next
  assume res: "dwe_resume t t'"
  have "exec_status (dwe_core t') = Running"
    by (rule post_resume_core_running[OF res])
  with res dwe_resume_epoch_Suc[OF res] dwe_resume_emitted_same[OF res]
  show ?thesis by blast
qed

subsection \<open>Per-segment terminality: the landed reading, strengthened per segment\<close>

text \<open>
  Within a resume-free segment, a Recovered state is LITERALLY terminal:
  not merely ``no DoDownstream / DoSource'' (the landed reading) but no
  state change at all --- the strongest true restatement, subsuming
  per-segment status absorption, ledger freeze, and epoch constancy in
  one equation.  Disclosed strengthening, per segment only: the
  unscoped whole-trace form is FALSE on this machine (the designed
  negative control at the end of this section).
\<close>

theorem recovered_segment_terminal:
  assumes "dwe_temporal_trace t xs t'"
      and "resume_free xs"
      and "exec_status (dwe_core t) = Recovered"
  shows "t' = t"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  show ?case by (rule refl)
next
  case (dwe_label_step t a t' as t'')
  from recovered_label_step_identity[OF dwe_label_step.hyps(3)
        dwe_label_step.prems(2)]
  have t'_eq: "t' = t" by blast
  have "t'' = t'"
    by (rule dwe_label_step.IH)
       (use dwe_label_step.prems t'_eq in simp_all)
  with t'_eq show ?case by simp
next
  case (dwe_reconcile_step m t f t' as t'')
  from recovered_cannot_reconcile_cyclic[OF dwe_reconcile_step.prems(2)]
       dwe_reconcile_step.hyps(1)
  show ?case by blast
next
  case (dwe_resume_step t t' as t'')
  from dwe_resume_step.prems(1) show ?case by simp
qed

corollary recovered_segment_absorbing:
  assumes "dwe_temporal_trace t xs t'"
      and "resume_free xs"
      and "exec_status (dwe_core t) = Recovered"
  shows "exec_status (dwe_core t') = Recovered"
  using recovered_segment_terminal[OF assms] assms(3) by simp

corollary recovered_segment_ledger_frozen:
  assumes "dwe_temporal_trace t xs t'"
      and "resume_free xs"
      and "exec_status (dwe_core t) = Recovered"
  shows "dwe_emitted t' = dwe_emitted t"
  using recovered_segment_terminal[OF assms] by simp

subsection \<open>The trace-level only-exit theorem\<close>

text \<open>
  Any activity whatsoever out of a Recovered state --- in particular
  re-entering Running --- passes through Resume, hence (with
  @{thm [source] dwe_trace_epoch_mono} and
  @{thm [source] dwe_resume_epoch_Suc}) strictly increments the epoch.
  Combine with @{thm [source] resume_crossing_inventory} for the
  epoch-increment-plus-what-survives reading.
\<close>

theorem recovered_only_exit_is_resume:
  assumes tr: "dwe_temporal_trace t xs t'"
      and rec: "exec_status (dwe_core t) = Recovered"
      and ne: "t' \<noteq> t"
  shows "DWE_Resume \<in> set xs"
proof (rule ccontr)
  assume "DWE_Resume \<notin> set xs"
  then have "t' = t" by (rule recovered_segment_terminal[OF tr _ rec])
  with ne show False by simp
qed

corollary recovered_status_change_needs_resume:
  assumes tr: "dwe_temporal_trace t xs t'"
      and rec: "exec_status (dwe_core t) = Recovered"
      and ch: "exec_status (dwe_core t') \<noteq> Recovered"
  shows "DWE_Resume \<in> set xs"
proof (rule recovered_only_exit_is_resume[OF tr rec])
  show "t' \<noteq> t" using ch rec by auto
qed

subsection \<open>The designed negative control\<close>

text \<open>
  THE UNSCOPED RESTATEMENT IS FALSE --- by design.  ``Once Recovered,
  always Recovered'' fails over full cyclic traces: the banked witness
  chain @{const t_fin_w} (Recovered, reachable) crosses by
  @{const dwe_resume} into @{const f_run_w} (Running, reachable).  This
  is the DESIGNED seam: Resume exists precisely to break terminal
  absorption (the promoted cycle, G5), so this control is banked
  content restated as a boundary certificate for the scoping of the
  section above --- never a discovered surprise, never a defect of the
  landed tier.  The honest residue is exact:
  @{thm [source] recovered_exit_classification},
  @{thm [source] recovered_only_exit_is_resume},
  @{thm [source] resume_crossing_inventory}.
\<close>

theorem recovered_not_absorbing_cyclic:
  "\<exists>t t'. dwe_reachable t \<and> dwe_reachable t'
        \<and> exec_status (dwe_core t) = Recovered
        \<and> dwe_resume t t'
        \<and> exec_status (dwe_core t') = Running"
proof -
  have "dwe_reachable t_fin_w \<and> dwe_reachable f_run_w
      \<and> exec_status (dwe_core t_fin_w) = Recovered
      \<and> dwe_resume t_fin_w f_run_w
      \<and> exec_status (dwe_core f_run_w) = Running"
    by (intro conjI reach_t_fin reach_f_run res_f)
       (simp_all add: t_fin_w_def f_run_w_def mkT_def mkC_def)
  then show ?thesis by blast
qed


section \<open>SITE 4 --- running-start per epoch\<close>

text \<open>
  The segment-start vocabulary is owned by the foundation and cited,
  not redefined (gate F4): @{const dwe_segment_start} with
  @{thm [source] dwe_segment_start_running},
  @{thm [source] dwe_init_core_running}, and
  @{thm [source] post_resume_core_running} say that epoch 0 starts at
  @{const dwe_init} (core @{const initial_exec_state}, Running by
  definition) and epoch @{term "k + (1::nat)"} starts at a post-Resume
  state (Running by the Resume rule).  The landed converse framework's
  Running-start premise is therefore satisfiable BY CONSTRUCTION at
  every segment start --- the honest per-segment analogue of ``start
  Running''.  This section re-founds the tier-1 two-sided
  characterization at those starts and prices the premise: still
  load-bearing (on a reachable cyclic core), and NOT a cleanliness
  guarantee (the boundary certificate at the end).
\<close>

subsection \<open>Guarded wrapper-segment implementation infrastructure\<close>

text \<open>
  The carrier below uses the cyclic wrapper state and exactly the wrapper's
  label guard together with @{const dwe_step}.  Thus its traces are guarded
  label-step continuations of the wrapper, rather than unrestricted landed
  core traces.  Reconcile and Resume remain outside this label-only carrier.

  Two generalizations of landed proof skeletons then apply to this carrier:
  the vacuous faithfulness of a not-Running start (landed
  @{thm [source] crash_only_initial_running_image_faithful}) and the
  empty-trace bad-crash package of an initially-mismatched
  start (landed
  @{thm [source] crash_only_initial_mismatch_reachable_bad_crash}).
\<close>

definition guarded_segment_implementation
  :: "('k, 'v) dwe_state \<Rightarrow>
      (('k, 'v) dwe_state, 'k, 'v) dual_write_implementation"
where
  "guarded_segment_implementation t0 =
     \<lparr>dwi_initial = t0,
      dwi_step = (\<lambda>t a t'.
        exec_label_preserves_history_wf (dwe_core t) a
        \<and> dwe_step t a t'),
      dwi_state = dwe_core\<rparr>"

lemma guarded_segment_implementation_refines_exec:
  "dwi_refines_exec (guarded_segment_implementation t0)"
  by (auto simp: dwi_refines_exec_def guarded_segment_implementation_def
           intro: dwe_step_core)

lemma guarded_segment_implementation_crash_closed:
  "crash_closed_implementation (guarded_segment_implementation t0)"
  unfolding crash_closed_implementation_def
proof (intro allI impI, elim conjE)
  fix t c
  assume running:
    "exec_status
       (dwi_state (guarded_segment_implementation t0) t) = Running"
  have running': "exec_status (dwe_core t) = Running"
    using running by (simp add: guarded_segment_implementation_def)
  let ?c' = "(dwe_core t)\<lparr>exec_status := Crashed c\<rparr>"
  let ?t' = "t\<lparr>dwe_core := ?c'\<rparr>"
  have core: "dw_exec_step (dwe_core t) (Crash c) ?c'"
    by (rule dw_exec_step.crash[OF running'])
  have wrapper: "dwe_step t (Crash c) ?t'"
    by (rule dwe_step.lift_nonpub[OF core]) simp
  show "\<exists>t'. dwi_step (guarded_segment_implementation t0)
          t (Crash c) t'"
    by (intro exI[of _ ?t'])
       (simp add: guarded_segment_implementation_def
                  exec_label_preserves_history_wf_def wrapper)
qed

lemma guarded_segment_trace_imp_wrapper_label_trace:
  assumes trace:
    "dwi_trace (guarded_segment_implementation t0) t xs t'"
      and wf: "wellformed_exec_state (dwe_core t)"
  shows "dwe_temporal_trace t (map DWE_Label xs) t'"
  using trace wf
proof (induction xs arbitrary: t t')
  case Nil
  then have "t' = t"
    by (cases rule: dwi_trace.cases) auto
  have "dwe_temporal_trace t [] t"
    by (rule dwe_temporal_trace.dwe_refl)
  with \<open>t' = t\<close> show ?case by simp
next
  case (Cons a xs)
  from Cons.prems(1) obtain u where
      impl_step:
        "dwi_step (guarded_segment_implementation t0) t a u"
      and impl_tail:
        "dwi_trace (guarded_segment_implementation t0) u xs t'"
    by (cases rule: dwi_trace.cases) auto
  have guard: "exec_label_preserves_history_wf (dwe_core t) a"
      and step: "dwe_step t a u"
    using impl_step
    by (simp_all add: guarded_segment_implementation_def)
  have wf_u: "wellformed_exec_state (dwe_core u)"
    by (rule dw_exec_step_wellformed_exec_state
        [OF dwe_step_core[OF step] Cons.prems(2) guard])
  have tail: "dwe_temporal_trace u (map DWE_Label xs) t'"
    by (rule Cons.IH[OF impl_tail wf_u])
  show ?case
    by (simp add: dwe_temporal_trace.dwe_label_step
        [OF Cons.prems(2) guard step tail])
qed

lemma wrapper_label_trace_imp_guarded_segment_trace:
  assumes trace: "dwe_temporal_trace t (map DWE_Label xs) t'"
  shows "dwi_trace (guarded_segment_implementation t0) t xs t'"
  using trace
proof (induction xs arbitrary: t)
  case Nil
  then have "t' = t"
    by (cases rule: dwe_temporal_trace.cases) auto
  then show ?case
    by (subst \<open>t' = t\<close>)
       (rule dwi_trace.dwi_trace_refl)
next
  case (Cons a xs)
  from Cons.prems obtain u where
      guard: "exec_label_preserves_history_wf (dwe_core t) a"
      and step: "dwe_step t a u"
      and tail: "dwe_temporal_trace u (map DWE_Label xs) t'"
    by (auto elim: dwe_trace_label_headE)
  have impl_step:
    "dwi_step (guarded_segment_implementation t0) t a u"
    using guard step by (simp add: guarded_segment_implementation_def)
  have impl_tail:
    "dwi_trace (guarded_segment_implementation t0) u xs t'"
    by (rule Cons.IH[OF tail])
  show ?case
    by (rule dwi_trace.dwi_trace_step[OF impl_step impl_tail])
qed

theorem guarded_segment_trace_iff_wrapper_label_trace:
  assumes wf: "wellformed_exec_state (dwe_core t)"
  shows "dwi_trace (guarded_segment_implementation t0) t xs t'
     \<longleftrightarrow> dwe_temporal_trace t (map DWE_Label xs) t'"
  using guarded_segment_trace_imp_wrapper_label_trace[OF _ wf]
        wrapper_label_trace_imp_guarded_segment_trace
  by blast

lemma guarded_segment_not_running_start_vacuously_faithful:
  assumes nr: "exec_status (dwe_core t0) \<noteq> Running"
  shows "running_image_faithful (guarded_segment_implementation t0)"
  unfolding running_image_faithful_def
proof (intro allI impI, elim conjE)
  fix xs t c k
  let ?I = "guarded_segment_implementation t0"
  assume tr: "dwi_trace ?I (dwi_initial ?I) xs t"
     and run: "exec_status (dwi_state ?I t) = Running"
  have raw:
    "dw_exec_trace (dwe_core t0) xs (dwe_core t)"
    using dwi_trace_refines_exec
      [OF guarded_segment_implementation_refines_exec tr]
    by (simp add: guarded_segment_implementation_def)
  from dw_exec_trace_not_running_preserved[OF raw nr] run
  show "\<not> mismatch_at (proto_of_exec_at (dwi_state ?I t) c) c k"
    by (simp add: guarded_segment_implementation_def)
qed

lemma guarded_segment_initial_observable_mismatch_unsafe:
  assumes mis: "observable_mismatch (dwe_core t0) c k"
  shows "implementation_has_reachable_observable_bad_crash
           (guarded_segment_implementation t0)"
proof -
  let ?I = "guarded_segment_implementation t0"
  have trace0: "dwi_trace ?I t0 [] t0"
    by (rule dwi_trace.dwi_trace_refl)
  have trace: "dwi_trace ?I (dwi_initial ?I) [] t0"
    using trace0 by (simp add: guarded_segment_implementation_def)
  have div: "diverges (proto_of_exec_at (dwe_core t0) c) c"
    by (rule observable_mismatch_imp_diverges[OF mis])
  have "reachable_observable_bad_crash ?I [] c k t0"
    using trace mis div
    by (simp add: reachable_observable_bad_crash_def
                  guarded_segment_implementation_def)
  then show ?thesis
    by (auto simp: implementation_has_reachable_observable_bad_crash_def)
qed

subsection \<open>The re-founded per-segment iff\<close>

text \<open>
  DISCLOSED SCOPE (mandatory): @{const guarded_segment_implementation} at
  @{term t'} runs guarded wrapper label steps from the segment start and
  projects them through @{const dwe_core}.  These are exactly the
  label-step continuations of the epoch-(k+1) segment; they
  DO NOT contain the wrapper's @{const emitting_reconcile} (an atomic
  big-step, not a label) nor any later @{const DWE_Resume}
  (@{thm [source] resume_breaks_core_simulation}).  So this is the
  tier-1 two-sided characterization
  @{thm [source] safe_iff_running_image_faithful} re-founded at each
  segment start, governing that segment's label-step portion only: a
  restatement with disclosed scope --- NOT an upgrade, NOT full-trace
  safety, and silent about the emission ledger by design (the boundary
  certificate below prices the ledger side).  The reconcile's heal
  remains separately banked (@{thm [source] emitting_reconcile_heals}).

  COMPLEMENTARY FORM (cross-reference; single-owner per gate F5): the
  converse theory (@{text Dual_Write_Effect_Converse}, site 3) lands
  the honest full-machine restatement of the same tier-1
  characterization on a NEW implementation carrier over the full cyclic
  action grammar (labels + reconcile + Resume) --- a form the landed
  implementation record cannot express.  THIS form is the landed iff
  instantiated verbatim through the landed framework's own parametric
  start slot at segment-start cores.  The two forms are complements,
  not duplicates; neither consumes the other.
\<close>

theorem post_resume_segment_safe_iff_running_image_faithful:
  assumes res: "dwe_resume t t'"
  shows "(\<not> implementation_has_reachable_observable_bad_crash
             (guarded_segment_implementation t'))
     \<longleftrightarrow> running_image_faithful
           (guarded_segment_implementation t')"
proof (rule safe_iff_running_image_faithful)
  show "crash_closed_implementation
          (guarded_segment_implementation t')"
    by (rule guarded_segment_implementation_crash_closed)
  show "dwi_refines_exec (guarded_segment_implementation t')"
    by (rule guarded_segment_implementation_refines_exec)
  show "exec_status
          (dwi_state (guarded_segment_implementation t')
            (dwi_initial (guarded_segment_implementation t')))
        = Running"
    by (simp add: guarded_segment_implementation_def
                  post_resume_core_running[OF res])
qed

theorem epoch0_segment_safe_iff_running_image_faithful:
  "(\<not> implementation_has_reachable_observable_bad_crash
       (guarded_segment_implementation
          (dwe_init Map.empty {0, 1} ec2 :: (nat, nat) dwe_state)))
 \<longleftrightarrow> running_image_faithful
       (guarded_segment_implementation
          (dwe_init Map.empty {0, 1} ec2 :: (nat, nat) dwe_state))"
proof (rule safe_iff_running_image_faithful)
  show "crash_closed_implementation
          (guarded_segment_implementation
             (dwe_init Map.empty {0, 1} ec2 :: (nat, nat) dwe_state))"
    by (rule guarded_segment_implementation_crash_closed)
  show "dwi_refines_exec
          (guarded_segment_implementation
             (dwe_init Map.empty {0, 1} ec2 :: (nat, nat) dwe_state))"
    by (rule guarded_segment_implementation_refines_exec)
  show "exec_status
          (dwi_state
            (guarded_segment_implementation
               (dwe_init Map.empty {0, 1} ec2 :: (nat, nat) dwe_state))
            (dwi_initial
              (guarded_segment_implementation
                 (dwe_init Map.empty {0, 1} ec2 :: (nat, nat) dwe_state))))
        = Running"
    by (simp add: guarded_segment_implementation_def dwe_init_core_running)
qed

subsection \<open>THE CONTROL: the Running-start premise is STILL load-bearing\<close>

text \<open>
  Same five-conjunct shape as the landed control
  @{thm [source] running_start_is_load_bearing}, with two upgrades of
  provenance, disclosed as such: (i) the vacuously-faithful-yet-unsafe
  start is no longer a hand-built state but @{term "dwe_core t_mid_w"}
  --- a core the cyclic machine actually REACHES
  (@{thm [source] reach_t_mid}), mid-segment, Crashed with a real
  observable mismatch (@{thm [source] t_mid_mismatch}); (ii) it is
  exactly the kind of state the segment-start premise EXCLUDES.
  Reading: in the re-founded per-segment iff above, ``start Running''
  is what pins the characterization to segment STARTS; dropping it
  admits mid-segment crashed suffixes where faithfulness holds
  vacuously while the bad crash is already on the table.  The landed
  control stays citable verbatim for epoch 0; this control covers every
  epoch, because @{const t_mid_w}-shaped cores recur in any epoch's
  interior.
\<close>

theorem running_start_still_load_bearing_at_reachable_core:
  "dwe_reachable t_mid_w
 \<and> crash_closed_implementation
     (guarded_segment_implementation t_mid_w)
 \<and> dwi_refines_exec (guarded_segment_implementation t_mid_w)
 \<and> running_image_faithful (guarded_segment_implementation t_mid_w)
 \<and> implementation_has_reachable_observable_bad_crash
     (guarded_segment_implementation t_mid_w)
 \<and> exec_status
     (dwi_state (guarded_segment_implementation t_mid_w)
       (dwi_initial (guarded_segment_implementation t_mid_w)))
   \<noteq> Running"
proof (intro conjI)
  show "dwe_reachable t_mid_w" by (rule reach_t_mid)
  show "crash_closed_implementation
          (guarded_segment_implementation t_mid_w)"
    by (rule guarded_segment_implementation_crash_closed)
  show "dwi_refines_exec (guarded_segment_implementation t_mid_w)"
    by (rule guarded_segment_implementation_refines_exec)
  show "running_image_faithful
          (guarded_segment_implementation t_mid_w)"
    by (rule guarded_segment_not_running_start_vacuously_faithful)
       (simp add: t_mid_w_def mkT_def mkC_def)
  show "implementation_has_reachable_observable_bad_crash
          (guarded_segment_implementation t_mid_w)"
    by (rule guarded_segment_initial_observable_mismatch_unsafe
        [OF t_mid_mismatch])
  show "exec_status
          (dwi_state (guarded_segment_implementation t_mid_w)
            (dwi_initial (guarded_segment_implementation t_mid_w)))
        \<noteq> Running"
    by (simp add: guarded_segment_implementation_def
                  t_mid_w_def mkT_def mkC_def)
qed

subsection \<open>Ledger permanence along traces (shared-wave copy)\<close>

text \<open>
  The trace-level companion of the banked single-transition
  @{thm [source] effect_unsafe_monotone_reachable}: effect-unsafety is
  permanent along every continuation from a reachable state.  This is
  the shared-wave copy mandated by the gate (section 2.6) as general
  infrastructure anticipated for the tightness and completeness lanes;
  the audit-recorded single-owner placement lands it HERE, outside those
  lanes' import cones, and its landed consumer is this theory's own
  honest-boundary certificate below.
  The reachability companion @{thm [source] dwe_trace_reachable_ext} is
  already banked in the foundation and is cited, not re-proved.
\<close>

theorem effect_unsafe_trace_monotone:
  assumes "dwe_reachable t"
      and "effect_unsafe t"
      and "dwe_temporal_trace t xs t'"
  shows "effect_unsafe t'"
  using assms(3) assms(1) assms(2)
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  then show ?case by simp
next
  case (dwe_label_step t a t' as t'')
  have reach': "dwe_reachable t'"
    by (rule dwe_reachable_label_ext[OF dwe_label_step.prems(1)
          dwe_label_step.hyps(1) dwe_label_step.hyps(2)
          dwe_label_step.hyps(3)])
  have unsafe': "effect_unsafe t'"
    by (rule effect_unsafe_monotone_reachable[OF dwe_label_step.prems(1)
          dwe_label_step.prems(2) disjI1[OF dwe_label_step.hyps(3)]])
  show ?case by (rule dwe_label_step.IH[OF reach' unsafe'])
next
  case (dwe_reconcile_step m t f t' as t'')
  have reach': "dwe_reachable t'"
    by (rule dwe_reachable_reconcile_ext[OF dwe_reconcile_step.prems(1)
          dwe_reconcile_step.hyps(1)])
  have unsafe': "effect_unsafe t'"
    by (rule effect_unsafe_monotone_reachable[OF dwe_reconcile_step.prems(1)
          dwe_reconcile_step.prems(2)
          disjI2[OF disjI1[OF dwe_reconcile_step.hyps(1)]]])
  show ?case by (rule dwe_reconcile_step.IH[OF reach' unsafe'])
next
  case (dwe_resume_step t t' as t'')
  have reach': "dwe_reachable t'"
    by (rule dwe_reachable_resume_ext[OF dwe_resume_step.prems(1)
          dwe_resume_step.hyps(1)])
  have unsafe': "effect_unsafe t'"
    by (rule effect_unsafe_monotone_reachable[OF dwe_resume_step.prems(1)
          dwe_resume_step.prems(2)
          disjI2[OF disjI2[OF dwe_resume_step.hyps(1)]]])
  show ?case by (rule dwe_resume_step.IH[OF reach' unsafe'])
qed

subsection \<open>The honest boundary: an epoch-k running start is NOT a clean start\<close>

text \<open>
  The banked post-Resume Running witness @{const f_run_w} opens epoch 1
  Running --- with a NON-INITIAL core (non-empty committed source
  history) and a non-empty emission ledger that is ALREADY effect-unsafe
  (its ledger carries the payload duplicate; same evaluation as
  @{thm [source] t_fin_unsafe}).  This is the boundary certificate that
  the per-segment Running-start premise buys STORE-IMAGE claims only:
  segment-scoped image faithfulness can never launder the ledger,
  because unsafety is permanent across every later transition
  (@{thm [source] effect_unsafe_trace_monotone} above).  Consequence for
  every consumer: an epoch-k segment start is an ARBITRARY carried state
  with Running status --- nothing more.
\<close>

theorem post_resume_running_start_not_clean:
  "dwe_reachable f_run_w
 \<and> exec_status (dwe_core f_run_w) = Running
 \<and> dwe_epoch f_run_w = 1
 \<and> genuinely_emitting f_run_w
 \<and> effect_unsafe f_run_w
 \<and> exec_src_hist (dwe_core f_run_w) \<noteq> []
 \<and> dwe_core f_run_w \<noteq> initial_exec_state Map.empty {0, 1} ec2"
proof (intro conjI)
  show "dwe_reachable f_run_w" by (rule reach_f_run)
  show "exec_status (dwe_core f_run_w) = Running"
    by (simp add: f_run_w_def mkT_def mkC_def)
  show "dwe_epoch f_run_w = 1"
    by (simp add: f_run_w_def mkT_def)
  show "genuinely_emitting f_run_w"
    by (simp add: genuinely_emitting_def f_run_w_def mkT_def)
  show "effect_unsafe f_run_w"
    by (simp add: effect_unsafe_def duplicate_def f_run_w_def mkT_def
                  e1_def e2_def ec_defs)
  show "exec_src_hist (dwe_core f_run_w) \<noteq> []"
    by (simp add: f_run_w_def mkT_def mkC_def)
  show "dwe_core f_run_w \<noteq> initial_exec_state Map.empty {0, 1} ec2"
    by (simp add: f_run_w_def mkT_def mkC_def initial_exec_state_def)
qed

end
