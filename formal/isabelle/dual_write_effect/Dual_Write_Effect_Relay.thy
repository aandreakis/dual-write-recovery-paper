(*  Title:       Dual_Write_Effect_Relay.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    SITE 6 of the S4d per-epoch re-landing: the relay invariant re-founded
    on the cyclic effect machine.  The landed POINTWISE safety law
    relay_inv_no_observable_mismatch is reachability-free and is consumed
    VERBATIM; what restates is the induction CARRIER: the landed
    relay_reachable_inv is founded once at the initial state over
    label-only dwi_traces and cannot see Reconcile/Resume
    (resume_breaks_core_simulation).  Here the same state predicate
    relay_inv is RE-ESTABLISHED by the machine's own reconcile and
    preserved by Resume, so one global induction over a disciplined
    cyclic grammar replaces per-segment re-foundations: the invariant is
    self-reproducing across crash/reconcile/Resume cycles.

    Reconciliation re-establishes the occurrence-prefix invariant using the
    core theorem that a bounded replay is a prefix of the unbounded in-scope
    source stream.  Frontier safety separately requires
    relay_complete_through, so tied-coordinate occurrences are never treated
    as complete after only one delivery.

    Produced by the S4d proof-wave P4 prover per the committed design
    (paper/dual_write/phase3/s4d_design/site_3_6_safety_family.md, SITE 6,
    gate-canonicalized); the scratch original's in-source ML oracle gates are STRIPPED here:
    oracle-freedom is certified by scratch-side per-slice gate sessions
    with confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Relay
  imports Dual_Write_Effect_Segments
begin

section \<open>Replay lemmas at the advertised frontier\<close>

text \<open>
  The WF-H1 toolbox (@{thm [source] wellformed_src_history_coord_mono},
  @{thm [source] wellformed_src_history_last_max},
  @{thm [source] wellformed_src_history_filter}) and
  @{thm [source] replay_down_hist_wellformed} are consumed from the
  landed segment foundation --- ONE canonical copy.  The two lemmas
  below are the relay-specific consequences: the replay at the base
  coordinate is empty (WF-H2: no wellformed event sits at @{const c0}),
  and THE REFILTER LEMMA --- the replay at @{term f} re-filters
  identically at its OWN last coordinate.  Sortedness of the source
  history (WF-H1) is load-bearing in the latter: an in-scope event of
  @{term H} in the window @{text "(adv, f]"} would itself be in the
  @{term f}-replay, hence coordinate-bounded by the replay's last
  (maximal) coordinate --- a contradiction.  No strictness is needed;
  WF-H1's @{text "\<le>"} ties are handled by maximality, not uniqueness.
\<close>

lemma replay_down_hist_at_c0:
  assumes wf: "wellformed_src_history H"
  shows "replay_down_hist H K c0 = []"
  unfolding replay_down_hist_def
proof (rule filter_False)
  show "\<forall>x \<in> set H. \<not> (case x of (c, e) \<Rightarrow> c \<le> c0 \<and> key_of e \<in> K)"
  proof
    fix x
    assume xin: "x \<in> set H"
    obtain i where i: "i < length H" and nth: "x = H ! i"
      using xin by (auto simp: in_set_conv_nth)
    have ne: "hist_coord (H ! i) \<noteq> c0"
      using wf i unfolding wellformed_src_history_def by blast
    show "\<not> (case x of (c, e) \<Rightarrow> c \<le> c0 \<and> key_of e \<in> K)"
    proof
      assume "case x of (c, e) \<Rightarrow> c \<le> c0 \<and> key_of e \<in> K"
      then have "fst x \<le> c0" by (cases x) simp
      then have "src_le (fst x) c0" by (simp add: src_le_eq_less_eq)
      then have "fst x = c0" using c0_least by (rule src_le_antisym)
      with ne nth show False by simp
    qed
  qed
qed

text \<open>
  THE REFILTER LEMMA (front-loaded per the wave brief): the replayed
  prefix is its own advertised frontier's replay.  Route: pointwise
  predicate equality on @{term "set H"} under @{thm [source] filter_cong}.
  Forward inclusion of predicates: an event kept at the last coordinate
  @{term g} is kept at @{term f} since @{text "g \<le> f"} (the last element
  of the @{term f}-bounded filter obeys the filter bound).  Backward: an
  event kept at @{term f} IS an element of the replay, so its coordinate
  is @{text "\<le>"} the last (maximal) coordinate @{term g} ---
  @{thm [source] wellformed_src_history_last_max} on the FILTERED list,
  wellformed via @{thm [source] replay_down_hist_wellformed}.
\<close>

lemma replay_down_hist_refilter_at_last:
  assumes wf: "wellformed_src_history H"
      and ne: "replay_down_hist H K f \<noteq> []"
  shows "replay_down_hist H K (fst (last (replay_down_hist H K f)))
       = replay_down_hist H K f"
proof -
  define R where "R = replay_down_hist H K f"
  define g where "g = fst (last R)"
  have neR: "R \<noteq> []" using ne by (simp add: R_def)
  have wfR: "wellformed_src_history R"
    unfolding R_def by (rule replay_down_hist_wellformed[OF wf])
  have lastR: "last R \<in> set R"
    using neR by (rule last_in_set)
  have R_pred: "fst x \<le> f \<and> key_of (snd x) \<in> K" if "x \<in> set R" for x
    using that unfolding R_def replay_down_hist_def
    by (auto simp: case_prod_beta)
  have g_le_f: "g \<le> f"
    unfolding g_def using R_pred[OF lastR] by simp
  have ptwise: "(c \<le> g \<and> key_of e \<in> K) \<longleftrightarrow> (c \<le> f \<and> key_of e \<in> K)"
    if xin: "(c, e) \<in> set H" for c e
  proof
    assume "c \<le> g \<and> key_of e \<in> K"
    then show "c \<le> f \<and> key_of e \<in> K"
      using g_le_f by (auto intro: order_trans)
  next
    assume ce: "c \<le> f \<and> key_of e \<in> K"
    then have "(c, e) \<in> set R"
      unfolding R_def replay_down_hist_def using xin by auto
    then have "src_le (hist_coord (c, e)) (hist_coord (last R))"
      by (rule wellformed_src_history_last_max[OF wfR])
    then have "c \<le> g"
      unfolding g_def by (simp add: src_le_eq_less_eq)
    with ce show "c \<le> g \<and> key_of e \<in> K" by simp
  qed
  have "replay_down_hist H K g = replay_down_hist H K f"
    unfolding replay_down_hist_def
  proof (rule filter_cong[OF refl])
    fix x
    assume xin: "x \<in> set H"
    obtain c e where xce: "x = (c, e)" by (cases x)
    show "(case x of (c, e) \<Rightarrow> c \<le> g \<and> key_of e \<in> K)
        = (case x of (c, e) \<Rightarrow> c \<le> f \<and> key_of e \<in> K)"
      unfolding xce using ptwise[OF xin[unfolded xce]] by simp
  qed
  then show ?thesis by (simp add: R_def g_def)
qed

section \<open>The reconcile re-establishes the invariant (core-level twins)\<close>

text \<open>
  Landed vocabulary, no wrapper: the landed relay reconcile
  @{const relay_bounded_replay_reconcile} preserves core wellformedness
  (the down history is overwritten by a wellformed replay,
  @{thm [source] replay_down_hist_wellformed}; pending is emptied; src /
  enqueued / acked are untouched) and RE-ESTABLISHES @{const relay_inv}
  outright: the only facts it needs from the pre-state are
  wellformedness and the genesis base --- both carried by
  @{const relay_inv} itself.  The structural clause is the general fact that a
  frontier-bounded replay of a wellformed source history is an occurrence
  prefix of its unbounded in-scope stream.
\<close>

theorem relay_bounded_replay_reconcile_wellformed:
  assumes rec: "relay_bounded_replay_reconcile s f s'"
      and wf: "wellformed_exec_state s"
  shows "wellformed_exec_state s'"
proof -
  have s'_eq: "s' = s\<lparr>exec_down_hist :=
                        replay_down_hist (exec_src_hist s) (exec_scope s) f,
                      exec_pending := {}, exec_status := Recovered\<rparr>"
    using rec by (simp add: relay_bounded_replay_reconcile_def)
  have wf_src: "wellformed_src_history (exec_src_hist s)"
    using wf by (simp add: ws_defs)
  show ?thesis
    using wf replay_down_hist_wellformed[OF wf_src]
    unfolding s'_eq ws_defs by simp
qed

text \<open>
  The design-noted generality, machine-checked: the reconcile needs from
  the pre-state ONLY wellformedness and the genesis base --- it
  re-establishes the structural clause unconditionally.  The pinned
  @{text relay_inv}-to-@{text relay_inv} form follows as a corollary.
\<close>

theorem relay_inv_reconcile_from_wf_base:
  assumes rec: "relay_bounded_replay_reconcile s f s'"
      and wf: "wellformed_exec_state s"
      and base: "exec_base s = (\<lambda>_. None)"
  shows "relay_inv s'"
proof -
  define R where "R = replay_down_hist (exec_src_hist s) (exec_scope s) f"
  have s'_eq: "s' = s\<lparr>exec_down_hist := R, exec_pending := {},
                      exec_status := Recovered\<rparr>"
    using rec by (simp add: relay_bounded_replay_reconcile_def R_def)
  have fields: "exec_down_hist s' = R"
               "exec_src_hist s' = exec_src_hist s"
               "exec_scope s' = exec_scope s"
    by (simp_all add: s'_eq)
  have wf_src: "wellformed_src_history (exec_src_hist s)"
    using wf by (simp add: ws_defs)
  have wf': "wellformed_exec_state s'"
    by (rule relay_bounded_replay_reconcile_wellformed[OF rec wf])
  have base': "exec_base s' = (\<lambda>_. None)"
    using base by (simp add: s'_eq)
  have struct':
    "relay_history_prefix
       (exec_down_hist s')
       (scoped_replay_history (exec_src_hist s') (exec_scope s'))"
    unfolding fields R_def
    by (rule replay_down_hist_prefix_scoped[OF wf_src])
  show ?thesis
    unfolding relay_inv_def using wf' base' struct' by blast
qed

theorem relay_inv_bounded_replay_reconcile:
  assumes rec: "relay_bounded_replay_reconcile s f s'"
      and inv: "relay_inv s"
  shows "relay_inv s'"
  by (rule relay_inv_reconcile_from_wf_base[OF rec])
     (use inv in \<open>simp_all add: relay_inv_def\<close>)

section \<open>The disciplined cyclic relay grammar\<close>

text \<open>
  The landed advertise discipline lifted to the cyclic machine:
  disciplined label steps are machine steps whose CORE action is
  @{const relay_admits}-admitted; reconcile and Resume are the machine's
  own rules, unguarded --- the cyclic relay's recovery IS the landed
  reconcile plus the epoch-opening Resume.  The label rule carries the
  same start-wellformedness guard as the machine's own trace rule; the
  wf-preservation guard of @{const dwe_temporal_trace} is RECOVERED from
  the discipline itself (@{thm [source] relay_admits_preserves_wf}), so
  every disciplined trace is a machine trace.
\<close>

definition dwe_relay_step
  :: "('k, 'v) dwe_state \<Rightarrow> ('k, 'v) dw_exec_label \<Rightarrow> ('k, 'v) dwe_state \<Rightarrow> bool"
where
  "dwe_relay_step t a t' \<longleftrightarrow> dwe_step t a t' \<and> relay_admits (dwe_core t) a"

inductive dwe_relay_trace
  :: "('k, 'v) dwe_state \<Rightarrow> ('k, 'v) dwe_action list \<Rightarrow> ('k, 'v) dwe_state \<Rightarrow> bool"
where
  drt_refl:
    "dwe_relay_trace t [] t"
| drt_label:
    "\<lbrakk>wellformed_exec_state (dwe_core t); dwe_relay_step t a t';
      dwe_relay_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwe_relay_trace t (DWE_Label a # as) t''"
| drt_reconcile:
    "\<lbrakk>emitting_reconcile m t f t'; dwe_relay_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwe_relay_trace t (DWE_Reconcile m f # as) t''"
| drt_resume:
    "\<lbrakk>dwe_resume t t'; dwe_relay_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwe_relay_trace t (DWE_Resume # as) t''"

lemma dwe_relay_trace_is_temporal:
  assumes "dwe_relay_trace t xs t'"
  shows "dwe_temporal_trace t xs t'"
  using assms
proof (induction rule: dwe_relay_trace.induct)
  case (drt_refl t)
  show ?case by (rule dwe_temporal_trace.dwe_refl)
next
  case (drt_label t a t' as t'')
  have adm: "relay_admits (dwe_core t) a"
    using drt_label.hyps(2) by (simp add: dwe_relay_step_def)
  have step: "dwe_step t a t'"
    using drt_label.hyps(2) by (simp add: dwe_relay_step_def)
  show ?case
    by (rule dwe_temporal_trace.dwe_label_step[OF drt_label.hyps(1)
          relay_admits_preserves_wf[OF adm] step drt_label.IH])
next
  case (drt_reconcile m t f t' as t'')
  show ?case
    by (rule dwe_temporal_trace.dwe_reconcile_step[OF drt_reconcile.hyps(1)
          drt_reconcile.IH])
next
  case (drt_resume t t' as t'')
  show ?case
    by (rule dwe_temporal_trace.dwe_resume_step[OF drt_resume.hyps(1)
          drt_resume.IH])
qed

section \<open>The invariant preservation family\<close>

lemma relay_inv_emitting_reconcile:
  assumes rec: "emitting_reconcile m t f t'"
      and inv: "relay_inv (dwe_core t)"
  shows "relay_inv (dwe_core t')"
  by (rule relay_inv_bounded_replay_reconcile[OF
        emitting_reconcile_core[OF rec] inv])

lemma relay_inv_dwe_resume:
  assumes res: "dwe_resume t t'"
      and inv: "relay_inv (dwe_core t)"
  shows "relay_inv (dwe_core t')"
proof -
  have core_eq: "dwe_core t' = (dwe_core t)\<lparr>exec_status := Running\<rparr>"
    by (rule dwe_resume_core[OF res])
  have wf0: "wellformed_exec_state (dwe_core t)"
   and base0: "exec_base (dwe_core t) = (\<lambda>_. None)"
   and struct0:
     "relay_history_prefix
       (exec_down_hist (dwe_core t))
       (scoped_replay_history
         (exec_src_hist (dwe_core t)) (exec_scope (dwe_core t)))"
    using inv by (simp_all add: relay_inv_def)
  have wf': "wellformed_exec_state (dwe_core t')"
    using wf0 unfolding core_eq ws_defs by simp
  have base': "exec_base (dwe_core t') = (\<lambda>_. None)"
    using base0 by (simp add: core_eq)
  have struct':
    "relay_history_prefix
       (exec_down_hist (dwe_core t'))
       (scoped_replay_history
         (exec_src_hist (dwe_core t')) (exec_scope (dwe_core t')))"
    unfolding core_eq by (simp add: struct0)
  show ?thesis
    unfolding relay_inv_def using wf' base' struct' by blast
qed

lemma relay_inv_dwe_relay_step:
  assumes step: "dwe_relay_step t a t'"
      and inv: "relay_inv (dwe_core t)"
  shows "relay_inv (dwe_core t')"
proof -
  have core: "dw_exec_step (dwe_core t) a (dwe_core t')"
    using step by (intro dwe_step_core) (simp add: dwe_relay_step_def)
  have adm: "relay_admits (dwe_core t) a"
    using step by (simp add: dwe_relay_step_def)
  have rstep: "relay_step (dwe_core t) a (dwe_core t')"
    using core adm by (simp add: relay_step_def)
  show ?thesis by (rule relay_inv_step[OF rstep inv])
qed

section \<open>THE RE-FOUNDED INDUCTION\<close>

text \<open>
  MANDATORY DISCLOSURE (restatement with disclosed scope; per-epoch
  re-landing, plan section 10): the invariant induction is RE-FOUNDED,
  not transferred.  The landed carrier @{thm [source] relay_reachable_inv}
  is founded once at the initial state over label-only
  @{const dwi_trace}s and cannot see Reconcile/Resume --- a resume-using
  step relation has no landed-record packaging that refines the core
  (@{thm [source] resume_breaks_core_simulation}).  Here the same state
  predicate @{const relay_inv} is re-established by the reconcile itself
  (@{thm [source] relay_inv_bounded_replay_reconcile}) and preserved by
  Resume, so it holds across ALL epochs of the disciplined cyclic relay
  --- stronger than a per-segment re-founding, never an upgrade of the
  landed theorem.

  STALE-HEAL SCOPE (the honest boundary): a reconcile at a frontier
  @{term f} strictly below prior durable progress may rewind the downstream
  history.  The invariant records only occurrence-prefix discipline; the safe
  side below applies exactly where @{const relay_complete_through} is proved
  for the current state, never merely because a coordinate was previously
  advertised.  The strengthening
  "once advertised, always safe" is FALSE on this machine and BANNED:
  a stale heal that resumes exposes the un-replayed committed suffix to
  a genuinely observable bad crash (the converse theory's stale-heal
  witness chain).
\<close>

theorem relay_inv_dwe_relay_trace:
  assumes "dwe_relay_trace t xs t'"
      and "relay_inv (dwe_core t)"
  shows "relay_inv (dwe_core t')"
  using assms
proof (induction rule: dwe_relay_trace.induct)
  case (drt_refl t)
  then show ?case by simp
next
  case (drt_label t a t' as t'')
  then show ?case using relay_inv_dwe_relay_step by blast
next
  case (drt_reconcile m t f t' as t'')
  then show ?case using relay_inv_emitting_reconcile by blast
next
  case (drt_resume t t' as t'')
  then show ?case using relay_inv_dwe_resume by blast
qed

text \<open>
  The re-founded carrier, parametric in scope and finish frontier: the
  pinned machine's instance is the special case @{term "K = {0, 1}"},
  @{term "fin = ec2"} (and @{term Map.empty} is by definition
  @{term "\<lambda>_. None"}, so the pinned @{const dwe_reachable} base state is
  literally this one).  Foundation: the core of @{term "dwe_init"} IS the
  landed initial state, closed by @{thm [source] relay_inv_initial}.
\<close>

theorem cyclic_relay_reachable_inv:
  assumes "dwe_relay_trace (dwe_init (\<lambda>_. None) K fin) xs t"
  shows "relay_inv (dwe_core t)"
proof -
  have core0: "dwe_core (dwe_init (\<lambda>_. None) K fin)
             = initial_exec_state (\<lambda>_. None) K fin"
    by (simp add: dwe_init_def)
  have "relay_inv (dwe_core (dwe_init (\<lambda>_. None) K fin))"
    unfolding core0 by (rule relay_inv_initial)
  from relay_inv_dwe_relay_trace[OF assms this] show ?thesis .
qed

text \<open>
  Segment-start corollary --- the plan's literal item, isolated: the
  state entered by ANY reconcile+Resume pair out of an invariant state
  satisfies the invariant and is Running, i.e. the post-Resume segment
  start is a legitimate new foundation.  The per-segment view of the
  global induction: @{thm [source] relay_inv_dwe_relay_trace} is
  start-agnostic, so restricting it to Resume-free suffixes founded at
  such states needs no extra work.
\<close>

corollary post_resume_segment_start_relay_inv:
  assumes rec: "emitting_reconcile m t f t1"
      and res: "dwe_resume t1 t2"
      and inv: "relay_inv (dwe_core t)"
  shows "relay_inv (dwe_core t2) \<and> exec_status (dwe_core t2) = Running"
proof
  have inv1: "relay_inv (dwe_core t1)"
    by (rule relay_inv_emitting_reconcile[OF rec inv])
  show "relay_inv (dwe_core t2)"
    by (rule relay_inv_dwe_resume[OF res inv1])
  show "exec_status (dwe_core t2) = Running"
    by (rule post_resume_core_running[OF res])
qed

section \<open>VERBATIM consumption of the landed pointwise safety law\<close>

text \<open>
  The landed @{thm [source] relay_inv_no_observable_mismatch} carries NO
  reachability premise --- it is a pointwise consequence of the state
  predicate.  It is therefore applied UNCHANGED at every
  disciplined-reachable state of every epoch; nothing about the safety
  law itself restates.
\<close>

theorem cyclic_relay_no_observable_mismatch:
  assumes reach: "dwe_relay_trace (dwe_init (\<lambda>_. None) K fin) xs t"
      and complete: "relay_complete_through (dwe_core t) f"
      and le_fin: "f \<le> exec_finish (dwe_core t)"
  shows "\<not> observable_mismatch ((dwe_core t)\<lparr>exec_status := Crashed f\<rparr>) f k"
  by (rule relay_inv_no_observable_mismatch[OF
        cyclic_relay_reachable_inv[OF reach] complete le_fin])

section \<open>Honesty controls: the disciplined heal still duplicates\<close>

text \<open>
  LEDGER-BLINDNESS (mandatory disclosure): the SAME disciplined run that
  maintains @{const relay_inv} through the heal is effect-unsafe --- the
  re-founded store invariant says NOTHING about the ledger
  (@{thm [source] dwe_duplicate_separation}: the effect verdict is not a
  function of the core).  The witness chain to @{const t_fin_w} is
  relay-admitted step by step (advertised-frontier computations
  @{term c0} @{text "\<rightarrow>"} @{const ec1} @{text "\<rightarrow>"} @{const ec2}), its
  reconcile is the machine's own; the effect verdict is the banked
  @{thm [source] t_fin_unsafe}.

  FENCE (cross-tier witness, gate ruling F9): the two statements below
  are cross-tier WITNESS statements --- a tier-1-disciplined run
  exhibiting a banked tier-2 verdict --- not effect-tier
  @{text "\<forall>"}-laws acquiring an advertised-frontier premise.  No
  effect-tier law in this development carries @{const adv} vocabulary;
  the same reconcile's incident form without any discipline vocabulary
  is the banked @{thm [source] crash_heal_reemit_bridge}.
\<close>

subsection \<open>The witness chain is relay-admitted, step by step\<close>

lemma adm_W0_src1: "relay_admits (dwe_core W0) (DoSource ec1 e1)"
  using g_W0_src1
  by (simp add: relay_admits_def W0_def mkT_def mkC_def adv_def ec_defs)

lemma adm_W1_enq1: "relay_admits (dwe_core W1) (EnqueueDownstream ec1 e1)"
  using g_W1_enq1 by (simp add: relay_admits_def)

lemma adm_W2_down1: "relay_admits (dwe_core W2) (DoDownstream ec1 e1)"
  using g_W2_down1
  by (simp add: relay_admits_def W2_def mkT_def mkC_def
                relay_history_prefix_def scoped_replay_history_def
                e1_def ec_defs)

lemma adm_W3_src2: "relay_admits (dwe_core W3) (DoSource ec2 e2)"
  using g_W3_src2
  by (simp add: relay_admits_def W3_def mkT_def mkC_def adv_def ec_defs)

lemma adm_W4_enq2: "relay_admits (dwe_core W4) (EnqueueDownstream ec2 e2)"
  using g_W4_enq2 by (simp add: relay_admits_def)

lemma adm_W5_crash: "relay_admits (dwe_core W5) (Crash ec2)"
  using g_W5_crash by (simp add: relay_admits_def)

lemma drs_W0: "dwe_relay_step W0 (DoSource ec1 e1) W1"
  using ws1 adm_W0_src1 by (simp add: dwe_relay_step_def)

lemma drs_W1: "dwe_relay_step W1 (EnqueueDownstream ec1 e1) W2"
  using ws2 adm_W1_enq1 by (simp add: dwe_relay_step_def)

lemma drs_W2: "dwe_relay_step W2 (DoDownstream ec1 e1) W3"
  using ws3 adm_W2_down1 by (simp add: dwe_relay_step_def)

lemma drs_W3: "dwe_relay_step W3 (DoSource ec2 e2) W4"
  using ws4 adm_W3_src2 by (simp add: dwe_relay_step_def)

lemma drs_W4: "dwe_relay_step W4 (EnqueueDownstream ec2 e2) W5"
  using ws5 adm_W4_enq2 by (simp add: dwe_relay_step_def)

lemma drs_W5: "dwe_relay_step W5 (Crash ec2) t_mid_w"
  using ws6 adm_W5_crash by (simp add: dwe_relay_step_def)

subsection \<open>The disciplined trace to the duplicated heal\<close>

theorem cyclic_relay_trace_to_t_fin:
  "dwe_relay_trace (dwe_init (\<lambda>_. None) {0, 1} ec2)
     (map DWE_Label witness_labels @ [DWE_Reconcile 0 ec2]) t_fin_w"
proof -
  have a7: "dwe_relay_trace t_mid_w [DWE_Reconcile 0 ec2] t_fin_w"
    by (rule dwe_relay_trace.drt_reconcile[OF rec_fin dwe_relay_trace.drt_refl])
  have a6: "dwe_relay_trace W5
              [DWE_Label (Crash ec2), DWE_Reconcile 0 ec2] t_fin_w"
    by (rule dwe_relay_trace.drt_label[OF wf_W5 drs_W5 a7])
  have a5: "dwe_relay_trace W4
              [DWE_Label (EnqueueDownstream ec2 e2), DWE_Label (Crash ec2),
               DWE_Reconcile 0 ec2] t_fin_w"
    by (rule dwe_relay_trace.drt_label[OF wf_W4 drs_W4 a6])
  have a4: "dwe_relay_trace W3
              [DWE_Label (DoSource ec2 e2),
               DWE_Label (EnqueueDownstream ec2 e2), DWE_Label (Crash ec2),
               DWE_Reconcile 0 ec2] t_fin_w"
    by (rule dwe_relay_trace.drt_label[OF wf_W3 drs_W3 a5])
  have a3: "dwe_relay_trace W2
              [DWE_Label (DoDownstream ec1 e1), DWE_Label (DoSource ec2 e2),
               DWE_Label (EnqueueDownstream ec2 e2), DWE_Label (Crash ec2),
               DWE_Reconcile 0 ec2] t_fin_w"
    by (rule dwe_relay_trace.drt_label[OF wf_W2 drs_W2 a4])
  have a2: "dwe_relay_trace W1
              [DWE_Label (EnqueueDownstream ec1 e1),
               DWE_Label (DoDownstream ec1 e1), DWE_Label (DoSource ec2 e2),
               DWE_Label (EnqueueDownstream ec2 e2), DWE_Label (Crash ec2),
               DWE_Reconcile 0 ec2] t_fin_w"
    by (rule dwe_relay_trace.drt_label[OF wf_W1 drs_W1 a3])
  have a1: "dwe_relay_trace W0
              [DWE_Label (DoSource ec1 e1),
               DWE_Label (EnqueueDownstream ec1 e1),
               DWE_Label (DoDownstream ec1 e1), DWE_Label (DoSource ec2 e2),
               DWE_Label (EnqueueDownstream ec2 e2), DWE_Label (Crash ec2),
               DWE_Reconcile 0 ec2] t_fin_w"
    by (rule dwe_relay_trace.drt_label[OF wf_W0 drs_W0 a2])
  show ?thesis
    using a1 unfolding W0_init witness_labels_def by simp
qed

corollary relay_disciplined_heal_still_duplicates:
  "relay_inv (dwe_core t_fin_w) \<and> effect_unsafe t_fin_w"
proof
  show "relay_inv (dwe_core t_fin_w)"
    by (rule cyclic_relay_reachable_inv[OF cyclic_relay_trace_to_t_fin])
  show "effect_unsafe t_fin_w" by (rule t_fin_unsafe)
qed


section \<open>The complete two-action relay machine: invariant closure and safe side\<close>

text \<open>
  The ingredients above close @{const relay_inv} under each action FORM
  separately: @{thm [source] relay_inv_step} under the label steps and
  @{thm [source] relay_inv_bounded_replay_reconcile} under the bounded
  replay.  The lift below closes the COMPLETE two-action machine
  @{const relay_machine_step} / @{const relay_trace} itself --- own-machine
  reachability instead of the label-only carrier
  @{thm [source] relay_reachable_inv} --- and lands its safe side: along any
  @{const relay_trace} of @{const I_relay} from the genesis initial state,
  no observable mismatch exists when crashing at a
  @{const relay_complete_through} frontier.  This closes the two-action
  machine's own-safety gap: the label-only carrier sees no
  \<open>Relay_Reconcile\<close> action, so it cannot serve the machine that also
  reconciles.
\<close>

theorem relay_inv_machine_step:
  assumes step: "relay_machine_step s a s'"
      and inv: "relay_inv s"
  shows "relay_inv s'"
  using step
proof (cases rule: relay_machine_step.cases)
  case (rms_label b)
  have "relay_step s b s'" using rms_label by simp
  from relay_inv_step[OF this inv] show ?thesis .
next
  case (rms_reconcile g)
  have rec: "relay_bounded_replay_reconcile s g s'" using rms_reconcile by simp
  show ?thesis by (rule relay_inv_bounded_replay_reconcile[OF rec inv])
qed

theorem relay_inv_relay_trace:
  assumes trace: "relay_trace I s xs s'"
      and machine: "relay_transition I = relay_machine_step"
      and inv: "relay_inv s"
  shows "relay_inv s'"
  using trace machine inv
proof (induction rule: relay_trace.induct)
  case (relay_trace_refl I s)
  show ?case by (rule relay_trace_refl.prems(2))
next
  case (relay_trace_step I s a s' as s'')
  have step: "relay_machine_step s a s'"
    using relay_trace_step.hyps(1) relay_trace_step.prems(1) by simp
  have "relay_inv s'"
    by (rule relay_inv_machine_step[OF step relay_trace_step.prems(2)])
  then show ?case by (rule relay_trace_step.IH[OF relay_trace_step.prems(1)])
qed

corollary I_relay_reachable_relay_inv:
  assumes trace: "relay_trace (I_relay s0) s xs s'"
      and inv: "relay_inv s"
  shows "relay_inv s'"
  by (rule relay_inv_relay_trace[OF trace _ inv]) (simp add: I_relay_def)

theorem complete_relay_machine_safe_side:
  assumes reach: "relay_trace (I_relay (initial_exec_state (\<lambda>_. None) K fin))
                    (relay_initial (I_relay (initial_exec_state (\<lambda>_. None) K fin)))
                    xs s"
      and complete: "relay_complete_through s f"
      and le_fin: "f \<le> exec_finish s"
  shows "\<not> observable_mismatch (s\<lparr>exec_status := Crashed f\<rparr>) f k"
proof -
  have init: "relay_initial (I_relay (initial_exec_state (\<lambda>_. None) K fin))
                = initial_exec_state (\<lambda>_. None) K fin"
    by (simp add: I_relay_def)
  have inv: "relay_inv s"
    by (rule I_relay_reachable_relay_inv[OF reach[unfolded init] relay_inv_initial])
  show ?thesis
    by (rule relay_inv_no_observable_mismatch[OF inv complete le_fin])
qed

text \<open>The same fact against the NAMED frontier-scoped property
  (@{const relay_complete_frontier_safe}): the two-action machine's
  reachable states carry the relay's whole safe side --- complete-frontier
  safety, never membership of the global no-reachable-bad-crash class ---
  as one predicate.  A thin wrapper; the statement of record above is
  unchanged.\<close>

corollary complete_relay_machine_complete_frontier_safe:
  assumes reach: "relay_trace (I_relay (initial_exec_state (\<lambda>_. None) K fin))
                    (relay_initial (I_relay (initial_exec_state (\<lambda>_. None) K fin)))
                    xs s"
  shows "relay_complete_frontier_safe s"
proof -
  have init: "relay_initial (I_relay (initial_exec_state (\<lambda>_. None) K fin))
                = initial_exec_state (\<lambda>_. None) K fin"
    by (simp add: I_relay_def)
  have inv: "relay_inv s"
    by (rule I_relay_reachable_relay_inv[OF reach[unfolded init] relay_inv_initial])
  show ?thesis
    by (rule relay_inv_complete_frontier_safe[OF inv])
qed

end
