(*  Title:       Dual_Write_Effect_Terminal_Class_Membership.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    The terminal machine is a member of the absorbing-atomic-recovery
    class (theory-backlog item K, slice K2) --- an additive post-freeze
    slice under the freeze's own protocol: no landed statement, proof,
    definition, name, import, or session-DAG change to the frozen
    corpus.

    THIS THEORY LIVES ON THE TERMINAL (Design B) BRANCH.  It imports the
    branch-neutral class theory (Dual_Write_Effect_Recovery_Class) and
    the landed terminal lane (Dual_Write_Effect_Terminal_Inexpressibility);
    nothing cyclic sits in its import cone (the freeze's namespace rule;
    the cyclic branch's class-violation certificate is this theory's
    sibling on the other branch, cited as prose only).

    WHAT IT PROVES.  The terminal wrapper's two transition kinds are
    packaged as ONE unified step relation over a two-constructor action
    type; the init FAMILY is the whole (b, K, fin) parameter range as a
    set; and the interpretation below discharges the class's four
    assumptions FROM THE LANDED SECTION-17 LEMMA SET, lemma for lemma:
    pre_recovery_sync_init feeds init_sync; dwe_step_recovered_stays and
    no_reconcile_from_recovered feed absorbing;
    dwe_step_pre_recovery_sync (whose guarded shape enters through the
    class theory's atomic_divergence_from_guarded adapter, consumed
    verbatim) and emitting_reconcile_status_recovered feed
    atomic_divergence; status-datatype distinctness feeds
    crashed_not_absorbed.  Membership makes the abstract no-pair law an
    instantiated theorem of this machine, and the landed headline
    (terminal_no_payload_divergent_crashed_pair, the theorem of record)
    RE-DERIVES as an interpretation corollary under a new name --- a
    sanity tie-back, never a replacement.

    THE REACHABILITY GLUE IS DELIBERATELY WIDER THAN THE LANDED TRACE
    RELATION.  The class's reach closes the unified step over the init
    family WITHOUT the temporal trace's wellformedness side conditions
    (wellformed_exec_state / exec_label_preserves_history_wf on label
    steps).  Dropping side conditions only ENLARGES the reachable set,
    and every class conclusion consumed here is a NEGATIVE over reach
    (no pair exists within reach), so the conclusions for the landed
    dwe_reachable states follow a fortiori --- the safe direction, said
    here once and relied on below.

    THE OBS CHOICE CARRIES THE PAYLOAD-LEVEL QUALIFIER.  Membership
    holds at obs := the ledger's PAYLOAD projection.  At the
    stamp-inclusive ledger itself (obs := dwe_emitted) membership is
    IMPOSSIBLE FOR EVERY CANDIDATE ANCHOR: the landed nuance witnesses
    tA/tB (equal cores, stamp-divergent ledgers, both reachable and
    crashed) refute every anchor function pointwise, and hence every
    interpretation of the class at that observable.  Both forms are
    proved below as designed CONTROLS --- the class-level face of the
    landed payload-level qualifier (crashed_stamp_divergence), not new
    negative laws about recovery.

    THE CLASS LAW STAYS ONE-DIRECTIONAL, and its \<forall> ranges over the
    named premise class on the INEXPRESSIBILITY side only: no defeat
    theorem of the landed corpus is restated, strengthened, or
    generalized here (those stay exists-system, on their own branch),
    and class-membership failure implies nothing about pair
    reachability (the class theory records the counterexample; no
    converse is stated or suggested anywhere in this theory).

    PROVENANCE: theory-backlog item K
    (paper/dual_write/theory_backlog/BACKLOG_EXPLORATION.md section 6,
    flipped to conditional candidate by the design spike
    paper/dual_write/theory_backlog/KL_LOCALE_DESIGN.md, whose sections
    2-3 pin the locale and the lemma-for-lemma lift table this
    interpretation realizes).

    In-source ML oracle gates are STRIPPED at landing: oracle-freedom
    is certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Terminal_Class_Membership
  imports Dual_Write_Effect_Recovery_Class
          Dual_Write_Effect_Terminal_Inexpressibility
begin

section \<open>The unified step and the class parameters, terminal readings\<close>

text \<open>
  The class sees ONE transition relation.  The terminal machine has two
  transition kinds --- lifted labels (@{const dwe_step}) and the
  checkpointed emitting reconcile (@{const emitting_reconcile}) --- and
  its OWN temporal action vocabulary already tags exactly them
  (@{typ "('k, 'v) dwe_action"}, the landed trace-action type), so the
  unified step below is a case split over that landed type; nothing
  else is added, and in particular NO rule of the landed machine is
  changed, duplicated, or extended.  The init family is the whole
  @{term "(b, K, fin)"} parameter range at once: the class's
  cross-parameter strength lives in @{text terminal_class_inits}
  (defined below) being a SET, exactly as the landed headline's
  cross-parameter form quantifies both sides' parameters independently.
\<close>

definition terminal_class_step
  :: "('k, 'v) dwe_state \<Rightarrow> ('k, 'v) dwe_action \<Rightarrow>
      ('k, 'v) dwe_state \<Rightarrow> bool"
where
  "terminal_class_step t a t' \<longleftrightarrow>
     (case a of
        DWE_Label l \<Rightarrow> dwe_step t l t'
      | DWE_Reconcile m f \<Rightarrow> emitting_reconcile m t f t')"

definition terminal_class_inits :: "('k, 'v) dwe_state set" where
  "terminal_class_inits = (\<Union>b K fin. {dwe_init b K fin})"

text \<open>The remaining class parameters, in this machine's vocabulary:
  the divergence observable is the ledger's PAYLOAD projection (the
  qualifier the landed section-17 lane already carries; the controls at
  the end show it is load-bearing at class level too); the anchor is
  the core's durable downstream history; absorbed is the terminal
  recovery status; crashed is the status every recovery transition of
  this machine fires from.\<close>

definition terminal_class_obs
  :: "('k, 'v) dwe_state \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list"
where
  "terminal_class_obs t = map e_payload (dwe_emitted t)"

definition terminal_class_absorbed :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "terminal_class_absorbed t \<longleftrightarrow> exec_status (dwe_core t) = Recovered"

definition terminal_class_crashed :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "terminal_class_crashed t \<longleftrightarrow> (\<exists>c. exec_status (dwe_core t) = Crashed c)"

section \<open>The four obligations, discharged from the landed lemma set\<close>

text \<open>
  Each obligation is a separate named lemma (house-debuggable) fed to
  the interpretation command, and each consumes the landed section-17
  facts as-is --- the design study's lift table, realized: no landed
  proof is re-done, and the one genuinely machine-specific fact
  (@{thm [source] dwe_step_pre_recovery_sync}) enters through the class
  theory's guarded-shape adapter exactly as banked.
\<close>

lemma terminal_class_init_sync:
  assumes "t \<in> terminal_class_inits"
  shows "terminal_class_obs t = exec_down_hist (dwe_core t)"
proof -
  from assms obtain b K fin where t: "t = dwe_init b K fin"
    by (auto simp: terminal_class_inits_def)
  have "exec_status (dwe_core t) \<noteq> Recovered"
    by (simp add: t dwe_init_def initial_exec_state_def)
  with pre_recovery_sync_init[of b K fin] show ?thesis
    by (simp add: t terminal_class_obs_def pre_recovery_sync_def
                  ledger_matches_down_def)
qed

lemma terminal_class_absorbing:
  assumes "terminal_class_step t a t'"
      and "terminal_class_absorbed t"
  shows "terminal_class_absorbed t'"
proof (cases a)
  case (DWE_Label l)
  with assms show ?thesis
    unfolding terminal_class_step_def terminal_class_absorbed_def
    by (auto intro: dwe_step_recovered_stays)
next
  case (DWE_Reconcile m f)
  with assms have False
    unfolding terminal_class_step_def terminal_class_absorbed_def
    by (auto dest: no_reconcile_from_recovered)
  then show ?thesis ..
qed

text \<open>The guarded invariant preservation over the UNIFIED step: the
  label part is the landed @{thm [source] dwe_step_pre_recovery_sync}
  verbatim; the reconcile part lands absorbed
  (@{thm [source] emitting_reconcile_status_recovered}), making the
  guard vacuous.\<close>

lemma terminal_class_guarded:
  assumes "terminal_class_step t a t'"
      and "pre_recovery_sync t"
  shows "pre_recovery_sync t'"
proof (cases a)
  case (DWE_Label l)
  with assms show ?thesis
    unfolding terminal_class_step_def
    by (auto intro: dwe_step_pre_recovery_sync)
next
  case (DWE_Reconcile m f)
  with assms(1) have "exec_status (dwe_core t') = Recovered"
    unfolding terminal_class_step_def
    by (auto intro: emitting_reconcile_status_recovered)
  then show ?thesis by (simp add: pre_recovery_sync_def)
qed

text \<open>The same fact in the adapter's guarded shape (the class
  parameters spelled out), then @{text atomic_divergence} via the class
  theory's @{thm [source] atomic_divergence_from_guarded} --- the
  verbatim-discharge claim of the design study, executed.\<close>

lemma terminal_class_guarded_shape:
  assumes "terminal_class_step t a t'"
      and "\<not> terminal_class_absorbed t \<longrightarrow>
             terminal_class_obs t = exec_down_hist (dwe_core t)"
  shows "\<not> terminal_class_absorbed t' \<longrightarrow>
           terminal_class_obs t' = exec_down_hist (dwe_core t')"
  using terminal_class_guarded[OF assms(1)] assms(2)
  by (simp add: pre_recovery_sync_def ledger_matches_down_def
                terminal_class_obs_def terminal_class_absorbed_def)

lemma terminal_class_atomic_divergence:
  assumes "terminal_class_step t a t'"
      and "\<not> terminal_class_absorbed t"
      and "terminal_class_obs t = exec_down_hist (dwe_core t)"
  shows "terminal_class_obs t' = exec_down_hist (dwe_core t')
         \<or> terminal_class_absorbed t'"
  by (rule atomic_divergence_from_guarded[where step = terminal_class_step
        and absorbed = terminal_class_absorbed and obs = terminal_class_obs
        and anchor = exec_down_hist and core = dwe_core,
        OF terminal_class_guarded_shape assms])

lemma terminal_class_crashed_not_absorbed:
  assumes "terminal_class_crashed t"
  shows "\<not> terminal_class_absorbed t"
  using assms
  by (auto simp: terminal_class_crashed_def terminal_class_absorbed_def)

section \<open>Membership: the terminal machine interprets the class\<close>

text \<open>
  The interpretation is the membership certificate.  Everything the
  class proves --- the disjunctive invariant, the anchored-crashed-state
  equation, and the no-pair law --- becomes a theorem of THIS machine at
  these parameter readings, cross-parameter because the init family is
  the whole parameter range.  (Command choice: @{command
  interpretation} at theory level, which persists and exports the
  instantiated theorems; @{command global_interpretation}'s extra
  power --- mixin definitions --- is not needed because every parameter
  is already a named definition.)
\<close>

interpretation terminal_class: absorbing_atomic_recovery
  terminal_class_step terminal_class_inits dwe_core terminal_class_obs
  exec_down_hist terminal_class_absorbed terminal_class_crashed
proof (unfold_locales)
  show "\<And>t. t \<in> terminal_class_inits \<Longrightarrow>
          terminal_class_obs t = exec_down_hist (dwe_core t)"
    by (rule terminal_class_init_sync)
  show "\<And>t a t'. terminal_class_step t a t' \<Longrightarrow>
          terminal_class_absorbed t \<Longrightarrow> terminal_class_absorbed t'"
    by (rule terminal_class_absorbing)
  show "\<And>t a t'. terminal_class_step t a t' \<Longrightarrow>
          \<not> terminal_class_absorbed t \<Longrightarrow>
          terminal_class_obs t = exec_down_hist (dwe_core t) \<Longrightarrow>
          terminal_class_obs t' = exec_down_hist (dwe_core t')
          \<or> terminal_class_absorbed t'"
    by (rule terminal_class_atomic_divergence)
  show "\<And>t. terminal_class_crashed t \<Longrightarrow> \<not> terminal_class_absorbed t"
    by (rule terminal_class_crashed_not_absorbed)
qed

section \<open>Reachability glue: landed reachability lands inside class reach\<close>

text \<open>
  The landed temporal traces walk inside the class's reach: a label
  step is a @{const DWE_Label} unified step, a reconcile a
  @{const DWE_Reconcile} one, and the trace rules' wellformedness side
  conditions are simply DROPPED (the disclosed safe direction --- see
  the header: reach only grows, and the class conclusions are negatives
  over reach).
\<close>

lemma dwe_temporal_trace_class_reach:
  assumes "dwe_temporal_trace t acts t'"
      and "terminal_class.reach t"
  shows "terminal_class.reach t'"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_temporal_refl t)
  then show ?case .
next
  case (dwe_temporal_label_step t a t' as t'')
  have "terminal_class_step t (DWE_Label a) t'"
    using dwe_temporal_label_step.hyps(1)
    by (simp add: terminal_class_step_def)
  then have "terminal_class.reach t'"
    by (rule terminal_class.reach_step[OF dwe_temporal_label_step.prems])
  then show ?case by (rule dwe_temporal_label_step.IH)
next
  case (dwe_temporal_reconcile_step m t f t' as t'')
  have "terminal_class_step t (DWE_Reconcile m f) t'"
    using dwe_temporal_reconcile_step.hyps(1)
    by (simp add: terminal_class_step_def)
  then have "terminal_class.reach t'"
    by (rule terminal_class.reach_step[OF dwe_temporal_reconcile_step.prems])
  then show ?case by (rule dwe_temporal_reconcile_step.IH)
qed

theorem dwe_reachable_class_reach:
  assumes "dwe_reachable b K fin t"
  shows "terminal_class.reach t"
proof -
  from assms obtain acts
    where tr: "dwe_temporal_trace (dwe_init b K fin) acts t"
    by (auto simp: dwe_reachable_def)
  have "dwe_init b K fin \<in> terminal_class_inits"
    by (auto simp: terminal_class_inits_def)
  then have "terminal_class.reach (dwe_init b K fin)"
    by (rule terminal_class.reach_init)
  with tr show ?thesis by (rule dwe_temporal_trace_class_reach)
qed

section \<open>The sanity tie-back: the landed headline as an interpretation corollary\<close>

text \<open>
  The landed @{thm [source] terminal_no_payload_divergent_crashed_pair}
  (@{text Dual_Write_Effect_Terminal_Inexpressibility}) remains THE THEOREM OF
  RECORD; the corollary below re-derives its statement through the
  class law and the glue, under a new name, as the designed sanity
  tie-back --- if the abstraction had lost content, this derivation
  would not close.  It shadows nothing and replaces nothing.
\<close>

theorem terminal_no_payload_divergent_crashed_pair_via_class:
  "\<not> (\<exists>(t :: ('k, 'v) dwe_state) t' b K fin b' K' fin' c c'.
        dwe_reachable b K fin t
      \<and> dwe_reachable b' K' fin' t'
      \<and> exec_status (dwe_core t) = Crashed c
      \<and> exec_status (dwe_core t') = Crashed c'
      \<and> dwe_core t = dwe_core t'
      \<and> map e_payload (dwe_emitted t) \<noteq> map e_payload (dwe_emitted t'))"
proof
  assume "\<exists>(t :: ('k, 'v) dwe_state) t' b K fin b' K' fin' c c'.
            dwe_reachable b K fin t
          \<and> dwe_reachable b' K' fin' t'
          \<and> exec_status (dwe_core t) = Crashed c
          \<and> exec_status (dwe_core t') = Crashed c'
          \<and> dwe_core t = dwe_core t'
          \<and> map e_payload (dwe_emitted t) \<noteq> map e_payload (dwe_emitted t')"
  then obtain t t' b K fin b' K' fin' c c'
    where reach: "dwe_reachable b K fin (t :: ('k, 'v) dwe_state)"
      and reach': "dwe_reachable b' K' fin' t'"
      and crashed: "exec_status (dwe_core t) = Crashed c"
      and crashed': "exec_status (dwe_core t') = Crashed c'"
      and cores: "dwe_core t = dwe_core t'"
      and diverge: "map e_payload (dwe_emitted t) \<noteq> map e_payload (dwe_emitted t')"
    by blast
  have "terminal_class_obs t = exec_down_hist (dwe_core t)"
    by (rule terminal_class.crashed_obs_anchored
          [OF dwe_reachable_class_reach[OF reach]])
       (auto simp: terminal_class_crashed_def crashed)
  moreover have "terminal_class_obs t' = exec_down_hist (dwe_core t')"
    by (rule terminal_class.crashed_obs_anchored
          [OF dwe_reachable_class_reach[OF reach']])
       (auto simp: terminal_class_crashed_def crashed')
  ultimately have "terminal_class_obs t = terminal_class_obs t'"
    by (simp add: cores)
  with diverge show False
    by (simp add: terminal_class_obs_def)
qed

section \<open>CONTROLS: at the stamp-inclusive observable, no anchor exists\<close>

text \<open>
  The class-level face of the landed payload-level qualifier.  The
  landed nuance witnesses @{const tA} / @{const tB}
  (@{thm [source] crashed_stamp_divergence}) are reachable crashed
  states with EQUAL cores and DIFFERENT ledgers, differing only in a
  stamp.  Consequences, both designed controls and neither a new law:
  (i) POINTWISE, no function of the core can reproduce the raw ledger
  across this machine's reachable crashed states --- so the anchored
  equation the class law rests on has NO candidate anchor at
  obs := @{const dwe_emitted}; (ii) AT CLASS LEVEL, no anchor function
  makes this machine (same unified step, same init family, same
  absorbed/crashed readings) a member of the class at the
  stamp-inclusive observable: the payload projection in
  @{const terminal_class_obs} is load-bearing for membership, exactly
  as the payload qualifier is load-bearing in the landed headline.
\<close>

theorem stamp_level_no_anchor:
  "\<not> (\<exists>anchor. \<forall>t :: (nat, nat) dwe_state.
        dwe_reachable Map.empty {0, 1} ec2 t \<longrightarrow>
        terminal_class_crashed t \<longrightarrow>
        dwe_emitted t = anchor (dwe_core t))"
proof
  assume "\<exists>anchor. \<forall>t :: (nat, nat) dwe_state.
            dwe_reachable Map.empty {0, 1} ec2 t \<longrightarrow>
            terminal_class_crashed t \<longrightarrow>
            dwe_emitted t = anchor (dwe_core t)"
  then obtain anchor
    where A: "\<forall>t :: (nat, nat) dwe_state.
                dwe_reachable Map.empty {0, 1} ec2 t \<longrightarrow>
                terminal_class_crashed t \<longrightarrow>
                dwe_emitted t = anchor (dwe_core t)" ..
  have cA: "terminal_class_crashed tA"
    using crashed_tA by (auto simp: terminal_class_crashed_def)
  have cB: "terminal_class_crashed tB"
    using crashed_tB by (auto simp: terminal_class_crashed_def)
  have "dwe_emitted tA = anchor (dwe_core tA)"
    by (rule A[rule_format, OF reach_tA cA])
  moreover have "dwe_emitted tB = anchor (dwe_core tB)"
    by (rule A[rule_format, OF reach_tB cB])
  ultimately have "dwe_emitted tA = dwe_emitted tB"
    by (metis cores_equal_stamp_pair)
  with ledgers_stamp_divergent show False ..
qed

theorem stamp_obs_no_class_membership:
  "\<not> (\<exists>anchor. absorbing_atomic_recovery terminal_class_step
                 (terminal_class_inits :: (nat, nat) dwe_state set)
                 dwe_core dwe_emitted anchor
                 terminal_class_absorbed terminal_class_crashed)"
proof
  assume "\<exists>anchor. absorbing_atomic_recovery terminal_class_step
                     (terminal_class_inits :: (nat, nat) dwe_state set)
                     dwe_core dwe_emitted anchor
                     terminal_class_absorbed terminal_class_crashed"
  then obtain anchor
    where mem: "absorbing_atomic_recovery terminal_class_step
                  (terminal_class_inits :: (nat, nat) dwe_state set)
                  dwe_core dwe_emitted anchor
                  terminal_class_absorbed terminal_class_crashed" ..
  have rA: "terminal_class.reach tA"
    by (rule dwe_reachable_class_reach[OF reach_tA])
  have rB: "terminal_class.reach tB"
    by (rule dwe_reachable_class_reach[OF reach_tB])
  have cA: "terminal_class_crashed tA"
    using crashed_tA by (auto simp: terminal_class_crashed_def)
  have cB: "terminal_class_crashed tB"
    using crashed_tB by (auto simp: terminal_class_crashed_def)
  have "dwe_emitted tA = anchor (dwe_core tA)"
    by (rule absorbing_atomic_recovery.crashed_obs_anchored[OF mem rA cA])
  moreover have "dwe_emitted tB = anchor (dwe_core tB)"
    by (rule absorbing_atomic_recovery.crashed_obs_anchored[OF mem rB cB])
  ultimately have "dwe_emitted tA = dwe_emitted tB"
    by (metis cores_equal_stamp_pair)
  with ledgers_stamp_divergent show False ..
qed


end
