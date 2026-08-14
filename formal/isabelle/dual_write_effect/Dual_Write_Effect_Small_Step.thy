(*  Title:       Dual_Write_Effect_Small_Step.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    The small-step reconcile variant (theory-backlog item D, Design B of
    the priced design study) --- an additive post-freeze slice under the
    freeze's own protocol: no landed statement, proof, definition, name,
    import, or session-DAG change to the frozen corpus.  This theory is a
    ROBUSTNESS CERTIFICATE for the disclosed atomic big-step reconcile
    boundary (boundary row 1), never a new primary machine: owner
    decision D5 (cyclic promotion) stays closed, and every landed theorem
    keeps its own machine.

    THE VARIANT MACHINE.  One new rule and nothing else: ss_fire_one
    fires ONE entry of the scoped, frontier-bounded replay from a Crashed
    state, appending it to the emission ledger stamped exactly as the
    landed rules stamp (committed-prefix length, current epoch) --- a
    CORE STUTTER: no core field and no epoch changes, so boundary row 9's
    simulation-seam inventory is untouched (the only core-touching rules
    remain the landed ones).  The variant trace relation has the four
    landed rule kinds with the landed relations (dwe_step,
    emitting_reconcile, dwe_resume) as their rule bodies VERBATIM, plus
    the fire case, over its own action datatype (the frozen dwe_action
    is not extended); dwe_ss_reachable starts from the same pinned init
    as the landed dwe_reachable.

    WHAT BECOMES EXPRESSIBLE.  A crash DURING a re-drive is a STOPPED
    fire sequence: the machine is already Crashed while firing, a crash
    while crashed is a no-op, and the epoch counts Resumes (recovery
    generations), not crash attempts --- no new status, no new crash
    rule, no epoch semantics question.  The landed atomic reconcile
    factors through the variant (atomic_redrive_decomposes): cursor-m
    re-drive = fire the suffix entry by entry, then the HEAL-ONLY
    reconcile, which is the landed rule itself at cursor length-of-replay
    (heal_only_reconcile: drop (length R) R = [], so the bare heal is a
    special case of the landed rule, not a new rule).  A mid-redrive
    state is a genuine machine state here; the new-behavior witness at
    the end exhibits one REACHED BY A FIRE and machine-checked
    UNREACHABLE on the landed cyclic machine (via the epoch-0
    pre-recovery sync invariant proved below), so the variant genuinely
    adds behavior --- an in-flight partial ledger extension at Crashed
    status.

    STATUS PHYSICS OF A FIRE EPISODE (checked against the locked core,
    the design study's R2 check): every dw_exec_step rule except recover
    and the identity observe requires Running status, so while the
    machine is Crashed the core is FROZEN up to identity Observe
    stutters --- no source commit can interleave a fire episode.  The
    interleavings the variant adds are stopped and abandoned episodes
    (fires followed by Recover without the completing heal), not commit
    interleavings.

    HAZARD PHYSICS.  Fires are replay-bounded, so every fired entry is
    justified at its fire-time stamp (ss_fire_emission_justified, the
    pointwise form of the landed redrive_emissions_justified) --- the
    fire rule cannot create premature entries.  It CAN refire an
    already-emitted payload: the machine is at-least-once physics, and
    the refire-duplicate witness below reaches a duplicate state by two
    fires of the same payload, every entry individually justified.
    Ordering and freshness live in the discipline (the landed T2.8
    guards; the variant's discipline twin is the follow-on slice), never
    in the rule.

    THE DILEMMA TRANSFER (the robustness claim of boundary row 1, made a
    theorem).  The landed defeat certificate is machine-independent
    everywhere except its two reachability conjuncts: policy_redrive is
    a definition, and store_measured, effect_unsafe, lost_effect,
    mismatch_at, genuinely_emitting are functions of states of the
    unchanged record type.  Every cyclic trace embeds into the variant
    (cyclic_traces_embed), a small-step machine only GROWS the reachable
    set, and an exists-pair defeat evaluated at fixed states survives
    added behaviors --- so batch_agreement_dilemma,
    recovery_information_dilemma (+ pair form), and
    epoch_measured_dilemma restate VERBATIM with dwe_ss_reachable.  The
    exists-system polarity is preserved: there is a dual-write system
    (the pinned witness machine, now with more behaviors) on which every
    store-measured re-drive policy is defeated; nothing here says "for
    every system".

    THE ADAPTIVE ADDENDUM.  A per-entry strategy chooses each fired
    entry as a function of the EVOLVING state (option-valued chooser;
    fuel-bounded fired sequence, so every statement is about the n-step
    episode --- an honest bound, not a termination claim).  Because
    fires are core stutters, a core-measured strategy fires
    LOCKSTEP-EQUAL sequences on any equal-core pair
    (ss_adaptive_lockstep), so its induced n-step episode policy agrees
    on the dilemma pair and the landed batch-agreement kernel defeats it
    (ss_adaptive_strategy_dilemma); the (core, epoch)-measured class
    falls to the same pair (equal epochs, fires epoch-constant).  When
    the fired sequence is replay-bounded the episode is realizable as a
    genuine variant trace ending in the policy redrive's own result
    state (ss_adaptive_episode_realizable via policy_redrive_decomposes).

    FENCES (binding, from the freeze documents).  The variant is an
    appendix-grade robustness certificate; the landed cyclic machine
    remains the machine of record for every landed theorem.  The
    terminal branch stays out of the import cone, and the
    terminal-inexpressibility scoping ("the operational dilemma needs
    the recovery cycle", per-machine, for the landed atomic rule set) is
    untouched by this slice: the fire rule exists on the CYCLIC lane
    only.  No unqualified exactly-once claim is made or implied;
    lost_effect carries the landed definition site's two pinned readings
    (bulk-restore; terminal-state stand-in) unchanged.

    IMPORTS: Dual_Write_Effect_Dilemma alone --- the headline family,
    the policy vocabulary, and the designed equal-core pair this theory
    restates; through it the cyclic machine and the locked core.  The
    terminal branch (Dual_Write_Effect_Machine / _Witnesses) is
    deliberately NOT imported (namespace rule: the two branches share
    hazard names by design).

    PROVENANCE: theory-backlog item D, Design B
    (paper/dual_write/theory_backlog/D_SMALLSTEP_DESIGN.md, build
    ratified by paper/dual_write/theory_backlog/EXTENSION_DIRECTIVE.md
    slice W2).

    In-source ML oracle gates are STRIPPED at landing: oracle-freedom is
    certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Small_Step
  imports Dual_Write_Effect_Dilemma
begin

section \<open>The per-entry fire rule: one replay-covered emission, core untouched\<close>

text \<open>
  @{text ss_fire_one} fires one entry @{term p} of the scoped,
  frontier-bounded replay of the committed source prefix from a Crashed
  state: the ledger appends one emission stamped with the CURRENT
  committed-prefix length and the CURRENT epoch --- exactly how the
  landed publish and re-drive rules stamp --- and nothing else moves.
  The rule's guards are the landed reconcile's own status and frontier
  guards plus replay membership of the fired entry; the persisted-cursor
  reading of the landed rule is recovered by the decomposition theorem
  below (the cursor suffix is fired entry by entry).
\<close>

definition ss_fire_one
  :: "frontier \<Rightarrow> (src_coord \<times> (nat, nat) source_event) \<Rightarrow>
      (nat, nat) dwe_state \<Rightarrow> (nat, nat) dwe_state \<Rightarrow> bool"
where
  "ss_fire_one f p t t' \<longleftrightarrow>
     (\<exists>c. exec_status (dwe_core t) = Crashed c)
   \<and> f \<le> exec_finish (dwe_core t)
   \<and> p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                 (exec_scope (dwe_core t)) f)
   \<and> t' = t\<lparr>dwe_emitted := dwe_emitted t
              @ [(length (exec_src_hist (dwe_core t)),
                  dwe_epoch t, fst p, snd p)]\<rparr>"

lemma ss_fire_oneI:
  assumes "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and "f \<le> exec_finish (dwe_core t)"
      and "p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                      (exec_scope (dwe_core t)) f)"
      and "t' = t\<lparr>dwe_emitted := dwe_emitted t
                    @ [(length (exec_src_hist (dwe_core t)),
                        dwe_epoch t, fst p, snd p)]\<rparr>"
  shows "ss_fire_one f p t t'"
  using assms by (simp add: ss_fire_one_def)

lemma ss_fire_one_core:
  assumes "ss_fire_one f p t t'"
  shows "dwe_core t' = dwe_core t"
  using assms by (simp add: ss_fire_one_def)

lemma ss_fire_one_epoch_const:
  assumes "ss_fire_one f p t t'"
  shows "dwe_epoch t' = dwe_epoch t"
  using assms by (simp add: ss_fire_one_def)

lemma ss_fire_one_emitted:
  assumes "ss_fire_one f p t t'"
  shows "dwe_emitted t' = dwe_emitted t
           @ [(length (exec_src_hist (dwe_core t)), dwe_epoch t, p)]"
  using assms by (simp add: ss_fire_one_def)

lemma ss_fire_one_emitted_ext:
  assumes "ss_fire_one f p t t'"
  shows "\<exists>es. dwe_emitted t' = dwe_emitted t @ es"
  using ss_fire_one_emitted[OF assms] by blast

lemma ss_fire_one_src_same:
  assumes "ss_fire_one f p t t'"
  shows "exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t)"
  using ss_fire_one_core[OF assms] by simp

text \<open>
  THE CORE STUTTER, as a named theorem (the seam-inventory fact of
  boundary row 9): a fire changes no core field and no epoch --- the
  only core-touching rules of the variant remain the landed ones, so no
  new simulation seam exists and the landed per-epoch wave is
  structurally unaffected.
\<close>

theorem ss_fire_core_stutter:
  assumes "ss_fire_one f p t t'"
  shows "dwe_core t' = dwe_core t \<and> dwe_epoch t' = dwe_epoch t"
  using ss_fire_one_core[OF assms] ss_fire_one_epoch_const[OF assms]
  by blast

text \<open>
  Fire-time justification physics (the pointwise form of the landed
  @{thm [source] redrive_emissions_justified}): the fired entry is
  justified against the committed prefix at its own stamp, for every
  fire.  The rule cannot create premature entries; what it CAN create is
  duplicates (witnessed at the end) --- at-least-once physics.
\<close>

theorem ss_fire_emission_justified:
  assumes "ss_fire_one f p t t'"
  shows "justified_at (exec_src_hist (dwe_core t'))
           (length (exec_src_hist (dwe_core t)), dwe_epoch t, p)"
proof -
  have p_in: "e_payload (length (exec_src_hist (dwe_core t)), dwe_epoch t, p)
                \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                         (exec_scope (dwe_core t)) f)"
    using assms by (simp add: ss_fire_one_def)
  have st: "e_stamp (length (exec_src_hist (dwe_core t)), dwe_epoch t, p)
              = length (exec_src_hist (dwe_core t))"
    by (simp add: e_stamp_def)
  show ?thesis
    unfolding ss_fire_one_src_same[OF assms]
    by (rule redrive_emissions_justified[OF p_in st])
qed

section \<open>The variant action type, trace relation, and reachability\<close>

text \<open>
  The frozen @{type dwe_action} datatype cannot be extended (freeze
  protocol), so the variant carries its own action type: the three
  landed kinds mirrored one-to-one plus the fire.  In the trace relation
  the three mirrored rules have the LANDED relations as their bodies
  verbatim --- same guards, same successor states --- so every landed
  per-rule lemma applies to the variant's cases unchanged.
\<close>

datatype ss_action =
    SS_Label "(nat, nat) dw_exec_label"
  | SS_Reconcile nat frontier
  | SS_Resume
  | SS_Fire frontier "src_coord \<times> (nat, nat) source_event"

inductive dwe_ss_temporal_trace
  :: "(nat, nat) dwe_state \<Rightarrow> ss_action list \<Rightarrow> (nat, nat) dwe_state \<Rightarrow> bool"
where
  dwe_ss_refl:
    "dwe_ss_temporal_trace t [] t"
| dwe_ss_label_step:
    "\<lbrakk>wellformed_exec_state (dwe_core t);
      exec_label_preserves_history_wf (dwe_core t) a;
      dwe_step t a t';
      dwe_ss_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwe_ss_temporal_trace t (SS_Label a # as) t''"
| dwe_ss_reconcile_step:
    "\<lbrakk>emitting_reconcile m t f t';
      dwe_ss_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwe_ss_temporal_trace t (SS_Reconcile m f # as) t''"
| dwe_ss_resume_step:
    "\<lbrakk>dwe_resume t t';
      dwe_ss_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwe_ss_temporal_trace t (SS_Resume # as) t''"
| dwe_ss_fire_step:
    "\<lbrakk>ss_fire_one f p t t';
      dwe_ss_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwe_ss_temporal_trace t (SS_Fire f p # as) t''"

lemma dwe_ss_temporal_trace_append:
  assumes "dwe_ss_temporal_trace s as s'"
      and "dwe_ss_temporal_trace s' bs s''"
  shows "dwe_ss_temporal_trace s (as @ bs) s''"
  using assms
  by (induction rule: dwe_ss_temporal_trace.induct)
     (auto intro: dwe_ss_temporal_trace.intros)

text \<open>Reachability, from the SAME pinned init as the landed
  @{const dwe_reachable}: type @{typ "(nat, nat) dwe_state"}, empty
  base, scope @{term "{0, 1}"}, finish frontier @{const ec2}.\<close>

definition dwe_ss_reachable :: "(nat, nat) dwe_state \<Rightarrow> bool" where
  "dwe_ss_reachable t \<longleftrightarrow>
     (\<exists>xs. dwe_ss_temporal_trace (dwe_init Map.empty {0, 1} ec2) xs t)"

lemma dwe_ss_reachable_fire_ext:
  assumes "dwe_ss_reachable t"
      and "ss_fire_one f p t t'"
  shows "dwe_ss_reachable t'"
proof -
  obtain xs where xs: "dwe_ss_temporal_trace (dwe_init Map.empty {0, 1} ec2) xs t"
    using assms(1) unfolding dwe_ss_reachable_def by blast
  have one: "dwe_ss_temporal_trace t [SS_Fire f p] t'"
    by (rule dwe_ss_temporal_trace.dwe_ss_fire_step[OF assms(2)
          dwe_ss_temporal_trace.dwe_ss_refl])
  show ?thesis
    unfolding dwe_ss_reachable_def
    using dwe_ss_temporal_trace_append[OF xs one] by blast
qed

section \<open>The embedding: every cyclic trace is a variant trace\<close>

text \<open>
  Rule inclusion, action by action: the variant's mirrored rules ARE the
  landed rules, so a cyclic trace maps to a variant trace under the
  one-to-one action lift.  This is the transfer engine of the dilemma
  restatements below: a small-step machine only GROWS the reachable set.
\<close>

fun lift_action :: "(nat, nat) dwe_action \<Rightarrow> ss_action" where
  "lift_action (DWE_Label a) = SS_Label a"
| "lift_action (DWE_Reconcile m f) = SS_Reconcile m f"
| "lift_action DWE_Resume = SS_Resume"

theorem cyclic_traces_embed:
  assumes "dwe_temporal_trace t xs t'"
  shows "dwe_ss_temporal_trace t (map lift_action xs) t'"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  then show ?case by (simp add: dwe_ss_temporal_trace.dwe_ss_refl)
next
  case (dwe_label_step t a t' as t'')
  then show ?case
    by (auto intro: dwe_ss_temporal_trace.dwe_ss_label_step)
next
  case (dwe_reconcile_step m t f t' as t'')
  then show ?case
    by (auto intro: dwe_ss_temporal_trace.dwe_ss_reconcile_step)
next
  case (dwe_resume_step t t' as t'')
  then show ?case
    by (auto intro: dwe_ss_temporal_trace.dwe_ss_resume_step)
qed

corollary ss_reachable_of_reachable:
  assumes "dwe_reachable t"
  shows "dwe_ss_reachable t"
proof -
  obtain xs where "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2) xs t"
    using assms unfolding dwe_reachable_def by blast
  then show ?thesis
    unfolding dwe_ss_reachable_def
    using cyclic_traces_embed by blast
qed

section \<open>The decomposition: the atomic re-drive factors through fires + the bare heal\<close>

text \<open>
  Fires preserve the core, so along a pure fire sequence the committed
  prefix, the scope, and the epoch are frozen: firing a batch composes
  into ONE cumulative ledger extension stamped at the fire episode's
  constant stamp.
\<close>

lemma ss_fires_compose:
  assumes "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and "f \<le> exec_finish (dwe_core t)"
      and "set ps \<subseteq> set (replay_down_hist (exec_src_hist (dwe_core t))
                           (exec_scope (dwe_core t)) f)"
  shows "dwe_ss_temporal_trace t (map (SS_Fire f) ps)
           (t\<lparr>dwe_emitted := dwe_emitted t
                @ map (\<lambda>p. (length (exec_src_hist (dwe_core t)),
                            dwe_epoch t, p)) ps\<rparr>)"
  using assms
proof (induction ps arbitrary: t)
  case Nil
  have "t\<lparr>dwe_emitted := dwe_emitted t
            @ map (\<lambda>p. (length (exec_src_hist (dwe_core t)),
                        dwe_epoch t, p)) []\<rparr> = t"
    by (cases t) simp
  then show ?case
    using dwe_ss_temporal_trace.dwe_ss_refl by fastforce
next
  case (Cons p ps)
  define t1 where
    "t1 = t\<lparr>dwe_emitted := dwe_emitted t
              @ [(length (exec_src_hist (dwe_core t)), dwe_epoch t, p)]\<rparr>"
  have fire: "ss_fire_one f p t t1"
    by (rule ss_fire_oneI)
       (use Cons.prems in \<open>auto simp: t1_def\<close>)
  have core1: "dwe_core t1 = dwe_core t"
    by (simp add: t1_def)
  have crashed1: "\<exists>c. exec_status (dwe_core t1) = Crashed c"
    using Cons.prems(1) core1 by simp
  have fin1: "f \<le> exec_finish (dwe_core t1)"
    using Cons.prems(2) core1 by simp
  have sub1: "set ps \<subseteq> set (replay_down_hist (exec_src_hist (dwe_core t1))
                              (exec_scope (dwe_core t1)) f)"
    using Cons.prems(3) core1 by auto
  have rest: "dwe_ss_temporal_trace t1 (map (SS_Fire f) ps)
                (t1\<lparr>dwe_emitted := dwe_emitted t1
                      @ map (\<lambda>q. (length (exec_src_hist (dwe_core t1)),
                                  dwe_epoch t1, q)) ps\<rparr>)"
    by (rule Cons.IH[OF crashed1 fin1 sub1])
  have end_eq: "t1\<lparr>dwe_emitted := dwe_emitted t1
                     @ map (\<lambda>q. (length (exec_src_hist (dwe_core t1)),
                                 dwe_epoch t1, q)) ps\<rparr>
              = t\<lparr>dwe_emitted := dwe_emitted t
                    @ map (\<lambda>q. (length (exec_src_hist (dwe_core t)),
                                dwe_epoch t, q)) (p # ps)\<rparr>"
    by (simp add: t1_def)
  have "dwe_ss_temporal_trace t1 (map (SS_Fire f) ps)
          (t\<lparr>dwe_emitted := dwe_emitted t
               @ map (\<lambda>q. (length (exec_src_hist (dwe_core t)),
                           dwe_epoch t, q)) (p # ps)\<rparr>)"
    using rest end_eq by simp
  then have "dwe_ss_temporal_trace t (SS_Fire f p # map (SS_Fire f) ps)
               (t\<lparr>dwe_emitted := dwe_emitted t
                    @ map (\<lambda>q. (length (exec_src_hist (dwe_core t)),
                                dwe_epoch t, q)) (p # ps)\<rparr>)"
    by (rule dwe_ss_temporal_trace.dwe_ss_fire_step[OF fire])
  then show ?case by simp
qed

text \<open>
  THE BARE HEAL ALREADY EXISTS: the landed reconcile at cursor
  length-of-replay appends @{term "drop (length R) R = []"} --- the
  heal-only reconcile is a special case of the landed rule, not a new
  rule.
\<close>

lemma heal_only_reconcile:
  assumes crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and fin: "f \<le> exec_finish (dwe_core t)"
  shows "emitting_reconcile
           (length (replay_down_hist (exec_src_hist (dwe_core t))
                      (exec_scope (dwe_core t)) f))
           t f
           (t\<lparr>dwe_core := (dwe_core t)
                \<lparr>exec_down_hist :=
                   replay_down_hist (exec_src_hist (dwe_core t))
                     (exec_scope (dwe_core t)) f,
                 exec_pending := {},
                 exec_status := Recovered\<rparr>\<rparr>)"
proof -
  have emit_id: "t\<lparr>dwe_core := (dwe_core t)
                     \<lparr>exec_down_hist :=
                        replay_down_hist (exec_src_hist (dwe_core t))
                          (exec_scope (dwe_core t)) f,
                      exec_pending := {},
                      exec_status := Recovered\<rparr>\<rparr>
               = t\<lparr>dwe_core := (dwe_core t)
                     \<lparr>exec_down_hist :=
                        replay_down_hist (exec_src_hist (dwe_core t))
                          (exec_scope (dwe_core t)) f,
                      exec_pending := {},
                      exec_status := Recovered\<rparr>,
                   dwe_emitted := dwe_emitted t\<rparr>"
    by (cases t) simp
  show ?thesis
    unfolding emitting_reconcile_def
    using crashed fin emit_id by simp
qed

text \<open>
  THE DECOMPOSITION CORRESPONDENCE: the landed cursor-@{term m} atomic
  re-drive at frontier @{term f} equals, on the variant, firing the
  cursor suffix entry by entry and then completing with the bare heal
  --- same fired stamps, same final state EXACTLY.  Every mid-point of
  that action list is a machine state with the landed section-18
  modeled-intermediate footprint (a stamped prefix of the batch appended
  to the ledger, core untouched).
\<close>

theorem atomic_redrive_decomposes:
  assumes rec: "emitting_reconcile m t f t'"
      and R_def: "R = replay_down_hist (exec_src_hist (dwe_core t))
                        (exec_scope (dwe_core t)) f"
  shows "dwe_ss_temporal_trace t
           (map (SS_Fire f) (drop m R) @ [SS_Reconcile (length R) f]) t'"
proof -
  have crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
    using rec by (simp add: emitting_reconcile_def)
  have fin: "f \<le> exec_finish (dwe_core t)"
    using rec by (simp add: emitting_reconcile_def)
  define tmid where
    "tmid = t\<lparr>dwe_emitted := dwe_emitted t
                @ map (\<lambda>q. (length (exec_src_hist (dwe_core t)),
                            dwe_epoch t, q)) (drop m R)\<rparr>"
  have sub: "set (drop m R) \<subseteq> set (replay_down_hist (exec_src_hist (dwe_core t))
                                     (exec_scope (dwe_core t)) f)"
    unfolding R_def by (rule set_drop_subset)
  have fires: "dwe_ss_temporal_trace t (map (SS_Fire f) (drop m R)) tmid"
    unfolding tmid_def by (rule ss_fires_compose[OF crashed fin sub])
  have core_mid: "dwe_core tmid = dwe_core t"
    by (simp add: tmid_def)
  have crashed_mid: "\<exists>c. exec_status (dwe_core tmid) = Crashed c"
    using crashed core_mid by simp
  have fin_mid: "f \<le> exec_finish (dwe_core tmid)"
    using fin core_mid by simp
  have len_mid: "length (replay_down_hist (exec_src_hist (dwe_core tmid))
                           (exec_scope (dwe_core tmid)) f) = length R"
    using core_mid R_def by simp
  have heal: "emitting_reconcile (length R) tmid f
                (tmid\<lparr>dwe_core := (dwe_core tmid)
                        \<lparr>exec_down_hist :=
                           replay_down_hist (exec_src_hist (dwe_core tmid))
                             (exec_scope (dwe_core tmid)) f,
                         exec_pending := {},
                         exec_status := Recovered\<rparr>\<rparr>)"
    using heal_only_reconcile[OF crashed_mid fin_mid] len_mid by simp
  have t'_eq: "t' = t\<lparr>dwe_core := (dwe_core t)
                        \<lparr>exec_down_hist :=
                           replay_down_hist (exec_src_hist (dwe_core t))
                             (exec_scope (dwe_core t)) f,
                         exec_pending := {},
                         exec_status := Recovered\<rparr>,
                      dwe_emitted := dwe_emitted t
                        @ map (\<lambda>q. (length (exec_src_hist (dwe_core t)),
                                    dwe_epoch t, q)) (drop m R)\<rparr>"
    using rec by (simp add: emitting_reconcile_def R_def)
  have end_eq: "tmid\<lparr>dwe_core := (dwe_core tmid)
                       \<lparr>exec_down_hist :=
                          replay_down_hist (exec_src_hist (dwe_core tmid))
                            (exec_scope (dwe_core tmid)) f,
                        exec_pending := {},
                        exec_status := Recovered\<rparr>\<rparr> = t'"
    unfolding t'_eq tmid_def by (simp add: core_mid tmid_def)
  have last: "dwe_ss_temporal_trace tmid [SS_Reconcile (length R) f] t'"
    using heal end_eq
    by (metis dwe_ss_temporal_trace.dwe_ss_reconcile_step
          dwe_ss_temporal_trace.dwe_ss_refl)
  show ?thesis
    by (rule dwe_ss_temporal_trace_append[OF fires last])
qed

text \<open>
  The same decomposition for an arbitrary policy redrive whose batch is
  replay-bounded: fire the policy's batch entry by entry, then the bare
  heal.  (The landed kernel's alien-batch policies are deliberately NOT
  replay-bounded --- their episodes are defeated at the function level;
  this lemma is the machine-level realization for the bounded ones.)
\<close>

theorem policy_redrive_decomposes:
  assumes pr: "policy_redrive P t f t'"
      and sub: "set (P t) \<subseteq> set (replay_down_hist (exec_src_hist (dwe_core t))
                                   (exec_scope (dwe_core t)) f)"
  shows "dwe_ss_temporal_trace t
           (map (SS_Fire f) (P t)
            @ [SS_Reconcile (length (replay_down_hist
                 (exec_src_hist (dwe_core t)) (exec_scope (dwe_core t)) f)) f])
           t'"
proof -
  have crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
    using pr by (simp add: policy_redrive_def)
  have fin: "f \<le> exec_finish (dwe_core t)"
    using pr by (simp add: policy_redrive_def)
  define R where "R = replay_down_hist (exec_src_hist (dwe_core t))
                        (exec_scope (dwe_core t)) f"
  define tmid where
    "tmid = t\<lparr>dwe_emitted := dwe_emitted t
                @ map (\<lambda>q. (length (exec_src_hist (dwe_core t)),
                            dwe_epoch t, q)) (P t)\<rparr>"
  have fires: "dwe_ss_temporal_trace t (map (SS_Fire f) (P t)) tmid"
    unfolding tmid_def by (rule ss_fires_compose[OF crashed fin sub])
  have core_mid: "dwe_core tmid = dwe_core t"
    by (simp add: tmid_def)
  have crashed_mid: "\<exists>c. exec_status (dwe_core tmid) = Crashed c"
    using crashed core_mid by simp
  have fin_mid: "f \<le> exec_finish (dwe_core tmid)"
    using fin core_mid by simp
  have len_mid: "length (replay_down_hist (exec_src_hist (dwe_core tmid))
                           (exec_scope (dwe_core tmid)) f) = length R"
    using core_mid R_def by simp
  have heal: "emitting_reconcile (length R) tmid f
                (tmid\<lparr>dwe_core := (dwe_core tmid)
                        \<lparr>exec_down_hist :=
                           replay_down_hist (exec_src_hist (dwe_core tmid))
                             (exec_scope (dwe_core tmid)) f,
                         exec_pending := {},
                         exec_status := Recovered\<rparr>\<rparr>)"
    using heal_only_reconcile[OF crashed_mid fin_mid] len_mid by simp
  have t'_eq: "t' = t\<lparr>dwe_core := (dwe_core t)
                        \<lparr>exec_down_hist :=
                           replay_down_hist (exec_src_hist (dwe_core t))
                             (exec_scope (dwe_core t)) f,
                         exec_pending := {},
                         exec_status := Recovered\<rparr>,
                      dwe_emitted := dwe_emitted t
                        @ map (\<lambda>q. (length (exec_src_hist (dwe_core t)),
                                    dwe_epoch t, q)) (P t)\<rparr>"
    using pr by (simp add: policy_redrive_def)
  have end_eq: "tmid\<lparr>dwe_core := (dwe_core tmid)
                       \<lparr>exec_down_hist :=
                          replay_down_hist (exec_src_hist (dwe_core tmid))
                            (exec_scope (dwe_core tmid)) f,
                        exec_pending := {},
                        exec_status := Recovered\<rparr>\<rparr> = t'"
    unfolding t'_eq tmid_def by (simp add: core_mid tmid_def)
  have last: "dwe_ss_temporal_trace tmid [SS_Reconcile (length R) f] t'"
    using heal end_eq
    by (metis dwe_ss_temporal_trace.dwe_ss_reconcile_step
          dwe_ss_temporal_trace.dwe_ss_refl)
  show ?thesis
    unfolding R_def[symmetric]
    by (rule dwe_ss_temporal_trace_append[OF fires last])
qed

section \<open>Status physics of a fire episode: the crashed core is frozen\<close>

text \<open>
  The design study's R2 build-time check, done and machine-checked
  (correcting the design document's interleaving note, which mis-read
  the locked core): every @{const dw_exec_step} rule EXCEPT
  @{text recover} and the identity @{text observe} requires
  @{const Running} status.  So while the machine is Crashed --- the only
  status a fire can happen at --- the core admits exactly two moves: the
  identity Observe stutter and the status-only Recover.  NO source
  commit can interleave a fire episode; the interleavings the variant
  genuinely adds are STOPPED and ABANDONED episodes (fires followed by
  Recover without the completing heal), never commit interleavings.
  The design study's priced interleaved-commit composition lemma is
  therefore vacuous on this core and is not built.
\<close>

theorem crashed_core_frozen:
  assumes "dw_exec_step s a s'"
      and "exec_status s = Crashed c"
  shows "s' = s \<or> s' = s\<lparr>exec_status := Recovered\<rparr>"
  using assms by (cases rule: dw_exec_step.cases) auto

theorem crashed_wrapper_label_freeze:
  assumes step: "dwe_step t a t'"
      and crashed: "exec_status (dwe_core t) = Crashed c"
  shows "dwe_emitted t' = dwe_emitted t
       \<and> (dwe_core t' = dwe_core t
          \<or> dwe_core t' = (dwe_core t)\<lparr>exec_status := Recovered\<rparr>)"
  using step
proof (cases rule: dwe_step.cases)
  case (lift_nonpub c')
  then show ?thesis
    using crashed_core_frozen[OF _ crashed] by auto
next
  case (publish_emit pc pe c')
  have "dw_exec_step (dwe_core t) (DoDownstream pc pe) c'"
    using publish_emit by simp
  then have False
    using crashed by (cases rule: dw_exec_step.cases) auto
  then show ?thesis ..
qed

section \<open>The invariant twins: stamps, epoch factorization, anti-healing\<close>

text \<open>
  The variant machine re-proves the landed cyclic structural-invariant
  family on itself.  The four mirrored rule kinds have the landed
  relations as their bodies, so the landed per-rule lemmas
  (@{thm [source] dwe_step_stamps_bounded},
  @{thm [source] emitting_reconcile_stamps_bounded},
  @{thm [source] dwe_resume_stamps_bounded}, and the landed
  single-transition monotonicity @{thm [source] effect_unsafe_monotone})
  apply to those cases VERBATIM; the only new mathematics is the
  @{const ss_fire_one} case --- a fire stamps at the CURRENT committed
  length (in bounds by construction) and appends through the landed
  justified-append preservation lemmas.
\<close>

lemma ss_fire_one_stamps_bounded:
  assumes fire: "ss_fire_one f p t t'"
      and sb: "stamps_bounded t"
  shows "stamps_bounded t'"
proof -
  have em: "dwe_emitted t' = dwe_emitted t
              @ [(length (exec_src_hist (dwe_core t)), dwe_epoch t, p)]"
    by (rule ss_fire_one_emitted[OF fire])
  have src: "exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t)"
    by (rule ss_fire_one_src_same[OF fire])
  show ?thesis
    using sb unfolding stamps_bounded_def em src
    by (auto simp: e_stamp_def)
qed

lemma dwe_ss_trace_stamps_bounded:
  assumes "dwe_ss_temporal_trace t xs t'"
      and "stamps_bounded t"
  shows "stamps_bounded t'"
  using assms
proof (induction rule: dwe_ss_temporal_trace.induct)
  case (dwe_ss_refl t)
  then show ?case by simp
next
  case (dwe_ss_label_step t a t' as t'')
  then show ?case using dwe_step_stamps_bounded by blast
next
  case (dwe_ss_reconcile_step m t f t' as t'')
  then show ?case using emitting_reconcile_stamps_bounded by blast
next
  case (dwe_ss_resume_step t t' as t'')
  then show ?case using dwe_resume_stamps_bounded by blast
next
  case (dwe_ss_fire_step f p t t' as t'')
  then show ?case using ss_fire_one_stamps_bounded by blast
qed

theorem dwe_ss_reachable_stamps_bounded:
  assumes "dwe_ss_reachable t"
  shows "stamps_bounded t"
proof -
  obtain xs where "dwe_ss_temporal_trace (dwe_init Map.empty {0, 1} ec2) xs t"
    using assms unfolding dwe_ss_reachable_def by blast
  from dwe_ss_trace_stamps_bounded[OF this dwe_init_stamps_bounded]
  show ?thesis .
qed

text \<open>The epoch-factorization pair: fires are epoch-constant, so epochs
  are monotone along variant traces and constant on Resume-free variant
  traces --- the same segment-interface shape the landed pair
  @{thm [source] dwe_trace_epoch_mono} /
  @{thm [source] dwe_trace_no_resume_epoch_const} exposes.\<close>

lemma dwe_ss_trace_epoch_mono:
  assumes "dwe_ss_temporal_trace t xs t'"
  shows "dwe_epoch t \<le> dwe_epoch t'"
  using assms
proof (induction rule: dwe_ss_temporal_trace.induct)
  case (dwe_ss_refl t)
  then show ?case by simp
next
  case (dwe_ss_label_step t a t' as t'')
  then show ?case using dwe_step_epoch_const by fastforce
next
  case (dwe_ss_reconcile_step m t f t' as t'')
  then show ?case using emitting_reconcile_epoch_const by fastforce
next
  case (dwe_ss_resume_step t t' as t'')
  then show ?case using dwe_resume_epoch_Suc by fastforce
next
  case (dwe_ss_fire_step f p t t' as t'')
  then show ?case using ss_fire_one_epoch_const by fastforce
qed

lemma dwe_ss_trace_no_resume_epoch_const:
  assumes "dwe_ss_temporal_trace t xs t'"
      and "SS_Resume \<notin> set xs"
  shows "dwe_epoch t' = dwe_epoch t"
  using assms
proof (induction rule: dwe_ss_temporal_trace.induct)
  case (dwe_ss_refl t)
  then show ?case by simp
next
  case (dwe_ss_label_step t a t' as t'')
  then show ?case using dwe_step_epoch_const by fastforce
next
  case (dwe_ss_reconcile_step m t f t' as t'')
  then show ?case using emitting_reconcile_epoch_const by fastforce
next
  case (dwe_ss_resume_step t t' as t'')
  then show ?case by simp
next
  case (dwe_ss_fire_step f p t t' as t'')
  then show ?case using ss_fire_one_epoch_const by fastforce
qed

text \<open>
  Anti-healing on the variant: once effect-unsafe, always effect-unsafe,
  now ALSO along fires.  A fire appends one justified-at-fire-time entry
  and moves no core field, so both landed preservation engines
  (@{thm [source] premature_preserved}, @{thm [source] duplicate_preserved})
  apply; the three landed rule kinds are discharged by the landed
  single-transition theorem itself.  As on the landed machine, the
  @{const stamps_bounded} premise is load-bearing, not decorative (the
  landed cyclic stamp-invariant control), and reachability discharges
  it at every @{const dwe_ss_reachable} state.
\<close>

theorem ss_effect_unsafe_monotone:
  assumes sb: "stamps_bounded t"
      and un: "effect_unsafe t"
      and step: "dwe_step t a t' \<or> emitting_reconcile m t f t'
                 \<or> dwe_resume t t' \<or> ss_fire_one g p t t'"
  shows "effect_unsafe t'"
  using step
proof (elim disjE)
  assume "dwe_step t a t'"
  then show ?thesis
    using effect_unsafe_monotone[OF sb un] by blast
next
  assume "emitting_reconcile m t f t'"
  then show ?thesis
    using effect_unsafe_monotone[OF sb un] by blast
next
  assume "dwe_resume t t'"
  then show ?thesis
    using effect_unsafe_monotone[OF sb un] by blast
next
  assume fire: "ss_fire_one g p t t'"
  have em: "\<exists>es. dwe_emitted t' = dwe_emitted t @ es"
    by (rule ss_fire_one_emitted_ext[OF fire])
  have src: "\<exists>ext. exec_src_hist (dwe_core t')
                     = exec_src_hist (dwe_core t) @ ext"
    using ss_fire_one_src_same[OF fire] by (metis append_Nil2)
  from un show ?thesis
    unfolding effect_unsafe_def
    using premature_preserved[OF sb _ em src] duplicate_preserved[OF _ em]
    by blast
qed

corollary ss_effect_unsafe_monotone_reachable:
  assumes "dwe_ss_reachable t"
      and "effect_unsafe t"
      and "dwe_step t a t' \<or> emitting_reconcile m t f t'
           \<or> dwe_resume t t' \<or> ss_fire_one g p t t'"
  shows "effect_unsafe t'"
  by (rule ss_effect_unsafe_monotone[OF dwe_ss_reachable_stamps_bounded[OF assms(1)]
        assms(2) assms(3)])

text \<open>Trace-level persistence, both landed premise profiles: the
  stamps-premised general form (the Decider theory's
  @{text effect_unsafe_trace_persistent} profile) and the
  reachability-premised form (the Segment-Boundaries theory's
  @{text effect_unsafe_trace_monotone} profile; both siblings sit
  outside this import cone, so the profiles are named as prose and the
  twins are proved directly --- the corpus's disclosed forced-duplication
  pattern for ROOT-sibling lanes).\<close>

theorem ss_effect_unsafe_trace_persistent:
  assumes "dwe_ss_temporal_trace t acts t'"
      and "stamps_bounded t"
      and "effect_unsafe t"
  shows "effect_unsafe t'"
  using assms
proof (induction rule: dwe_ss_temporal_trace.induct)
  case (dwe_ss_refl t)
  then show ?case by simp
next
  case (dwe_ss_label_step t a t' as t'')
  have sb': "stamps_bounded t'"
    by (rule dwe_step_stamps_bounded[OF dwe_ss_label_step.hyps(3)
          dwe_ss_label_step.prems(1)])
  have un': "effect_unsafe t'"
    by (rule ss_effect_unsafe_monotone[OF dwe_ss_label_step.prems(1)
          dwe_ss_label_step.prems(2) disjI1[OF dwe_ss_label_step.hyps(3)]])
  show ?case by (rule dwe_ss_label_step.IH[OF sb' un'])
next
  case (dwe_ss_reconcile_step m t f t' as t'')
  have sb': "stamps_bounded t'"
    by (rule emitting_reconcile_stamps_bounded[OF dwe_ss_reconcile_step.hyps(1)
          dwe_ss_reconcile_step.prems(1)])
  have un': "effect_unsafe t'"
    by (rule ss_effect_unsafe_monotone[OF dwe_ss_reconcile_step.prems(1)
          dwe_ss_reconcile_step.prems(2)
          disjI2[OF disjI1[OF dwe_ss_reconcile_step.hyps(1)]]])
  show ?case by (rule dwe_ss_reconcile_step.IH[OF sb' un'])
next
  case (dwe_ss_resume_step t t' as t'')
  have sb': "stamps_bounded t'"
    by (rule dwe_resume_stamps_bounded[OF dwe_ss_resume_step.hyps(1)
          dwe_ss_resume_step.prems(1)])
  have un': "effect_unsafe t'"
    by (rule ss_effect_unsafe_monotone[OF dwe_ss_resume_step.prems(1)
          dwe_ss_resume_step.prems(2)
          disjI2[OF disjI2[OF disjI1[OF dwe_ss_resume_step.hyps(1)]]]])
  show ?case by (rule dwe_ss_resume_step.IH[OF sb' un'])
next
  case (dwe_ss_fire_step f p t t' as t'')
  have sb': "stamps_bounded t'"
    by (rule ss_fire_one_stamps_bounded[OF dwe_ss_fire_step.hyps(1)
          dwe_ss_fire_step.prems(1)])
  have un': "effect_unsafe t'"
    by (rule ss_effect_unsafe_monotone[OF dwe_ss_fire_step.prems(1)
          dwe_ss_fire_step.prems(2)
          disjI2[OF disjI2[OF disjI2[OF dwe_ss_fire_step.hyps(1)]]]])
  show ?case by (rule dwe_ss_fire_step.IH[OF sb' un'])
qed

theorem ss_effect_unsafe_trace_monotone:
  assumes "dwe_ss_reachable t"
      and "effect_unsafe t"
      and "dwe_ss_temporal_trace t xs t'"
  shows "effect_unsafe t'"
  by (rule ss_effect_unsafe_trace_persistent[OF assms(3)
        dwe_ss_reachable_stamps_bounded[OF assms(1)] assms(2)])

section \<open>The dilemma transfer: the headline family restated at the variant's reachability\<close>

text \<open>
  Boundary row 1's robustness claim, made a theorem.  Each statement
  below is the landed statement VERBATIM with @{const dwe_reachable}
  replaced by @{const dwe_ss_reachable} --- nothing else changes,
  because everything else in the landed statements is
  machine-independent: @{const policy_redrive} is a definition (not a
  rule of any trace relation), and @{const store_measured},
  @{const store_epoch_measured}, @{const effect_unsafe},
  @{const lost_effect}, @{const mismatch_at},
  @{const genuinely_emitting} are functions of states of the unchanged
  record type.  The proofs obtain the landed pair and embed its two
  reachability conjuncts through
  @{thm [source] ss_reachable_of_reachable}; every other conjunct
  carries unchanged.  Polarity preserved: these are exists-system
  statements (the pinned witness machine, now with MORE behaviors,
  defeats every policy of the stated class); nothing below says "for
  every system".
\<close>

theorem ss_batch_agreement_dilemma:
  "\<exists>t1 t2.
     dwe_ss_reachable t1 \<and> dwe_ss_reachable t2
   \<and> dwe_core t1 = dwe_core t2
   \<and> dwe_epoch t1 = dwe_epoch t2
   \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
   \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
   \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
   \<and> (\<forall>P. P t1 = P t2 \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')))"
proof -
  obtain t1 t2 where
    r1: "dwe_reachable t1" and r2: "dwe_reachable t2"
    and rest: "dwe_core t1 = dwe_core t2"
              "dwe_epoch t1 = dwe_epoch t2"
              "dwe_emitted t1 \<noteq> dwe_emitted t2"
              "\<not> effect_unsafe t1" "\<not> effect_unsafe t2"
              "genuinely_emitting t1" "genuinely_emitting t2"
    and inner: "\<forall>P. P t1 = P t2 \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2'))"
    using batch_agreement_dilemma by blast
  have s1: "dwe_ss_reachable t1"
    by (rule ss_reachable_of_reachable[OF r1])
  have s2: "dwe_ss_reachable t2"
    by (rule ss_reachable_of_reachable[OF r2])
  show ?thesis
    using s1 s2 rest inner by blast
qed

theorem ss_recovery_information_dilemma_pair:
  "\<exists>t1 t2.
     dwe_ss_reachable t1 \<and> dwe_ss_reachable t2
   \<and> dwe_core t1 = dwe_core t2
   \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
   \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
   \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
   \<and> (\<forall>P. store_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')))"
proof -
  obtain t1 t2 where
    r1: "dwe_reachable t1" and r2: "dwe_reachable t2"
    and rest: "dwe_core t1 = dwe_core t2"
              "dwe_emitted t1 \<noteq> dwe_emitted t2"
              "\<not> effect_unsafe t1" "\<not> effect_unsafe t2"
              "genuinely_emitting t1" "genuinely_emitting t2"
    and inner: "\<forall>P. store_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2'))"
    using recovery_information_dilemma_pair by blast
  show ?thesis
    using ss_reachable_of_reachable[OF r1] ss_reachable_of_reachable[OF r2]
          rest inner
    by blast
qed

theorem ss_recovery_information_dilemma:
  "\<forall>P. store_measured P \<longrightarrow>
     (\<exists>t1 t2 t1' t2'.
        dwe_ss_reachable t1 \<and> dwe_ss_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
      \<and> policy_redrive P t1 ec2 t1'
      \<and> policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
      \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2'))"
proof (intro allI impI)
  fix P :: redrive_policy
  assume sm: "store_measured P"
  obtain t1 t2 t1' t2' where
    base: "dwe_reachable t1" "dwe_reachable t2"
          "dwe_core t1 = dwe_core t2"
          "dwe_emitted t1 \<noteq> dwe_emitted t2"
          "\<not> effect_unsafe t1" "\<not> effect_unsafe t2"
          "genuinely_emitting t1" "genuinely_emitting t2"
          "policy_redrive P t1 ec2 t1'"
          "policy_redrive P t2 ec2 t2'"
          "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k"
          "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k"
          "effect_unsafe t1' \<or> lost_effect ec2 t2'"
    using recovery_information_dilemma sm by blast
  show "\<exists>t1 t2 t1' t2'.
        dwe_ss_reachable t1 \<and> dwe_ss_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
      \<and> policy_redrive P t1 ec2 t1'
      \<and> policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
      \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')"
    using ss_reachable_of_reachable[OF base(1)]
          ss_reachable_of_reachable[OF base(2)]
          base(3-13)
    by blast
qed

theorem ss_epoch_measured_dilemma:
  "\<forall>P. store_epoch_measured P \<longrightarrow>
     (\<exists>t1 t2 t1' t2'.
        dwe_ss_reachable t1 \<and> dwe_ss_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
      \<and> policy_redrive P t1 ec2 t1'
      \<and> policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
      \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2'))"
proof (intro allI impI)
  fix P :: redrive_policy
  assume sem: "store_epoch_measured P"
  obtain t1 t2 t1' t2' where
    base: "dwe_reachable t1" "dwe_reachable t2"
          "dwe_core t1 = dwe_core t2"
          "dwe_emitted t1 \<noteq> dwe_emitted t2"
          "\<not> effect_unsafe t1" "\<not> effect_unsafe t2"
          "genuinely_emitting t1" "genuinely_emitting t2"
          "policy_redrive P t1 ec2 t1'"
          "policy_redrive P t2 ec2 t2'"
          "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k"
          "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k"
          "effect_unsafe t1' \<or> lost_effect ec2 t2'"
    using epoch_measured_dilemma sem by blast
  show "\<exists>t1 t2 t1' t2'.
        dwe_ss_reachable t1 \<and> dwe_ss_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
      \<and> policy_redrive P t1 ec2 t1'
      \<and> policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
      \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')"
    using ss_reachable_of_reachable[OF base(1)]
          ss_reachable_of_reachable[OF base(2)]
          base(3-13)
    by blast
qed

section \<open>The adaptive addendum: per-entry strategies that cannot read the sink\<close>

text \<open>
  The one-shot policies of the landed dilemma emit their whole batch at
  once.  On a small-step machine a referee may object that a REAL
  recovery chooses each fired entry adaptively, watching the state
  evolve between fires.  This section defeats that class honestly.

  THE CLASS.  A fire strategy consults the machine state plus its own
  episode log (the list of entries it has fired so far --- a recovery
  process knows its own in-memory progress) and answers the next entry
  to fire, or stops.  Sink-blindness is measurability, exactly as for
  the landed one-shot classes: the strategy factors through
  (core, epoch, own log) --- everything EXCEPT the ledger.  The class is
  genuinely adaptive (the chooser sees its own progress and may branch
  on it) and genuinely rich: every (core, epoch)-measured one-shot batch
  policy embeds as the strategy that fires its batch entry by entry
  (@{text ss_strategy_implements_batch} below).  The sink-reading escape
  is NOT in the class --- it reads the one component sink-blindness
  denies --- and that is the point: the dilemma's information boundary,
  not its batch granularity, is what bites.

  THE DEFEAT.  Fires are core stutters and epoch-constant, so along a
  fire episode the strategy's visible state never changes except through
  its own log: on any equal-core, equal-epoch pair a sink-blind
  strategy fires LOCKSTEP-EQUAL sequences (the lockstep induction
  below).  Hence its n-step episode, read as a one-shot policy, is
  (core, epoch)-measured --- and the landed equal-epoch kernel defeats
  it via the GAP-2 restatement above.  The fuel bound n makes every
  statement about the n-step episode: an honest bound, not a
  termination claim.

  REALIZABILITY.  The episode is not a hypothetical batch: when the
  fired sequence is replay-bounded at a crashed state, firing it entry
  by entry and completing with the bare heal is a genuine variant trace
  ending in the policy redrive's own result state
  (@{text ss_adaptive_episode_realizable}), and the strategy recursion
  is consulted at exactly the machine's own mid-states (the fire rule's
  successor state IS @{text ss_fire_result}, the state the recursion
  threads).
\<close>

type_synonym ss_fire_strategy =
  "(nat, nat) dwe_state
     \<Rightarrow> (src_coord \<times> (nat, nat) source_event) list
     \<Rightarrow> (src_coord \<times> (nat, nat) source_event) option"

definition ss_fire_result
  :: "src_coord \<times> (nat, nat) source_event
      \<Rightarrow> (nat, nat) dwe_state \<Rightarrow> (nat, nat) dwe_state"
where
  "ss_fire_result p t =
     t\<lparr>dwe_emitted := dwe_emitted t
         @ [(length (exec_src_hist (dwe_core t)), dwe_epoch t,
             fst p, snd p)]\<rparr>"

lemma ss_fire_result_core [simp]:
  "dwe_core (ss_fire_result p t) = dwe_core t"
  by (simp add: ss_fire_result_def)

lemma ss_fire_result_epoch [simp]:
  "dwe_epoch (ss_fire_result p t) = dwe_epoch t"
  by (simp add: ss_fire_result_def)

text \<open>The fire rule's successor state is exactly the recursion's
  threading function --- both directions, so the strategy recursion
  below is consulted at genuine machine mid-states.\<close>

lemma ss_fire_one_result_eq:
  assumes "ss_fire_one f p t t'"
  shows "t' = ss_fire_result p t"
  using assms by (simp add: ss_fire_one_def ss_fire_result_def)

lemma ss_fire_one_to_result:
  assumes "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and "f \<le> exec_finish (dwe_core t)"
      and "p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                      (exec_scope (dwe_core t)) f)"
  shows "ss_fire_one f p t (ss_fire_result p t)"
  by (rule ss_fire_oneI[OF assms]) (simp add: ss_fire_result_def)

fun ss_strategy_fired
  :: "ss_fire_strategy \<Rightarrow> nat \<Rightarrow> (nat, nat) dwe_state
      \<Rightarrow> (src_coord \<times> (nat, nat) source_event) list
      \<Rightarrow> (src_coord \<times> (nat, nat) source_event) list"
where
  "ss_strategy_fired S 0 t log = []"
| "ss_strategy_fired S (Suc n) t log =
     (case S t log of
        None \<Rightarrow> []
      | Some p \<Rightarrow> p # ss_strategy_fired S n (ss_fire_result p t) (log @ [p]))"

definition ss_strategy_sink_blind :: "ss_fire_strategy \<Rightarrow> bool" where
  "ss_strategy_sink_blind S \<longleftrightarrow>
     (\<exists>g. \<forall>t log. S t log = g (dwe_core t) (dwe_epoch t) log)"

definition ss_strategy_policy :: "ss_fire_strategy \<Rightarrow> nat \<Rightarrow> redrive_policy" where
  "ss_strategy_policy S n = (\<lambda>t. ss_strategy_fired S n t [])"

theorem ss_adaptive_lockstep:
  assumes blind: "ss_strategy_sink_blind S"
      and cores: "dwe_core t1 = dwe_core t2"
      and epochs: "dwe_epoch t1 = dwe_epoch t2"
  shows "ss_strategy_fired S n t1 log = ss_strategy_fired S n t2 log"
proof -
  obtain g where g: "\<forall>t log. S t log = g (dwe_core t) (dwe_epoch t) log"
    using blind unfolding ss_strategy_sink_blind_def by blast
  show ?thesis
    using cores epochs
  proof (induction n arbitrary: t1 t2 log)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    have consult: "S t1 log = S t2 log"
      using g Suc.prems by metis
    show ?case
    proof (cases "S t1 log")
      case None
      then show ?thesis using consult by simp
    next
      case (Some p)
      have cores': "dwe_core (ss_fire_result p t1)
                      = dwe_core (ss_fire_result p t2)"
        using Suc.prems(1) by simp
      have epochs': "dwe_epoch (ss_fire_result p t1)
                       = dwe_epoch (ss_fire_result p t2)"
        using Suc.prems(2) by simp
      show ?thesis
        using Some consult Suc.IH[OF cores' epochs'] by simp
    qed
  qed
qed

theorem ss_adaptive_policy_epoch_measured:
  assumes blind: "ss_strategy_sink_blind S"
  shows "store_epoch_measured (ss_strategy_policy S n)"
  unfolding store_epoch_measured_def
proof (intro exI[of _ "\<lambda>c ep. ss_strategy_fired S n (mkT c [] ep) []"] allI)
  fix t :: "(nat, nat) dwe_state"
  have cores: "dwe_core t = dwe_core (mkT (dwe_core t) [] (dwe_epoch t))"
    by (simp add: mkT_def)
  have epochs: "dwe_epoch t = dwe_epoch (mkT (dwe_core t) [] (dwe_epoch t))"
    by (simp add: mkT_def)
  show "ss_strategy_policy S n t
          = ss_strategy_fired S n (mkT (dwe_core t) [] (dwe_epoch t)) []"
    unfolding ss_strategy_policy_def
    by (rule ss_adaptive_lockstep[OF blind cores epochs])
qed

text \<open>The defeat: a sink-blind strategy's n-step episode policy falls to
  the equal-epoch kernel --- the statement is the GAP-2 restatement's
  defeat block instantiated at the episode policy, on the variant's own
  reachability.\<close>

theorem ss_adaptive_strategy_dilemma:
  assumes blind: "ss_strategy_sink_blind S"
  shows "\<exists>t1 t2 t1' t2'.
        dwe_ss_reachable t1 \<and> dwe_ss_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
      \<and> policy_redrive (ss_strategy_policy S n) t1 ec2 t1'
      \<and> policy_redrive (ss_strategy_policy S n) t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
      \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')"
  using ss_epoch_measured_dilemma ss_adaptive_policy_epoch_measured[OF blind]
  by blast

theorem ss_adaptive_episode_realizable:
  assumes crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and fin: "f \<le> exec_finish (dwe_core t)"
      and sub: "set (ss_strategy_policy S n t)
                  \<subseteq> set (replay_down_hist (exec_src_hist (dwe_core t))
                           (exec_scope (dwe_core t)) f)"
  shows "dwe_ss_temporal_trace t
           (map (SS_Fire f) (ss_strategy_policy S n t)
            @ [SS_Reconcile (length (replay_down_hist
                 (exec_src_hist (dwe_core t)) (exec_scope (dwe_core t)) f)) f])
           (redrive_result (ss_strategy_policy S n) t f)"
proof -
  have pr: "policy_redrive (ss_strategy_policy S n) t f
              (redrive_result (ss_strategy_policy S n) t f)"
    by (rule policy_redriveI[OF crashed fin])
  show ?thesis by (rule policy_redrive_decomposes[OF pr sub])
qed

text \<open>Class non-vacuity: the sink-blind strategies subsume every
  (core, epoch)-measured one-shot batch --- the strategy that fires the
  batch entry by entry, indexing by its own log length, is sink-blind
  and reproduces the batch exactly at any sufficient fuel.  Adaptivity
  is a strict generalization of the landed one-shot classes, not a
  disjoint toy.\<close>

lemma ss_batch_strategy_sink_blind:
  "ss_strategy_sink_blind
     (\<lambda>t log. if length log < length (B (dwe_core t) (dwe_epoch t))
              then Some (B (dwe_core t) (dwe_epoch t) ! length log)
              else None)"
  unfolding ss_strategy_sink_blind_def
  by (intro exI[of _ "\<lambda>c ep log. if length log < length (B c ep)
                                 then Some (B c ep ! length log)
                                 else None"])
     simp

lemma ss_batch_strategy_fired:
  assumes S_eq: "\<forall>t log. S t log =
                   (if length log < length (B (dwe_core t) (dwe_epoch t))
                    then Some (B (dwe_core t) (dwe_epoch t) ! length log)
                    else None)"
  shows "length (B (dwe_core t) (dwe_epoch t)) \<le> n + length log \<Longrightarrow>
         ss_strategy_fired S n t log
           = drop (length log) (B (dwe_core t) (dwe_epoch t))"
proof (induction n arbitrary: t log)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "length log < length (B (dwe_core t) (dwe_epoch t))")
    case True
    have consult: "S t log = Some (B (dwe_core t) (dwe_epoch t) ! length log)"
      using S_eq True by simp
    define p where "p = B (dwe_core t) (dwe_epoch t) ! length log"
    have B_same: "B (dwe_core (ss_fire_result p t))
                    (dwe_epoch (ss_fire_result p t))
                    = B (dwe_core t) (dwe_epoch t)"
      by simp
    have bound': "length (B (dwe_core (ss_fire_result p t))
                            (dwe_epoch (ss_fire_result p t)))
                    \<le> n + length (log @ [p])"
      using Suc.prems B_same by simp
    have tail: "ss_strategy_fired S n (ss_fire_result p t) (log @ [p])
                  = drop (Suc (length log)) (B (dwe_core t) (dwe_epoch t))"
      using Suc.IH[OF bound'] B_same by simp
    show ?thesis
      using consult tail True
      by (simp add: p_def Cons_nth_drop_Suc)
  next
    case False
    then have "S t log = None"
      using S_eq by simp
    moreover have "drop (length log) (B (dwe_core t) (dwe_epoch t)) = []"
      using False by simp
    ultimately show ?thesis by simp
  qed
qed

theorem ss_strategy_implements_batch:
  assumes S_eq: "\<forall>t log. S t log =
                   (if length log < length (B (dwe_core t) (dwe_epoch t))
                    then Some (B (dwe_core t) (dwe_epoch t) ! length log)
                    else None)"
      and fuel: "length (B (dwe_core t) (dwe_epoch t)) \<le> n"
  shows "ss_strategy_policy S n t = B (dwe_core t) (dwe_epoch t)"
  unfolding ss_strategy_policy_def
  using ss_batch_strategy_fired[OF S_eq, where t = t and log = "[]" and n = n]
        fuel
  by simp

section \<open>Non-vacuity: the fire rule adds genuine behavior\<close>

text \<open>
  The embedding shows every cyclic behavior is a variant behavior; this
  section shows the converse FAILS --- the variant genuinely adds
  states, so the robustness certificate is not vacuous.  The separation
  engine is an epoch-0 pre-recovery sync invariant of the LANDED cyclic
  machine (a new theorem about the landed machine, proved here
  additively): before the first Resume, at every non-Recovered state,
  the ledger's payload projection literally equals the core's durable
  downstream history --- the cyclic epoch-0 restriction of the terminal
  branch's crashed-sync law (that branch is outside this import cone;
  the analogy is prose).  The reasoning: at epoch 0 no Resume has
  happened; label steps append to ledger and down-history in lockstep
  (publishes) or touch neither projection (every other label); the only
  desynchronizing rule, the emitting reconcile, ends Recovered --- and
  the sole exits from Recovered are the identity Observe stutter and
  the epoch-bumping Resume.  A FIRE breaks exactly this invariant: it
  extends the ledger with the core untouched, producing an in-flight
  partial ledger extension at a Crashed epoch-0 state --- a state the
  landed machine PROVABLY cannot reach.
\<close>

definition epoch0_pre_recovery_sync :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "epoch0_pre_recovery_sync t \<longleftrightarrow>
     (dwe_epoch t = 0 \<and> exec_status (dwe_core t) \<noteq> Recovered \<longrightarrow>
        map e_payload (dwe_emitted t) = exec_down_hist (dwe_core t))"

lemma dw_exec_step_down_hist_cases:
  assumes "dw_exec_step s a s'"
  shows "(exec_down_hist s' = exec_down_hist s \<and> (\<forall>c e. a \<noteq> DoDownstream c e))
       \<or> (\<exists>c e. a = DoDownstream c e
            \<and> exec_down_hist s' = exec_down_hist s @ [(c, e)])"
  using assms by (cases rule: dw_exec_step.cases) auto

lemma dwe_step_split:
  assumes "dwe_step t a t'"
  shows "(dw_exec_step (dwe_core t) a (dwe_core t')
          \<and> (\<forall>c e. a \<noteq> DoDownstream c e)
          \<and> dwe_emitted t' = dwe_emitted t)
       \<or> (\<exists>c e. a = DoDownstream c e
            \<and> dw_exec_step (dwe_core t) a (dwe_core t')
            \<and> dwe_emitted t' = dwe_emitted t
                @ [(length (exec_src_hist (dwe_core t)), dwe_epoch t, c, e)])"
  using assms by (cases rule: dwe_step.cases) auto

lemma emitting_reconcile_ends_recovered:
  assumes "emitting_reconcile m t f t'"
  shows "exec_status (dwe_core t') = Recovered"
  using assms by (auto simp: emitting_reconcile_def)

lemma dwe_step_epoch0_sync:
  assumes step: "dwe_step t a t'"
      and inv: "epoch0_pre_recovery_sync t"
  shows "epoch0_pre_recovery_sync t'"
proof (cases "exec_status (dwe_core t') = Recovered")
  case True
  then show ?thesis by (simp add: epoch0_pre_recovery_sync_def)
next
  case False
  have core_step: "dw_exec_step (dwe_core t) a (dwe_core t')"
    by (rule dwe_step_core[OF step])
  have pre_nonrec: "exec_status (dwe_core t) \<noteq> Recovered"
    using recovered_stays_recovered[OF core_step] False by blast
  have ep: "dwe_epoch t' = dwe_epoch t"
    by (rule dwe_step_epoch_const[OF step])
  show ?thesis
  proof (cases "dwe_epoch t' = 0")
    case False
    then show ?thesis by (simp add: epoch0_pre_recovery_sync_def)
  next
    case True
    then have ep0: "dwe_epoch t = 0" using ep by simp
    have sync: "map e_payload (dwe_emitted t) = exec_down_hist (dwe_core t)"
      using inv ep0 pre_nonrec
      unfolding epoch0_pre_recovery_sync_def by blast
    from dwe_step_split[OF step] show ?thesis
    proof
      assume nonpub:
        "dw_exec_step (dwe_core t) a (dwe_core t')
         \<and> (\<forall>c e. a \<noteq> DoDownstream c e)
         \<and> dwe_emitted t' = dwe_emitted t"
      have down_eq: "exec_down_hist (dwe_core t') = exec_down_hist (dwe_core t)"
        using dw_exec_step_down_hist_cases[OF core_step] nonpub by blast
      show ?thesis
        using nonpub sync down_eq
        by (simp add: epoch0_pre_recovery_sync_def)
    next
      assume "\<exists>c e. a = DoDownstream c e
              \<and> dw_exec_step (dwe_core t) a (dwe_core t')
              \<and> dwe_emitted t' = dwe_emitted t
                  @ [(length (exec_src_hist (dwe_core t)), dwe_epoch t, c, e)]"
      then obtain c e where a_eq: "a = DoDownstream c e"
          and emit_eq: "dwe_emitted t' = dwe_emitted t
                          @ [(length (exec_src_hist (dwe_core t)), dwe_epoch t, c, e)]"
        by blast
      have down_eq:
        "exec_down_hist (dwe_core t') = exec_down_hist (dwe_core t) @ [(c, e)]"
        using dw_exec_step_down_hist_cases[OF core_step] a_eq by blast
      show ?thesis
        using sync
        by (simp add: epoch0_pre_recovery_sync_def emit_eq down_eq)
    qed
  qed
qed

lemma dwe_trace_epoch0_sync:
  assumes "dwe_temporal_trace t xs t'"
      and "epoch0_pre_recovery_sync t"
  shows "epoch0_pre_recovery_sync t'"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  then show ?case .
next
  case (dwe_label_step t a t' as t'')
  have "epoch0_pre_recovery_sync t'"
    by (rule dwe_step_epoch0_sync[OF dwe_label_step.hyps(3)
          dwe_label_step.prems])
  then show ?case by (rule dwe_label_step.IH)
next
  case (dwe_reconcile_step m t f t' as t'')
  have "epoch0_pre_recovery_sync t'"
    using emitting_reconcile_ends_recovered[OF dwe_reconcile_step.hyps(1)]
    by (simp add: epoch0_pre_recovery_sync_def)
  then show ?case by (rule dwe_reconcile_step.IH)
next
  case (dwe_resume_step t t' as t'')
  have "epoch0_pre_recovery_sync t'"
    using dwe_resume_epoch_Suc[OF dwe_resume_step.hyps(1)]
    by (simp add: epoch0_pre_recovery_sync_def)
  then show ?case by (rule dwe_resume_step.IH)
qed

lemma dwe_init_epoch0_sync:
  "epoch0_pre_recovery_sync (dwe_init b K fin)"
  by (simp add: epoch0_pre_recovery_sync_def dwe_init_def
                initial_exec_state_def)

theorem dwe_reachable_epoch0_crashed_sync:
  assumes reach: "dwe_reachable t"
      and ep0: "dwe_epoch t = 0"
      and crashed: "exec_status (dwe_core t) = Crashed c"
  shows "map e_payload (dwe_emitted t) = exec_down_hist (dwe_core t)"
proof -
  from reach obtain xs
    where "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2) xs t"
    unfolding dwe_reachable_def by blast
  from dwe_trace_epoch0_sync[OF this dwe_init_epoch0_sync]
  have "epoch0_pre_recovery_sync t" .
  then show ?thesis
    using ep0 crashed unfolding epoch0_pre_recovery_sync_def by simp
qed

subsection \<open>The new-behavior witness: an in-flight partial ledger extension\<close>

text \<open>
  Fire the still-missing second delivery from the banked crashed loaded
  window @{const t_mid_w} (epoch 0, status Crashed, ledger payloads =
  down-history): the post-state @{text ss_inflight_w} carries the fired
  entry in its ledger with the core untouched --- payload projection
  strictly ahead of the durable downstream history at a Crashed epoch-0
  state.  It is reachable on the variant (one fire from a
  cyclic-reachable state) and, by the sync invariant above,
  machine-checked UNREACHABLE on the landed cyclic machine.  It is also
  effect-SAFE: the fired entry is justified at its fire-time stamp ---
  the state is a genuine mid-redrive snapshot, not a hazard state.
\<close>

definition ss_inflight_w :: "(nat, nat) dwe_state" where
  "ss_inflight_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1)]
                          [(ec1, e1), (ec2, e2)] {(ec2, e2)} (Crashed ec2))
                       [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

lemma fire_inflight: "ss_fire_one ec2 (ec2, e2) t_mid_w ss_inflight_w"
  by (rule ss_fire_oneI)
     (simp_all add: t_mid_w_def ss_inflight_w_def mkT_def mkC_def
                    replay_down_hist_def e1_def e2_def ec_defs
                    eval_nat_numeral)

lemma ss_inflight_fields:
  "exec_status (dwe_core ss_inflight_w) = Crashed ec2"
  "dwe_epoch ss_inflight_w = 0"
  "dwe_core ss_inflight_w = dwe_core t_mid_w"
  "map e_payload (dwe_emitted ss_inflight_w) = [(ec1, e1), (ec2, e2)]"
  "exec_down_hist (dwe_core ss_inflight_w) = [(ec1, e1)]"
  by (simp_all add: ss_inflight_w_def t_mid_w_def mkT_def mkC_def)

lemma ss_inflight_ss_reachable: "dwe_ss_reachable ss_inflight_w"
  by (rule dwe_ss_reachable_fire_ext[OF
        ss_reachable_of_reachable[OF reach_t_mid] fire_inflight])

lemma ss_inflight_not_cyclic_reachable: "\<not> dwe_reachable ss_inflight_w"
proof
  assume "dwe_reachable ss_inflight_w"
  from dwe_reachable_epoch0_crashed_sync[OF this ss_inflight_fields(2)
         ss_inflight_fields(1)]
  have "map e_payload (dwe_emitted ss_inflight_w)
          = exec_down_hist (dwe_core ss_inflight_w)" .
  then show False
    by (simp add: ss_inflight_fields(4) ss_inflight_fields(5))
qed

lemma ss_inflight_safe: "\<not> effect_unsafe ss_inflight_w"
  by (simp add: effect_unsafe_def premature_def duplicate_def
                justified_at_def ss_inflight_w_def mkT_def mkC_def
                e1_def e2_def ec_defs eval_nat_numeral)

lemma ss_inflight_emitting: "genuinely_emitting ss_inflight_w"
  by (simp add: genuinely_emitting_def ss_inflight_w_def mkT_def)

theorem ss_new_behavior_witness:
  "dwe_ss_reachable ss_inflight_w
 \<and> \<not> dwe_reachable ss_inflight_w
 \<and> exec_status (dwe_core ss_inflight_w) = Crashed ec2
 \<and> dwe_epoch ss_inflight_w = 0
 \<and> dwe_core ss_inflight_w = dwe_core t_mid_w
 \<and> \<not> effect_unsafe ss_inflight_w
 \<and> genuinely_emitting ss_inflight_w"
  using ss_inflight_ss_reachable ss_inflight_not_cyclic_reachable
        ss_inflight_fields(1) ss_inflight_fields(2) ss_inflight_fields(3)
        ss_inflight_safe ss_inflight_emitting
  by blast

subsection \<open>The refire-duplicate witness: at-least-once physics, per entry\<close>

text \<open>
  The hazard physics of the rule, witnessed: a fired entry can be
  REFIRED.  From the in-flight state above, firing the SAME payload
  again is legal (the guards read only the frozen core), and the
  resulting state is a duplicate --- two fires of one payload --- with
  EVERY ledger entry individually justified at its fire-time stamp.
  At-least-once physics, exactly as on the landed machine (whose stale
  cursors already reach duplicate states through the atomic rule);
  ordering and freshness live in the discipline, never in the rule.
  No cyclic-unreachability is claimed for this state: duplication is
  not the separation axis, the in-flight extension above is.
\<close>

definition ss_refire_w :: "(nat, nat) dwe_state" where
  "ss_refire_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1)]
                        [(ec1, e1), (ec2, e2)] {(ec2, e2)} (Crashed ec2))
                     [(1, 0, ec1, e1), (2, 0, ec2, e2), (2, 0, ec2, e2)] 0"

lemma fire_refire: "ss_fire_one ec2 (ec2, e2) ss_inflight_w ss_refire_w"
  by (rule ss_fire_oneI)
     (simp_all add: ss_inflight_w_def ss_refire_w_def mkT_def mkC_def
                    replay_down_hist_def e1_def e2_def ec_defs
                    eval_nat_numeral)

lemma ss_refire_ss_reachable: "dwe_ss_reachable ss_refire_w"
  by (rule dwe_ss_reachable_fire_ext[OF ss_inflight_ss_reachable fire_refire])

lemma ss_refire_duplicate: "duplicate ss_refire_w"
  by (simp add: duplicate_def ss_refire_w_def mkT_def)

lemma ss_refire_justified:
  "\<forall>x \<in> set (dwe_emitted ss_refire_w).
     justified_at (exec_src_hist (dwe_core ss_refire_w)) x"
  by (simp add: justified_at_def ss_refire_w_def mkT_def mkC_def
                e1_def e2_def ec_defs eval_nat_numeral)

theorem ss_refire_duplicate_witness:
  "dwe_ss_reachable ss_refire_w
 \<and> duplicate ss_refire_w
 \<and> effect_unsafe ss_refire_w
 \<and> (\<forall>x \<in> set (dwe_emitted ss_refire_w).
      justified_at (exec_src_hist (dwe_core ss_refire_w)) x)"
  using ss_refire_ss_reachable ss_refire_duplicate ss_refire_justified
  by (auto simp: effect_unsafe_def)


end
