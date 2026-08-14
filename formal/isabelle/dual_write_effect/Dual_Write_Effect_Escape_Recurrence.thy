(*  Title:       Dual_Write_Effect_Escape_Recurrence.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    The recurrent escape run (discovery candidate A1 of the lens-A
    referee review, paper/dual_write/theory_review/discovery/
    LENS_A_REFEREE.md; probe LensA_Probe.thy, green qd=false) --- an
    additive post-freeze slice under the freeze's own protocol: no
    landed statement, proof, definition, name, import, or session-DAG
    change to the frozen corpus.

    WHAT THIS THEORY ADDS.  The landed positive side of the effect tier
    is ONE-SHOT: @{text sink_reading_escape_general} and
    @{text sink_delta_achieves_exactly_once} certify a SINGLE sink-delta
    redrive from a SINGLE crashed state, while the corpus's own negative
    recurrence theorem (@{text resume_cycle_amplification}, G5(ii))
    proves the crash/resume cycle is exactly where store-measured
    recovery degrades --- a one-shot-vs-recurrence asymmetry a referee
    can name.  This theory closes it on the positive side: a run
    relation (escape_run) whose recovery transitions are the landed
    sink-delta policy redrives, effect safety proved inductive along it,
    and the recurrent law --- EVERY redrive fired anywhere along any
    escape run from an effect-safe start heals at its own frontier and
    lands exactly_once_at that frontier, across arbitrarily many
    crash/recovery cycles with new work in between.  A two-cycle
    machine witness realizes the shape (second recovery recomputes an
    EMPTY delta), IS also a genuine reachable machine run (both its
    redrives coincide with machine reconciles: cursor 1, then the
    heal-only cursor), and is contrasted against the banked cursor-0
    amplification schedule.  A load-bearing control shows the run
    relation's one recovery-side guard (strictly ascending source)
    cannot be dropped.

    SCOPE AND GRADE.  This STRENGTHENS THE ESCAPE LANE of the landed
    positive side --- the one-shot escape becomes whole-run recurrent.
    The headline law (T2.10 and its kernel), the discipline (T2.8), the
    two-tier contrast theorems, and T2.11's necessity face are all
    untouched: never a new impossibility, never a headline promotion,
    no contribution-list reframe.  The exists/parametric polarity of
    the landed corpus is unchanged: everything here lives on the
    positive side at the pinned witness type (the policy type
    @{text redrive_policy} is pinned, so the run relation is pinned
    with it), in the B1 any-state posture (no reachability premise on
    the general laws; the witness run is separately proved reachable).

    IMPORTS.  Dual_Write_Effect_Exactly_Once alone: it supplies
    exactly_once_at and @{text sink_delta_achieves_exactly_once} (the
    one-shot law this theory iterates) and, through it, the cyclic
    branch --- Dilemma (policy_redrive, sink_delta, the ascending
    premise, B1) and Discipline (the per-rule preservation lemmas and
    the epoch-1 witness chain).  Namespace rule holds: the terminal
    branch (Dual_Write_Effect_Machine / _Witnesses) stays out of the
    import cone; the one terminal-branch-adjacent fact mentioned in
    prose (the landed section-18 control state @{text psl_w}, which
    lives in Dual_Write_Effect_Sink_Delta_Idempotence, also outside
    this cone) is cited as text and re-declared locally, per the
    Decider / Compensation precedent.
*)

theory Dual_Write_Effect_Escape_Recurrence
  imports Dual_Write_Effect_Exactly_Once
begin

section \<open>The escape-run relation\<close>

text \<open>
  MANDATORY DISCLOSURE (the recovery-model status of escape runs).
  Escape runs EXTEND machine runs by policy-redrive recovery
  transitions: the @{text ea_redrive} rule below fires the landed
  @{const policy_redrive} with the landed sink-reading batch
  @{const sink_delta} --- exactly the recovery model the landed dilemma
  itself quantifies over (@{text batch_agreement_dilemma} and its
  family judge policies by their @{const policy_redrive} results), and
  the same transition shape whose store-measured instances that family
  defeats.  A policy redrive is NOT in general a transition of the
  cyclic machine: @{const emitting_reconcile} fires drop-m suffixes of
  the scoped replay, and a sink-delta batch need not be such a suffix
  (the landed @{thm [source] sink_delta_d2_is_cursor_suffix} notes the
  coincidence at one witness and discloses the non-generality in its
  own text).  Consequently T2.8's brand --- "the discipline restricts
  the SCHEDULER only: every disciplined run is a genuine temporal run
  of the machine" --- does NOT carry over to escape runs and is not
  claimed: an escape run is a machine run INTERLEAVED WITH the
  dilemma's own recovery transitions.  At the two-cycle witness below
  both redrives happen to coincide with machine reconciles (cursor 1,
  then the heal-only cursor at the full replay length), and THAT run
  is also proved to be a genuine reachable machine run --- proved at
  the witness, never generalized.

  THE RULES.  Label steps carry the T2.8 discipline guards verbatim
  (wellformedness + history-wf admissibility on every label; fire-time
  justification + ledger freshness on publishes --- the landed
  @{text disciplined_trace} label cases).  The recovery rule
  @{text ea_redrive} fires @{term "policy_redrive (sink_delta f)"}
  guarded ONLY by the landed ascending-source premise on the crashed
  state's committed history (src-local --- the exact premise the landed
  B1 consumes; @{const policy_redrive} carries its own crashed-status
  and frontier guards).  Resume is guard-free, exactly as in the landed
  discipline (@{thm [source] resume_preserves_effect_safe}: a Resume
  step preserves ledger and committed source verbatim).
\<close>

datatype escape_act =
    EA_Label "(nat, nat) dw_exec_label"
  | EA_Redrive frontier
  | EA_Resume

inductive escape_run
  :: "(nat, nat) dwe_state \<Rightarrow> escape_act list \<Rightarrow> (nat, nat) dwe_state \<Rightarrow> bool"
where
  ea_refl:
    "escape_run t [] t"
| ea_nonpub:
    "\<lbrakk>dwe_step t a t';
      wellformed_exec_state (dwe_core t);
      exec_label_preserves_history_wf (dwe_core t) a;
      \<forall>c e. a \<noteq> DoDownstream c e;
      escape_run t' as t''\<rbrakk> \<Longrightarrow>
     escape_run t (EA_Label a # as) t''"
| ea_publish:
    "\<lbrakk>dwe_step t (DoDownstream c e) t';
      wellformed_exec_state (dwe_core t);
      exec_label_preserves_history_wf (dwe_core t) (DoDownstream c e);
      (c, e) \<in> set (exec_src_hist (dwe_core t));
      (c, e) \<notin> e_payload ` set (dwe_emitted t);
      escape_run t' as t''\<rbrakk> \<Longrightarrow>
     escape_run t (EA_Label (DoDownstream c e) # as) t''"
| ea_redrive:
    "\<lbrakk>policy_redrive (sink_delta f) t f t';
      strictly_ascending_source (exec_src_hist (dwe_core t));
      escape_run t' as t''\<rbrakk> \<Longrightarrow>
     escape_run t (EA_Redrive f # as) t''"
| ea_resume:
    "\<lbrakk>dwe_resume t t';
      escape_run t' as t''\<rbrakk> \<Longrightarrow>
     escape_run t (EA_Resume # as) t''"

lemma escape_run_append:
  assumes "escape_run t as t'"
      and "escape_run t' bs t''"
  shows "escape_run t (as @ bs) t''"
  using assms
  by (induction rule: escape_run.induct)
     (auto intro: escape_run.intros)

subsection \<open>The redrive preserves effect safety (B1's safety conjunct)\<close>

text \<open>
  The one genuinely new preservation case: a guarded sink-delta redrive
  from an effect-safe state lands effect-safe.  This is literally the
  safety conjunct of the landed
  @{thm [source] sink_reading_escape_general}; the crashed-status and
  frontier premises of that theorem are @{const policy_redrive}'s own
  guards, so only the ascending guard is consumed from the rule.
\<close>

lemma sink_delta_redrive_preserves_effect_safe:
  assumes pr: "policy_redrive (sink_delta f) t f t'"
      and asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
      and safe: "\<not> effect_unsafe t"
  shows "\<not> effect_unsafe t'"
proof -
  have crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
    using pr by (auto simp: policy_redrive_def)
  have fin: "f \<le> exec_finish (dwe_core t)"
    using pr by (auto simp: policy_redrive_def)
  show ?thesis
    using sink_reading_escape_general[OF safe crashed fin asc] pr by blast
qed

subsection \<open>Effect safety is inductive along escape runs\<close>

text \<open>
  The label and Resume cases reuse the landed per-rule preservation
  lemmas verbatim (@{thm [source] nonpub_preserves_effect_safe},
  @{thm [source] publish_preserves_effect_safe},
  @{thm [source] resume_preserves_effect_safe}); the redrive case is
  the lemma above.
\<close>

theorem escape_run_effect_safe:
  assumes "escape_run t as t'"
      and "\<not> effect_unsafe t"
  shows "\<not> effect_unsafe t'"
  using assms
proof (induction rule: escape_run.induct)
  case (ea_refl t)
  then show ?case .
next
  case (ea_nonpub t a t' as t'')
  then show ?case using nonpub_preserves_effect_safe by blast
next
  case (ea_publish t c e t' as t'')
  then show ?case using publish_preserves_effect_safe by blast
next
  case (ea_redrive f t t' as t'')
  then show ?case using sink_delta_redrive_preserves_effect_safe by blast
next
  case (ea_resume t t' as t'')
  then show ?case using resume_preserves_effect_safe by blast
qed


section \<open>The recurrent law: every recovery along an escape run is
  exactly-once at its own frontier\<close>

text \<open>
  NAME DISCIPLINE AND INHERITED STAND-IN STATUS (re-disclosed here, in
  the same breath as every exactly-once statement of this theory).
  "Exactly-once" below is ALWAYS the landed frontier-qualified
  @{const exactly_once_at}, evaluated at THE REDRIVE'S OWN frontier
  @{term f} at the redrive's own result state; the bare phrase is never
  a formal name.  Its delivery-completeness conjunct
  (@{const at_least_once_at}, the complement of the landed
  @{const lost_effect} through
  @{thm [source] at_least_once_iff_not_lost}) is a TERMINAL-STATE
  STAND-IN for delivery liveness of the landed
  acknowledgement-durability kind (boundary row 4), NOT a temporal
  eventually: emissions of a later Running segment are new application
  work, not the recovery's redrive.  Every per-redrive conclusion below
  inherits exactly that status, per redrive, at that redrive's own
  frontier and result state.

  FINITE-TRACE MAXIMUM, disclosed as such.  A temporal
  "eventually delivered under fair scheduling" claim would need
  infinite traces, coinduction, and a fairness predicate --- machinery
  this corpus deliberately does not have; any finite-trace rendering of
  that question reduces to runs whose crash windows end with a
  completed recovery, which is precisely the escape-run shape.  This
  theory is therefore the honest finite-trace maximum on that axis; no
  delivery-liveness claim is made or implied, and none of the
  vocabulary of that axis is used as a formal name here.
\<close>

theorem escape_run_recurrent_exactly_once:
  assumes run: "escape_run t0 as t"
      and safe0: "\<not> effect_unsafe t0"
      and pr: "policy_redrive (sink_delta f) t f t'"
      and asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "(\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)
       \<and> exactly_once_at f t'"
proof -
  have safe: "\<not> effect_unsafe t"
    by (rule escape_run_effect_safe[OF run safe0])
  have crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
    using pr by (auto simp: policy_redrive_def)
  have fin: "f \<le> exec_finish (dwe_core t)"
    using pr by (auto simp: policy_redrive_def)
  show ?thesis
    using sink_delta_achieves_exactly_once[OF safe crashed fin asc] pr by blast
qed

subsection \<open>Mid-run decomposition: the law quantifies over every redrive
  INSIDE a run, not only at its end\<close>

lemma escape_run_nil_dest:
  assumes "escape_run t [] t'"
  shows "t' = t"
  using assms by (cases rule: escape_run.cases) auto

lemma escape_run_cons_dest:
  assumes "escape_run t (x # xs) t''"
  shows "\<exists>t'. escape_run t [x] t' \<and> escape_run t' xs t''"
  using assms
  by (cases rule: escape_run.cases)
     (blast intro: escape_run.intros)+

lemma escape_run_append_dest:
  assumes "escape_run t (as @ bs) t''"
  shows "\<exists>t'. escape_run t as t' \<and> escape_run t' bs t''"
  using assms
proof (induction as arbitrary: t)
  case Nil
  then show ?case by (auto intro: escape_run.intros)
next
  case (Cons x as)
  obtain t1 where s1: "escape_run t [x] t1"
      and s2: "escape_run t1 (as @ bs) t''"
    using escape_run_cons_dest[OF Cons.prems[unfolded append_Cons]] by blast
  obtain t' where s3: "escape_run t1 as t'" and s4: "escape_run t' bs t''"
    using Cons.IH[OF s2] by blast
  have "escape_run t ([x] @ as) t'"
    by (rule escape_run_append[OF s1 s3])
  then show ?case using s4 by auto
qed

lemma escape_run_single_redrive_dest:
  assumes "escape_run t [EA_Redrive f] t'"
  shows "policy_redrive (sink_delta f) t f t'
       \<and> strictly_ascending_source (exec_src_hist (dwe_core t))"
  using assms
  by (cases rule: escape_run.cases) (auto dest: escape_run_nil_dest)

text \<open>
  THE RECURRENT LAW.  Along any escape run from an effect-safe start,
  every redrive --- wherever it occurs in the action word --- heals
  every scoped store mismatch at its own frontier and lands
  @{const exactly_once_at} that frontier at its own result state.  The
  landed one-shot law is the @{term "as = []"} instance; the recurrence
  is carried by the safety induction plus the decomposition lemmas
  above.  (Both stand-in disclosures of this section apply verbatim to
  the @{const exactly_once_at} conjunct here.)
\<close>

theorem escape_run_every_redrive_exactly_once:
  assumes run: "escape_run t0 (as @ EA_Redrive f # bs) tend"
      and safe0: "\<not> effect_unsafe t0"
  shows "\<exists>t t'. escape_run t0 as t
             \<and> policy_redrive (sink_delta f) t f t'
             \<and> escape_run t' bs tend
             \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)
             \<and> exactly_once_at f t'"
proof -
  obtain t where pre: "escape_run t0 as t"
      and rest: "escape_run t (EA_Redrive f # bs) tend"
    using escape_run_append_dest[OF run] by blast
  obtain t' where mid: "escape_run t [EA_Redrive f] t'"
      and post: "escape_run t' bs tend"
    using escape_run_cons_dest[OF rest] by blast
  have pr: "policy_redrive (sink_delta f) t f t'"
    and asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
    using escape_run_single_redrive_dest[OF mid] by blast+
  show ?thesis
    using pre pr post escape_run_recurrent_exactly_once[OF pre safe0 pr asc]
    by blast
qed


section \<open>The two-cycle witness: two crash/recovery cycles, new work in
  between, both recoveries exactly-once at their frontier\<close>

text \<open>
  Cycle 1: from the banked loaded window @{const t_mid_w}, the
  sink-delta redrive at @{const ec2} lands EXACTLY on the banked safe
  state @{const t_safe_w} (the landed
  @{thm [source] t_safe_exactly_once} already certifies that state).
  Then Resume (the landed @{thm [source] res_d}), and the landed
  epoch-1 chain commits and publishes the third business event
  \<open>e3\<close> (the landed steps @{thm [source] ws_d1},
  @{thm [source] ws_d2}, @{thm [source] ws_d3}).  Cycle 2: crash again
  at @{const ec2}, redrive again --- the recomputed delta is EMPTY
  (nothing re-fires; the second recovery is heal-only).  The witness
  states extend the landed Discipline \<open>d\<close>-chain past
  @{const d_pub3_w} and are named into it (\<open>d_crash2_w\<close>,
  \<open>d_heal2_w\<close>).
\<close>

definition d_crash2_w :: "(nat, nat) dwe_state" where
  "d_crash2_w = mkT (mkC [(ec1, e1), (ec2, e2), (ec3, e3)]
                      [(ec1, e1), (ec2, e2), (ec3, e3)]
                      [(ec1, e1), (ec2, e2), (ec3, e3)] {} (Crashed ec2))
                    [(1, 0, ec1, e1), (2, 0, ec2, e2), (3, 1, ec3, e3)] 1"

definition d_heal2_w :: "(nat, nat) dwe_state" where
  "d_heal2_w = mkT (mkC [(ec1, e1), (ec2, e2), (ec3, e3)]
                     [(ec1, e1), (ec2, e2)]
                     [(ec1, e1), (ec2, e2), (ec3, e3)] {} Recovered)
                   [(1, 0, ec1, e1), (2, 0, ec2, e2), (3, 1, ec3, e3)] 1"

subsection \<open>Cycle-1 engine facts\<close>

lemma asc_t_mid:
  "strictly_ascending_source (exec_src_hist (dwe_core t_mid_w))"
  by (simp add: strictly_ascending_source_def t_mid_w_def mkT_def mkC_def
                ec_defs)

lemma escape_redrive_cycle1:
  "policy_redrive (sink_delta ec2) t_mid_w ec2 t_safe_w"
  by (simp add: policy_redrive_def sink_delta_def t_mid_w_def t_safe_w_def
                mkT_def mkC_def replay_down_hist_def e1_def e2_def ec_defs
                eval_nat_numeral)

text \<open>The cycle-1 owed batch, computed: exactly the one still-missing
  effect --- at this state the sink-delta batch coincides with the warm
  cursor-1 suffix (the landed coincidence note
  @{thm [source] sink_delta_d2_is_cursor_suffix} applies at
  @{const d2_w}; this is its analogue at @{const t_mid_w}).\<close>

lemma sink_delta_cycle1_batch:
  "sink_delta ec2 t_mid_w = [(ec2, e2)]"
  by (simp add: sink_delta_def t_mid_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs eval_nat_numeral)

lemma sink_delta_cycle1_cursor_suffix:
  "sink_delta ec2 t_mid_w
     = drop 1 (replay_down_hist (exec_src_hist (dwe_core t_mid_w))
                 (exec_scope (dwe_core t_mid_w)) ec2)"
  by (simp add: sink_delta_def t_mid_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs eval_nat_numeral)

subsection \<open>Cycle-2 engine facts\<close>

lemma wf_d_pub3: "wellformed_exec_state (dwe_core d_pub3_w)"
  by (simp add: d_pub3_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_triple)

lemma g_d_pub3_crash:
  "exec_label_preserves_history_wf (dwe_core d_pub3_w) (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma ws_crash2: "dwe_step d_pub3_w (Crash ec2) d_crash2_w"
proof -
  have c: "dw_exec_step (dwe_core d_pub3_w) (Crash ec2) (dwe_core d_crash2_w)"
    by (rule crashI) (simp_all add: d_pub3_w_def d_crash2_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c])
       (simp_all add: d_pub3_w_def d_crash2_w_def mkT_def)
qed

lemma asc_d_crash2:
  "strictly_ascending_source (exec_src_hist (dwe_core d_crash2_w))"
  by (simp add: strictly_ascending_source_def d_crash2_w_def mkT_def mkC_def
                ec_defs)

lemma escape_redrive_cycle2:
  "policy_redrive (sink_delta ec2) d_crash2_w ec2 d_heal2_w"
  by (simp add: policy_redrive_def sink_delta_def d_crash2_w_def d_heal2_w_def
                mkT_def mkC_def replay_down_hist_def e1_def e2_def e3_def
                ec_defs eval_nat_numeral)

text \<open>The cycle-2 owed batch, computed: EMPTY --- after cycle 1's
  recovery and the fresh epoch-1 publish, the ledger already covers the
  scoped replay at @{const ec2}, so the second recovery re-fires
  nothing and is heal-only.\<close>

lemma sink_delta_cycle2_empty:
  "sink_delta ec2 d_crash2_w = []"
  by (simp add: sink_delta_def d_crash2_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def e3_def ec_defs
                eval_nat_numeral)

lemma exactly_once_cycle2: "exactly_once_at ec2 d_heal2_w"
  by (simp add: exactly_once_at_def at_least_once_at_def effect_unsafe_def
                premature_def duplicate_def justified_at_def
                replay_down_hist_def d_heal2_w_def mkT_def mkC_def
                e1_def e2_def e3_def ec_defs eval_nat_numeral)

subsection \<open>The witness, assembled\<close>

theorem escape_two_cycle_witness:
  "escape_run t_mid_w
     [EA_Redrive ec2, EA_Resume,
      EA_Label (DoSource ec3 e3), EA_Label (EnqueueDownstream ec3 e3),
      EA_Label (DoDownstream ec3 e3), EA_Label (Crash ec2),
      EA_Redrive ec2]
     d_heal2_w
 \<and> exactly_once_at ec2 t_safe_w
 \<and> exactly_once_at ec2 d_heal2_w
 \<and> \<not> effect_unsafe d_heal2_w
 \<and> dwe_epoch d_heal2_w = 1"
proof -
  have s7: "escape_run d_heal2_w [] d_heal2_w"
    by (rule ea_refl)
  have s6: "escape_run d_crash2_w [EA_Redrive ec2] d_heal2_w"
    by (rule ea_redrive[OF escape_redrive_cycle2 asc_d_crash2 s7])
  have s5: "escape_run d_pub3_w [EA_Label (Crash ec2), EA_Redrive ec2]
              d_heal2_w"
    by (rule ea_nonpub[OF ws_crash2 wf_d_pub3 g_d_pub3_crash _ s6]) simp
  have pubJ: "(ec3, e3) \<in> set (exec_src_hist (dwe_core d_enq3_w))"
    by (simp add: d_enq3_w_def mkT_def mkC_def)
  have pubF: "(ec3, e3) \<notin> e_payload ` set (dwe_emitted d_enq3_w)"
    by (simp add: d_enq3_w_def mkT_def mkC_def e1_def e2_def e3_def ec_defs)
  have s4: "escape_run d_enq3_w
              [EA_Label (DoDownstream ec3 e3), EA_Label (Crash ec2),
               EA_Redrive ec2] d_heal2_w"
    by (rule ea_publish[OF ws_d3 wf_d_enq3 g_d_enq3_down3 pubJ pubF s5])
  have s3: "escape_run d_src3_w
              [EA_Label (EnqueueDownstream ec3 e3),
               EA_Label (DoDownstream ec3 e3), EA_Label (Crash ec2),
               EA_Redrive ec2] d_heal2_w"
    by (rule ea_nonpub[OF ws_d2 wf_d_src3 g_d_src3_enq3 _ s4]) simp
  have s2: "escape_run d_run_w
              [EA_Label (DoSource ec3 e3),
               EA_Label (EnqueueDownstream ec3 e3),
               EA_Label (DoDownstream ec3 e3), EA_Label (Crash ec2),
               EA_Redrive ec2] d_heal2_w"
    by (rule ea_nonpub[OF ws_d1 wf_d_run g_d_run_src3 _ s3]) simp
  have s1: "escape_run t_safe_w
              [EA_Resume,
               EA_Label (DoSource ec3 e3),
               EA_Label (EnqueueDownstream ec3 e3),
               EA_Label (DoDownstream ec3 e3), EA_Label (Crash ec2),
               EA_Redrive ec2] d_heal2_w"
    by (rule ea_resume[OF res_d s2])
  have s0: "escape_run t_mid_w
              [EA_Redrive ec2, EA_Resume,
               EA_Label (DoSource ec3 e3),
               EA_Label (EnqueueDownstream ec3 e3),
               EA_Label (DoDownstream ec3 e3), EA_Label (Crash ec2),
               EA_Redrive ec2] d_heal2_w"
    by (rule ea_redrive[OF escape_redrive_cycle1 asc_t_mid s1])
  have ep: "dwe_epoch d_heal2_w = 1"
    by (simp add: d_heal2_w_def mkT_def)
  have ns: "\<not> effect_unsafe d_heal2_w"
    using exactly_once_cycle2 by (simp add: exactly_once_at_def)
  show ?thesis
    using s0 t_safe_exactly_once exactly_once_cycle2 ns ep by blast
qed


section \<open>The witness run is a genuine machine run (reachability
  included)\<close>

text \<open>
  The general disclosure above stands: escape runs are NOT machine runs
  in general.  At THIS witness both redrives coincide with machine
  reconciles --- cycle 1 is the landed warm-cursor reconcile
  @{thm [source] rec_safe} (m = 1; the computed batch coincidence is
  @{thm [source] sink_delta_cycle1_cursor_suffix}), and cycle 2 is the
  heal-only reconcile at the full replay length (m = 2 fires the empty
  suffix, matching the empty recomputed delta
  @{thm [source] sink_delta_cycle2_empty}) --- so the SAME seven-step
  schedule is a genuine @{const dwe_temporal_trace} of the cyclic
  machine, and its states (in particular both recovery results) are
  @{const dwe_reachable}.  Proved at the witness, never generalized.
\<close>

lemma rec_heal2: "emitting_reconcile 2 d_crash2_w ec2 d_heal2_w"
  by (simp add: emitting_reconcile_def d_crash2_w_def d_heal2_w_def
                mkT_def mkC_def replay_down_hist_def e1_def e2_def e3_def
                ec_defs eval_nat_numeral)

lemma reach_d_crash2: "dwe_reachable d_crash2_w"
  by (rule dwe_reachable_label_ext[OF reach_d_pub3 wf_d_pub3
        g_d_pub3_crash ws_crash2])

lemma reach_d_heal2: "dwe_reachable d_heal2_w"
  by (rule dwe_reachable_reconcile_ext[OF reach_d_crash2 rec_heal2])

theorem escape_witness_run_is_machine_run:
  "dwe_temporal_trace t_mid_w
     [DWE_Reconcile 1 ec2, DWE_Resume,
      DWE_Label (DoSource ec3 e3), DWE_Label (EnqueueDownstream ec3 e3),
      DWE_Label (DoDownstream ec3 e3), DWE_Label (Crash ec2),
      DWE_Reconcile 2 ec2]
     d_heal2_w
 \<and> dwe_reachable d_crash2_w
 \<and> dwe_reachable d_heal2_w"
proof -
  have m7: "dwe_temporal_trace d_heal2_w [] d_heal2_w"
    by (rule dwe_temporal_trace.dwe_refl)
  have m6: "dwe_temporal_trace d_crash2_w [DWE_Reconcile 2 ec2] d_heal2_w"
    by (rule dwe_temporal_trace.dwe_reconcile_step[OF rec_heal2 m7])
  have m5: "dwe_temporal_trace d_pub3_w
              [DWE_Label (Crash ec2), DWE_Reconcile 2 ec2] d_heal2_w"
    by (rule dwe_temporal_trace.dwe_label_step[OF wf_d_pub3 g_d_pub3_crash
          ws_crash2 m6])
  have m4: "dwe_temporal_trace d_enq3_w
              [DWE_Label (DoDownstream ec3 e3), DWE_Label (Crash ec2),
               DWE_Reconcile 2 ec2] d_heal2_w"
    by (rule dwe_temporal_trace.dwe_label_step[OF wf_d_enq3 g_d_enq3_down3
          ws_d3 m5])
  have m3: "dwe_temporal_trace d_src3_w
              [DWE_Label (EnqueueDownstream ec3 e3),
               DWE_Label (DoDownstream ec3 e3), DWE_Label (Crash ec2),
               DWE_Reconcile 2 ec2] d_heal2_w"
    by (rule dwe_temporal_trace.dwe_label_step[OF wf_d_src3 g_d_src3_enq3
          ws_d2 m4])
  have m2: "dwe_temporal_trace d_run_w
              [DWE_Label (DoSource ec3 e3),
               DWE_Label (EnqueueDownstream ec3 e3),
               DWE_Label (DoDownstream ec3 e3), DWE_Label (Crash ec2),
               DWE_Reconcile 2 ec2] d_heal2_w"
    by (rule dwe_temporal_trace.dwe_label_step[OF wf_d_run g_d_run_src3
          ws_d1 m3])
  have m1: "dwe_temporal_trace t_safe_w
              [DWE_Resume,
               DWE_Label (DoSource ec3 e3),
               DWE_Label (EnqueueDownstream ec3 e3),
               DWE_Label (DoDownstream ec3 e3), DWE_Label (Crash ec2),
               DWE_Reconcile 2 ec2] d_heal2_w"
    by (rule dwe_temporal_trace.dwe_resume_step[OF res_d m2])
  have m0: "dwe_temporal_trace t_mid_w
              [DWE_Reconcile 1 ec2, DWE_Resume,
               DWE_Label (DoSource ec3 e3),
               DWE_Label (EnqueueDownstream ec3 e3),
               DWE_Label (DoDownstream ec3 e3), DWE_Label (Crash ec2),
               DWE_Reconcile 2 ec2] d_heal2_w"
    by (rule dwe_temporal_trace.dwe_reconcile_step[OF rec_safe m1])
  show ?thesis
    using m0 reach_d_crash2 reach_d_heal2 by blast
qed


section \<open>The contrast pin: the banked two-cycle cursor schedule
  amplifies; the escape run stays exactly-once at both recoveries' own
  frontier\<close>

text \<open>
  The banked amplification chain (@{const t_mid_w} \<open>\<rightarrow>\<close>
  @{const t_fin_w} \<open>\<rightarrow>\<close> @{const f_run_w} \<open>\<rightarrow>\<close> @{const f_crash_w}
  \<open>\<rightarrow>\<close> @{const f_amp_w}, the landed
  @{thm [source] resume_cycle_amplification}) takes two crash/recovery
  cycles from the SAME banked loaded window across one Resume with the
  cold cursor-0 reconcile as its recovery: the same committed payload
  reaches count 3 and the end state is effect-unsafe.  The escape run
  above takes two crash/recovery cycles from the same window across one
  Resume --- doing strictly more application work in between (a fresh
  epoch-1 publish) --- and both its recoveries land
  @{const exactly_once_at} their own frontier.  This is the escape twin
  of the banked cursor-amplification schedule: recurrence is exactly
  where the landed G5(ii) negative lives, and the sink-reading escape
  is certified on that shape.
\<close>

lemma f_amp_two_cycle_unsafe: "effect_unsafe f_amp_w"
  using resume_cycle_amplification by blast

theorem escape_twin_amplification_contrast:
  "exactly_once_at ec2 t_safe_w
 \<and> exactly_once_at ec2 d_heal2_w
 \<and> effect_unsafe f_amp_w
 \<and> 3 \<le> count_list (map e_payload (dwe_emitted f_amp_w)) (ec1, e1)"
  using t_safe_exactly_once exactly_once_cycle2 resume_cycle_amplification
  by blast


section \<open>Load-bearing control: the ea\_redrive ascending guard bites\<close>

text \<open>
  THE CONTROL (the duplicated-batch face of the landed aliasing axis).
  At a WF-H1-LEGAL equal-coordinate CRASHED state --- the landed
  section-18 aliasing posture re-declared locally as \<open>epsl_w\<close> with
  @{term "Crashed ec1"} status, because that theory is not in this
  import cone (the Decider / Compensation precedent; the landed
  constant is @{text psl_w}, a Running state) --- one business payload
  is committed twice, so the sink-computed batch contains the payload
  TWICE.  Every guard of the landed @{const policy_redrive} itself
  holds, the start state is effect-safe, and the redrive result is
  effect-UNSAFE: the internally duplicated batch lands as a ledger
  duplicate.  Hence an @{text ea_redrive} rule WITHOUT the
  strictly-ascending guard would step an escape run from an effect-safe
  state to an effect-unsafe one, and @{thm [source]
  escape_run_effect_safe} would be FALSE for that guard-dropped
  variant: the guard is load-bearing exactly where the landed B1
  consumes the same premise.

  HONESTY NOTE (the lens-A shelf record, kept with the control): at
  this state the payload-level loses-nothing conjunct does NOT fail ---
  both committed instances share one payload, and instance-level
  counting under aliasing is the landed layer-2 control's job
  (@{thm [source] aliasing_defeats_instance_exactness}).  The failure
  the guard prevents is exactly the duplicated-batch / effect-unsafe
  form exhibited here, and only that is claimed.  The state is a state
  of the type, not claimed reachable, matching the run relation's own
  any-state posture.
\<close>

definition epsl_w :: "(nat, nat) dwe_state" where
  "epsl_w = mkT (mkC [(ec1, e1), (ec1, e1)] [] [] {} (Crashed ec1)) [] 0"

lemma epsl_wf: "wellformed_src_history (exec_src_hist (dwe_core epsl_w))"
proof -
  have "exec_src_hist (dwe_core epsl_w) = [(ec1, e1), (ec1, e1)]"
    by (simp add: epsl_w_def mkT_def mkC_def)
  moreover have "wellformed_src_history [(ec1, e1), (ec1, e1)]"
    by (rule wf_hist_pair) (simp_all add: ec_defs)
  ultimately show ?thesis by simp
qed

lemma epsl_not_asc:
  "\<not> strictly_ascending_source (exec_src_hist (dwe_core epsl_w))"
  by (simp add: strictly_ascending_source_def epsl_w_def mkT_def mkC_def
                ec_defs)

lemma epsl_safe: "\<not> effect_unsafe epsl_w"
  by (simp add: effect_unsafe_def premature_def duplicate_def epsl_w_def
                mkT_def)

lemma epsl_crashed: "\<exists>c. exec_status (dwe_core epsl_w) = Crashed c"
  by (simp add: epsl_w_def mkT_def mkC_def)

lemma epsl_fin: "ec1 \<le> exec_finish (dwe_core epsl_w)"
  by (simp add: epsl_w_def mkT_def mkC_def ec_defs)

lemma epsl_batch: "sink_delta ec1 epsl_w = [(ec1, e1), (ec1, e1)]"
  by (simp add: sink_delta_def epsl_w_def mkT_def mkC_def
                replay_down_hist_def e1_def ec_defs)

lemma epsl_batch_duplicate: "\<not> distinct (sink_delta ec1 epsl_w)"
  by (simp add: epsl_batch)

lemma epsl_redrive_unsafe:
  "effect_unsafe (redrive_result (sink_delta ec1) epsl_w ec1)"
  by (simp add: effect_unsafe_def duplicate_def redrive_result_def
                sink_delta_def epsl_w_def mkT_def mkC_def
                replay_down_hist_def e1_def ec_defs)

theorem escape_asc_guard_load_bearing:
  "wellformed_src_history (exec_src_hist (dwe_core epsl_w))
 \<and> \<not> strictly_ascending_source (exec_src_hist (dwe_core epsl_w))
 \<and> \<not> effect_unsafe epsl_w
 \<and> (\<exists>c. exec_status (dwe_core epsl_w) = Crashed c)
 \<and> ec1 \<le> exec_finish (dwe_core epsl_w)
 \<and> \<not> distinct (sink_delta ec1 epsl_w)
 \<and> policy_redrive (sink_delta ec1) epsl_w ec1
     (redrive_result (sink_delta ec1) epsl_w ec1)
 \<and> effect_unsafe (redrive_result (sink_delta ec1) epsl_w ec1)"
  by (intro conjI epsl_wf epsl_not_asc epsl_safe epsl_crashed epsl_fin
        epsl_batch_duplicate policy_redriveI[OF epsl_crashed epsl_fin]
        epsl_redrive_unsafe)


end
