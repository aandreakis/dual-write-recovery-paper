(*  Title:       Dual_Write_Effect_Small_Step_Escape.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    The POSITIVE HALF of the small-step robustness certificate
    (theory-backlog item D, Design B, work package WP4) --- an additive
    post-freeze slice under the freeze's own protocol: no landed
    statement, proof, definition, name, import, or session-DAG change
    to the frozen corpus.  Like its sibling
    Dual_Write_Effect_Small_Step, this theory is part of the
    ROBUSTNESS CERTIFICATE for the disclosed atomic big-step reconcile
    boundary (boundary row 1), never a new primary machine: owner
    decision D5 (cyclic promotion) stays closed, and every landed
    theorem keeps its own machine.

    THE UPGRADE, SAID HONESTLY.  The landed section-18 lane proved its
    partial-append laws at MODELED INTERMEDIATES --- states of the
    ledger SHAPE an interrupted sink-delta re-drive would leave, with
    no claim that any machine reaches them; the landed section-20 lane
    iterated that shape.  On the small-step variant those very states
    ARE machine states: firing the first n entries of the currently
    computed sink-delta batch from a crashed variant-reachable state
    is a genuine variant trace whose end state is ss-reachable and
    carries the section-18 footprint EXACTLY.  So the section-18 laws
    (remainder, effect-safety, completion) and the section-20
    multi-round laws (convergence, cumulative footprint, no
    duplication, completion) apply AT machine states BY CITATION ---
    their statements are any-state function equations, and the
    variant realizes their states.  This theory never retro-claims
    that the section-18/20 theories asserted machine reachability:
    they deliberately did not; the realization is new and lives here.

    WHY THE FIXED-SOURCE PREMISE IS THE MACHINE'S OWN PHYSICS.  The
    section-18/20 laws hold the committed source FIXED across the
    partial append and across rounds.  On the variant this is not an
    assumption but a theorem about the machine: fires happen only at
    Crashed status, and a Crashed core is FROZEN up to the identity
    Observe stutter and the status-only Recover
    (crashed_core_frozen, crashed_wrapper_label_freeze) --- no source
    commit can interleave a fire episode, so along every fire episode
    the committed source, the scope, and the epoch are literally
    constant.  The W2-landing amendment to the wave directive recorded
    the consequence: the priced interleaved-commit composition lemma
    is VACUOUS on this core and is not built; the honest composition
    axis is across STOPPED and ABANDONED episodes, built below.

    THE ROUNDS REALIZATION (the I+J machine composition).  A STOPPED
    episode --- fire n entries of the current batch, stop --- lands
    exactly on the section-20 iterator's round state
    (ss_stopped_episode_realizes_round: the two states are EQUAL, not
    similar), and consecutive stopped episodes within ONE crashed
    window realize the whole iterator: rounds with fired-prefix
    lengths ns are the concatenated fire sequences, machine-checked as
    one variant trace (ss_rounds_realized).  The section-20 laws then
    hold at ss-reachable states (ss_crashed_window_multi_round_
    convergence): after any interleaving of stopped retries the
    recomputed delta is exactly the drop (sum_list ns) remainder of
    the original batch, nothing is fired twice, completion happens at
    the batch length, and every round state is effect-safe --- under
    the NAMED strictly-ascending-source premise, witnessed biting at
    machine level by the aliasing control at the end.  Within one
    window "same epoch, core frozen" is itself machine-checked: the
    realization's action list contains fires only.

    ACROSS ABANDONED EPISODES (fires, then Recover WITHOUT the
    completing heal, then a cyclic Resume into a new epoch, later a
    new crash), the honest statement is scoped per-window: stamps
    carry the NEW epoch after Resume, so the section-20 stamp-constant
    footprint holds PER WINDOW and provably does NOT extend across
    windows (ss_cross_window_stamp_footprint_control: the concrete
    two-window ledger below carries two distinct emission epochs, so
    no single stamped map covers it).  What DOES survive abandonment
    is the delta itself: the remainder law RE-FOUNDS at the new
    window's own batch (ss_new_window_delta_refound) --- any later
    state that still carries the abandoned mid-state's ledger and
    whose committed source grew only by entries strictly beyond the
    frontier computes, as its own batch, exactly the abandoned
    window's remainder; status and epoch are deliberately free, which
    is precisely what Recover, Resume, and a fresh crash move.  The
    two-window witness chain (the cw states) runs the whole story end to end
    on the machine: fire one of two owed entries, abandon, Resume,
    crash again, complete in epoch 1 --- recomputed delta empty,
    effect-safe, one emission per window per epoch.  No uniform
    cross-window law is claimed: commits at or below the frontier in
    a later epoch genuinely change the new window's batch (the
    section-20 frontier-bound control already bites there), and the
    per-window re-founding is the honest general form.

    THE DISCIPLINE TWIN (T2.8 on the variant).  The variant's for-all
    safety theorem (ss_general_positive_discipline) consumes the three
    LANDED T2.8 guards --- fire-time justification, publish freshness,
    reconcile-suffix fresh-and-internally-distinct --- plus ONE guard
    on the new rule: each fired entry fresh against the current
    ledger.  The fire guard is the landed reconcile-suffix guard
    RESTRICTED TO SINGLETONS (distinctness of a one-element suffix is
    trivial, freshness is exactly ledger-freshness), never a new
    premise class; Resume stays guard-free.  The landed discipline
    embeds (disciplined_traces_embed), the landed per-rule
    preservation lemmas are reused verbatim on the mirrored rule
    kinds, and the only new mathematics is the one-entry fire case.
    The cycle-exercising non-vacuity witness re-runs the landed
    epoch-crossing disciplined run with the reconcile step DECOMPOSED:
    fire the missing entry (through the genuinely new mid-state
    ss_inflight_w), complete with the bare heal --- landing exactly on
    the landed run's own post-reconcile state --- then Resume and
    publish fresh work in epoch 1.  Both controls are machine-level:
    dropping the singleton guard reaches an effect-unsafe duplicate
    (the D1 refire witness, re-packaged as the discipline-side
    control), and dropping the ascending premise starves a committed
    instance at a WF-legal equal-coordinate state through a genuine
    machine fire that IS the take-1 stopped episode.

    FENCES (binding, from the freeze documents).  Everything here is
    the robustness certificate's positive half --- an appendix-grade
    companion to the landed corpus, never a new primary machine.  The
    strictly-ascending-source premise is NAMED at every consuming
    statement; the impossibility half of the landed corpus consumes
    no ordering premise, and nothing here changes that.  No
    unqualified exactly-once claim is made or implied: the completion
    laws below speak of the RECOMPUTED DELTA and of EFFECT-SAFETY,
    and the landed exactly-once vocabulary (T2.11) is cited only at
    its own disclosed strengths.  The exists-system polarity of the
    dilemma family and the R1 scope of the terminal-inexpressibility
    reading ("the operational dilemma needs the recovery cycle",
    per-machine, for the landed atomic rule set) are untouched: the
    fire rule exists on the cyclic lane only.  lost_effect keeps its
    two pinned definition-site readings unchanged.

    IMPORTS (each earns its place; all cyclic-lane, namespace rule
    holds --- the terminal branch stays out of this import cone).
    Dual_Write_Effect_Small_Step: the variant machine, the fire
    composition engine, the embedding, and the witnesses this theory
    extends.  Dual_Write_Effect_Sink_Delta_Convergence: the
    section-20 rounds iterator and its laws (through it the
    section-18 lane and, for the code setup it inherits, the
    locked-core decider session).  Dual_Write_Effect_Discipline: the
    landed T2.8 guard shapes, the per-rule preservation lemmas reused
    verbatim, and the landed cycle-exercising witness chain the twin's
    non-vacuity run extends.  Cross-cone facts (the effect-tier
    decider lane, the Segments lane) are cited as prose only.

    PROVENANCE: theory-backlog item D, Design B, WP4
    (paper/dual_write/theory_backlog/D_SMALLSTEP_DESIGN.md section 5;
    build ratified by paper/dual_write/theory_backlog/
    EXTENSION_DIRECTIVE.md slice W3, consumed WITH its W2-landing
    amendment: the interleaved-commit composition lemma is vacuous on
    the locked core and DROPPED; the stopped/abandoned-episode
    composition below is the honest analogue).

    In-source ML oracle gates are STRIPPED at landing: oracle-freedom
    is certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Small_Step_Escape
  imports
    Dual_Write_Effect_Small_Step
    Dual_Write_Effect_Sink_Delta_Convergence
    Dual_Write_Effect_Discipline
begin

section \<open>Plumbing: trace-closure of the variant's reachability\<close>

text \<open>D1 banked the one-fire extension (@{thm [source]
  dwe_ss_reachable_fire_ext}); the episode theorems below extend
  reachability along whole traces.\<close>

lemma dwe_ss_reachable_trace_ext:
  assumes "dwe_ss_reachable t"
      and "dwe_ss_temporal_trace t xs t'"
  shows "dwe_ss_reachable t'"
proof -
  obtain ys where ys: "dwe_ss_temporal_trace (dwe_init Map.empty {0, 1} ec2) ys t"
    using assms(1) unfolding dwe_ss_reachable_def by blast
  show ?thesis
    unfolding dwe_ss_reachable_def
    using dwe_ss_temporal_trace_append[OF ys assms(2)] by blast
qed

text \<open>The sink-computed batch is replay-bounded by construction ---
  the subset facts the fire compositions below feed on, composed by
  explicit rule application (house lore: quantified library facts
  never enter @{method blast} chains).\<close>

lemma sink_delta_replay_subset:
  "set (sink_delta f t)
     \<subseteq> set (replay_down_hist (exec_src_hist (dwe_core t))
              (exec_scope (dwe_core t)) f)"
  unfolding sink_delta_def by (rule filter_is_subset)

lemma sink_delta_take_replay_subset:
  "set (take n (sink_delta f t))
     \<subseteq> set (replay_down_hist (exec_src_hist (dwe_core t))
              (exec_scope (dwe_core t)) f)"
  by (rule subset_trans[OF set_take_subset sink_delta_replay_subset])


section \<open>The escape's mid-states are machine states\<close>

text \<open>
  @{text ss_escape_mid} is the state reached by firing the first
  @{term n} entries of the CURRENTLY computed sink-delta batch: the
  ledger extended by the stamped take-@{term n} prefix, stamped
  exactly as the landed rules stamp (committed-prefix length, current
  epoch), nothing else touched.  This is LITERALLY the section-18
  modeled-intermediate footprint (the
  @{thm [source] sink_delta_partial_redrive_remainder} state shape)
  --- and on the variant it is the end state of a genuine fire
  sequence, so the section-18 modeled intermediates are realized as
  reachable variant states.  The section-18 theory itself claimed no
  such reachability, correctly: its machine has no rule that stops
  mid-batch; this one does.
\<close>

definition ss_escape_mid
  :: "frontier \<Rightarrow> nat \<Rightarrow> (nat, nat) dwe_state \<Rightarrow> (nat, nat) dwe_state"
where
  "ss_escape_mid f n t =
     t\<lparr>dwe_emitted := dwe_emitted t
         @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                          dwe_epoch t, c, e))
             (take n (sink_delta f t))\<rparr>"

lemma ss_escape_mid_core [simp]:
  "dwe_core (ss_escape_mid f n t) = dwe_core t"
  by (simp add: ss_escape_mid_def)

lemma ss_escape_mid_epoch [simp]:
  "dwe_epoch (ss_escape_mid f n t) = dwe_epoch t"
  by (simp add: ss_escape_mid_def)

text \<open>THE REALIZATION: firing the prefix entry by entry is a variant
  trace from @{term t} to the mid-state --- the fire composition
  engine of D1 at the sink-delta batch.  The core never moves along
  the episode (fires are core stutters; while Crashed the core admits
  no commit at all, @{thm [source] crashed_core_frozen}), so the
  fixed-committed-source posture of the section-18 laws is the
  machine's own physics here, not a premise.\<close>

theorem ss_escape_mid_trace:
  assumes crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and fin: "f \<le> exec_finish (dwe_core t)"
  shows "dwe_ss_temporal_trace t (map (SS_Fire f) (take n (sink_delta f t)))
           (ss_escape_mid f n t)"
proof -
  have fires: "dwe_ss_temporal_trace t
                 (map (SS_Fire f) (take n (sink_delta f t)))
                 (t\<lparr>dwe_emitted := dwe_emitted t
                      @ map (\<lambda>p. (length (exec_src_hist (dwe_core t)),
                                  dwe_epoch t, p))
                          (take n (sink_delta f t))\<rparr>)"
    by (rule ss_fires_compose[OF crashed fin sink_delta_take_replay_subset])
  have eq: "t\<lparr>dwe_emitted := dwe_emitted t
               @ map (\<lambda>p. (length (exec_src_hist (dwe_core t)),
                           dwe_epoch t, p))
                   (take n (sink_delta f t))\<rparr> = ss_escape_mid f n t"
    by (simp add: ss_escape_mid_def)
  show ?thesis using fires eq by simp
qed

corollary ss_escape_mid_reachable:
  assumes reach: "dwe_ss_reachable t"
      and crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and fin: "f \<le> exec_finish (dwe_core t)"
  shows "dwe_ss_reachable (ss_escape_mid f n t)"
  by (rule dwe_ss_reachable_trace_ext[OF reach
        ss_escape_mid_trace[OF crashed fin]])

text \<open>The section-18 laws AT the machine state, by citation.  Where
  the named premise @{const strictly_ascending_source} is consumed,
  it is consumed for exactly what section 18 consumed it for:
  internal distinctness of the computed batch, witnessed biting at
  machine level by @{text ss_fire_asc_load_bearing} below.\<close>

theorem ss_escape_mid_delta:
  assumes asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "sink_delta f (ss_escape_mid f n t) = drop n (sink_delta f t)"
  unfolding ss_escape_mid_def
  by (rule sink_delta_partial_redrive_remainder[OF asc])

theorem ss_escape_mid_effect_safe:
  assumes safe: "\<not> effect_unsafe t"
      and asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "\<not> effect_unsafe (ss_escape_mid f n t)"
  unfolding ss_escape_mid_def
  by (rule sink_delta_partial_state_effect_safe[OF safe asc])

text \<open>The package: at every crashed, effect-safe, ss-reachable state
  with a strictly ascending committed source, EVERY interrupted
  sink-delta re-drive's mid-state is an ss-REACHABLE, EFFECT-SAFE
  machine state whose recomputed delta is exactly the remainder and
  whose core (hence store, scope, and epoch) is untouched.\<close>

theorem ss_escape_mid_states_are_machine_states:
  assumes reach: "dwe_ss_reachable t"
      and safe: "\<not> effect_unsafe t"
      and crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and fin: "f \<le> exec_finish (dwe_core t)"
      and asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "dwe_ss_reachable (ss_escape_mid f n t)
       \<and> \<not> effect_unsafe (ss_escape_mid f n t)
       \<and> sink_delta f (ss_escape_mid f n t) = drop n (sink_delta f t)
       \<and> dwe_core (ss_escape_mid f n t) = dwe_core t
       \<and> dwe_epoch (ss_escape_mid f n t) = dwe_epoch t"
  using ss_escape_mid_reachable[OF reach crashed fin]
        ss_escape_mid_effect_safe[OF safe asc]
        ss_escape_mid_delta[OF asc]
  by simp

text \<open>
  COMPLETION FROM THE MID-STATE.  Re-running the escape policy at the
  mid-state --- fire its own recomputed delta, then the bare heal ---
  is again a variant trace, and its end state satisfies the full B1
  contract: the store heals at the frontier, the state is effect-safe,
  nothing is lost, and the recomputed delta is empty (that last
  equation premise-free, the section-18 real-transition completion).
  The escape's recomputation COMPLETES an interrupted delivery at
  genuine machine states --- the design study's section-5 consumption,
  now with the mid-state itself reachable.  "Completes" is the
  function-equation and effect-safety reading fenced in the header;
  delivery liveness is not claimed.
\<close>

theorem ss_escape_mid_completes:
  assumes safe: "\<not> effect_unsafe t"
      and crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and fin: "f \<le> exec_finish (dwe_core t)"
      and asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "dwe_ss_temporal_trace (ss_escape_mid f n t)
           (map (SS_Fire f) (sink_delta f (ss_escape_mid f n t))
            @ [SS_Reconcile
                 (length (replay_down_hist (exec_src_hist (dwe_core t))
                            (exec_scope (dwe_core t)) f)) f])
           (redrive_result (sink_delta f) (ss_escape_mid f n t) f)
       \<and> sink_delta f (redrive_result (sink_delta f) (ss_escape_mid f n t) f)
           = []
       \<and> \<not> effect_unsafe (redrive_result (sink_delta f) (ss_escape_mid f n t) f)
       \<and> (\<forall>k. \<not> mismatch_at
                (proto_of_exec_at
                  (dwe_core (redrive_result (sink_delta f)
                               (ss_escape_mid f n t) f)) f) f k)
       \<and> \<not> lost_effect f (redrive_result (sink_delta f) (ss_escape_mid f n t) f)"
proof -
  let ?mid = "ss_escape_mid f n t"
  have crashed': "\<exists>c. exec_status (dwe_core ?mid) = Crashed c"
    using crashed by simp
  have fin': "f \<le> exec_finish (dwe_core ?mid)"
    using fin by simp
  have asc': "strictly_ascending_source (exec_src_hist (dwe_core ?mid))"
    using asc by simp
  have safe': "\<not> effect_unsafe ?mid"
    by (rule ss_escape_mid_effect_safe[OF safe asc])
  have pr: "policy_redrive (sink_delta f) ?mid f
              (redrive_result (sink_delta f) ?mid f)"
    by (rule policy_redriveI[OF crashed' fin'])
  have tr: "dwe_ss_temporal_trace ?mid
              (map (SS_Fire f) (sink_delta f ?mid)
               @ [SS_Reconcile
                    (length (replay_down_hist (exec_src_hist (dwe_core ?mid))
                               (exec_scope (dwe_core ?mid)) f)) f])
              (redrive_result (sink_delta f) ?mid f)"
    by (rule policy_redrive_decomposes[OF pr sink_delta_replay_subset])
  have empty: "sink_delta f (redrive_result (sink_delta f) ?mid f) = []"
    by (rule sink_delta_after_policy_redrive_empty[OF pr])
  have esc_all: "\<forall>t'. policy_redrive (sink_delta f) ?mid f t' \<longrightarrow>
                   (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)
                 \<and> \<not> effect_unsafe t' \<and> \<not> lost_effect f t'"
    using sink_reading_escape_general[OF safe' crashed' fin' asc'] by blast
  have esc: "(\<forall>k. \<not> mismatch_at
                    (proto_of_exec_at
                      (dwe_core (redrive_result (sink_delta f) ?mid f)) f) f k)
           \<and> \<not> effect_unsafe (redrive_result (sink_delta f) ?mid f)
           \<and> \<not> lost_effect f (redrive_result (sink_delta f) ?mid f)"
    using esc_all pr by blast
  show ?thesis using tr empty esc by simp
qed


section \<open>The rounds realization: stopped episodes ARE the section-20 iterator\<close>

text \<open>
  One STOPPED episode (fire @{term n} entries of the current batch,
  stop) lands exactly on the section-20 round state --- state-level
  EQUALITY, not simulation: @{const ss_escape_mid} and one round of
  @{const partial_redrive_rounds} are the same state.
\<close>

theorem ss_stopped_episode_realizes_round:
  "ss_escape_mid f n t = partial_redrive_rounds f [n] t"
  by (simp add: ss_escape_mid_def)

lemma partial_redrive_rounds_cons_mid:
  "partial_redrive_rounds f (n # ns) t
     = partial_redrive_rounds f ns (ss_escape_mid f n t)"
  by (simp add: ss_escape_mid_def)

text \<open>
  The action list of the multi-round realization: round @{term i}
  fires the take-@{term "ns ! i"} prefix of the batch as recomputed
  AT its own round state --- exactly the iterator's recursion,
  spelled as machine actions.
\<close>

fun ss_round_actions
  :: "frontier \<Rightarrow> nat list \<Rightarrow> (nat, nat) dwe_state \<Rightarrow> ss_action list"
where
  "ss_round_actions f [] t = []"
| "ss_round_actions f (n # ns) t =
     map (SS_Fire f) (take n (sink_delta f t))
     @ ss_round_actions f ns (ss_escape_mid f n t)"

text \<open>The realization stays within ONE crashed window: every action
  is a fire (no Resume, no reconcile, no label), so the epoch is
  constant along it (@{thm [source] dwe_ss_trace_no_resume_epoch_const})
  and the core is frozen (@{thm [source] partial_redrive_rounds_core}
  --- and, machine-side, @{thm [source] ss_fire_core_stutter}).\<close>

lemma ss_round_actions_all_fires:
  "\<forall>a \<in> set (ss_round_actions f ns t). \<exists>g p. a = SS_Fire g p"
  by (induction ns arbitrary: t) auto

lemma ss_round_actions_no_resume:
  "SS_Resume \<notin> set (ss_round_actions f ns t)"
  by (induction ns arbitrary: t) auto

text \<open>THE MULTI-ROUND REALIZATION: consecutive stopped episodes with
  fired-prefix lengths @{term ns}, run as one variant trace, end
  exactly at the section-20 iterator's state.\<close>

theorem ss_rounds_realized:
  assumes crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and fin: "f \<le> exec_finish (dwe_core t)"
  shows "dwe_ss_temporal_trace t (ss_round_actions f ns t)
           (partial_redrive_rounds f ns t)"
  using assms
proof (induction ns arbitrary: t)
  case Nil
  then show ?case by (simp add: dwe_ss_temporal_trace.dwe_ss_refl)
next
  case (Cons n ns)
  have fires: "dwe_ss_temporal_trace t
                 (map (SS_Fire f) (take n (sink_delta f t)))
                 (ss_escape_mid f n t)"
    by (rule ss_escape_mid_trace[OF Cons.prems(1) Cons.prems(2)])
  have crashed': "\<exists>c. exec_status (dwe_core (ss_escape_mid f n t)) = Crashed c"
    using Cons.prems(1) by simp
  have fin': "f \<le> exec_finish (dwe_core (ss_escape_mid f n t))"
    using Cons.prems(2) by simp
  have rest: "dwe_ss_temporal_trace (ss_escape_mid f n t)
                (ss_round_actions f ns (ss_escape_mid f n t))
                (partial_redrive_rounds f ns (ss_escape_mid f n t))"
    by (rule Cons.IH[OF crashed' fin'])
  have "dwe_ss_temporal_trace t
          (map (SS_Fire f) (take n (sink_delta f t))
           @ ss_round_actions f ns (ss_escape_mid f n t))
          (partial_redrive_rounds f ns (ss_escape_mid f n t))"
    by (rule dwe_ss_temporal_trace_append[OF fires rest])
  then show ?case
    by (simp add: ss_escape_mid_def)
qed

corollary ss_rounds_reachable:
  assumes reach: "dwe_ss_reachable t"
      and crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and fin: "f \<le> exec_finish (dwe_core t)"
  shows "dwe_ss_reachable (partial_redrive_rounds f ns t)"
  by (rule dwe_ss_reachable_trace_ext[OF reach
        ss_rounds_realized[OF crashed fin]])

text \<open>
  THE WITHIN-WINDOW HEADLINE: machine-level multi-round
  crash-interrupted redrive convergence.  At every crashed
  ss-reachable state with a strictly ascending committed source
  (NAMED premise), for EVERY list of fired-prefix lengths @{term ns}:
  the round states are ss-reachable machine states; the recomputed
  delta is exactly the drop-@{term "sum_list ns"} remainder of the
  original batch; a duplicate-free ledger stays duplicate-free (no
  payload is fired twice across the whole loop); once the cumulative
  fired count reaches the batch length the recomputed delta is empty;
  and from an effect-safe start every round state is effect-safe.
  Every conjunct beyond reachability is the corresponding section-20
  law consumed by citation at the realized state --- the "convergence"
  vocabulary is theirs: function equations and hazard-freedom, never
  a delivery or liveness claim.
\<close>

theorem ss_crashed_window_multi_round_convergence:
  assumes reach: "dwe_ss_reachable t"
      and crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and fin: "f \<le> exec_finish (dwe_core t)"
      and asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "dwe_ss_reachable (partial_redrive_rounds f ns t)
       \<and> sink_delta f (partial_redrive_rounds f ns t)
           = drop (sum_list ns) (sink_delta f t)
       \<and> (distinct (map e_payload (dwe_emitted t)) \<longrightarrow>
            distinct (map e_payload
              (dwe_emitted (partial_redrive_rounds f ns t))))
       \<and> (length (sink_delta f t) \<le> sum_list ns \<longrightarrow>
            sink_delta f (partial_redrive_rounds f ns t) = [])
       \<and> (\<not> effect_unsafe t \<longrightarrow>
            \<not> effect_unsafe (partial_redrive_rounds f ns t))"
proof (intro conjI impI)
  show "dwe_ss_reachable (partial_redrive_rounds f ns t)"
    by (rule ss_rounds_reachable[OF reach crashed fin])
next
  show "sink_delta f (partial_redrive_rounds f ns t)
          = drop (sum_list ns) (sink_delta f t)"
    by (rule partial_redrive_rounds_delta[OF asc])
next
  assume "distinct (map e_payload (dwe_emitted t))"
  then show "distinct (map e_payload
               (dwe_emitted (partial_redrive_rounds f ns t)))"
    by (rule partial_redrive_rounds_no_duplication[OF asc])
next
  assume "length (sink_delta f t) \<le> sum_list ns"
  then show "sink_delta f (partial_redrive_rounds f ns t) = []"
    by (rule partial_redrive_rounds_complete[OF asc])
next
  assume "\<not> effect_unsafe t"
  then show "\<not> effect_unsafe (partial_redrive_rounds f ns t)"
    by (rule partial_redrive_rounds_effect_safe[OF _ asc])
qed

corollary ss_crashed_window_effective_complete:
  assumes reach: "dwe_ss_reachable t"
      and crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and fin: "f \<le> exec_finish (dwe_core t)"
      and asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
      and prog: "\<forall>n \<in> set ns. 0 < n"
      and len: "length (sink_delta f t) \<le> length ns"
  shows "dwe_ss_reachable (partial_redrive_rounds f ns t)
       \<and> sink_delta f (partial_redrive_rounds f ns t) = []"
  using ss_rounds_reachable[OF reach crashed fin]
        partial_redrive_rounds_effective_complete[OF asc prog len]
  by blast


section \<open>Across abandoned episodes: the per-window re-founding\<close>

text \<open>
  An ABANDONED episode fires part of its batch and never completes:
  the core then leaves the window through Recover (the only move a
  Crashed core admits besides the identity stutter,
  @{thm [source] crashed_core_frozen}), a cyclic Resume opens the
  next epoch, and a later crash opens a NEW window.  What survives is
  the LEDGER (no rule removes an entry) and therefore the delta
  bookkeeping: any later state that still carries the abandoned
  mid-state's ledger, whose scope is unchanged, and whose committed
  source grew only by entries with coordinates STRICTLY BEYOND the
  frontier computes --- as its own current batch --- exactly the
  abandoned window's remainder.  Status and epoch are deliberately
  unconstrained: Recover, Resume, and a fresh crash move exactly
  those.  The two section-20 premises do exactly their landed jobs:
  the NAMED ascending premise makes the abandoned window's remainder
  law hold, and the beyond-the-frontier bound is the landed
  frontier-robustness condition (its necessity is the landed control
  @{thm [source] frontier_bound_load_bearing}) --- commits at or
  below the frontier in a later epoch genuinely change the new
  window's batch, which is why no uniform cross-window law is
  claimed and the re-founding below is the honest general form.
\<close>

theorem ss_new_window_delta_refound:
  assumes asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
      and src': "exec_src_hist (dwe_core t2) = exec_src_hist (dwe_core t) @ E"
      and scope': "exec_scope (dwe_core t2) = exec_scope (dwe_core t)"
      and em': "dwe_emitted t2 = dwe_emitted (ss_escape_mid f n t)"
      and beyond: "\<forall>x \<in> set E. f < fst x"
  shows "sink_delta f t2 = drop n (sink_delta f t)"
proof -
  have src'': "exec_src_hist (dwe_core t2)
                 = exec_src_hist (dwe_core (ss_escape_mid f n t)) @ E"
    using src' by simp
  have scope'': "exec_scope (dwe_core t2)
                   = exec_scope (dwe_core (ss_escape_mid f n t))"
    using scope' by simp
  have "sink_delta f t2 = sink_delta f (ss_escape_mid f n t)"
    by (rule sink_delta_source_append_beyond_frontier[OF src'' scope'' em' beyond])
  also have "\<dots> = drop n (sink_delta f t)"
    by (rule ss_escape_mid_delta[OF asc])
  finally show ?thesis .
qed

subsection \<open>The two-window witness: abandon, Resume, re-found, complete\<close>

text \<open>
  The whole abandonment story, end to end on the machine: commit two
  events (no publishes --- both deliveries owed), crash; WINDOW 1
  fires one of the two owed entries and is ABANDONED (Recover without
  the completing heal); Resume opens epoch 1; a fresh crash opens
  WINDOW 2, whose own batch is exactly the abandoned remainder; the
  new window fires it --- stamped with the NEW epoch --- and completes
  with the bare heal.  End state: recomputed delta empty, effect-safe,
  ledger duplicate-free, ONE emission per window, each carrying its
  own window's epoch.
\<close>

definition cw_run_w :: "(nat, nat) dwe_state" where
  "cw_run_w = mkT (mkC [(ec1, e1), (ec2, e2)] [] [] {} Running) [] 0"

definition cw0_w :: "(nat, nat) dwe_state" where
  "cw0_w = mkT (mkC [(ec1, e1), (ec2, e2)] [] [] {} (Crashed ec2)) [] 0"

definition cw_mid_w :: "(nat, nat) dwe_state" where
  "cw_mid_w = mkT (mkC [(ec1, e1), (ec2, e2)] [] [] {} (Crashed ec2))
                  [(2, 0, ec1, e1)] 0"

definition cw_rec_w :: "(nat, nat) dwe_state" where
  "cw_rec_w = mkT (mkC [(ec1, e1), (ec2, e2)] [] [] {} Recovered)
                  [(2, 0, ec1, e1)] 0"

definition cw_run1_w :: "(nat, nat) dwe_state" where
  "cw_run1_w = mkT (mkC [(ec1, e1), (ec2, e2)] [] [] {} Running)
                   [(2, 0, ec1, e1)] 1"

definition cw1_w :: "(nat, nat) dwe_state" where
  "cw1_w = mkT (mkC [(ec1, e1), (ec2, e2)] [] [] {} (Crashed ec2))
               [(2, 0, ec1, e1)] 1"

definition cw_mid2_w :: "(nat, nat) dwe_state" where
  "cw_mid2_w = mkT (mkC [(ec1, e1), (ec2, e2)] [] [] {} (Crashed ec2))
                   [(2, 0, ec1, e1), (2, 1, ec2, e2)] 1"

definition cw_done_w :: "(nat, nat) dwe_state" where
  "cw_done_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)] [] {}
                      Recovered)
                   [(2, 0, ec1, e1), (2, 1, ec2, e2)] 1"

text \<open>Wellformedness and admissibility along the chain.\<close>

lemma wf_cw_run: "wellformed_exec_state (dwe_core cw_run_w)"
  by (simp add: cw_run_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_pair)

lemma wf_cw_mid: "wellformed_exec_state (dwe_core cw_mid_w)"
  by (simp add: cw_mid_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_pair)

lemma wf_cw_run1: "wellformed_exec_state (dwe_core cw_run1_w)"
  by (simp add: cw_run1_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_pair)

lemma g_W1_src2:
  "exec_label_preserves_history_wf (dwe_core W1) (DoSource ec2 e2)"
  by (simp add: W1_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_cw_run_crash:
  "exec_label_preserves_history_wf (dwe_core cw_run_w) (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma g_cw_mid_recover:
  "exec_label_preserves_history_wf (dwe_core cw_mid_w) Recover"
  by (simp add: exec_label_preserves_history_wf_def)

lemma g_cw_run1_crash:
  "exec_label_preserves_history_wf (dwe_core cw_run1_w) (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

text \<open>Equation-form intro rule for the locked core's Recover (the
  witness-scaffolding pattern; the Segments lane banks its own twin
  @{text recoverI} outside this import cone --- the corpus's disclosed
  forced-duplication pattern for ROOT-sibling lanes).\<close>

lemma ss_recoverI:
  assumes "exec_status s = Crashed c"
      and "s' = s\<lparr>exec_status := Recovered\<rparr>"
  shows "dw_exec_step s Recover s'"
  unfolding assms(2) by (rule dw_exec_step.recover[OF assms(1)])

text \<open>The steps of the chain.\<close>

lemma cw_ws1: "dwe_step W1 (DoSource ec2 e2) cw_run_w"
proof -
  have c: "dw_exec_step (dwe_core W1) (DoSource ec2 e2) (dwe_core cw_run_w)"
    by (rule do_sourceI) (simp_all add: W1_def cw_run_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: W1_def cw_run_w_def mkT_def)
qed

lemma cw_ws2: "dwe_step cw_run_w (Crash ec2) cw0_w"
proof -
  have c: "dw_exec_step (dwe_core cw_run_w) (Crash ec2) (dwe_core cw0_w)"
    by (rule crashI) (simp_all add: cw_run_w_def cw0_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: cw_run_w_def cw0_w_def mkT_def)
qed

lemma cw_fire1: "ss_fire_one ec2 (ec1, e1) cw0_w cw_mid_w"
  by (rule ss_fire_oneI)
     (simp_all add: cw0_w_def cw_mid_w_def mkT_def mkC_def
                    replay_down_hist_def e1_def e2_def ec_defs
                    eval_nat_numeral)

lemma cw_ws3: "dwe_step cw_mid_w Recover cw_rec_w"
proof -
  have c: "dw_exec_step (dwe_core cw_mid_w) Recover (dwe_core cw_rec_w)"
    by (rule ss_recoverI) (simp_all add: cw_mid_w_def cw_rec_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: cw_mid_w_def cw_rec_w_def mkT_def)
qed

lemma cw_res: "dwe_resume cw_rec_w cw_run1_w"
  by (simp add: dwe_resume_def cw_rec_w_def cw_run1_w_def mkT_def mkC_def)

lemma cw_ws4: "dwe_step cw_run1_w (Crash ec2) cw1_w"
proof -
  have c: "dw_exec_step (dwe_core cw_run1_w) (Crash ec2) (dwe_core cw1_w)"
    by (rule crashI) (simp_all add: cw_run1_w_def cw1_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: cw_run1_w_def cw1_w_def mkT_def)
qed

lemma cw_fire2: "ss_fire_one ec2 (ec2, e2) cw1_w cw_mid2_w"
  by (rule ss_fire_oneI)
     (simp_all add: cw1_w_def cw_mid2_w_def mkT_def mkC_def
                    replay_down_hist_def e1_def e2_def ec_defs
                    eval_nat_numeral)

lemma cw_rec2: "emitting_reconcile 2 cw_mid2_w ec2 cw_done_w"
  by (simp add: emitting_reconcile_def cw_mid2_w_def cw_done_w_def
                mkT_def mkC_def replay_down_hist_def e1_def e2_def ec_defs
                eval_nat_numeral)

text \<open>Trace assembly and reachability of every window state.\<close>

lemma cw_t1: "dwe_ss_temporal_trace W0 [SS_Label (DoSource ec1 e1)] W1"
  by (rule dwe_ss_temporal_trace.dwe_ss_label_step[OF wf_W0 g_W0_src1 ws1
        dwe_ss_temporal_trace.dwe_ss_refl])

lemma cw_t2: "dwe_ss_temporal_trace W1 [SS_Label (DoSource ec2 e2)] cw_run_w"
  by (rule dwe_ss_temporal_trace.dwe_ss_label_step[OF wf_W1 g_W1_src2 cw_ws1
        dwe_ss_temporal_trace.dwe_ss_refl])

lemma cw_t3: "dwe_ss_temporal_trace cw_run_w [SS_Label (Crash ec2)] cw0_w"
  by (rule dwe_ss_temporal_trace.dwe_ss_label_step[OF wf_cw_run g_cw_run_crash
        cw_ws2 dwe_ss_temporal_trace.dwe_ss_refl])

lemma cw_t4: "dwe_ss_temporal_trace cw0_w [SS_Fire ec2 (ec1, e1)] cw_mid_w"
  by (rule dwe_ss_temporal_trace.dwe_ss_fire_step[OF cw_fire1
        dwe_ss_temporal_trace.dwe_ss_refl])

lemma cw_t5: "dwe_ss_temporal_trace cw_mid_w [SS_Label Recover] cw_rec_w"
  by (rule dwe_ss_temporal_trace.dwe_ss_label_step[OF wf_cw_mid g_cw_mid_recover
        cw_ws3 dwe_ss_temporal_trace.dwe_ss_refl])

lemma cw_t6: "dwe_ss_temporal_trace cw_rec_w [SS_Resume] cw_run1_w"
  by (rule dwe_ss_temporal_trace.dwe_ss_resume_step[OF cw_res
        dwe_ss_temporal_trace.dwe_ss_refl])

lemma cw_t7: "dwe_ss_temporal_trace cw_run1_w [SS_Label (Crash ec2)] cw1_w"
  by (rule dwe_ss_temporal_trace.dwe_ss_label_step[OF wf_cw_run1 g_cw_run1_crash
        cw_ws4 dwe_ss_temporal_trace.dwe_ss_refl])

lemma cw_t8: "dwe_ss_temporal_trace cw1_w [SS_Fire ec2 (ec2, e2)] cw_mid2_w"
  by (rule dwe_ss_temporal_trace.dwe_ss_fire_step[OF cw_fire2
        dwe_ss_temporal_trace.dwe_ss_refl])

lemma cw_t9: "dwe_ss_temporal_trace cw_mid2_w [SS_Reconcile 2 ec2] cw_done_w"
  by (rule dwe_ss_temporal_trace.dwe_ss_reconcile_step[OF cw_rec2
        dwe_ss_temporal_trace.dwe_ss_refl])

lemma cw_reach_cw0: "dwe_ss_reachable cw0_w"
  by (rule dwe_ss_reachable_trace_ext[OF
        dwe_ss_reachable_trace_ext[OF
          dwe_ss_reachable_trace_ext[OF
            ss_reachable_of_reachable[OF reach_W0] cw_t1] cw_t2] cw_t3])

lemma cw_reach_mid: "dwe_ss_reachable cw_mid_w"
  by (rule dwe_ss_reachable_trace_ext[OF cw_reach_cw0 cw_t4])

lemma cw_reach_cw1: "dwe_ss_reachable cw1_w"
  by (rule dwe_ss_reachable_trace_ext[OF
        dwe_ss_reachable_trace_ext[OF
          dwe_ss_reachable_trace_ext[OF cw_reach_mid cw_t5] cw_t6] cw_t7])

lemma cw_reach_done: "dwe_ss_reachable cw_done_w"
  by (rule dwe_ss_reachable_trace_ext[OF
        dwe_ss_reachable_trace_ext[OF cw_reach_cw1 cw_t8] cw_t9])

text \<open>Window bookkeeping, computed.  Window 1's fire is the take-1
  stopped episode of the batch (the mid-state IS
  @{const ss_escape_mid}); the abandoned remainder re-founds as
  window 2's own batch --- an instance of
  @{thm [source] ss_new_window_delta_refound} with the empty
  between-window source extension.\<close>

lemma cw_asc: "strictly_ascending_source (exec_src_hist (dwe_core cw0_w))"
  by (simp add: strictly_ascending_source_def cw0_w_def mkT_def mkC_def
                e1_def e2_def ec_defs)

lemma cw_batch: "sink_delta ec2 cw0_w = [(ec1, e1), (ec2, e2)]"
  by (simp add: sink_delta_def cw0_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs)

lemma cw_mid_is_escape_mid: "cw_mid_w = ss_escape_mid ec2 1 cw0_w"
  by (simp add: cw_mid_w_def cw0_w_def ss_escape_mid_def mkT_def mkC_def
                sink_delta_def replay_down_hist_def e1_def e2_def ec_defs
                eval_nat_numeral)

lemma cw_mid_delta: "sink_delta ec2 cw_mid_w = [(ec2, e2)]"
  by (simp add: sink_delta_def cw_mid_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs)

lemma cw1_refound: "sink_delta ec2 cw1_w = drop 1 (sink_delta ec2 cw0_w)"
proof -
  have src': "exec_src_hist (dwe_core cw1_w)
                = exec_src_hist (dwe_core cw0_w) @ []"
    by (simp add: cw1_w_def cw0_w_def mkT_def mkC_def)
  have scope': "exec_scope (dwe_core cw1_w) = exec_scope (dwe_core cw0_w)"
    by (simp add: cw1_w_def cw0_w_def mkT_def mkC_def)
  have em': "dwe_emitted cw1_w = dwe_emitted (ss_escape_mid ec2 1 cw0_w)"
    unfolding cw_mid_is_escape_mid[symmetric]
    by (simp add: cw1_w_def cw_mid_w_def mkT_def)
  show ?thesis
    by (rule ss_new_window_delta_refound[OF cw_asc src' scope' em']) simp
qed

lemma cw_done_delta: "sink_delta ec2 cw_done_w = []"
  by (simp add: sink_delta_def cw_done_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs)

lemma cw_done_safe: "\<not> effect_unsafe cw_done_w"
  by (simp add: effect_unsafe_def premature_def duplicate_def justified_at_def
                cw_done_w_def mkT_def mkC_def e1_def e2_def ec_defs
                eval_nat_numeral)

lemma cw_done_epochs: "map e_epoch (dwe_emitted cw_done_w) = [0, 1]"
  by (simp add: cw_done_w_def mkT_def)

text \<open>
  THE CROSS-WINDOW PACKAGE.  Everything above in one certificate: the
  abandoned window's fire is a stopped take-1 episode; its mid-state
  is ss-reachable; the new window (one Recover, one Resume, one crash
  later --- a different epoch) re-founds the delta at exactly the
  abandoned remainder; completing there empties the recomputed delta,
  effect-safely; and each window's emission carries its own epoch.
\<close>

theorem ss_cross_window_witness:
  "dwe_ss_reachable cw0_w
 \<and> strictly_ascending_source (exec_src_hist (dwe_core cw0_w))
 \<and> ss_fire_one ec2 (ec1, e1) cw0_w cw_mid_w
 \<and> cw_mid_w = ss_escape_mid ec2 1 cw0_w
 \<and> dwe_ss_reachable cw_mid_w
 \<and> dwe_ss_temporal_trace cw_mid_w
     [SS_Label Recover, SS_Resume, SS_Label (Crash ec2)] cw1_w
 \<and> dwe_epoch cw1_w = Suc (dwe_epoch cw_mid_w)
 \<and> sink_delta ec2 cw1_w = drop 1 (sink_delta ec2 cw0_w)
 \<and> dwe_ss_temporal_trace cw1_w [SS_Fire ec2 (ec2, e2), SS_Reconcile 2 ec2]
     cw_done_w
 \<and> sink_delta ec2 cw_done_w = []
 \<and> \<not> effect_unsafe cw_done_w
 \<and> map e_epoch (dwe_emitted cw_done_w) = [0, 1]
 \<and> dwe_ss_reachable cw_done_w"
proof -
  have mid_to_cw1: "dwe_ss_temporal_trace cw_mid_w
                      [SS_Label Recover, SS_Resume, SS_Label (Crash ec2)] cw1_w"
    using dwe_ss_temporal_trace_append[OF cw_t5
            dwe_ss_temporal_trace_append[OF cw_t6 cw_t7]]
    by simp
  have cw1_to_done: "dwe_ss_temporal_trace cw1_w
                       [SS_Fire ec2 (ec2, e2), SS_Reconcile 2 ec2] cw_done_w"
    using dwe_ss_temporal_trace_append[OF cw_t8 cw_t9] by simp
  have epochs: "dwe_epoch cw1_w = Suc (dwe_epoch cw_mid_w)"
    by (simp add: cw1_w_def cw_mid_w_def mkT_def)
  show ?thesis
    using cw_reach_cw0 cw_asc cw_fire1 cw_mid_is_escape_mid cw_reach_mid
          mid_to_cw1 epochs cw1_refound cw1_to_done cw_done_delta
          cw_done_safe cw_done_epochs cw_reach_done
    by blast
qed

text \<open>
  THE SCOPE CONTROL: the section-20 stamp-constant cumulative
  footprint does NOT extend across windows.  Within one window the
  whole loop's ledger extension is one stamped map at one (stamp,
  epoch) --- @{thm [source] partial_redrive_rounds_emitted}.  Across
  the abandonment the two-window ledger above carries emission epochs
  0 AND 1, so NO single stamped map of any batch equals it: the
  per-window scoping of the rounds laws is load-bearing, not
  cautious phrasing.
\<close>

theorem ss_cross_window_stamp_footprint_control:
  "\<not> (\<exists>st ep B. dwe_emitted cw_done_w
        = dwe_emitted cw0_w @ map (\<lambda>(c, e). (st, ep, c, e)) B)"
proof
  assume "\<exists>st ep B. dwe_emitted cw_done_w
            = dwe_emitted cw0_w @ map (\<lambda>(c, e). (st, ep, c, e)) B"
  then obtain st ep B
    where eq: "dwe_emitted cw_done_w
                 = dwe_emitted cw0_w @ map (\<lambda>(c, e). (st, ep, c, e)) B"
    by blast
  have "map e_epoch (dwe_emitted cw_done_w) = map (\<lambda>p. ep) B"
    unfolding eq
    by (simp add: cw0_w_def mkT_def e_epoch_def)
  then have "map (\<lambda>p. ep) B = [0, 1]"
    by (simp add: cw_done_epochs)
  then have "(0 :: nat) \<in> set (map (\<lambda>p. ep) B)"
        and "(1 :: nat) \<in> set (map (\<lambda>p. ep) B)"
    by simp_all
  then show False by auto
qed


section \<open>The discipline twin: T2.8 on the variant, one singleton guard\<close>

text \<open>
  The variant's disciplined traces: the four mirrored rule kinds carry
  the LANDED discipline's guards verbatim (the rule bodies are the
  landed relations, so the landed per-rule preservation lemmas apply
  unchanged), Resume stays guard-free, and the new fire rule carries
  ONE guard --- the fired entry is fresh against the current ledger.
  That guard is the landed reconcile-suffix guard RESTRICTED TO
  SINGLETONS: for the one-element suffix @{term "[p]"}, internal
  distinctness is trivially true and ledger-freshness is exactly
  @{term "p \<notin> e_payload ` set (dwe_emitted t)"} --- the same premise
  class, at batch size one, never a new one.  Fire-time justification
  needs no guard on fires at all: it is the RULE's own physics
  (@{thm [source] ss_fire_emission_justified} --- fires are
  replay-bounded by construction).
\<close>

inductive ss_disciplined_trace
  :: "(nat, nat) dwe_state \<Rightarrow> ss_action list \<Rightarrow> (nat, nat) dwe_state \<Rightarrow> bool"
where
  ssd_refl:
    "ss_disciplined_trace t [] t"
| ssd_nonpub:
    "\<lbrakk>dwe_step t a t';
      wellformed_exec_state (dwe_core t);
      exec_label_preserves_history_wf (dwe_core t) a;
      \<forall>c e. a \<noteq> DoDownstream c e;
      ss_disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     ss_disciplined_trace t (SS_Label a # as) t''"
| ssd_publish:
    "\<lbrakk>dwe_step t (DoDownstream c e) t';
      wellformed_exec_state (dwe_core t);
      exec_label_preserves_history_wf (dwe_core t) (DoDownstream c e);
      (c, e) \<in> set (exec_src_hist (dwe_core t));
      (c, e) \<notin> e_payload ` set (dwe_emitted t);
      ss_disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     ss_disciplined_trace t (SS_Label (DoDownstream c e) # as) t''"
| ssd_reconcile:
    "\<lbrakk>emitting_reconcile m t f t';
      distinct (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                          (exec_scope (dwe_core t)) f));
      set (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                     (exec_scope (dwe_core t)) f))
        \<inter> e_payload ` set (dwe_emitted t) = {};
      ss_disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     ss_disciplined_trace t (SS_Reconcile m f # as) t''"
| ssd_resume:
    "\<lbrakk>dwe_resume t t';
      ss_disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     ss_disciplined_trace t (SS_Resume # as) t''"
| ssd_fire:
    "\<lbrakk>ss_fire_one f p t t';
      p \<notin> e_payload ` set (dwe_emitted t);
      ss_disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     ss_disciplined_trace t (SS_Fire f p # as) t''"

lemma ss_disciplined_trace_append:
  assumes "ss_disciplined_trace t as t'"
      and "ss_disciplined_trace t' bs t''"
  shows "ss_disciplined_trace t (as @ bs) t''"
  using assms
  by (induction rule: ss_disciplined_trace.induct)
     (auto intro: ss_disciplined_trace.intros)

text \<open>The twin restricts the SCHEDULER only: every disciplined variant
  run is a genuine variant trace.\<close>

lemma ss_disciplined_imp_ss_temporal:
  assumes "ss_disciplined_trace t acts t'"
  shows "dwe_ss_temporal_trace t acts t'"
  using assms
  by (induction rule: ss_disciplined_trace.induct)
     (auto intro: dwe_ss_temporal_trace.intros)

text \<open>The LANDED discipline embeds: the twin extends it conservatively
  (same guards on the mirrored kinds, one new rule) --- the discipline
  analogue of @{thm [source] cyclic_traces_embed}.\<close>

theorem disciplined_traces_embed:
  assumes "disciplined_trace t acts t'"
  shows "ss_disciplined_trace t (map lift_action acts) t'"
  using assms
proof (induction rule: disciplined_trace.induct)
  case (disciplined_refl t)
  then show ?case by (simp add: ss_disciplined_trace.ssd_refl)
next
  case (disciplined_nonpub t a t' as t'')
  then show ?case
    by (auto intro: ss_disciplined_trace.ssd_nonpub)
next
  case (disciplined_publish t c e t' as t'')
  then show ?case
    by (auto intro: ss_disciplined_trace.ssd_publish)
next
  case (disciplined_reconcile m t f t' as t'')
  then show ?case
    by (auto intro: ss_disciplined_trace.ssd_reconcile)
next
  case (disciplined_resume t t' as t'')
  then show ?case
    by (auto intro: ss_disciplined_trace.ssd_resume)
qed

subsection \<open>Singleton intro helpers\<close>

lemma ssd_fire_singleI:
  assumes "ss_fire_one f p t t'"
      and "p \<notin> e_payload ` set (dwe_emitted t)"
  shows "ss_disciplined_trace t [SS_Fire f p] t'"
  by (rule ss_disciplined_trace.ssd_fire[OF assms ss_disciplined_trace.ssd_refl])

lemma ssd_reconcile_singleI:
  assumes "emitting_reconcile m t f t'"
      and "distinct (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                               (exec_scope (dwe_core t)) f))"
      and "set (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                          (exec_scope (dwe_core t)) f))
             \<inter> e_payload ` set (dwe_emitted t) = {}"
  shows "ss_disciplined_trace t [SS_Reconcile m f] t'"
  by (rule ss_disciplined_trace.ssd_reconcile[OF assms
        ss_disciplined_trace.ssd_refl])

lemma ssd_resume_singleI:
  assumes "dwe_resume t t'"
  shows "ss_disciplined_trace t [SS_Resume] t'"
  by (rule ss_disciplined_trace.ssd_resume[OF assms
        ss_disciplined_trace.ssd_refl])

subsection \<open>Safety preservation: the one new case\<close>

text \<open>A guarded fire preserves effect safety: the fired entry is
  justified at its own fire-time stamp BY THE RULE
  (@{thm [source] ss_fire_emission_justified}), and the singleton
  guard supplies exactly the freshness that keeps the payload
  projection distinct.  The mirrored rule kinds are discharged by the
  LANDED preservation lemmas verbatim in the induction below --- this
  lemma is the only new mathematics of the twin.\<close>

lemma ss_fire_preserves_effect_safe:
  assumes fire: "ss_fire_one f p t t'"
      and fresh: "p \<notin> e_payload ` set (dwe_emitted t)"
      and safe: "\<not> effect_unsafe t"
  shows "\<not> effect_unsafe t'"
proof -
  have em: "dwe_emitted t' = dwe_emitted t
              @ [(length (exec_src_hist (dwe_core t)), dwe_epoch t, p)]"
    by (rule ss_fire_one_emitted[OF fire])
  have src: "exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t)"
    by (rule ss_fire_one_src_same[OF fire])
  have just_new: "justified_at (exec_src_hist (dwe_core t'))
                    (length (exec_src_hist (dwe_core t)), dwe_epoch t, p)"
    by (rule ss_fire_emission_justified[OF fire])
  have old_just: "\<forall>x \<in> set (dwe_emitted t).
                    justified_at (exec_src_hist (dwe_core t)) x"
    and old_dist: "distinct (map e_payload (dwe_emitted t))"
    using safe by (auto simp: effect_safe_alt)
  have just': "\<forall>x \<in> set (dwe_emitted t').
                 justified_at (exec_src_hist (dwe_core t')) x"
    using old_just just_new by (auto simp: em src)
  have dist': "distinct (map e_payload (dwe_emitted t'))"
    using old_dist fresh by (simp add: em)
  show ?thesis
    using just' dist' by (simp add: effect_safe_alt)
qed

lemma ss_disciplined_trace_preserves_effect_safe:
  assumes "ss_disciplined_trace t acts t'"
      and "\<not> effect_unsafe t"
  shows "\<not> effect_unsafe t'"
  using assms
proof (induction rule: ss_disciplined_trace.induct)
  case (ssd_refl t)
  then show ?case .
next
  case (ssd_nonpub t a t' as t'')
  have "\<not> effect_unsafe t'"
    by (rule nonpub_preserves_effect_safe
        [OF ssd_nonpub.hyps(1) ssd_nonpub.hyps(4) ssd_nonpub.prems])
  then show ?case by (rule ssd_nonpub.IH)
next
  case (ssd_publish t c e t' as t'')
  have "\<not> effect_unsafe t'"
    by (rule publish_preserves_effect_safe
        [OF ssd_publish.hyps(1) ssd_publish.hyps(4) ssd_publish.hyps(5)
            ssd_publish.prems])
  then show ?case by (rule ssd_publish.IH)
next
  case (ssd_reconcile m t f t' as t'')
  have "\<not> effect_unsafe t'"
    by (rule reconcile_preserves_effect_safe
        [OF ssd_reconcile.hyps(1) ssd_reconcile.hyps(2) ssd_reconcile.hyps(3)
            ssd_reconcile.prems])
  then show ?case by (rule ssd_reconcile.IH)
next
  case (ssd_resume t t' as t'')
  have "\<not> effect_unsafe t'"
    using resume_preserves_effect_safe[OF ssd_resume.hyps(1)]
          ssd_resume.prems
    by simp
  then show ?case by (rule ssd_resume.IH)
next
  case (ssd_fire f p t t' as t'')
  have "\<not> effect_unsafe t'"
    by (rule ss_fire_preserves_effect_safe
        [OF ssd_fire.hyps(1) ssd_fire.hyps(2) ssd_fire.prems])
  then show ?case by (rule ssd_fire.IH)
qed

text \<open>
  HEADLINE (the discipline twin).  Every disciplined variant trace
  from ANY initial state ends effect-safe.  The premises are the
  landed three guards plus the singleton fresh-fire guard; Resume
  carries none.  STATEMENT AUDIT, in the landed S4c style: no premise
  mentions @{const dwe_epoch}, @{const e_epoch}, or an advertised
  frontier; the only new guard is the reconcile-suffix guard at batch
  size one; the variant forced NO new premise class.
\<close>

theorem ss_general_positive_discipline:
  assumes "ss_disciplined_trace (dwe_init b K fin) acts t"
  shows "\<not> effect_unsafe t"
proof -
  have "\<not> effect_unsafe (dwe_init b K fin)"
    by (simp add: effect_unsafe_def premature_def duplicate_def dwe_init_def)
  then show ?thesis
    by (rule ss_disciplined_trace_preserves_effect_safe[OF assms])
qed

corollary ss_general_positive_discipline_pinned:
  assumes "ss_disciplined_trace
             (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2) acts t"
  shows "\<not> effect_unsafe t"
  by (rule ss_general_positive_discipline[OF assms])

corollary ss_disciplined_runs_are_ss_reachable:
  assumes "ss_disciplined_trace
             (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2) acts t"
  shows "dwe_ss_reachable t"
  using ss_disciplined_imp_ss_temporal[OF assms]
  unfolding dwe_ss_reachable_def by blast

subsection \<open>Non-vacuity: a disciplined variant run with fires and a Resume\<close>

text \<open>
  The witness re-runs the landed cycle-exercising disciplined run with
  its reconcile step DECOMPOSED into machine steps: the landed loaded
  window (six disciplined label steps to @{const t_mid_w}), then a
  GUARDED FIRE of the missing delivery --- passing through the D1
  separation witness @{const ss_inflight_w}, a state the landed
  machine provably cannot reach --- then the completing bare heal
  (the landed rule at cursor length-of-replay, guards trivially
  satisfied), landing EXACTLY on @{const t_safe_w}, the landed m = 1
  reconcile's own post-state (the witness-level face of
  @{thm [source] atomic_redrive_decomposes}).  From there the landed
  epilogue verbatim: Resume into epoch 1 and a fresh disciplined
  publish of @{const e3}.  The run ends Running, epoch 1, three-entry
  ledger spanning both epochs, effect-safe --- the twin is inhabited
  by a run that genuinely uses the new rule AND the cycle.
\<close>

lemma ss_fire_guard_inflight:
  "(ec2, e2) \<notin> e_payload ` set (dwe_emitted t_mid_w)"
  by (simp add: t_mid_w_def mkT_def e1_def e2_def ec_defs)

lemma ss_rec_complete: "emitting_reconcile 2 ss_inflight_w ec2 t_safe_w"
  by (simp add: emitting_reconcile_def ss_inflight_w_def t_safe_w_def
                mkT_def mkC_def replay_down_hist_def e1_def e2_def ec_defs
                eval_nat_numeral)

lemma ss_rec_complete_suffix_distinct:
  "distinct (drop 2 (replay_down_hist (exec_src_hist (dwe_core ss_inflight_w))
                       (exec_scope (dwe_core ss_inflight_w)) ec2))"
  by (simp add: ss_inflight_w_def mkT_def mkC_def replay_down_hist_def
                e1_def e2_def ec_defs eval_nat_numeral)

lemma ss_rec_complete_suffix_fresh:
  "set (drop 2 (replay_down_hist (exec_src_hist (dwe_core ss_inflight_w))
                  (exec_scope (dwe_core ss_inflight_w)) ec2))
     \<inter> e_payload ` set (dwe_emitted ss_inflight_w) = {}"
  by (simp add: ss_inflight_w_def mkT_def mkC_def replay_down_hist_def
                e1_def e2_def ec_defs eval_nat_numeral)

lemma ssd_sg1: "ss_disciplined_trace W0 [SS_Label (DoSource ec1 e1)] W1"
  using disciplined_traces_embed[OF dv_sg1] by simp

lemma ssd_sg2:
  "ss_disciplined_trace W1 [SS_Label (EnqueueDownstream ec1 e1)] W2"
  using disciplined_traces_embed[OF dv_sg2] by simp

lemma ssd_sg3: "ss_disciplined_trace W2 [SS_Label (DoDownstream ec1 e1)] W3"
  using disciplined_traces_embed[OF dv_sg3] by simp

lemma ssd_sg4: "ss_disciplined_trace W3 [SS_Label (DoSource ec2 e2)] W4"
  using disciplined_traces_embed[OF dv_sg4] by simp

lemma ssd_sg5:
  "ss_disciplined_trace W4 [SS_Label (EnqueueDownstream ec2 e2)] W5"
  using disciplined_traces_embed[OF dv_sg5] by simp

lemma ssd_sg6: "ss_disciplined_trace W5 [SS_Label (Crash ec2)] t_mid_w"
  using disciplined_traces_embed[OF dv_sg6] by simp

lemma ssd_sg7f:
  "ss_disciplined_trace t_mid_w [SS_Fire ec2 (ec2, e2)] ss_inflight_w"
  by (rule ssd_fire_singleI[OF fire_inflight ss_fire_guard_inflight])

lemma ssd_sg7h:
  "ss_disciplined_trace ss_inflight_w [SS_Reconcile 2 ec2] t_safe_w"
  by (rule ssd_reconcile_singleI[OF ss_rec_complete
        ss_rec_complete_suffix_distinct ss_rec_complete_suffix_fresh])

lemma ssd_sg8: "ss_disciplined_trace t_safe_w [SS_Resume] d_run_w"
  by (rule ssd_resume_singleI[OF res_d])

lemma ssd_sg9:
  "ss_disciplined_trace d_run_w [SS_Label (DoSource ec3 e3)] d_src3_w"
  using disciplined_traces_embed[OF dv_sg9] by simp

lemma ssd_sg10:
  "ss_disciplined_trace d_src3_w [SS_Label (EnqueueDownstream ec3 e3)] d_enq3_w"
  using disciplined_traces_embed[OF dv_sg10] by simp

lemma ssd_sg11:
  "ss_disciplined_trace d_enq3_w [SS_Label (DoDownstream ec3 e3)] d_pub3_w"
  using disciplined_traces_embed[OF dv_sg11] by simp

lemma ssd_witness_raw:
  "ss_disciplined_trace W0
     (map SS_Label witness_labels
      @ [SS_Fire ec2 (ec2, e2), SS_Reconcile 2 ec2, SS_Resume,
         SS_Label (DoSource ec3 e3), SS_Label (EnqueueDownstream ec3 e3),
         SS_Label (DoDownstream ec3 e3)])
     d_pub3_w"
  using ss_disciplined_trace_append[OF ssd_sg1
          ss_disciplined_trace_append[OF ssd_sg2
            ss_disciplined_trace_append[OF ssd_sg3
              ss_disciplined_trace_append[OF ssd_sg4
                ss_disciplined_trace_append[OF ssd_sg5
                  ss_disciplined_trace_append[OF ssd_sg6
                    ss_disciplined_trace_append[OF ssd_sg7f
                      ss_disciplined_trace_append[OF ssd_sg7h
                        ss_disciplined_trace_append[OF ssd_sg8
                          ss_disciplined_trace_append[OF ssd_sg9
                            ss_disciplined_trace_append[OF ssd_sg10
                              ssd_sg11]]]]]]]]]]]
  by (simp add: witness_labels_def)

lemma ssd_witness_init:
  "ss_disciplined_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
     (map SS_Label witness_labels
      @ [SS_Fire ec2 (ec2, e2), SS_Reconcile 2 ec2, SS_Resume,
         SS_Label (DoSource ec3 e3), SS_Label (EnqueueDownstream ec3 e3),
         SS_Label (DoDownstream ec3 e3)])
     d_pub3_w"
  using ssd_witness_raw unfolding W0_init .

theorem ss_discipline_nonvacuous:
  "ss_disciplined_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
     (map SS_Label witness_labels
      @ [SS_Fire ec2 (ec2, e2), SS_Reconcile 2 ec2, SS_Resume,
         SS_Label (DoSource ec3 e3), SS_Label (EnqueueDownstream ec3 e3),
         SS_Label (DoDownstream ec3 e3)])
     d_pub3_w
 \<and> genuinely_emitting d_pub3_w
 \<and> dwe_emitted d_pub3_w = [(1, 0, ec1, e1), (2, 0, ec2, e2), (3, 1, ec3, e3)]
 \<and> dwe_epoch d_pub3_w = 1
 \<and> exec_status (dwe_core d_pub3_w) = Running
 \<and> (\<exists>x \<in> set (dwe_emitted d_pub3_w). e_epoch x = 0)
 \<and> (\<exists>x \<in> set (dwe_emitted d_pub3_w). e_epoch x = 1)
 \<and> \<not> effect_unsafe d_pub3_w
 \<and> dwe_ss_reachable d_pub3_w"
  by (intro conjI ssd_witness_init d_pub3_emitting d_pub3_emitted d_pub3_epoch
        d_pub3_running d_pub3_ep0 d_pub3_ep1 d_pub3_safe
        ss_reachable_of_reachable[OF reach_d_pub3])


section \<open>Load-bearing controls: both new premises bite at machine level\<close>

text \<open>
  CONTROL 1 (the NAMED ascending premise bites through the machine
  realization).  The crashed twin of the landed WF-H1-legal
  equal-coordinate control state: one business payload committed
  twice (the landed aliasing axis), no emissions, status Crashed.  A
  GENUINE machine fire of the batch head --- which IS the take-1
  stopped episode, state-level --- payload-blocks BOTH committed
  occurrences: the recomputed delta is empty instead of the
  one-element remainder, so @{thm [source] ss_escape_mid_delta} fails
  without @{const strictly_ascending_source}: exactly the landed
  section-18/20 controls (@{thm [source] partial_append_asc_load_bearing},
  @{thm [source] rounds_asc_load_bearing}) surfacing at machine level.
  As with those controls, the state is a state of the type, not
  claimed reachable --- matching the laws' premise set.
\<close>

definition ss_psl_w :: "(nat, nat) dwe_state" where
  "ss_psl_w = mkT (mkC [(ec1, e1), (ec1, e1)] [] [] {} (Crashed ec1)) [] 0"

definition ss_psl_mid_w :: "(nat, nat) dwe_state" where
  "ss_psl_mid_w = mkT (mkC [(ec1, e1), (ec1, e1)] [] [] {} (Crashed ec1))
                      [(2, 0, ec1, e1)] 0"

lemma ss_psl_wf: "wellformed_src_history (exec_src_hist (dwe_core ss_psl_w))"
proof -
  have "exec_src_hist (dwe_core ss_psl_w) = [(ec1, e1), (ec1, e1)]"
    by (simp add: ss_psl_w_def mkT_def mkC_def)
  then show ?thesis using wfh_e1_pair_eq by simp
qed

lemma ss_psl_not_asc:
  "\<not> strictly_ascending_source (exec_src_hist (dwe_core ss_psl_w))"
  by (simp add: strictly_ascending_source_def ss_psl_w_def mkT_def mkC_def
                ec_defs)

lemma ss_psl_batch: "sink_delta ec1 ss_psl_w = [(ec1, e1), (ec1, e1)]"
  by (simp add: sink_delta_def ss_psl_w_def mkT_def mkC_def
                replay_down_hist_def e1_def ec_defs)

lemma ss_psl_fire: "ss_fire_one ec1 (ec1, e1) ss_psl_w ss_psl_mid_w"
  by (rule ss_fire_oneI)
     (simp_all add: ss_psl_w_def ss_psl_mid_w_def mkT_def mkC_def
                    replay_down_hist_def e1_def ec_defs eval_nat_numeral)

lemma ss_psl_mid_is_escape_mid: "ss_psl_mid_w = ss_escape_mid ec1 1 ss_psl_w"
  by (simp add: ss_psl_mid_w_def ss_psl_w_def ss_escape_mid_def mkT_def
                mkC_def sink_delta_def replay_down_hist_def e1_def ec_defs
                eval_nat_numeral)

lemma ss_psl_starves: "sink_delta ec1 ss_psl_mid_w = []"
  by (simp add: sink_delta_def ss_psl_mid_w_def mkT_def mkC_def
                replay_down_hist_def e1_def ec_defs)

theorem ss_fire_asc_load_bearing:
  "\<exists>(t :: (nat, nat) dwe_state) f p t' n.
     wellformed_src_history (exec_src_hist (dwe_core t))
   \<and> ss_fire_one f p t t'
   \<and> t' = ss_escape_mid f n t
   \<and> sink_delta f t' \<noteq> drop n (sink_delta f t)"
proof -
  have ne: "sink_delta ec1 ss_psl_mid_w \<noteq> drop 1 (sink_delta ec1 ss_psl_w)"
    by (simp add: ss_psl_starves ss_psl_batch)
  show ?thesis
    using ss_psl_wf ss_psl_fire ss_psl_mid_is_escape_mid ne by blast
qed

text \<open>
  CONTROL 2 (the singleton fresh-fire guard is load-bearing).  Drop
  ONLY the fire guard and the twin's conclusion fails at a reachable
  state: the pre-state @{const ss_inflight_w} is reached by a FULLY
  disciplined variant run (the witness prefix above), is effect-safe,
  and already carries the payload; re-firing it --- legal for the
  RULE, whose guards read only the frozen core --- lands in the D1
  refire state: a duplicate, effect-unsafe, and still ss-reachable.
  This is @{thm [source] ss_refire_duplicate_witness} re-packaged as
  the discipline-side control, exactly parallel to the landed
  publish-freshness control (control (b) of the landed T2.8 suite).
\<close>

theorem ss_fresh_fire_guard_load_bearing:
  "ss_disciplined_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
     (map SS_Label witness_labels @ [SS_Fire ec2 (ec2, e2)]) ss_inflight_w
 \<and> \<not> effect_unsafe ss_inflight_w
 \<and> ss_fire_one ec2 (ec2, e2) ss_inflight_w ss_refire_w
 \<and> (ec2, e2) \<in> e_payload ` set (dwe_emitted ss_inflight_w)
 \<and> duplicate ss_refire_w
 \<and> effect_unsafe ss_refire_w
 \<and> dwe_ss_reachable ss_refire_w"
proof -
  have pfx: "ss_disciplined_trace W0
               (map SS_Label witness_labels @ [SS_Fire ec2 (ec2, e2)])
               ss_inflight_w"
    using ss_disciplined_trace_append[OF ssd_sg1
            ss_disciplined_trace_append[OF ssd_sg2
              ss_disciplined_trace_append[OF ssd_sg3
                ss_disciplined_trace_append[OF ssd_sg4
                  ss_disciplined_trace_append[OF ssd_sg5
                    ss_disciplined_trace_append[OF ssd_sg6 ssd_sg7f]]]]]]
    by (simp add: witness_labels_def)
  have pfx_init: "ss_disciplined_trace
                    (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
                    (map SS_Label witness_labels @ [SS_Fire ec2 (ec2, e2)])
                    ss_inflight_w"
    using pfx unfolding W0_init .
  have viol: "(ec2, e2) \<in> e_payload ` set (dwe_emitted ss_inflight_w)"
    by (simp add: ss_inflight_w_def mkT_def)
  show ?thesis
    using pfx_init ss_inflight_safe fire_refire viol ss_refire_duplicate
          ss_refire_ss_reachable
    by (auto simp: effect_unsafe_def)
qed


section \<open>Verdict permanence on variant traces (the T2.12 profile)\<close>

text \<open>
  The landed T2.12 permanence corollary (@{text effect_verdict_permanent}
  of the effect-decider lane, a ROOT sibling outside this import cone)
  is, semantically, effect-unsafe persistence read through a
  computable verdict function.  Restated here at the variant's
  reachability in the corpus's disclosed ROOT-sibling style: for ANY
  verdict function that agrees with @{const effect_unsafe}, a positive
  verdict at an ss-reachable state is PERMANENT along every variant
  trace --- one new case (the fire) versus the landed statement,
  carried by D1's persistence twins.  The landed corollary is the
  instance at the landed decider through its own correctness iff
  (@{text dwe_effect_unsafe_decider_correct}, cited as prose).
\<close>

theorem ss_effect_verdict_permanent:
  assumes corr: "\<forall>s :: (nat, nat) dwe_state. V s \<longleftrightarrow> effect_unsafe s"
      and reach: "dwe_ss_reachable t"
      and pos: "V t"
      and tr: "dwe_ss_temporal_trace t acts t'"
  shows "V t'"
proof -
  have un: "effect_unsafe t" using corr pos by blast
  have "effect_unsafe t'"
    by (rule ss_effect_unsafe_trace_monotone[OF reach un tr])
  then show ?thesis using corr by blast
qed


end
